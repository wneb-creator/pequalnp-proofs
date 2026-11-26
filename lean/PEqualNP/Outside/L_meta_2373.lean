import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373

namespace Factoring
def edges : Finset (Fin 10 × Fin 10) :=
  {(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
   (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)}

def Adj (u v : Fin 10) : Prop := (u, v) ∈ edges ∨ (v, u) ∈ edges

def Independent (S : Finset (Fin 10)) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, ¬ Adj u v

def Cover (S : Finset (Fin 10)) : Prop :=
  ∀ e ∈ edges, e.1 ∈ S ∨ e.2 ∈ S

def Biclique (A B : Finset (Fin 10)) : Prop :=
  A.Nonempty ∧ B.Nonempty ∧ ∀ a ∈ A, ∀ b ∈ B, Adj a b

lemma edges_card : edges.card = 15 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma no_four_cycle : ∀ a b c d : Fin 10,
    a ≠ b → c ≠ d → Adj a c → Adj a d → Adj b c → ¬ Adj b d := by
  unfold Adj
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cover_card : ∀ S : Finset (Fin 10), Cover S → 6 ≤ S.card := by
  unfold Cover
  decide

lemma cover_six : Cover {0, 2, 3, 5, 6, 9} := by
  unfold Cover
  decide

lemma cover_six_card : ({0, 2, 3, 5, 6, 9} : Finset (Fin 10)).card = 6 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma independent_card : ∀ S : Finset (Fin 10), Independent S → S.card ≤ 4 := by
  unfold Independent Adj
  decide

lemma independent_four : Independent {1, 4, 7, 8} := by
  unfold Independent Adj
  decide

lemma independent_four_card : ({1, 4, 7, 8} : Finset (Fin 10)).card = 4 := by decide

lemma biclique_singleton {A B : Finset (Fin 10)} (h : Biclique A B) :
    A.card = 1 ∨ B.card = 1 := by
  obtain ⟨hA, hB, hcross⟩ := h
  by_cases ha : A.card ≤ 1
  · exact Or.inl (Nat.le_antisymm ha (Finset.one_le_card.mpr hA))
  · right
    have hb : B.card ≤ 1 := by
      by_contra hb
      obtain ⟨a, haA, b, hbA, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
      obtain ⟨c, hcB, d, hdB, hcd⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
      exact no_four_cycle a b c d hab hcd
        (hcross a haA c hcB) (hcross a haA d hdB)
        (hcross b hbA c hcB) (hcross b hbA d hdB)
    exact Nat.le_antisymm hb (Finset.one_le_card.mpr hB)

lemma biclique_center {A B : Finset (Fin 10)} (h : Biclique A B) :
    ∃ c : Fin 10, ∀ a ∈ A, ∀ b ∈ B, a = c ∨ b = c := by
  rcases biclique_singleton h with hA | hB
  · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hA
    refine ⟨c, ?_⟩
    intro a ha b hb
    left
    simpa only [hc, Finset.mem_singleton] using ha
  · obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hB
    refine ⟨c, ?_⟩
    intro a ha b hb
    right
    simpa only [hc, Finset.mem_singleton] using hb

lemma biclique_cover_count {ι : Type*} [Fintype ι]
    (A B : ι → Finset (Fin 10)) (hbi : ∀ i, Biclique (A i) (B i))
    (hcover : ∀ e ∈ edges, ∃ i,
      (e.1 ∈ A i ∧ e.2 ∈ B i) ∨ (e.2 ∈ A i ∧ e.1 ∈ B i)) :
    6 ≤ Fintype.card ι := by
  classical
  choose center hc using fun i => biclique_center (hbi i)
  let centers : Finset (Fin 10) := Finset.univ.image center
  have hmem (i : ι) : center i ∈ centers := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hcov : Cover centers := by
    intro e he
    obtain ⟨i, hi⟩ := hcover e he
    rcases hi with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · rcases hc i e.1 ha e.2 hb with hc1 | hc2
      · exact Or.inl (hc1 ▸ hmem i)
      · exact Or.inr (hc2 ▸ hmem i)
    · rcases hc i e.2 hb e.1 ha with hc2 | hc1
      · exact Or.inr (hc2 ▸ hmem i)
      · exact Or.inl (hc1 ▸ hmem i)
  calc
    6 ≤ centers.card := cover_card centers hcov
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = Fintype.card ι := Finset.card_univ




variable {n : ℕ}

def unionGate (L : List (Finset (Fin n))) (p : ℕ × ℕ) : Finset (Fin n) :=
  L.getD p.1 ∅ ∪ L.getD p.2 ∅

def unionRun : List (ℕ × ℕ) → List (Finset (Fin n)) → List (Finset (Fin n))
  | [], L => L
  | p :: ps, L => unionRun ps (L ++ [unionGate L p])

def unionCreated : List (ℕ × ℕ) → List (Finset (Fin n)) → List (Finset (Fin n))
  | [], _ => []
  | p :: ps, L => unionGate L p :: unionCreated ps (L ++ [unionGate L p])

def unionInputs (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun v : Fin n => {v}

def inside (S T : Finset (Fin n)) : Finset (Fin n) := if T ⊆ S then T else ∅

def productive (S T : Finset (Fin n)) : Bool := decide (T ⊆ S ∧ 2 ≤ T.card)

def unionCount (S : Finset (Fin n)) (ps : List (ℕ × ℕ))
    (L : List (Finset (Fin n))) : ℕ :=
  ((unionCreated ps L).filter (productive S)).length

def poolBound (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

lemma getD_append_singleton_ne {α : Type} (L : List α) (z d : α) (j : ℕ)
    (hj : j ≠ L.length) : (L ++ [z]).getD j d = L.getD j d := by
  by_cases hlt : j < L.length
  · exact List.getD_append _ _ _ _ hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma poolBound_small (t : ℕ) (L : List (Finset (Fin n))) (z : Finset (Fin n))
    (hz : z.card ≤ 1) (h : poolBound t L) : poolBound t (L ++ [z]) := by
  intro W
  by_cases hm : L.length ∈ W
  · have hs : (W.biUnion fun j => (L ++ [z]).getD j ∅) ⊆
        ((W.erase L.length).biUnion fun j => L.getD j ∅) ∪ z := by
      intro a ha
      obtain ⟨j, hj, haj⟩ := Finset.mem_biUnion.mp ha
      by_cases he : j = L.length
      · subst j
        exact Finset.mem_union_right _ (by simpa using haj)
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_erase.mpr ⟨he, hj⟩, by rw [getD_append_singleton_ne L z ∅ j he] at haj; exact haj⟩)
    have h1 := Finset.card_le_card hs
    have h2 := Finset.card_union_le ((W.erase L.length).biUnion fun j => L.getD j ∅) z
    have h3 := h (W.erase L.length)
    have h4 := Finset.card_erase_of_mem hm
    have h5 := Finset.card_pos.mpr ⟨_, hm⟩
    omega
  · have heq : (W.biUnion fun j => (L ++ [z]).getD j ∅) =
        (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_append_singleton_ne _ _ _ _ (fun e => hm (e ▸ hj))
    rw [heq]
    exact h W

lemma poolBound_union (t : ℕ) (L : List (Finset (Fin n))) (a b : ℕ)
    (h : poolBound t L) : poolBound (t + 1) (L ++ [L.getD a ∅ ∪ L.getD b ∅]) := by
  intro W
  by_cases hm : L.length ∈ W
  · have hs : (W.biUnion fun j =>
        (L ++ [L.getD a ∅ ∪ L.getD b ∅]).getD j ∅) ⊆
        ((W.erase L.length ∪ {a, b}).biUnion fun j => L.getD j ∅) := by
      intro v hv
      obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hv
      by_cases he : j = L.length
      · subst j
        have hvab : v ∈ L.getD a ∅ ∪ L.getD b ∅ := by simpa using hvj
        rcases Finset.mem_union.mp hvab with hva | hvb
        · exact Finset.mem_biUnion.mpr ⟨a, by simp, hva⟩
        · exact Finset.mem_biUnion.mpr ⟨b, by simp, hvb⟩
      · exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨he, hj⟩), by
          rw [getD_append_singleton_ne L _ ∅ j he] at hvj; exact hvj⟩
    have h1 := Finset.card_le_card hs
    have h2 := Finset.card_union_le (W.erase L.length) {a, b}
    have h3 := h (W.erase L.length ∪ {a, b})
    have h4 := Finset.card_erase_of_mem hm
    have h5 := Finset.card_pos.mpr ⟨_, hm⟩
    have h6 : ({a, b} : Finset ℕ).card ≤ 2 := by
      exact (Finset.card_insert_le _ _).trans (by simp)
    omega
  · have heq : (W.biUnion fun j =>
        (L ++ [L.getD a ∅ ∪ L.getD b ∅]).getD j ∅) =
        (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_append_singleton_ne _ _ _ _ (fun e => hm (e ▸ hj))
    rw [heq]
    exact (h W).trans (by omega)

lemma inside_getD (S : Finset (Fin n)) (L : List (Finset (Fin n))) (j : ℕ) :
    (L.map (inside S)).getD j ∅ = inside S (L.getD j ∅) := by
  have hd : inside S ∅ = ∅ := by simp [inside]
  simpa [hd] using List.getD_map (f := inside S) (l := L) (n := j) (d := ∅)

lemma inside_union_of_subset (S : Finset (Fin n)) (L : List (Finset (Fin n)))
    (p : ℕ × ℕ) (h : unionGate L p ⊆ S) :
    inside S (unionGate L p) = unionGate (L.map (inside S)) p := by
  have ha : L.getD p.1 ∅ ⊆ S := fun v hv => h (Finset.mem_union_left _ hv)
  have hb : L.getD p.2 ∅ ⊆ S := fun v hv => h (Finset.mem_union_right _ hv)
  rw [inside, ite_eq_left h]
  unfold unionGate
  rw [inside_getD, inside_getD]
  rw [inside, ite_eq_left ha, inside, ite_eq_left hb]

lemma poolBound_inside_step (S : Finset (Fin n)) (L : List (Finset (Fin n)))
    (p : ℕ × ℕ) (t : ℕ) (h : poolBound t (L.map (inside S))) :
    poolBound (t + if productive S (unionGate L p) then 1 else 0)
      ((L ++ [unionGate L p]).map (inside S)) := by
  rw [List.map_append, List.map_singleton]
  by_cases hp : productive S (unionGate L p) = true
  · simp only [hp, ↓reduceIte]
    have hs : unionGate L p ⊆ S := (of_decide_eq_true hp).1
    rw [inside_union_of_subset S L p hs]
    exact poolBound_union t _ p.1 p.2 h
  · have hz : (inside S (unionGate L p)).card ≤ 1 := by
      by_cases hs : unionGate L p ⊆ S
      · have hc : ¬ 2 ≤ (unionGate L p).card := by
          intro hc
          exact hp (by simp [productive, hs, hc])
        simp [inside, hs]
        omega
      · simp [inside, hs]
    simpa [hp] using poolBound_small t _ _ hz h

lemma poolBound_inside_run (S : Finset (Fin n)) (ps : List (ℕ × ℕ)) :
    ∀ (L : List (Finset (Fin n))) (t : ℕ), poolBound t (L.map (inside S)) →
      poolBound (t + unionCount S ps L) ((unionRun ps L).map (inside S)) := by
  induction ps with
  | nil => intro L t h; simpa [unionRun, unionCount, unionCreated] using h
  | cons p ps ih =>
    intro L t h
    have hi := ih (L ++ [unionGate L p])
      (t + if productive S (unionGate L p) then 1 else 0)
      (poolBound_inside_step S L p t h)
    by_cases hp : productive S (unionGate L p) = true
    · simpa [unionRun, unionCount, unionCreated, hp, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using hi
    · simpa [unionRun, unionCount, unionCreated, hp] using hi

lemma poolBound_inside_inputs (S : Finset (Fin n)) :
    poolBound 0 ((unionInputs n).map (inside S)) := by
  intro W
  refine (Finset.card_biUnion_le).trans ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j hj
  rw [inside_getD]
  by_cases hlt : j < n
  · have hj : (unionInputs n).getD j ∅ = {⟨j, hlt⟩} := by
      simp [unionInputs, List.getD, hlt]
    rw [hj]
    by_cases hs : ({⟨j, hlt⟩} : Finset (Fin n)) ⊆ S <;> simp [inside, hs]
  · rw [List.getD_eq_default _ _ (by simp [unionInputs]; omega)]
    simp [inside]

lemma union_output_cost (S : Finset (Fin n)) (ps : List (ℕ × ℕ)) (out : ℕ)
    (he : (unionRun ps (unionInputs n)).getD out ∅ = S) :
    S.card ≤ unionCount S ps (unionInputs n) + 1 := by
  have h := poolBound_inside_run S ps (unionInputs n) 0 (poolBound_inside_inputs S) {out}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at h
  rw [inside_getD, he] at h
  simpa [inside] using h

lemma productive_unique {ι : Type} {S : ι → Finset (Fin n)} {i j : ι}
    (hij : (S i ∩ S j).card ≤ 1) {T : Finset (Fin n)}
    (hi : productive (S i) T = true) (hj : productive (S j) T = true) : False := by
  have hi' : T ⊆ S i ∧ 2 ≤ T.card := of_decide_eq_true hi
  have hj' : T ⊆ S j ∧ 2 ≤ T.card := of_decide_eq_true hj
  have hs : T ⊆ S i ∩ S j := fun v hv => Finset.mem_inter.mpr ⟨hi'.1 hv, hj'.1 hv⟩
  have hc := Finset.card_le_card hs
  omega

lemma productive_sum_le_one {ι : Type} [DecidableEq ι] (I : Finset ι)
    (S : ι → Finset (Fin n)) (T : Finset (Fin n))
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (S i ∩ S j).card ≤ 1) :
    (∑ i ∈ I, if productive (S i) T then 1 else 0) ≤ 1 := by
  by_cases he : ∃ i ∈ I, productive (S i) T = true
  · obtain ⟨i, hi, hp⟩ := he
    have hsum : (∑ j ∈ I, if productive (S j) T then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single i]
      · simp [hp]
      · intro j hj hji
        have hjp : productive (S j) T = false := by
          cases hc : productive (S j) T with
          | false => rfl
          | true => exact False.elim (productive_unique (hsep i hi j hj (Ne.symm hji)) hp hc)
        simp [hjp]
      · exact fun h => (h hi).elim
    omega
  · have hsum : (∑ i ∈ I, if productive (S i) T then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hp : productive (S i) T = false := by
        cases hc : productive (S i) T with
        | false => rfl
        | true => exact False.elim (he ⟨i, hi, hc⟩)
      simp [hp]
    omega

lemma productive_counts_le_length {ι : Type} [DecidableEq ι] (I : Finset ι)
    (S : ι → Finset (Fin n)) (L : List (Finset (Fin n)))
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (S i ∩ S j).card ≤ 1) :
    (∑ i ∈ I, (L.filter (productive (S i))).length) ≤ L.length := by
  induction L with
  | nil => simp
  | cons T L ih =>
    have heq : ∀ i, ((T :: L).filter (productive (S i))).length =
        (L.filter (productive (S i))).length + if productive (S i) T then 1 else 0 := by
      intro i
      cases hp : productive (S i) T <;> simp [hp]
    simp only [heq, Finset.sum_add_distrib, List.length_cons]
    have h := productive_sum_le_one I S T hsep
    omega

lemma unionCreated_length (ps : List (ℕ × ℕ)) (L : List (Finset (Fin n))) :
    (unionCreated ps L).length = ps.length := by
  induction ps generalizing L with
  | nil => rfl
  | cons p ps ih => simp [unionCreated, ih]

lemma union_family_cost {ι : Type} [DecidableEq ι] (I : Finset ι)
    (S : ι → Finset (Fin n)) (ps : List (ℕ × ℕ)) (out : ι → ℕ)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ i ∈ I, (unionRun ps (unionInputs n)).getD (out i) ∅ = S i) :
    (∑ i ∈ I, ((S i).card - 1)) ≤ ps.length := by
  have h1 : (∑ i ∈ I, ((S i).card - 1)) ≤ ∑ i ∈ I, unionCount (S i) ps (unionInputs n) := by
    apply Finset.sum_le_sum
    intro i hi
    have h := union_output_cost (S i) ps (out i) (hout i hi)
    omega
  have h2 := productive_counts_le_length I S (unionCreated ps (unionInputs n)) hsep
  rw [unionCreated_length] at h2
  exact h1.trans h2

def orValue (x : Fin n → Bool) (S : Finset (Fin n)) : Bool :=
  decide (∃ v ∈ S, x v = true)

lemma orValue_empty (x : Fin n → Bool) : orValue x ∅ = false := by
  simp [orValue]

lemma orValue_singleton (x : Fin n → Bool) (v : Fin n) : orValue x {v} = x v := by
  simp [orValue]

lemma orValue_union (x : Fin n → Bool) (A B : Finset (Fin n)) :
    orValue x (A ∪ B) = (orValue x A || orValue x B) := by
  simp [orValue, or_and_right, exists_or]

lemma orValue_getD (x : Fin n → Bool) (L : List (Finset (Fin n))) (j : ℕ) :
    (L.map (orValue x)).getD j false = orValue x (L.getD j ∅) := by
  simpa only [orValue_empty] using List.getD_map L ∅ (n := j) (orValue x)

lemma orValue_injective (S T : Finset (Fin n))
    (h : ∀ x : Fin n → Bool, orValue x S = orValue x T) : S = T := by
  ext v
  have he := congrArg (fun b => b = true) (h (fun w => decide (w = v)))
  simpa [orValue] using he

open PEqualNP.CircuitLowerBounds

def orCircuit (ps : List (ℕ × ℕ)) (out : ℕ) : Circuit :=
  ⟨ps.map (fun p => ⟨GateOp.or, [p.1, p.2]⟩), out⟩

lemma orCircuit_wires (ps : List (ℕ × ℕ)) (out : ℕ) (x : Fin n → Bool)
    (L : List (Finset (Fin n))) :
    (orCircuit ps out).wires (L.map (orValue x)) = (unionRun ps L).map (orValue x) := by
  induction ps generalizing L with
  | nil => simp [orCircuit, Circuit.wires, unionRun]
  | cons p ps ih =>
    have he : (L.map (orValue x)) ++
          [GateOp.or.eval ([p.1, p.2].map (fun j => (L.map (orValue x)).getD j false))] =
        (L ++ [unionGate L p]).map (orValue x) := by
      rw [List.map_append, List.map_singleton]
      congr 1
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        id_eq, Bool.or_false]
      rw [orValue_getD, orValue_getD, ← orValue_union]
      rfl
    change (orCircuit ps out).wires ((L.map (orValue x)) ++
      [GateOp.or.eval ([p.1, p.2].map (fun j => (L.map (orValue x)).getD j false))]) = _
    rw [he]
    exact ih (L ++ [unionGate L p])

lemma orCircuit_eval (ps : List (ℕ × ℕ)) (out : ℕ) (x : Fin n → Bool) :
    (orCircuit ps out).eval (List.ofFn x) =
      orValue x ((unionRun ps (unionInputs n)).getD out ∅) := by
  have hi : (unionInputs n).map (orValue x) = List.ofFn x := by
    simp only [unionInputs, List.map_ofFn]
    congr 1
    funext v
    exact orValue_singleton x v
  rw [Circuit.eval, ← hi, orCircuit_wires, orValue_getD]
  rfl

lemma or_circuit_family_cost {ι : Type} [DecidableEq ι] (I : Finset ι)
    (S : ι → Finset (Fin n)) (ps : List (ℕ × ℕ)) (out : ι → ℕ)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ i ∈ I, ∀ x : Fin n → Bool,
      (orCircuit ps (out i)).eval (List.ofFn x) = orValue x (S i)) :
    (∑ i ∈ I, ((S i).card - 1)) ≤ ps.length := by
  apply union_family_cost I S ps out hsep
  intro i hi
  apply orValue_injective
  intro x
  rw [← orCircuit_eval]
  exact hout i hi x

def orGatePair (limit : ℕ) (g : Gate) : ℕ × ℕ :=
  (g.inputs.getD 0 limit, g.inputs.getD 1 limit)

lemma orGatePair_eval (limit : ℕ) (g : Gate) (w : List Bool)
    (hop : g.op = GateOp.or) (hlen : g.inputs.length ≤ 2) (hw : w.length ≤ limit) :
    g.op.eval (g.inputs.map (fun j => w.getD j false)) =
      GateOp.or.eval ([ (orGatePair limit g).1, (orGatePair limit g).2 ].map
        (fun j => w.getD j false)) := by
  have hz : w.getD limit false = false := List.getD_eq_default _ _ hw
  simp only [List.getD] at hz
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen
  subst op
  cases ins with
  | nil => simp [orGatePair, GateOp.eval, hz]
  | cons a ins =>
    cases ins with
    | nil => simp [orGatePair, GateOp.eval, hz]
    | cons b ins =>
      cases ins with
      | nil => rfl
      | cons c ins => simp at hlen

lemma orGatePair_wires (gs : List Gate) (limit out : ℕ) :
    ∀ w : List Bool, (∀ g ∈ gs, g.op = GateOp.or ∧ g.inputs.length ≤ 2) →
      w.length + gs.length ≤ limit →
      ({ gates := gs, output := out } : Circuit).wires w =
        (orCircuit (gs.map (orGatePair limit)) out).wires w := by
  induction gs with
  | nil => intro w _ _; rfl
  | cons g gs ih =>
    intro w hg hw
    have hp := hg g List.mem_cons_self
    have hstep := orGatePair_eval limit g w hp.1 hp.2 (by simp at hw; omega)
    have htail : ∀ g' ∈ gs, g'.op = GateOp.or ∧ g'.inputs.length ≤ 2 := by
      intro g' hg'
      exact hg g' (List.mem_cons_of_mem _ hg')
    have hlen : (w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]).length +
        gs.length ≤ limit := by simp at hw ⊢; omega
    have hi := ih (w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]) htail hlen
    simpa only [Circuit.wires, List.foldl_cons, orCircuit, List.map_cons, hstep] using hi

lemma or_fanin_two_family_cost {ι : Type} [DecidableEq ι] (I : Finset ι)
    (S : ι → Finset (Fin n)) (gs : List Gate) (out : ι → ℕ)
    (hop : ∀ g ∈ gs, g.op = GateOp.or ∧ g.inputs.length ≤ 2)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hout : ∀ i ∈ I, ∀ x : Fin n → Bool,
      ({ gates := gs, output := out i } : Circuit).eval (List.ofFn x) = orValue x (S i)) :
    (∑ i ∈ I, ((S i).card - 1)) ≤ gs.length := by
  have h := or_circuit_family_cost I S (gs.map (orGatePair (n + gs.length))) out hsep
  have hh : ∀ i ∈ I, ∀ x : Fin n → Bool,
      (orCircuit (gs.map (orGatePair (n + gs.length))) (out i)).eval (List.ofFn x) =
        orValue x (S i) := by
    intro i hi x
    have hw := orGatePair_wires gs (n + gs.length) (out i) (List.ofFn x) hop (by simp)
    have he := hout i hi x
    unfold Circuit.eval at he ⊢
    rw [← hw]
    exact he
  simpa using h hh



def edgeValue (x : Fin 10 → Bool) : Bool :=
  decide (∃ e ∈ edges, x e.1 = true ∧ x e.2 = true)

lemma adj_symm {a b : Fin 10} (h : Adj a b) : Adj b a := h.symm

lemma adj_irrefl (a : Fin 10) : ¬ Adj a a := by
  unfold Adj
  fin_cases a <;> decide

lemma edgeValue_pair (a b : Fin 10) :
    edgeValue (fun v => decide (v = a ∨ v = b)) = true ↔ Adj a b := by
  simp only [edgeValue, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨u, v⟩, he, hu, hv⟩
    change (u = a ∨ u = b) at hu
    change (v = a ∨ v = b) at hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact False.elim (adj_irrefl _ (Or.inl he))
    · exact Or.inl he
    · exact Or.inr he
    · exact False.elim (adj_irrefl _ (Or.inl he))
  · rintro (h | h)
    · exact ⟨(a, b), h, Or.inl rfl, Or.inr rfl⟩
    · exact ⟨(b, a), h, Or.inr rfl, Or.inl rfl⟩

lemma safe_product_biclique {A B : Finset (Fin 10)}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hsafe : ∀ x, (orValue x A && orValue x B) = true → edgeValue x = true) :
    Biclique A B := by
  refine ⟨hA, hB, ?_⟩
  intro a ha b hb
  apply (edgeValue_pair a b).mp
  apply hsafe
  simp only [Bool.and_eq_true, orValue, decide_eq_true_eq]
  exact ⟨⟨a, ha, Or.inl rfl⟩, ⟨b, hb, Or.inr rfl⟩⟩

lemma biclique_safe_product {A B : Finset (Fin 10)} (h : Biclique A B) :
    ∀ x, (orValue x A && orValue x B) = true → edgeValue x = true := by
  intro x hx
  simp only [Bool.and_eq_true, orValue, decide_eq_true_eq] at hx
  obtain ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩ := hx
  simp only [edgeValue, decide_eq_true_eq]
  rcases h.2.2 a ha b hb with he | he
  · exact ⟨(a, b), he, hxa, hxb⟩
  · exact ⟨(b, a), he, hxb, hxa⟩

lemma safe_product_star {A B : Finset (Fin 10)}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hsafe : ∀ x, (orValue x A && orValue x B) = true → edgeValue x = true) :
    A.card = 1 ∨ B.card = 1 :=
  biclique_singleton (safe_product_biclique hA hB hsafe)

lemma safe_product_cover_count {ι : Type*} [Fintype ι]
    (A B : ι → Finset (Fin 10)) (hne : ∀ i, (A i).Nonempty ∧ (B i).Nonempty)
    (hsafe : ∀ i x,
      (orValue x (A i) && orValue x (B i)) = true → edgeValue x = true)
    (hcomplete : ∀ x, edgeValue x = true →
      ∃ i, (orValue x (A i) && orValue x (B i)) = true) :
    6 ≤ Fintype.card ι := by
  apply biclique_cover_count A B
    (fun i => safe_product_biclique (hne i).1 (hne i).2 (hsafe i))
  intro e he
  obtain ⟨i, hi⟩ := hcomplete (fun v => decide (v = e.1 ∨ v = e.2))
    ((edgeValue_pair e.1 e.2).mpr (Or.inl he))
  simp only [Bool.and_eq_true, orValue, decide_eq_true_eq] at hi
  obtain ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩ := hi
  have hcross := (safe_product_biclique (hne i).1 (hne i).2 (hsafe i)).2.2 a ha b hb
  refine ⟨i, ?_⟩
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · exact False.elim (adj_irrefl _ hcross)
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact False.elim (adj_irrefl _ hcross)

end Factoring

namespace UnsafeSix

open PEqualNP.AndCount

def graph : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel fun a b : Fin 10 =>
    (a.val, b.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
      (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
      (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ))

def circuit : AndCountCircuit 10 where
  size := 6
  leftVars := ![{7, 8}, {2, 4, 7}, {3}, {6}, {1, 3, 7}, {0}]
  rightVars := ![{5}, {9}, {4, 8}, {1, 8, 9}, {2}, {1, 4, 5}]
  leftGates := ![∅, ∅, {0, 1}, ∅, {0, 3}, {2, 4}]
  rightGates := ![∅, ∅, ∅, ∅, {1, 2, 3}, {3, 4}]
  outVars := ∅
  outGates := {0, 5}

lemma wellFormed : circuit.WellFormed := by
  unfold AndCountCircuit.WellFormed
  decide

lemma size_six : circuit.size = 6 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma singleton_false : ∀ (v : Fin 10) (i : Fin circuit.size),
    circuit.gateVal {v} i = false := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma computes : circuit.Computes graph := by
  unfold AndCountCircuit.Computes graph
  decide +kernel

lemma independent_pair : ∀ a ∈ ({2, 9} : Finset (Fin 10)),
    ∀ b ∈ ({2, 9} : Finset (Fin 10)), ¬ graph.Adj a b := by
  unfold graph
  decide

lemma unsafe_pair : circuit.gateVal {2, 9} ⟨1, by decide⟩ = true := by decide

end UnsafeSix





namespace Factoring

lemma edge_orientation_unique : ∀ a b : Fin 10,
    (a, b) ∈ edges → (b, a) ∉ edges := by decide

def otherEndpoint (c : Fin 10) (e : Fin 10 × Fin 10) : Fin 10 :=
  if e.1 = c then e.2 else e.1

def starEdges (c : Fin 10) (S : Finset (Fin 10)) : Finset (Fin 10 × Fin 10) :=
  edges.filter fun e => (e.1 = c ∧ e.2 ∈ S) ∨ (e.2 = c ∧ e.1 ∈ S)

lemma otherEndpoint_form (c : Fin 10) (e : Fin 10 × Fin 10)
    (hc : e.1 = c ∨ e.2 = c) :
    e = (c, otherEndpoint c e) ∨ e = (otherEndpoint c e, c) := by
  obtain ⟨a, b⟩ := e
  change a = c ∨ b = c at hc
  rcases hc with hc | hc
  · subst a
    exact Or.inl (by simp [otherEndpoint])
  · subst b
    by_cases ha : a = c
    · subst a
      exact Or.inl (by simp [otherEndpoint])
    · exact Or.inr (by simp [otherEndpoint, ha])

lemma starEdges_card (c : Fin 10) (S : Finset (Fin 10)) :
    (starEdges c S).card ≤ S.card := by
  apply Finset.card_le_card_of_injOn (otherEndpoint c)
  · intro e he
    obtain ⟨he, hs⟩ := Finset.mem_filter.mp he
    obtain ⟨a, b⟩ := e
    change (a = c ∧ b ∈ S) ∨ (b = c ∧ a ∈ S) at hs
    rcases hs with ⟨hc, hb⟩ | ⟨hc, ha⟩
    · subst a
      simpa [otherEndpoint] using hb
    · subst b
      by_cases heq : a = c
      · subst a
        simpa [otherEndpoint] using ha
      · simpa [otherEndpoint, heq] using ha
  · intro e he f hf hsame
    obtain ⟨he, hce⟩ := Finset.mem_filter.mp he
    obtain ⟨hf, hcf⟩ := Finset.mem_filter.mp hf
    have hfe := otherEndpoint_form c e (hce.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
    have hff := otherEndpoint_form c f (hcf.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
    rw [← hsame] at hff
    rcases hfe with hfe | hfe <;> rcases hff with hff | hff
    · exact hfe.trans hff.symm
    · exfalso
      have he' : (c, otherEndpoint c e) ∈ edges := hfe ▸ he
      have hf' : (otherEndpoint c e, c) ∈ edges := hff ▸ hf
      exact edge_orientation_unique _ _ he' hf'
    · exfalso
      have he' : (otherEndpoint c e, c) ∈ edges := hfe ▸ he
      have hf' : (c, otherEndpoint c e) ∈ edges := hff ▸ hf
      exact edge_orientation_unique _ _ he' hf'
    · exact hfe.trans hff.symm

lemma star_cover_support_sum {k : ℕ} (c : Fin k → Fin 10)
    (S : Fin k → Finset (Fin 10))
    (hcover : ∀ e ∈ edges, ∃ i,
      (e.1 = c i ∧ e.2 ∈ S i) ∨ (e.2 = c i ∧ e.1 ∈ S i)) :
    15 ≤ ∑ i, (S i).card := by
  have hs : edges ⊆ Finset.univ.biUnion (fun i => starEdges (c i) (S i)) := by
    intro e he
    obtain ⟨i, hi⟩ := hcover e he
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨he, hi⟩⟩
  calc
    15 = edges.card := edges_card.symm
    _ ≤ (Finset.univ.biUnion (fun i => starEdges (c i) (S i))).card := Finset.card_le_card hs
    _ ≤ ∑ i, (starEdges (c i) (S i)).card := Finset.card_biUnion_le
    _ ≤ ∑ i, (S i).card := Finset.sum_le_sum (fun i _ => starEdges_card (c i) (S i))

lemma star_cover_count {k : ℕ} (c : Fin k → Fin 10)
    (S : Fin k → Finset (Fin 10))
    (hcover : ∀ e ∈ edges, ∃ i,
      (e.1 = c i ∧ e.2 ∈ S i) ∨ (e.2 = c i ∧ e.1 ∈ S i)) :
    6 ≤ k := by
  have hc : Cover (Finset.univ.image c) := by
    intro e he
    obtain ⟨i, hi⟩ := hcover e he
    have hm : c i ∈ Finset.univ.image c := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    rcases hi with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl (h ▸ hm)
    · exact Or.inr (h ▸ hm)
  calc
    6 ≤ (Finset.univ.image c).card := cover_card _ hc
    _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
    _ = k := by simp

lemma star_support_intersections {k : ℕ} (c : Fin k → Fin 10)
    (S : Fin k → Finset (Fin 10)) (hcenters : Function.Injective c)
    (hneighbors : ∀ i, ∀ v ∈ S i, Adj (c i) v) :
    ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1 := by
  intro i j hij
  by_contra hcard
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (S i ∩ S j).card)
  obtain ⟨hai, haj⟩ := Finset.mem_inter.mp ha
  obtain ⟨hbi, hbj⟩ := Finset.mem_inter.mp hb
  exact no_four_cycle (c i) (c j) a b (fun h => hij (hcenters h)) hab
    (hneighbors i a hai) (hneighbors i b hbi)
    (hneighbors j a haj) (hneighbors j b hbj)

lemma or_all_cost (k : ℕ) (gs : List PEqualNP.CircuitLowerBounds.Gate) (out : ℕ)
    (hop : ∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2)
    (hout : ∀ x : Fin k → Bool,
      ({ gates := gs, output := out } : PEqualNP.CircuitLowerBounds.Circuit).eval
        (List.ofFn x) = orValue x Finset.univ) :
    k - 1 ≤ gs.length := by
  have h := or_fanin_two_family_cost ({0} : Finset (Fin 1))
    (fun _ => (Finset.univ : Finset (Fin k))) gs (fun _ => out) hop
    (by
      intro i hi j hj hij
      have hi0 : i = 0 := Finset.mem_singleton.mp hi
      have hj0 : j = 0 := Finset.mem_singleton.mp hj
      exact False.elim (hij (hi0.trans hj0.symm)))
    (by intro i hi x; exact hout x)
  simpa using h

lemma layered_star_lower {k : ℕ} (c : Fin k → Fin 10)
    (S : Fin k → Finset (Fin 10))
    (prep merge : List PEqualNP.CircuitLowerBounds.Gate)
    (prepOut : Fin k → ℕ) (mergeOut : ℕ)
    (hcenters : Function.Injective c)
    (hne : ∀ i, (S i).Nonempty)
    (hneighbors : ∀ i, ∀ v ∈ S i, Adj (c i) v)
    (hcover : ∀ e ∈ edges, ∃ i,
      (e.1 = c i ∧ e.2 ∈ S i) ∨ (e.2 = c i ∧ e.1 ∈ S i))
    (hprep : ∀ g ∈ prep, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2)
    (hmerge : ∀ g ∈ merge, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2)
    (hprepEval : ∀ i, ∀ x : Fin 10 → Bool,
      ({ gates := prep, output := prepOut i } : PEqualNP.CircuitLowerBounds.Circuit).eval
        (List.ofFn x) = orValue x (S i))
    (hmergeEval : ∀ x : Fin k → Bool,
      ({ gates := merge, output := mergeOut } : PEqualNP.CircuitLowerBounds.Circuit).eval
        (List.ofFn x) = orValue x Finset.univ) :
    20 ≤ prep.length + k + merge.length := by
  have hp := or_fanin_two_family_cost (Finset.univ : Finset (Fin k)) S prep prepOut hprep
    (fun i _ j _ hij => star_support_intersections c S hcenters hneighbors i j hij)
    (fun i _ => hprepEval i)
  have hm := or_all_cost k merge mergeOut hmerge hmergeEval
  have hk := star_cover_count c S hcover
  have hs := star_cover_support_sum c S hcover
  have hsum : (∑ i : Fin k, ((S i).card - 1)) + k = ∑ i : Fin k, (S i).card := by
    calc
      (∑ i : Fin k, ((S i).card - 1)) + k = ∑ i : Fin k, ((S i).card - 1 + 1) := by
        simp [Finset.sum_add_distrib]
      _ = ∑ i : Fin k, (S i).card := by
        apply Finset.sum_congr rfl
        intro i hi
        have h := Finset.one_le_card.mpr (hne i)
        omega
  omega

end Factoring

namespace UnsafeSixIrredundant

open PEqualNP.AndCount

def graph : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel fun a b : Fin 10 =>
    (a.val, b.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
      (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
      (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ))

def circuit : AndCountCircuit 10 where
  size := 6
  leftVars := ![{0, 7, 8}, ∅, {2}, {3}, {6}, {9}]
  rightVars := ![{5, 1, 4}, {0, 5}, {1, 7, 3}, {4, 8}, {1, 8, 9}, {4, 7}]
  leftGates := ![∅, {0}, ∅, ∅, ∅, ∅]
  rightGates := ![∅, ∅, ∅, ∅, ∅, ∅]
  outVars := ∅
  outGates := {1, 2, 3, 4, 5}

lemma wellFormed : circuit.WellFormed := by
  unfold AndCountCircuit.WellFormed
  decide

lemma size_six : circuit.size = 6 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma singleton_false : ∀ (v : Fin 10) (i : Fin circuit.size),
    circuit.gateVal {v} i = false := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma computes : circuit.Computes graph := by
  unfold AndCountCircuit.Computes graph
  decide +kernel

lemma independent_pair : ∀ a ∈ ({1, 7} : Finset (Fin 10)),
    ∀ b ∈ ({1, 7} : Finset (Fin 10)), ¬ graph.Adj a b := by
  unfold graph
  decide

lemma unsafe_pair : circuit.gateVal {1, 7} ⟨0, by decide⟩ = true := by decide

def edgeRows : Fin 15 → Finset (Fin 10) :=
  ![{0, 1}, {1, 2}, {2, 3}, {3, 4}, {4, 0}, {0, 5}, {1, 6}, {2, 7},
    {3, 8}, {4, 9}, {5, 7}, {7, 9}, {9, 6}, {6, 8}, {8, 5}]

lemma edge_rows_true : ∀ r : Fin 15, circuit.eval (edgeRows r) = true := by decide

def cutLeftVar (i : Fin 6) (v : Fin 10) : AndCountCircuit 10 :=
  { circuit with leftVars := fun j : Fin 6 =>
      if j.val = i.val then (circuit.leftVars j).erase v else circuit.leftVars j }

def cutRightVar (i : Fin 6) (v : Fin 10) : AndCountCircuit 10 :=
  { circuit with rightVars := fun j : Fin 6 =>
      if j.val = i.val then (circuit.rightVars j).erase v else circuit.rightVars j }

def cutLeftGate (i k : Fin 6) : AndCountCircuit 10 :=
  { circuit with leftGates := fun j : Fin 6 =>
      if j.val = i.val then (circuit.leftGates j).erase k else circuit.leftGates j }

def cutRightGate (i k : Fin 6) : AndCountCircuit 10 :=
  { circuit with rightGates := fun j : Fin 6 =>
      if j.val = i.val then (circuit.rightGates j).erase k else circuit.rightGates j }

def cutOutput (i : Fin 6) : AndCountCircuit 10 :=
  { circuit with outGates := circuit.outGates.erase i }

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma left_var_essential : ∀ (i : Fin 6) (v : Fin 10), v ∈ circuit.leftVars i →
    ∃ r : Fin 15, (cutLeftVar i v).eval (edgeRows r) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma right_var_essential : ∀ (i : Fin 6) (v : Fin 10), v ∈ circuit.rightVars i →
    ∃ r : Fin 15, (cutRightVar i v).eval (edgeRows r) = false := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma left_gate_essential : ∀ (i k : Fin 6), k ∈ circuit.leftGates i →
    ∃ r : Fin 15, (cutLeftGate i k).eval (edgeRows r) = false := by
  unfold circuit
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma right_gate_essential : ∀ (i k : Fin 6), k ∈ circuit.rightGates i →
    ∃ r : Fin 15, (cutRightGate i k).eval (edgeRows r) = false := by
  unfold circuit
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma output_essential : ∀ i : Fin 6, i ∈ circuit.outGates →
    ∃ r : Fin 15, (cutOutput i).eval (edgeRows r) = false := by
  unfold circuit
  decide +kernel

end UnsafeSixIrredundant

namespace BoundaryTransport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w
lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by simp
lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · change l₁.all id = true → l₂.all id = true
    simp only [List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · change l₁.any id = true → l₂.any id = true
    simp only [List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩
lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj
def rows : List ℕ := [3, 6, 12, 17, 24, 33, 50, 66, 69, 104, 116, 132, 138, 160, 201, 208, 264, 276, 288, 320, 385, 402, 521, 528, 548, 554, 576, 640, 770, 773]
def pos : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640]
def neg : List ℕ := [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]
def bits (r : ℕ) (i : Fin 10) := r.testBit i.val
def edge (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
def below (a b : Fin 10 → Bool) : Bool := (List.finRange 10).all fun i => !(a i) || b i
lemma below_elim {a b} (h : below a b = true) {i : Fin 10} (hi : a i = true) : b i = true := by
  have hh := List.all_eq_true.mp h i (by simp)
  simpa [hi] using hh
set_option maxRecDepth 20000 in
lemma endpoints : ∀ r : Fin 1024,
    (if edge (bits r) then pos.any (fun q => below (bits q) (bits r))
     else neg.any (fun q => below (bits r) (bits q))) = true := by decide +kernel
lemma liftRows (f : (Fin 10 → Bool) → Bool)
    (hm : ∀ a b : Fin 10 → Bool, (∀ i, a i = true → b i = true) → f a = true → f b = true)
    (hr : ∀ q ∈ rows, f (bits q) = decide (q ∈ pos)) : ∀ x, f x = edge x := by
  intro x
  let w := BitVec.ofBoolListLE (List.ofFn x)
  have hw : w.toNat < 1024 := by
    have h := w.isLt
    simpa [w] using h
  let r : Fin 1024 := ⟨w.toNat, hw⟩
  have eqx : bits r = x := by
    funext i
    change w.getLsbD i.val = x i
    rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have coverage := endpoints r
  rw [eqx] at coverage
  have hpRows : ∀ q ∈ pos, q ∈ rows := by decide +kernel
  have hnRows : ∀ q ∈ neg, q ∈ rows ∧ q ∉ pos := by decide +kernel
  cases he : edge x with
  | false =>
    rw [he] at coverage
    obtain ⟨q, hq, hle⟩ := List.any_eq_true.mp coverage
    have hn := hnRows q hq
    have hval := hr q hn.1
    rw [decide_eq_false hn.2] at hval
    cases hf : f x with
    | false => rfl
    | true =>
      have := hm x (bits q) (fun _ hi => below_elim hle hi) hf
      rw [hval] at this
      contradiction
  | true =>
    rw [he] at coverage
    obtain ⟨q, hq, hle⟩ := List.any_eq_true.mp coverage
    exact hm (bits q) x (fun _ hi => below_elim hle hi) (by simpa [hq] using hr q (hpRows q hq))
lemma eval_mono (C : Circuit) (hm : Monotone2 C) (x y : List Bool) (len : x.length=y.length)
    (hle : ∀ i, x.getD i false = true → y.getD i false = true) :
    C.eval x = true → C.eval y = true := by
  exact wiresFrom_mono C.gates (fun g hg => by simpa using (hm g hg).1) x y len hle C.output
lemma boundary_size : rows.length = 30 ∧ pos.length = 15 ∧ neg.length = 15 := by
  decide +kernel

lemma boundary_values : ∀ r ∈ rows, edge (bits r) = decide (r ∈ pos) := by
  decide +kernel

def InputMono (f : (Fin 10 → Bool) → Bool) : Prop :=
  ∀ a b : Fin 10 → Bool, (∀ i, a i = true → b i = true) → f a = true → f b = true

def bankEval {n : ℕ} (C : Circuit) (A : Fin n → (Fin 10 → Bool) → Bool)
    (x : Fin 10 → Bool) : Bool :=
  C.eval (List.ofFn (fun i => A i x))

lemma bankEval_mono {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (A : Fin n → (Fin 10 → Bool) → Bool) (hA : ∀ i, InputMono (A i)) :
    InputMono (bankEval C A) := by
  intro a b hab
  apply eval_mono C hm _ _ (by simp)
  intro j hj
  by_cases hlt : j < n
  · have ha : j < (List.ofFn (fun i => A i a)).length := by simpa using hlt
    have hb : j < (List.ofFn (fun i => A i b)).length := by simpa using hlt
    rw [List.getD_eq_getElem _ _ ha, List.getElem_ofFn] at hj
    rw [List.getD_eq_getElem _ _ hb, List.getElem_ofFn]
    exact hA ⟨j, hlt⟩ a b hab hj
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
    contradiction

lemma bankEval_congr {n : ℕ} (C : Circuit)
    (A B : Fin n → (Fin 10 → Bool) → Bool) (x : Fin 10 → Bool)
    (h : ∀ i, A i x = B i x) : bankEval C A x = bankEval C B x := by
  unfold bankEval
  congr 2
  exact funext h

lemma bank_boundary_iff {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (A : Fin n → (Fin 10 → Bool) → Bool) (hA : ∀ i, InputMono (A i)) :
    (∀ r ∈ rows, bankEval C A (bits r) = decide (r ∈ pos)) ↔
      ∀ x : Fin 10 → Bool, bankEval C A x = edge x := by
  constructor
  · exact liftRows (bankEval C A) (bankEval_mono C hm A hA)
  · intro h r hr
    exact (h (bits r)).trans (boundary_values r hr)

lemma bank_boundary_transport {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (A B : Fin n → (Fin 10 → Bool) → Bool)
    (hB : ∀ i, InputMono (B i))
    (hrows : ∀ i, ∀ r ∈ rows, A i (bits r) = B i (bits r))
    (hAexact : ∀ x : Fin 10 → Bool, bankEval C A x = edge x) :
    ∀ x : Fin 10 → Bool, bankEval C B x = edge x := by
  apply (bank_boundary_iff C hm B hB).mp
  intro r hr
  calc
    bankEval C B (bits r) = bankEval C A (bits r) :=
      bankEval_congr C B A (bits r) (fun i => (hrows i r hr).symm)
    _ = edge (bits r) := hAexact (bits r)
    _ = decide (r ∈ pos) := boundary_values r hr

lemma bank_boundary_transport_iff {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (A B : Fin n → (Fin 10 → Bool) → Bool)
    (hA : ∀ i, InputMono (A i)) (hB : ∀ i, InputMono (B i))
    (hrows : ∀ i, ∀ r ∈ rows, A i (bits r) = B i (bits r)) :
    (∀ x : Fin 10 → Bool, bankEval C A x = edge x) ↔
      ∀ x : Fin 10 → Bool, bankEval C B x = edge x := by
  constructor
  · exact bank_boundary_transport C hm A B hB hrows
  · exact bank_boundary_transport C hm B A hA (fun i r hr => (hrows i r hr).symm)

lemma bank_boundary_transport_reindex {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (A B : Fin n → (Fin 10 → Bool) → Bool) (e : Fin n ≃ Fin n)
    (hB : ∀ i, InputMono (B i))
    (hrows : ∀ i, ∀ r ∈ rows, A i (bits r) = B (e i) (bits r))
    (hAexact : ∀ x : Fin 10 → Bool, bankEval C A x = edge x) :
    ∀ x : Fin 10 → Bool, bankEval C (fun i => B (e i)) x = edge x :=
  bank_boundary_transport C hm A (fun i => B (e i)) (fun i => hB (e i)) hrows hAexact

end BoundaryTransport

namespace BoundaryDominance

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2373.BoundaryTransport

lemma bankEval_order {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (A B : Fin n → (Fin 10 → Bool) → Bool) (x : Fin 10 → Bool)
    (h : ∀ i, A i x = true → B i x = true) :
    bankEval C A x = true → bankEval C B x = true := by
  apply eval_mono C hm _ _ (by simp)
  intro j hj
  by_cases hlt : j < n
  · have ha : j < (List.ofFn (fun i => A i x)).length := by simpa using hlt
    have hb : j < (List.ofFn (fun i => B i x)).length := by simpa using hlt
    rw [List.getD_eq_getElem _ _ ha, List.getElem_ofFn] at hj
    rw [List.getD_eq_getElem _ _ hb, List.getElem_ofFn]
    exact h ⟨j, hlt⟩ hj
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
    contradiction

lemma rows_pos_or_neg : ∀ r ∈ rows, r ∈ pos ∨ r ∈ neg := by decide +kernel

lemma bank_ordered_transport {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (A B : Fin n → (Fin 10 → Bool) → Bool)
    (hB : ∀ i, InputMono (B i))
    (hpos : ∀ i, ∀ r ∈ pos, A i (bits r) = true → B i (bits r) = true)
    (hneg : ∀ i, ∀ r ∈ neg, B i (bits r) = true → A i (bits r) = true)
    (hAexact : ∀ x : Fin 10 → Bool, bankEval C A x = edge x) :
    ∀ x : Fin 10 → Bool, bankEval C B x = edge x := by
  apply (bank_boundary_iff C hm B hB).mp
  intro r hr
  by_cases hp : r ∈ pos
  · have ha : bankEval C A (bits r) = true := by
      rw [hAexact, boundary_values r hr]
      simp [hp]
    have hb := bankEval_order C hm A B (bits r) (fun i => hpos i r hp) ha
    simpa [hp] using hb
  · have hn : r ∈ neg := (rows_pos_or_neg r hr).resolve_left hp
    have ha : bankEval C A (bits r) = false := by
      rw [hAexact, boundary_values r hr]
      simp [hp]
    cases hb : bankEval C B (bits r) with
    | false => simp [hp]
    | true =>
      have hab := bankEval_order C hm B A (bits r) (fun i => hneg i r hn) hb
      rw [ha] at hab
      contradiction

lemma bank_replace_transport {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (A : Fin n → (Fin 10 → Bool) → Bool) (z w : Fin n)
    (hA : ∀ i, InputMono (A i))
    (hpos : ∀ r ∈ pos, A z (bits r) = true → A w (bits r) = true)
    (hneg : ∀ r ∈ neg, A w (bits r) = true → A z (bits r) = true)
    (hAexact : ∀ x : Fin 10 → Bool, bankEval C A x = edge x) :
    ∀ x : Fin 10 → Bool, bankEval C (Function.update A z (A w)) x = edge x := by
  apply bank_ordered_transport C hm A (Function.update A z (A w)) ?_ ?_ ?_ hAexact
  · intro i
    by_cases hi : i = z
    · subst i
      simpa using hA w
    · simpa only [Function.update_of_ne hi] using hA i
  · intro i r hr h
    by_cases hi : i = z
    · subst i
      simpa using hpos r hr h
    · simpa only [Function.update_of_ne hi] using h
  · intro i r hr h
    by_cases hi : i = z
    · subst i
      exact hneg r hr (by simpa using h)
    · simpa only [Function.update_of_ne hi] using h

end BoundaryDominance

namespace AliasMonotone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Base

def down (k i : ℕ) : ℕ := if i < k then i else i - 1

def gateValue (g : Gate) (xs : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => xs.getD i false)

lemma append_agree (k : ℕ) (xs ys : List Bool) (b : Bool)
    (hlen : xs.length + 1 = ys.length) (hk : k < ys.length)
    (heq : ∀ i, i ≠ k → xs.getD (down k i) false = ys.getD i false) :
    ∀ i, i ≠ k → (xs ++ [b]).getD (down k i) false = (ys ++ [b]).getD i false := by
  intro i hi
  rcases Nat.lt_trichotomy i ys.length with hlt | he | hgt
  · have hd : down k i < xs.length := by unfold down; split <;> omega
    rw [List.getD_append _ _ _ _ hd, List.getD_append _ _ _ _ hlt]
    exact heq i hi
  · subst i
    have hd : down k ys.length = xs.length := by unfold down; split <;> omega
    rw [hd]
    simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default _ _ (by
      simp only [List.length_append, List.length_singleton]
      unfold down; split <;> omega),
      List.getD_eq_default _ _ (by simp; omega)]

lemma initial_agree (xs : List Bool) (b : Bool) :
    ∀ i, i ≠ xs.length → xs.getD (down xs.length i) false = (xs ++ [b]).getD i false := by
  intro i hi
  by_cases hlt : i < xs.length
  · simp only [down, ite_eq_left hlt]
    rw [List.getD_append _ _ _ _ hlt]
  · have hgt : xs.length < i := by omega
    rw [List.getD_eq_default _ _ (by unfold down; split <;> omega),
      List.getD_eq_default _ _ (by simp; omega)]

lemma wires_length (gs : List Gate) (xs : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (xs ++ [gateValue g xs])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

end Base

open Base

def redirect (k p i : ℕ) : ℕ := if i = k then p else down k i

def renamed (k p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (redirect k p)⟩

lemma renamed_value (k p : ℕ) (g : Gate) (xs ys : List Bool)
    (heq : ∀ i, xs.getD (redirect k p i) false = ys.getD i false) :
    gateValue (renamed k p g) xs = gateValue g ys := by
  unfold gateValue renamed
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact heq i

lemma append_agree (k p : ℕ) (xs ys : List Bool) (b : Bool)
    (hlen : xs.length + 1 = ys.length) (hk : k < ys.length) (hp : p < k)
    (heq : ∀ i, xs.getD (redirect k p i) false = ys.getD i false) :
    ∀ i, (xs ++ [b]).getD (redirect k p i) false = (ys ++ [b]).getD i false := by
  intro i
  by_cases hi : i = k
  · subst i
    simp only [redirect, ite_true]
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hk]
    simpa [redirect] using heq k
  · simp only [redirect, ite_eq_right hi]
    apply Base.append_agree k xs ys b hlen hk _ i hi
    intro j hj
    simpa [redirect, hj] using heq j

lemma initial_agree (xs : List Bool) (p : ℕ) (b : Bool)
    (hcopy : b = xs.getD p false) :
    ∀ i, xs.getD (redirect xs.length p i) false = (xs ++ [b]).getD i false := by
  intro i
  by_cases hi : i = xs.length
  · subst i
    simp [redirect, List.getD_eq_getElem?_getD, hcopy]
  · simpa [redirect, hi] using Base.initial_agree xs b i hi

lemma wires_renamed (k p : ℕ) (gs : List Gate) (xs ys : List Bool)
    (hlen : xs.length + 1 = ys.length) (hk : k < ys.length) (hp : p < k)
    (heq : ∀ i, xs.getD (redirect k p i) false = ys.getD i false) :
    ∀ i, (Circuit.wires ⟨gs.map (renamed k p), 0⟩ xs).getD (redirect k p i) false =
      (Circuit.wires ⟨gs, 0⟩ ys).getD i false := by
  induction gs generalizing xs ys with
  | nil => exact heq
  | cons g gs ih =>
    have hg := renamed_value k p g xs ys heq
    change ∀ i,
      (Circuit.wires ⟨gs.map (renamed k p), 0⟩ (xs ++ [gateValue (renamed k p g) xs])).getD
        (redirect k p i) false =
      (Circuit.wires ⟨gs, 0⟩ (ys ++ [gateValue g ys])).getD i false
    rw [hg]
    apply ih _ _
    · simp only [List.length_append, List.length_singleton]; omega
    · simp only [List.length_append, List.length_singleton]; omega
    · exact append_agree k p xs ys _ hlen hk hp heq

lemma wires_input (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (Circuit.wires ⟨gs, 0⟩ xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (xs ++ [gateValue g xs])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

def erase (n : ℕ) (pre post : List Gate) (p o : ℕ) : Circuit :=
  ⟨pre ++ post.map (renamed (n + pre.length) p), redirect (n + pre.length) p o⟩

lemma erase_eval (n : ℕ) (pre post : List Gate) (g : Gate) (p o : ℕ)
    (hp : p < n + pre.length)
    (hcopy : ∀ x : Fin n → Bool,
      (Circuit.wires ⟨pre ++ g :: post, o⟩ (List.ofFn x)).getD (n + pre.length) false =
      (Circuit.wires ⟨pre ++ g :: post, o⟩ (List.ofFn x)).getD p false)
    (x : Fin n → Bool) :
    (erase n pre post p o).eval (List.ofFn x) =
      (Circuit.mk (pre ++ g :: post) o).eval (List.ofFn x) := by
  let xs := Circuit.wires ⟨pre, 0⟩ (List.ofFn x)
  have hx : xs.length = n + pre.length := by
    unfold xs
    rw [wires_length, List.length_ofFn]
  have hcopy' : gateValue g xs = xs.getD p false := by
    have h := hcopy x
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons] at h
    change (Circuit.wires ⟨post, 0⟩ (xs ++ [gateValue g xs])).getD (n + pre.length) false =
      (Circuit.wires ⟨post, 0⟩ (xs ++ [gateValue g xs])).getD p false at h
    rw [wires_input _ _ _ (by simp [hx]), wires_input _ _ _ (by simp [hx]; omega)] at h
    rw [List.getD_append xs [gateValue g xs] false p (by omega), ← hx] at h
    simpa [List.getD_eq_getElem?_getD] using h
  simp only [erase, Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
  change (Circuit.wires ⟨post.map (renamed (n + pre.length) p), 0⟩ xs).getD
      (redirect (n + pre.length) p o) false =
    (Circuit.wires ⟨post, 0⟩ (xs ++ [gateValue g xs])).getD o false
  apply wires_renamed _ _ _ _ _ (by simp) (by simp [hx]) hp _ o
  rw [← hx]
  exact initial_agree xs p _ hcopy'

lemma erase_size (n : ℕ) (pre post : List Gate) (g : Gate) (p o : ℕ) :
    (erase n pre post p o).size + 1 = (Circuit.mk (pre ++ g :: post) o).size := by
  simp [erase, Circuit.size]
  omega

lemma erase_monotone (n : ℕ) (pre post : List Gate) (g : Gate) (p o : ℕ)
    (hfan : Monotone2 (Circuit.mk (pre ++ g :: post) o)) :
    Monotone2 (erase n pre post p o) := by
  intro h hh
  change h ∈ pre ++ post.map (renamed (n + pre.length) p) at hh
  rcases List.mem_append.mp hh with hh | hh
  · exact hfan h (List.mem_append.mpr (Or.inl hh))
  · obtain ⟨q, hq, heq⟩ := List.mem_map.mp hh
    subst h
    have hhf := hfan q (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hq)))
    simpa [renamed] using hhf

lemma minimal_monotone_no_alias (n : ℕ) (C : Circuit) (hfan : Monotone2 C)
    (hmin : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (pre post : List Gate) (g : Gate) (hs : C.gates = pre ++ g :: post)
    (p : ℕ) (hp : p < n + pre.length) :
    ¬ ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + pre.length) false =
      (C.wires (List.ofFn x)).getD p false := by
  intro hcopy
  have hC : C = ⟨pre ++ g :: post, C.output⟩ := by cases C; simp_all
  have hD := erase_monotone n pre post g p C.output (hC ▸ hfan)
  have hsz := hmin (erase n pre post p C.output) hD (by
    intro x
    rw [erase_eval n pre post g p C.output hp (by simpa [← hC] using hcopy) x, ← hC])
  have hlen := erase_size n pre post g p C.output
  rw [← hC] at hlen
  omega

lemma minimal_monotone_no_alias_index (n : ℕ) (C : Circuit) (hfan : Monotone2 C)
    (hmin : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (k : ℕ) (hk : k < C.size) (p : ℕ) (hp : p < n + k) :
    ¬ ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + k) false = (C.wires (List.ofFn x)).getD p false := by
  have hk' : k < C.gates.length := hk
  have hs : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
    rw [List.getElem_cons_drop hk', List.take_append_drop]
  have hlen : (C.gates.take k).length = k := by simp; omega
  simpa [hlen] using minimal_monotone_no_alias n C hfan hmin _ _ _ hs p (by simpa [hlen] using hp)


lemma erase_or_copy_eval (n : ℕ) (pre post : List Gate) (p o : ℕ)
    (hp : p < n + pre.length) (x : Fin n → Bool) :
    (erase n pre post p o).eval (List.ofFn x) =
      (Circuit.mk (pre ++ ⟨GateOp.or, [p]⟩ :: post) o).eval (List.ofFn x) := by
  apply erase_eval n pre post ⟨GateOp.or, [p]⟩ p o hp ?_ x
  intro y
  let xs := Circuit.wires ⟨pre, 0⟩ (List.ofFn y)
  have hx : xs.length = n + pre.length := by
    unfold xs
    rw [Base.wires_length, List.length_ofFn]
  simp only [Circuit.wires, List.foldl_append, List.foldl_cons]
  change (Circuit.wires ⟨post, 0⟩ (xs ++ [gateValue ⟨GateOp.or, [p]⟩ xs])).getD
      (n + pre.length) false =
    (Circuit.wires ⟨post, 0⟩ (xs ++ [gateValue ⟨GateOp.or, [p]⟩ xs])).getD p false
  rw [wires_input _ _ _ (by simp [hx]), wires_input _ _ _ (by simp [hx]; omega)]
  rw [List.getD_append xs [gateValue ⟨GateOp.or, [p]⟩ xs] false p (by omega), ← hx]
  simp [gateValue, GateOp.eval, List.getD_eq_getElem?_getD]

lemma copy_replacement_improves (n : ℕ) (pre post : List Gate) (g : Gate) (p o : ℕ)
    (hp : p < n + pre.length)
    (hm : Monotone2 (Circuit.mk (pre ++ g :: post) o))
    (hreplace : ∀ x : Fin n → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.or, [p]⟩ :: post) o).eval (List.ofFn x) =
      (Circuit.mk (pre ++ g :: post) o).eval (List.ofFn x)) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + 1 = (Circuit.mk (pre ++ g :: post) o).size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        (Circuit.mk (pre ++ g :: post) o).eval (List.ofFn x) := by
  refine ⟨erase n pre post p o, erase_monotone n pre post g p o hm,
    erase_size n pre post g p o, ?_⟩
  intro x
  exact (erase_or_copy_eval n pre post p o hp x).trans (hreplace x)

lemma minimum_forbids_copy_replacement (n : ℕ) (pre post : List Gate)
    (g : Gate) (p o : ℕ) (hp : p < n + pre.length)
    (hm : Monotone2 (Circuit.mk (pre ++ g :: post) o))
    (hmin : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        (Circuit.mk (pre ++ g :: post) o).eval (List.ofFn x)) →
      (Circuit.mk (pre ++ g :: post) o).size ≤ D.size) :
    ¬ ∀ x : Fin n → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.or, [p]⟩ :: post) o).eval (List.ofFn x) =
      (Circuit.mk (pre ++ g :: post) o).eval (List.ofFn x) := by
  intro hreplace
  obtain ⟨D, hD, hsize, heval⟩ := copy_replacement_improves n pre post g p o hp hm hreplace
  have hle := hmin D hD heval
  omega

end AliasMonotone

namespace BoundaryDominance

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2373.BoundaryTransport

def prefixWire (pre : List Gate) (p : ℕ) (x : Fin 10 → Bool) : Bool :=
  (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD p false

def newGateValue (pre : List Gate) (g : Gate) (x : Fin 10 → Bool) : Bool :=
  g.op.eval (g.inputs.map (fun p => prefixWire pre p x))

lemma split_eval (pre post : List Gate) (g : Gate) (o : ℕ) (x : Fin 10 → Bool) :
    (Circuit.mk (pre ++ g :: post) o).eval (List.ofFn x) =
      (Circuit.mk post o).eval ((Circuit.mk pre 0).wires (List.ofFn x) ++ [newGateValue pre g x]) := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
  rfl

lemma copy_value (pre : List Gate) (p : ℕ) (x : Fin 10 → Bool) :
    newGateValue pre ⟨GateOp.or, [p]⟩ x = prefixWire pre p x := by
  simp [newGateValue, GateOp.eval]

lemma append_bool_order (w : List Bool) (a b : Bool) (h : a = true → b = true) :
    ∀ j, (w ++ [a]).getD j false = true → (w ++ [b]).getD j false = true := by
  intro j hj
  by_cases hlt : j < w.length
  · rw [List.getD_append _ _ _ _ hlt] at hj ⊢
    exact hj
  · by_cases heq : j = w.length
    · subst j
      rw [getD_snoc_eq] at hj ⊢
      exact h hj
    · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
      contradiction

lemma copy_replacement_monotone (pre post : List Gate) (g : Gate) (p o : ℕ)
    (hm : Monotone2 (Circuit.mk (pre ++ g :: post) o)) :
    Monotone2 (Circuit.mk (pre ++ ⟨GateOp.or, [p]⟩ :: post) o) := by
  intro q hq
  rcases List.mem_append.mp hq with hpre | hpost
  · exact hm q (List.mem_append.mpr (Or.inl hpre))
  · rcases List.mem_cons.mp hpost with rfl | hpost
    · exact ⟨by simp, by simp⟩
    · exact hm q (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hpost)))

lemma dominated_copy_computes (pre post : List Gate) (g : Gate) (p o : ℕ)
    (hm : Monotone2 (Circuit.mk (pre ++ g :: post) o))
    (hexact : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ g :: post) o).eval (List.ofFn x) = edge x)
    (hpos : ∀ r ∈ pos,
      newGateValue pre g (bits r) = true → prefixWire pre p (bits r) = true)
    (hneg : ∀ r ∈ neg,
      prefixWire pre p (bits r) = true → newGateValue pre g (bits r) = true) :
    ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.or, [p]⟩ :: post) o).eval (List.ofFn x) = edge x := by
  let D := Circuit.mk (pre ++ ⟨GateOp.or, [p]⟩ :: post) o
  have hD : Monotone2 D := copy_replacement_monotone pre post g p o hm
  have hpost : Monotone2 (Circuit.mk post o) := by
    intro q hq
    exact hm q (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hq)))
  have hmono : InputMono (fun x : Fin 10 → Bool => D.eval (List.ofFn x)) := by
    intro a b hab
    have h := bankEval_mono D hD (fun i : Fin 10 => fun x => x i)
      (fun i a b hab => hab i) a b hab
    simpa only [bankEval] using h
  apply liftRows _ hmono
  intro r hr
  by_cases hp : r ∈ pos
  · have ha : (Circuit.mk (pre ++ g :: post) o).eval (List.ofFn (bits r)) = true := by
      rw [hexact, boundary_values r hr]
      simp [hp]
    rw [split_eval] at ha
    have hb := eval_mono (Circuit.mk post o) hpost _ _ (by simp)
      (append_bool_order ((Circuit.mk pre 0).wires (List.ofFn (bits r)))
        (newGateValue pre g (bits r)) (prefixWire pre p (bits r)) (hpos r hp)) ha
    change (Circuit.mk (pre ++ ⟨GateOp.or, [p]⟩ :: post) o).eval _ = _
    rw [split_eval, copy_value]
    simpa [hp] using hb
  · have hn : r ∈ neg := (rows_pos_or_neg r hr).resolve_left hp
    have ha : (Circuit.mk (pre ++ g :: post) o).eval (List.ofFn (bits r)) = false := by
      rw [hexact, boundary_values r hr]
      simp [hp]
    rw [split_eval] at ha
    change (Circuit.mk (pre ++ ⟨GateOp.or, [p]⟩ :: post) o).eval _ = _
    rw [split_eval, copy_value]
    cases hb : (Circuit.mk post o).eval
        ((Circuit.mk pre 0).wires (List.ofFn (bits r)) ++ [prefixWire pre p (bits r)]) with
    | false => simp [hp]
    | true =>
      have hc := eval_mono (Circuit.mk post o) hpost _ _ (by simp)
        (append_bool_order ((Circuit.mk pre 0).wires (List.ofFn (bits r)))
          (prefixWire pre p (bits r)) (newGateValue pre g (bits r)) (hneg r hn)) hb
      rw [ha] at hc
      contradiction

lemma dominated_gate_improves (pre post : List Gate) (g : Gate) (p o : ℕ)
    (hp : p < 10 + pre.length)
    (hm : Monotone2 (Circuit.mk (pre ++ g :: post) o))
    (hexact : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ g :: post) o).eval (List.ofFn x) = edge x)
    (hpos : ∀ r ∈ pos,
      newGateValue pre g (bits r) = true → prefixWire pre p (bits r) = true)
    (hneg : ∀ r ∈ neg,
      prefixWire pre p (bits r) = true → newGateValue pre g (bits r) = true) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + 1 = (Circuit.mk (pre ++ g :: post) o).size ∧
      ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = edge x := by
  have hcopy := dominated_copy_computes pre post g p o hm hexact hpos hneg
  obtain ⟨D, hD, hsize, heval⟩ := AliasMonotone.copy_replacement_improves 10 pre post g p o hp hm
    (fun x => (hcopy x).trans (hexact x).symm)
  exact ⟨D, hD, hsize, fun x => (heval x).trans (hexact x)⟩

lemma minimum_forbids_dominated_gate (pre post : List Gate) (g : Gate) (p o : ℕ)
    (hp : p < 10 + pre.length)
    (hm : Monotone2 (Circuit.mk (pre ++ g :: post) o))
    (hexact : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ g :: post) o).eval (List.ofFn x) = edge x)
    (hmin : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = edge x) →
      (Circuit.mk (pre ++ g :: post) o).size ≤ D.size) :
    ¬ ((∀ r ∈ pos,
        newGateValue pre g (bits r) = true → prefixWire pre p (bits r) = true) ∧
      (∀ r ∈ neg,
        prefixWire pre p (bits r) = true → newGateValue pre g (bits r) = true)) := by
  rintro ⟨hpos, hneg⟩
  obtain ⟨D, hD, hsize, heval⟩ := dominated_gate_improves pre post g p o hp hm hexact hpos hneg
  have hle := hmin D hD heval
  omega

end BoundaryDominance


namespace SafeLower
def bipartiteAbove {α β : Type*} (r : α → β → Prop) [DecidableRel r]
    (t : Finset β) (a : α) := t.filter (r a)
def bipartiteBelow {α β : Type*} (r : α → β → Prop) [DecidableRel r]
    (s : Finset α) (b : β) := s.filter (fun a => r a b)
lemma double_count {α β : Type*} (s : Finset α) (t : Finset β)
    (r : α → β → Prop) [DecidableRel r] :
    (∑ a ∈ s, (bipartiteAbove r t a).card) =
      ∑ b ∈ t, (bipartiteBelow r s b).card := by
  simp only [bipartiteAbove, bipartiteBelow,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm
end SafeLower



-- The argument below is the checked proof of L-meta-1491 from this repository (Apache-2.0),
-- with its namespace renamed; the last lemma restates it in the form posted for L-meta-5781.

namespace SafeLower.Source5781

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

namespace S90


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_eq : OpMono Eq := by
  intro op _ l f g h
  rw [List.map_congr_left h]

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

open PEqualNP.EdgeOwnership in
lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

open PEqualNP.EdgeOwnership in
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

open PEqualNP.EdgeOwnership in
lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

open PEqualNP.EdgeOwnership in
lemma side_adj {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hbel : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + a) = true → F x = true)
    (p q : ℕ) (hin : (gateAt C a).inputs = [p, q]) (hp : p < n + a) (hq : q < n + a)
    (u v : Fin n) (hu : Relation.ReflTransGen (OrStep n C) p u.val)
    (hv : Relation.ReflTransGen (OrStep n C) q v.val) : G.Adj u v := by
  apply hF
  apply hbel
  rw [val_and (n := n) (by simp) ha hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, reach_var_val _ _ u hu (pairInput_left u v)⟩
  · exact ⟨hq, reach_var_val _ _ v hv (pairInput_right u v)⟩

open PEqualNP.EdgeOwnership in
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv

open PEqualNP.EdgeOwnership

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩

open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

open PEqualNP.TopForm in
lemma top_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (a : ℕ) (ha : a ∈ tops G C) :
    Disjoint (side (n := n) C a 0) (side (n := n) C a 1) ∧
    (∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v) ∧
    ((side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1) := by
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨halen, hop, hbel⟩ := ha
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have hp : p < n + a := hRB a halen p (by rw [hin]; simp)
  have hq : q < n + a := hRB a halen q (by rw [hin]; simp)
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hadj : ∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v := by
    intro u hu v hv
    simp only [side, e0] at hu
    simp only [side, e1] at hv
    exact side_adj G (graphFun G ∅) (fun u v h => (graphFun_pair G u v).mp h) a halen hop hbel
      p q hin hp hq u v (mem_orIn_reach u hu) (mem_orIn_reach v hv)
  refine ⟨?_, hadj, ?_⟩
  · rw [Finset.disjoint_left]
    intro u hu hv
    exact G.irrefl (hadj u hu u hv)
  · by_contra hcon
    simp only [not_or, not_le] at hcon
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcon.1
    have hsub : side (n := n) C a 1 ⊆ Finset.univ.filter (fun w => G.Adj x w ∧ G.Adj y w) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hadj x hx w hw, hadj y hy w hw⟩
    have h5 := Finset.card_le_card hsub
    have h6 := h4 x y hxy
    omega

open PEqualNP.TopForm in
lemma off_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : PEqualNP.TopForm.TopForm G C) (u v : Fin n)
    (huv : s(u, v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
      gateVal n C a (pairInput u v) = true ∧
      OrReaches n C (opnd C a b) h ∧
      gateVal n C h (pairInput u v) = true := by
  obtain ⟨⟨hAO, hRB, h2⟩, hfun, _⟩ := hL
  simp only [Ustar, Finset.mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at huv
  obtain ⟨hadj, hns⟩ := huv
  have hF : ∀ u v : Fin n, graphFun G ∅ (pairInput u v) = true → G.Adj u v :=
    fun u v h => (graphFun_pair G u v).mp h
  have hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = graphFun G ∅ x :=
    fun x => congrFun hfun x
  obtain ⟨a, halen, hnor, hreach, hval⟩ :=
    edge_trace G (graphFun G ∅) hF hout u v ((graphFun_pair G u v).mpr hadj)
  have hop : (gateAt C a).op = GateOp.and := by
    rcases hAO _ (gateAt_mem halen) with h | h
    · exact h
    · exact (hnor h).elim
  have hbel : BelowF G C a := fun x hx => below_of_reach (graphFun G ∅) hout a hreach x hx
  have hatop : a ∈ tops G C := by
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨halen, hop, hbel⟩
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hpq := (val_and (n := n) (by simp) halen hop).mp hval
  have hp := hpq p (by rw [hin]; simp)
  have hq := hpq q (by rw [hin]; simp)
  have junk_of : ∀ (w : ℕ) (b : Fin 2), opnd C a b = w → w ∈ (gateAt C a).inputs → w < n + a →
      ∀ h, h < C.gates.length → (gateAt C h).op ≠ GateOp.or →
      Relation.ReflTransGen (OrStep n C) w (n + h) →
      val C (List.ofFn (pairInput u v)) (n + h) = true →
      ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ h ∈ junk G C,
        gateVal n C a (pairInput u v) = true ∧
        OrReaches n C (opnd C a b) h ∧
        gateVal n C h (pairInput u v) = true := by
    intro w b hb hwin hwlt h hh hhor hr hv
    have hhand : (gateAt C h).op = GateOp.and := by
      rcases hAO _ (gateAt_mem hh) with h3 | h3
      · exact h3
      · exact (hhor h3).elim
    have hcone : InCone n C h a := operand_cone halen hwin hwlt hr
    have hnb : ¬ BelowF G C h := fun hb2 => hT h hh a halen hhand hb2 hop hcone
    have hdirty : IsDirtyAnd n G C h := by
      unfold IsDirtyAnd IsDirty
      refine ⟨hhand, hh, ?_⟩
      by_contra hne
      apply hnb
      intro x hx
      by_contra hfx
      exact hne ⟨x, hx, Bool.eq_false_iff.mpr hfx⟩
    have hjunk : h ∈ junk G C := by
      unfold junk gatesWhere
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hdirty⟩
    refine ⟨a, hatop, b, h, hjunk, hval, ?_, hv⟩
    rw [hb]
    exact reach_orReaches hr h rfl hh
  rcases operand_trace (C := C) u v p hp.2 with ⟨t1, ht1, hr1⟩ | ⟨h, hh, hhor, hr, hv⟩
  · rcases operand_trace (C := C) u v q hq.2 with ⟨t2, ht2, hr2⟩ | ⟨h, hh, hhor, hr, hv⟩
    · exfalso
      apply hns
      have hadj12 : G.Adj t1 t2 :=
        side_adj G (graphFun G ∅) hF a halen hop hbel p q hin hp.1 hq.1 t1 t2 hr1 hr2
      have hne : t1 ≠ t2 := G.ne_of_adj hadj12
      have hs : s(u, v) = s(t1, t2) := by
        rcases ht1 with h1 | h1 <;> rcases ht2 with h2 | h2
        · exact (hne (h1.trans h2.symm)).elim
        · rw [h1, h2]
        · rw [h1, h2]; exact Sym2.eq_swap
        · exact (hne (h1.trans h2.symm)).elim
      rw [hs]
      simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
      refine ⟨a, hatop, (t1, t2), ⟨?_, ?_⟩, rfl⟩
      · simp only [side, e0]
        exact reach_mem_orIn t1 hr1
      · simp only [side, e1]
        exact reach_mem_orIn t2 hr2
    · exact junk_of q 1 e1 (by rw [hin]; simp) hq.1 h hh hhor hr hv
  · exact junk_of p 0 e0 (by rw [hin]; simp) hp.1 h hh hhor hr hv

end S90

namespace S98


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

def shiftDown (wOld u : ℕ) : ℕ :=
  if wOld < u then u - 1 else u

def wiresMatch (w0 : List Bool) (bOld : Bool) (wC wD : List Bool) : Prop :=
  wC.length = wD.length + 1 ∧
  w0.length ≤ wD.length ∧
  wC.getD w0.length false = bOld ∧
  (∀ u, u < w0.length → wD.getD u false = w0.getD u false) ∧
  (∀ u, u < w0.length → wC.getD u false = w0.getD u false) ∧
  (∀ u, w0.length < u → wD.getD (u - 1) false = wC.getD u false)

lemma wiresMatch_init (w0 : List Bool) (bOld : Bool) :
    wiresMatch w0 bOld (w0 ++ [bOld]) w0 := by
  refine ⟨by simp, le_rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD]
  · intro u hu
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
  · intro u hu
    have h1 : w0.length ≤ u - 1 := by omega
    have h2 : (w0 ++ [bOld]).length ≤ u := by simp; omega
    rw [getD_ge_length w0 (u - 1) h1, getD_ge_length (w0 ++ [bOld]) u h2]

lemma wiresMatch_step {w0 : List Bool} {bOld : Bool} {wC wD : List Bool} {b : Bool}
    (hm : wiresMatch w0 bOld wC wD) :
    wiresMatch w0 bOld (wC ++ [b]) (wD ++ [b]) := by
  obtain ⟨hlen, hle, hbold, hltD, hltC, hgt⟩ := hm
  refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩
  · have hlt : w0.length < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    simpa [List.getD_eq_getElem?_getD] using hbold
  · intro u hu
    have h1 : u < wD.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    simpa [List.getD_eq_getElem?_getD] using hltD u hu
  · intro u hu
    have h2 : u < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2]
    simpa [List.getD_eq_getElem?_getD] using hltC u hu
  · intro u hu
    by_cases h1 : u - 1 < wD.length
    · have h2 : u < wC.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left h1, List.getElem?_append_left h2]
      simpa [List.getD_eq_getElem?_getD] using hgt u hu
    · by_cases heq : u - 1 = wD.length
      · have heqC : u = wC.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, heq, heqC,
            List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
        simp
      · have hg1 : (wD ++ [b]).length ≤ u - 1 := by simp; omega
        have hg2 : (wC ++ [b]).length ≤ u := by simp; omega
        rw [getD_ge_length _ _ hg1, getD_ge_length _ _ hg2]

lemma wiresMatch_getD_shiftDown {w0 : List Bool} {bOld : Bool} {wC wD : List Bool}
    (hm : wiresMatch w0 bOld wC wD) {u : ℕ} (hne : u ≠ w0.length) :
    wD.getD (shiftDown w0.length u) false = wC.getD u false := by
  unfold shiftDown
  by_cases hgt : w0.length < u
  · simp only [hgt, ↓reduceIte]; exact hm.2.2.2.2.2 u hgt
  · simp only [hgt, ↓reduceIte]
    have hlt : u < w0.length := by omega
    rw [hm.2.2.2.1 u hlt, hm.2.2.2.2.1 u hlt]

lemma foldl_wiresMatch (w0 : List Bool) (bOld : Bool) (gsC gsD : List Gate)
    (wC wD : List Bool) (hm : wiresMatch w0 bOld wC wD) (hlen : gsD.length = gsC.length)
    (hstep : ∀ (t : ℕ) (htC : t < gsC.length) (htD : t < gsD.length) (vC vD : List Bool),
      wiresMatch w0 bOld vC vD → vD.length = wD.length + t →
      (gsD[t]'htD).op.eval ((gsD[t]'htD).inputs.map fun i => vD.getD i false) =
      (gsC[t]'htC).op.eval ((gsC[t]'htC).inputs.map fun i => vC.getD i false)) :
    wiresMatch w0 bOld (gsC.foldl stepWire wC) (gsD.foldl stepWire wD) := by
  induction gsC generalizing gsD wC wD with
  | nil =>
    cases gsD with
    | nil => exact hm
    | cons => simp at hlen
  | cons gC restC ih =>
    cases gsD with
    | nil => simp at hlen
    | cons gD restD =>
      simp only [List.foldl_cons]
      have heq0 := hstep 0 (by simp) (by simp) wC wD hm (by simp)
      simp only [List.getElem_cons_zero] at heq0
      have hm1 : wiresMatch w0 bOld (stepWire wC gC) (stepWire wD gD) := by
        unfold stepWire
        rw [heq0]
        exact wiresMatch_step hm
      apply ih restD (stepWire wC gC) (stepWire wD gD) hm1 (by simp at hlen; omega)
      intro t htC htD vC vD hmv hvlen
      have h' := hstep (t + 1) (by simp; omega) (by simp; omega) vC vD hmv
        (by simp [stepWire] at hvlen ⊢; omega)
      simpa only [List.getElem_cons_succ] using h'

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def aliasWire (wOld wNew u : ℕ) : ℕ :=
  if u = wOld then wNew else shiftDown wOld u

def aliasGate (wOld wNew : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (aliasWire wOld wNew)⟩

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

def eraseC (n : ℕ) (C : Circuit) (j i : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (aliasGate (n + j) i),
    aliasWire (n + j) i C.output⟩

def appOr (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or, [a, b]⟩], n + C.gates.length⟩

def truncC (C : Circuit) (m : ℕ) : Circuit :=
  ⟨C.gates.take m, C.output⟩

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma erase_wires (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (x : Fin n → Bool)
    (h : W n C x i = W n C x (n + j) ∨
      ∀ k, j < k → k < C.gates.length → n + j ∉ (gateAt C k).inputs) :
    ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
      W n (eraseC n C j i) x (aliasWire (n + j) i u) = W n C x u := by
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj
  have hlenC : C.gates.length = pre.length + 1 + post.length := by
    have := congrArg List.length hgs; simp at this; omega
  have htake : C.gates.take j = pre := by rw [hgs, ← hpre_len]; simp
  have hdrop : C.gates.drop (j + 1) = post := by rw [hgs, ← hpre_len]; simp
  intro u hu
  simp only [W, eraseC, wires_eq_foldl, htake, hdrop]
  conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
  rw [List.foldl_append]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + j := by
    simp [w0, foldl_stepWire_length, hpre_len]
  let bOld := gj.op.eval (gj.inputs.map fun k => w0.getD k false)
  have hCi : W n C x i = w0.getD i false := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)
  have hCj : W n C x (n + j) = bOld := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len, bOld]
  have hm0 : wiresMatch w0 bOld (stepWire w0 gj) w0 := wiresMatch_init w0 bOld
  have halias_get : ∀ (vC vD : List Bool), wiresMatch w0 bOld vC vD →
      ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
        vD.getD (aliasWire (n + j) i u) false = vC.getD u false := by
    intro vC vD hmv u hu'
    unfold aliasWire
    by_cases hu : u = n + j
    · have hval_eq : w0.getD i false = bOld := by rw [← hCi, ← hCj]; exact hu' hu
      subst hu
      simp only [↓reduceIte]
      rw [hmv.2.2.2.1 i (by omega), hval_eq, ← hw0_len, hmv.2.2.1]
    · simp only [hu, ↓reduceIte]
      rw [← hw0_len]
      exact wiresMatch_getD_shiftDown hmv (by omega)
  have hmEnd : wiresMatch w0 bOld (post.foldl stepWire (stepWire w0 gj))
      ((post.map (aliasGate (n + j) i)).foldl stepWire w0) := by
    refine foldl_wiresMatch w0 bOld post (post.map (aliasGate (n + j) i)) (stepWire w0 gj) w0 hm0
      (by simp) ?_
    intro t htC htD vC vD hmv _
    simp only [List.getElem_map, aliasGate, List.map_map]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    refine halias_get vC vD hmv u ?_
    intro hun
    rcases h with h | h
    · exact h
    · exfalso
      have hget : gateAt C (j + 1 + t) = post[t] := by
        rw [gateAt_eq C (j + 1 + t) (by omega)]
        have h1 : (pre ++ gj :: post)[j + 1 + t]'(by rw [← hgs]; omega) = post[t]'htC := by
          rw [List.getElem_append_right (by omega)]
          have hsub : j + 1 + t - pre.length = t + 1 := by omega
          simp [hsub]
        simpa [hgs] using h1
      exact h (j + 1 + t) (by omega) (by omega) (by rw [hget, ← hun]; exact hu)
  exact halias_get _ _ hmEnd u hu

lemma erase_length (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) :
    (eraseC n C j i).gates.length + 1 = C.gates.length := by
  simp [eraseC]; omega

lemma erase_gateAt_lt (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : k < j) :
    gateAt (eraseC n C j i) k = gateAt C k := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega)]
  simp [hk]

lemma erase_gateAt_ge (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : j ≤ k)
    (hk2 : k + 1 < C.gates.length) :
    gateAt (eraseC n C j i) k = aliasGate (n + j) i (gateAt C (k + 1)) := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  have h1 : (List.take j C.gates).length = j := by simp; omega
  have h2 : j + 1 + (k - j) = k + 1 := by omega
  rw [h1, List.getElem?_map, List.getElem?_drop, h2, List.getElem?_eq_getElem hk2]
  rfl

lemma prefix_W (n : ℕ) (pre rest1 rest2 : List Gate) (o1 o2 : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + pre.length) :
    W n ⟨pre ++ rest1, o1⟩ x u = W n ⟨pre ++ rest2, o2⟩ x u := by
  simp only [W, wires_eq_foldl, List.foldl_append]
  have h : u < (pre.foldl stepWire (List.ofFn x)).length := by
    rw [foldl_stepWire_length]; simpa using hu
  rw [foldl_stepWire_getD_lt rest1 (pre.foldl stepWire (List.ofFn x)) u h,
    foldl_stepWire_getD_lt rest2 (pre.foldl stepWire (List.ofFn x)) u h]

lemma erase_W_lt (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool)
    (u : ℕ) (hu : u < n + j) : W n (eraseC n C j i) x u = W n C x u := by
  have h := prefix_W n (C.gates.take j) ((C.gates.drop (j + 1)).map (aliasGate (n + j) i))
    (C.gates.drop j) (aliasWire (n + j) i C.output) C.output x u
    (by rw [List.length_take]; omega)
  have e2 : (⟨C.gates.take j ++ C.gates.drop j, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h

lemma appOr_W_lt (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + C.gates.length) : W n (appOr n C a b) x u = W n C x u := by
  have h := prefix_W n C.gates [⟨GateOp.or, [a, b]⟩] [] (n + C.gates.length) C.output x u hu
  have e2 : (⟨C.gates ++ [], C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma appOr_gateAt_lt (n : ℕ) (C : Circuit) (a b k : ℕ) (hk : k < C.gates.length) :
    gateAt (appOr n C a b) k = gateAt C k := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma appOr_gateAt_last (n : ℕ) (C : Circuit) (a b : ℕ) :
    gateAt (appOr n C a b) C.gates.length = ⟨GateOp.or, [a, b]⟩ := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD]

lemma appOr_eval (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    (appOr n C a b).eval (List.ofFn x) = (W n C x a || W n C x b) := by
  have h := W_or n (appOr n C a b) x C.gates.length (by simp [appOr]) (by rw [appOr_gateAt_last])
    a b (by rw [appOr_gateAt_last]) ha hb
  rw [appOr_W_lt n C a b x a ha, appOr_W_lt n C a b x b hb] at h
  exact h

def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k

def Least (n : ℕ) (C : Circuit) : Prop :=
  AO n C ∧ ∀ D : Circuit, AO n D →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
    C.gates.length ≤ D.gates.length

def Bel (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  ∀ x : Fin n → Bool, W n C x (n + j) = true → C.eval (List.ofFn x) = true

lemma alias_lt (w i u N : ℕ) (hu : u < N + 1) (hi : i < w) (hw : w ≤ N) :
    aliasWire w i u < N := by
  unfold aliasWire shiftDown
  split_ifs <;> omega

lemma erase_AO (n : ℕ) (C : Circuit) (j i : ℕ) (hA : AO n C) (hj : j < C.gates.length)
    (hi : i < n + j) : AO n (eraseC n C j i) := by
  intro k hk
  have hlen := erase_length n C j i hj
  by_cases hkj : k < j
  · rw [erase_gateAt_lt n C j i k hj hkj]; exact hA k (by omega)
  · rw [erase_gateAt_ge n C j i k hj (by omega) (by omega)]
    obtain ⟨hop, a, b, hin, ha, hb⟩ := hA (k + 1) (by omega)
    refine ⟨hop, aliasWire (n + j) i a, aliasWire (n + j) i b, by simp [aliasGate, hin], ?_, ?_⟩
    · exact alias_lt (n + j) i a (n + k) (by omega) hi (by omega)
    · exact alias_lt (n + j) i b (n + k) (by omega) hi (by omega)

lemma appOr_AO (n : ℕ) (C : Circuit) (a b : ℕ) (hA : AO n C) (ha : a < n + C.gates.length)
    (hb : b < n + C.gates.length) : AO n (appOr n C a b) := by
  intro k hk
  have hlen : (appOr n C a b).gates.length = C.gates.length + 1 := by simp [appOr]
  by_cases hkl : k < C.gates.length
  · rw [appOr_gateAt_lt n C a b k hkl]; exact hA k hkl
  · have hke : k = C.gates.length := by omega
    subst hke
    rw [appOr_gateAt_last]
    exact ⟨Or.inr rfl, a, b, rfl, ha, hb⟩

lemma trunc_AO (n : ℕ) (C : Circuit) (m : ℕ) (hA : AO n C) (hm : m ≤ C.gates.length) :
    AO n (truncC C m) := by
  intro k hk
  have hk' : k < m := by simp [truncC] at hk; omega
  have h : gateAt (truncC C m) k = gateAt C k := by
    simp [gateAt, truncC, List.getD_eq_getElem?_getD, hk']
  rw [h]; exact hA k (by omega)

lemma trunc_W (n : ℕ) (C : Circuit) (m : ℕ) (x : Fin n → Bool) (u : ℕ) (hm : m ≤ C.gates.length)
    (hu : u < n + m) : W n (truncC C m) x u = W n C x u := by
  have h := prefix_W n (C.gates.take m) [] (C.gates.drop m) C.output C.output x u
    (by rw [List.length_take]; omega)
  have e1 : (⟨C.gates.take m ++ [], C.output⟩ : Circuit) = truncC C m := by simp [truncC]
  have e2 : (⟨C.gates.take m ++ C.gates.drop m, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e1, e2] at h
  exact h

lemma least_out (n : ℕ) (C : Circuit) (hL : Least n C)
    (hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false) :
    n ≤ C.output ∧ C.output + 1 = n + C.gates.length := by
  have h1 : n ≤ C.output := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, hf⟩ := hV ⟨C.output, h⟩
    have h2 : W n C x C.output = true := (W_input n C x C.output h).trans hx
    have h3 : W n C x C.output = false := hf
    rw [h2] at h3
    exact absurd h3 (by simp)
  have h2 : C.output < n + C.gates.length := by
    by_contra h
    obtain ⟨x, hx⟩ := hT
    have h3 : W n C x C.output = true := hx
    simp only [W] at h3
    rw [getD_ge_length _ _ (by rw [wires_length]; omega)] at h3
    exact absurd h3 (by simp)
  refine ⟨h1, ?_⟩
  by_contra h3
  have hm : C.output - n + 1 < C.gates.length := by omega
  have hfun : ∀ x : Fin n → Bool,
      (truncC C (C.output - n + 1)).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    trunc_W n C (C.output - n + 1) x C.output (by omega) (by omega)
  have h4 := hL.2 _ (trunc_AO n C (C.output - n + 1) hL.1 (by omega)) hfun
  simp [truncC] at h4
  omega

lemma least_read (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hj : j + 1 < C.gates.length) :
    ∃ k, j < k ∧ k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
  by_contra hno
  push Not at hno
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hL.1 j (by omega)
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j a).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j a (by omega) ha x (Or.inr hno) C.output (by intro h; omega)
  have h1 := hL.2 _ (erase_AO n C j a hL.1 (by omega) ha) hfun
  have h2 := erase_length n C j a (by omega)
  omega

lemma least_nodup (n : ℕ) (C : Circuit) (hL : Least n C) (i j : ℕ) (hij : i < n + j)
    (hj : j < C.gates.length) : ∃ x : Fin n → Bool, W n C x i ≠ W n C x (n + j) := by
  by_contra hsame
  push Not at hsame
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j i).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j i hj hij x (Or.inl (hsame x)) C.output (fun _ => hsame x)
  have h1 := hL.2 _ (erase_AO n C j i hL.1 hj hij) hfun
  have h2 := erase_length n C j i hj
  omega

lemma red (n : ℕ) (C : Circuit) (hA : AO n C) (j r : ℕ) (hr : r < C.gates.length)
    (hmem : n + j ∈ (gateAt C r).inputs) :
    ∃ p, p < n + r ∧
      ∀ x : Fin n → Bool, W n C x (n + j) = false → W n C x p = W n C x (n + r) := by
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hA r hr
  rw [hin] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hop with hop | hop
  · refine ⟨n + j, by rcases hmem with h | h <;> omega, fun x hx => ?_⟩
    rw [W_and n C x r hr hop a b hin ha hb, hx]
    rcases hmem with h | h
    · rw [← h, hx]; simp
    · rw [← h, hx]; simp
  · rcases hmem with h | h
    · refine ⟨b, hb, fun x hx => ?_⟩
      rw [W_or n C x r hr hop a b hin ha hb, ← h, hx]; simp
    · refine ⟨a, ha, fun x hx => ?_⟩
      rw [W_or n C x r hr hop a b hin ha hb, ← h, hx]; simp

lemma two_readers (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hB : Bel n C j) (r1 r2 : ℕ)
    (h12 : r1 < r2) (hr2 : r2 < C.gates.length)
    (hm1 : n + j ∈ (gateAt C r1).inputs) (hm2 : n + j ∈ (gateAt C r2).inputs) : False := by
  have hA := hL.1
  have hj1 : j < r1 := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA r1 (by omega)
    rw [hin] at hm1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1
    omega
  obtain ⟨p2, hp2, hv2⟩ := red n C hA j r2 hr2 hm2
  have hA1 := erase_AO n C r2 p2 hA hr2 hp2
  have hl1 := erase_length n C r2 p2 hr2
  have hW1 : ∀ (x : Fin n → Bool) (u : ℕ), u < n + r2 →
      W n (eraseC n C r2 p2) x u = W n C x u := fun x u hu => erase_W_lt n C r2 p2 hr2 x u hu
  have hg1 : gateAt (eraseC n C r2 p2) r1 = gateAt C r1 := erase_gateAt_lt n C r2 p2 r1 hr2 h12
  obtain ⟨p1, hp1, hv1⟩ := red n (eraseC n C r2 p2) hA1 j r1 (by omega) (by rw [hg1]; exact hm1)
  have hA2 := erase_AO n (eraseC n C r2 p2) r1 p1 hA1 (by omega) hp1
  have hl2 := erase_length n (eraseC n C r2 p2) r1 p1 (by omega)
  have ho1 : (eraseC n C r2 p2).output < n + (eraseC n C r2 p2).gates.length :=
    alias_lt (n + r2) p2 C.output _ (by omega) hp2 (by omega)
  have ho2 : (eraseC n (eraseC n C r2 p2) r1 p1).output <
      n + (eraseC n (eraseC n C r2 p2) r1 p1).gates.length :=
    alias_lt (n + r1) p1 (eraseC n C r2 p2).output _ (by omega) hp1 (by omega)
  have hfun : ∀ x : Fin n → Bool,
      (appOr n (eraseC n (eraseC n C r2 p2) r1 p1)
        (eraseC n (eraseC n C r2 p2) r1 p1).output (n + j)).eval (List.ofFn x) =
        C.eval (List.ofFn x) := by
    intro x
    rw [appOr_eval n _ _ (n + j) x ho2 (by omega)]
    have hj2 : W n (eraseC n (eraseC n C r2 p2) r1 p1) x (n + j) = W n C x (n + j) := by
      rw [erase_W_lt n _ r1 p1 (by omega) x (n + j) (by omega), hW1 x (n + j) (by omega)]
    rw [hj2]
    cases hx : W n C x (n + j)
    · have e2 := erase_wires n C r2 p2 hr2 hp2 x (Or.inl (hv2 x hx)) C.output (fun _ => hv2 x hx)
      have hx1 : W n (eraseC n C r2 p2) x (n + j) = false := by
        rw [hW1 x _ (by omega)]; exact hx
      have e1 := erase_wires n (eraseC n C r2 p2) r1 p1 (by omega) hp1 x (Or.inl (hv1 x hx1))
        (eraseC n C r2 p2).output (fun _ => hv1 x hx1)
      rw [Bool.or_false]
      exact e1.trans e2
    · rw [Bool.or_true]; exact (hB x hx).symm
  have h1 := hL.2 _ (appOr_AO n _ _ (n + j) hA2 ho2 (by omega)) hfun
  have h2 : (appOr n (eraseC n (eraseC n C r2 p2) r1 p1)
      (eraseC n (eraseC n C r2 p2) r1 p1).output (n + j)).gates.length =
      (eraseC n (eraseC n C r2 p2) r1 p1).gates.length + 1 := by simp [appOr]
  omega

lemma one_reader (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hj : j < C.gates.length)
    (hB : Bel n C j) (hne : n + j ≠ C.output) :
    ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
      (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
      (gateAt C r).op = GateOp.or := by
  have hA := hL.1
  obtain ⟨r, hjr, hr, hmr⟩ := least_read n C hL hout j (by omega)
  have huniq : ∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r := by
    intro k hk hmk
    by_contra hkr
    rcases Nat.lt_or_gt_of_ne hkr with h | h
    · exact two_readers n C hL hout j hB k r h hr hmk hmr
    · exact two_readers n C hL hout j hB r k h hk hmr hmk
  refine ⟨r, hr, hmr, huniq, ?_⟩
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hA r hr
  rcases hop with hop | hop
  swap
  · exact hop
  exfalso
  have hle : ∀ x : Fin n → Bool, W n C x (n + r) = true → W n C x (n + j) = true := by
    intro x hx
    rw [W_and n C x r hr hop a b hin ha hb] at hx
    have hmr' := hmr
    rw [hin] at hmr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmr'
    rcases hmr' with h | h
    · rw [h]; simp_all
    · rw [h]; simp_all
  by_cases hro : n + r = C.output
  · obtain ⟨x, hx⟩ := least_nodup n C hL (n + j) r (by omega) hr
    apply hx
    cases h1 : W n C x (n + r)
    · cases h2 : W n C x (n + j)
      · rfl
      · have h3 : W n C x C.output = true := hB x h2
        rw [← hro, h1] at h3
        exact absurd h3 (by simp)
    · exact hle x h1
  · obtain ⟨s, hrs, hs, hms⟩ := least_read n C hL hout r (by omega)
    have hv : ∀ x : Fin n → Bool, W n C x (n + j) = false →
        W n C x (n + j) = W n C x (n + r) := by
      intro x hx
      cases h1 : W n C x (n + r)
      · exact hx
      · rw [hle x h1] at hx; exact absurd hx (by simp)
    have hA1 := erase_AO n C r (n + j) hA hr (by omega)
    have hl1 := erase_length n C r (n + j) hr
    have ho1 : (eraseC n C r (n + j)).output < n + (eraseC n C r (n + j)).gates.length :=
      alias_lt (n + r) (n + j) C.output _ (by omega) (by omega) (by omega)
    have hWj : ∀ x : Fin n → Bool, W n (eraseC n C r (n + j)) x (n + j) = W n C x (n + j) :=
      fun x => erase_W_lt n C r (n + j) hr x (n + j) (by omega)
    have hfun : ∀ x : Fin n → Bool,
        (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)).eval (List.ofFn x) =
          C.eval (List.ofFn x) := by
      intro x
      rw [appOr_eval n _ _ (n + j) x ho1 (by omega), hWj x]
      cases hx : W n C x (n + j)
      · rw [Bool.or_false]
        exact erase_wires n C r (n + j) hr (by omega) x (Or.inl (hv x hx)) C.output
          (fun _ => hv x hx)
      · rw [Bool.or_true]; exact (hB x hx).symm
    have hA3 := appOr_AO n _ _ (n + j) hA1 ho1 (by omega)
    have hl3 : (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)).gates.length =
        C.gates.length := by simp [appOr]; omega
    have hL3 : Least n (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)) :=
      ⟨hA3, fun D hD hDf => by
        rw [hl3]; exact hL.2 D hD (fun x => (hDf x).trans (hfun x))⟩
    have hB3 : Bel n (appOr n (eraseC n C r (n + j)) (eraseC n C r (n + j)).output (n + j)) j := by
      intro x hx
      rw [hfun x]
      apply hB x
      rw [appOr_W_lt n _ _ _ x (n + j) (by omega), hWj x] at hx
      exact hx
    refine two_readers n _ hL3 (by simp [appOr]; omega) j hB3 (s - 1) (C.gates.length - 1)
      (by omega) (by rw [hl3]; omega) ?_ ?_
    · rw [appOr_gateAt_lt n _ _ _ (s - 1) (by omega),
        erase_gateAt_ge n C r (n + j) (s - 1) hr (by omega) (by omega)]
      have hs1 : s - 1 + 1 = s := by omega
      rw [hs1]
      simp only [aliasGate, List.mem_map]
      exact ⟨n + r, hms, by simp [aliasWire]⟩
    · have hs2 : C.gates.length - 1 = (eraseC n C r (n + j)).gates.length := by omega
      rw [hs2, appOr_gateAt_last]
      simp

lemma or_children (n : ℕ) (C : Circuit) (hL : Least n C)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (r : ℕ) (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) (hB : Bel n C r) :
    ∃ a b, (gateAt C r).inputs = [n + a, n + b] ∧ a < r ∧ b < r ∧ a ≠ b ∧
      Bel n C a ∧ Bel n C b := by
  obtain ⟨_, a, b, hin, ha, hb⟩ := hL.1 r hr
  have hWr := fun x => W_or n C x r hr hop a b hin ha hb
  have hvar : ∀ c, c < n → (∀ x : Fin n → Bool, W n C x c = true → W n C x (n + r) = true) →
      False := by
    intro c hc hcr
    obtain ⟨x, hx, hf⟩ := hV ⟨c, hc⟩
    have h1 : W n C x c = true := (W_input n C x c hc).trans hx
    have h2 := hB x (hcr x h1)
    rw [hf] at h2
    exact absurd h2 (by simp)
  have hna : n ≤ a := by
    by_contra h
    push Not at h
    exact hvar a h (fun x hx => by rw [hWr x, hx]; rfl)
  have hnb : n ≤ b := by
    by_contra h
    push Not at h
    exact hvar b h (fun x hx => by rw [hWr x, hx]; simp)
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le hna
  obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hnb
  refine ⟨a', b', hin, by omega, by omega, ?_, ?_, ?_⟩
  · intro hab
    subst hab
    obtain ⟨x, hx⟩ := least_nodup n C hL (n + a') r ha hr
    exact hx (by rw [hWr x]; simp)
  · intro x hx; exact hB x (by rw [hWr x, hx]; rfl)
  · intro x hx; exact hB x (by rw [hWr x, hx]; simp)

lemma has_top (n : ℕ) (C : Circuit) (hL : Least n C)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (Cone : ℕ → ℕ → Prop)
    (c1 : ∀ i k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → Cone i k)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k) :
    ∀ j, j < C.gates.length → Bel n C j →
      ∃ t, t < C.gates.length ∧ (gateAt C t).op = GateOp.and ∧ Bel n C t ∧ (t = j ∨ Cone t j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hB
    rcases (hL.1 j hj).1 with hop | hop
    · exact ⟨j, hj, hop, hB, Or.inl rfl⟩
    · obtain ⟨a, b, hin, ha, hb, hab, hBa, hBb⟩ := or_children n C hL hV j hj hop hB
      obtain ⟨t, ht, hopt, hBt, htj⟩ := ih a ha (by omega) hBa
      refine ⟨t, ht, hopt, hBt, Or.inr ?_⟩
      have hmem : n + a ∈ (gateAt C j).inputs := by rw [hin]; simp
      rcases htj with rfl | h
      · exact c1 _ j hj hmem
      · exact c2 t a j hj h hmem

lemma up (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output + 1 = n + C.gates.length)
    (Cone : ℕ → ℕ → Prop)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k)
    (t : ℕ) (hTop : ∀ s, s < C.gates.length → (gateAt C s).op = GateOp.and → ¬ Cone t s) :
    ∀ d s, s < C.gates.length → C.gates.length - s = d → Cone t s → Bel n C s := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro s hs hd hc
    by_cases hso : n + s = C.output
    · intro x hx
      have h1 : W n C x C.output = true := by rw [← hso]; exact hx
      exact h1
    · obtain ⟨k, hsk, hk, hmk⟩ := least_read n C hL hout s (by omega)
      have hck := c2 t s k hk hc hmk
      have hBk := ih (C.gates.length - k) (by omega) k hk rfl hck
      obtain ⟨hop, a, b, hin, ha, hb⟩ := hL.1 k hk
      have hopk : (gateAt C k).op = GateOp.or := by
        rcases hop with h | h
        · exact absurd hck (hTop k hk h)
        · exact h
      intro x hx
      apply hBk x
      rw [W_or n C x k hk hopk a b hin ha hb]
      rw [hin] at hmk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmk
      rcases hmk with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp

lemma main_abs (n : ℕ) (C : Circuit) (hL : Least n C)
    (hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false)
    (Cone : ℕ → ℕ → Prop)
    (c1 : ∀ i k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → Cone i k)
    (c2 : ∀ t i k, k < C.gates.length → Cone t i → n + i ∈ (gateAt C k).inputs → Cone t k)
    (hTop : ∀ t s, t < C.gates.length → s < C.gates.length → (gateAt C t).op = GateOp.and →
      Bel n C t → (gateAt C s).op = GateOp.and → ¬ Cone t s) :
    (∀ j, j < C.gates.length → Bel n C j → n + j ≠ C.output →
      ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
        (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
        (gateAt C r).op = GateOp.or ∧ Bel n C r) ∧
    (n ≤ C.output ∧ C.output + 1 = n + C.gates.length) ∧
    (∀ O A : Finset ℕ,
      (∀ k, k ∈ O ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ Bel n C k) →
      (∀ k, k ∈ A ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ Bel n C k) →
      O.card + 1 = A.card) := by
  have hout := least_out n C hL hT hV
  have part1 : ∀ j, j < C.gates.length → Bel n C j → n + j ≠ C.output →
      ∃ r, r < C.gates.length ∧ n + j ∈ (gateAt C r).inputs ∧
        (∀ k, k < C.gates.length → n + j ∈ (gateAt C k).inputs → k = r) ∧
        (gateAt C r).op = GateOp.or ∧ Bel n C r := by
    intro j hj hB hne
    obtain ⟨r, hr, hmr, huniq, hopr⟩ := one_reader n C hL hout.2 j hj hB hne
    refine ⟨r, hr, hmr, huniq, hopr, ?_⟩
    obtain ⟨t, ht, hopt, hBt, htj⟩ := has_top n C hL hV Cone c1 c2 j hj hB
    have hc : Cone t r := by
      rcases htj with rfl | h
      · exact c1 _ r hr hmr
      · exact c2 t j r hr h hmr
    exact up n C hL hout.2 Cone c2 t (fun s hs hops => hTop t s ht hs hopt hBt hops) _ r hr rfl hc
  refine ⟨part1, hout, ?_⟩
  intro O A hO hA
  classical
  have hBo : Bel n C (C.gates.length - 1) := by
    intro x hx
    have h1 : n + (C.gates.length - 1) = C.output := by omega
    rw [h1] at hx
    exact hx
  have hoB : C.gates.length - 1 ∈ O ∪ A := by
    rcases (hL.1 (C.gates.length - 1) (by omega)).1 with h | h
    · exact Finset.mem_union_right _ ((hA _).2 ⟨by omega, h, hBo⟩)
    · exact Finset.mem_union_left _ ((hO _).2 ⟨by omega, h, hBo⟩)
  have hdisj : Disjoint O A := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    have e1 := ((hO k).1 h1).2.1
    have e2 := ((hA k).1 h2).2.1
    rw [e1] at e2
    cases e2
  obtain ⟨B, hBdef⟩ : ∃ B, B = (O ∪ A).erase (C.gates.length - 1) := ⟨_, rfl⟩
  have hBmem : ∀ j, j ∈ B ↔ j < C.gates.length ∧ Bel n C j ∧ n + j ≠ C.output := by
    intro j
    rw [hBdef, Finset.mem_erase, Finset.mem_union, hO, hA]
    constructor
    · rintro ⟨h1, h2 | h2⟩
      · exact ⟨h2.1, h2.2.2, by omega⟩
      · exact ⟨h2.1, h2.2.2, by omega⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨by omega, ?_⟩
      rcases (hL.1 j h1).1 with h | h
      · exact Or.inr ⟨h1, h, h2⟩
      · exact Or.inl ⟨h1, h, h2⟩
  have hcount := SafeLower.double_count B O
    (fun j k => n + j ∈ (gateAt C k).inputs)
  have hleft : ∀ j ∈ B,
      (SafeLower.bipartiteAbove (fun j k => n + j ∈ (gateAt C k).inputs) O j).card = 1 := by
    intro j hj
    obtain ⟨hj1, hj2, hj3⟩ := (hBmem j).1 hj
    obtain ⟨r, hr, hmr, huniq, hopr, hBr⟩ := part1 j hj1 hj2 hj3
    rw [Finset.card_eq_one]
    refine ⟨r, ?_⟩
    ext k
    simp only [SafeLower.bipartiteAbove, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, hmk⟩
      exact huniq k ((hO k).1 hk).1 hmk
    · rintro rfl
      exact ⟨(hO _).2 ⟨hr, hopr, hBr⟩, hmr⟩
  have hright : ∀ k ∈ O,
      (SafeLower.bipartiteBelow (fun j k => n + j ∈ (gateAt C k).inputs) B k).card = 2 := by
    intro k hk
    obtain ⟨hk1, hk2, hk3⟩ := (hO k).1 hk
    obtain ⟨a, b, hin, ha, hb, hab, hBa, hBb⟩ := or_children n C hL hV k hk1 hk2 hk3
    rw [Finset.card_eq_two]
    refine ⟨a, b, hab, ?_⟩
    ext j
    simp only [SafeLower.bipartiteBelow, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      hin, List.mem_cons, List.not_mem_nil, or_false, hBmem]
    constructor
    · rintro ⟨_, h | h⟩
      · left; omega
      · right; omega
    · rintro (rfl | rfl)
      · exact ⟨⟨by omega, hBa, by omega⟩, Or.inl rfl⟩
      · exact ⟨⟨by omega, hBb, by omega⟩, Or.inr rfl⟩
  rw [Finset.sum_congr rfl hleft, Finset.sum_congr rfl hright] at hcount
  simp only [Finset.sum_const, smul_eq_mul] at hcount
  have hBc : B.card = (O ∪ A).card - 1 := by rw [hBdef]; exact Finset.card_erase_of_mem hoB
  have hU : (O ∪ A).card = O.card + A.card := Finset.card_union_of_disjoint hdisj
  have hpos : 0 < (O ∪ A).card := Finset.card_pos.mpr ⟨_, hoB⟩
  omega

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h

lemma inCone_c1 (n : ℕ) (C : Circuit) (hA : AO n C) (i k : ℕ) (hk : k < C.gates.length)
    (hm : n + i ∈ (gateAt C k).inputs) : InCone n C i k := by
  rw [inCone_iff n C i k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  exact ⟨n + i, hm, by omega, hlt, Or.inl (by omega)⟩

lemma inCone_c2 (n : ℕ) (C : Circuit) (hA : AO n C) (t i k : ℕ) (hk : k < C.gates.length)
    (hc : InCone n C t i) (hm : n + i ∈ (gateAt C k).inputs) : InCone n C t k := by
  rw [inCone_iff n C t k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  have he : n + i - n = i := by omega
  exact ⟨n + i, hm, by omega, hlt, Or.inr (by rw [he]; exact hc)⟩

lemma edge_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) :
    ∃ x : Fin n → Bool, ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  obtain ⟨e, he⟩ := h
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨fun _ => true, u, v, he, rfl, rfl⟩

lemma edge_var (n : ℕ) (G : SimpleGraph (Fin n)) (u : Fin n) :
    ∃ x : Fin n → Bool, x u = true ∧ ¬ ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by
  refine ⟨fun w => decide (w = u), by simp, ?_⟩
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha
  subst hb
  exact G.loopless.irrefl _ hab

lemma gf_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : G.edgeFinset.Nonempty) : ∃ x : Fin n → Bool, graphFun G ∅ x = true := by
  obtain ⟨x, hx⟩ := edge_true n G h
  exact ⟨x, by simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]; exact Or.inr hx⟩

lemma gf_var (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    ∃ x : Fin n → Bool, x u = true ∧ graphFun G ∅ x = false := by
  obtain ⟨x, hx, hno⟩ := edge_var n G u
  refine ⟨x, hx, ?_⟩
  simp only [graphFun, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  exact ⟨by simp, hno⟩

lemma AO_of_IsAO2 (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO n C := by
  obtain ⟨hao, hrb, hlen⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]; exact List.getElem_mem hk
  have hl := hlen _ hmem
  refine ⟨hao _ hmem, ?_⟩
  match hin : (gateAt C k).inputs, hl with
  | [a, b], _ =>
    exact ⟨a, b, rfl, hrb k hk a (by rw [hin]; simp), hrb k hk b (by rw [hin]; simp)⟩

lemma IsAO2_of_AO (n : ℕ) (C : Circuit) (h : AO n C) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq C k hk]
    exact (h k hk).1
  · intro k hk i hi
    obtain ⟨_, a, b, hin, ha, hb⟩ := h k hk
    rw [hin] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq C k hk]
    obtain ⟨_, a, b, hin, _, _⟩ := h k hk
    rw [hin]; rfl

lemma main_real (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hne : G.edgeFinset.Nonempty) (hL : PEqualNP.TopForm.IsLeastAO G C)
    (hTF : PEqualNP.TopForm.TopForm G C) :
    (∀ j < C.gates.length, PEqualNP.TopForm.BelowF G C j → n + j ≠ C.output →
      ∃ r, PEqualNP.TopForm.readers n C j = {r} ∧ (gateAt C r).op = GateOp.or ∧
        PEqualNP.TopForm.BelowF G C r) ∧
    PEqualNP.TopForm.readers n C (C.output - n) = ∅ ∧
    (PEqualNP.TopForm.orT G C).card + 1 = (PEqualNP.TopForm.tops G C).card := by
  have hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x := fun x =>
    congrFun hL.2.1 x
  have hAO : AO n C := AO_of_IsAO2 n C hL.1
  have hLeast : Least n C := ⟨hAO, fun D hD hDf =>
    hL.2.2 D (IsAO2_of_AO n D hD) (funext fun x => (hDf x).trans (hfun x))⟩
  have hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true := by
    obtain ⟨x, hx⟩ := gf_true n G hne
    exact ⟨x, (hfun x).trans hx⟩
  have hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false := by
    intro u
    obtain ⟨x, hx, hf⟩ := gf_var n G u
    exact ⟨x, hx, (hfun x).trans hf⟩
  have hBel : ∀ j, PEqualNP.TopForm.BelowF G C j ↔ Bel n C j := fun j =>
    ⟨fun h x hx => (hfun x).trans (h x hx), fun h x hx => (hfun x).symm.trans (h x hx)⟩
  obtain ⟨p1, p2, p3⟩ := main_abs n C hLeast hT hV (InCone n C) (inCone_c1 n C hAO)
    (inCone_c2 n C hAO)
    (fun t s ht hs hopt hBt hops => hTF t ht s hs hopt ((hBel t).2 hBt) hops)
  refine ⟨?_, ?_, ?_⟩
  · intro j hj hB hne'
    obtain ⟨r, hr, hmr, huniq, hopr, hBr⟩ := p1 j hj ((hBel j).1 hB) hne'
    refine ⟨r, ?_, hopr, (hBel r).2 hBr⟩
    ext k
    simp only [PEqualNP.TopForm.readers, Finset.mem_filter, Finset.mem_range,
      Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      exact huniq k h1 h2
    · rintro rfl
      exact ⟨hr, hmr⟩
  · rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    simp only [PEqualNP.TopForm.readers, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨_, a, b, hin, ha, hb⟩ := hAO k hk.1
    have h2 := hk.2
    rw [hin] at h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h2
    omega
  · refine p3 _ _ (fun k => ?_) (fun k => ?_)
    · simp only [PEqualNP.TopForm.orT, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
        Finset.mem_range, hBel]
    · simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
        Finset.mem_range, hBel]

end S98

lemma cover_g {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset α)
    (hf : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ) (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) :
    f (n + r) ⊆ stops.biUnion f ∧ ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
  have hdown : ∀ k, k ∈ R → f (n + k) ⊆ stops.biUnion f := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk u hu
      by_cases hs : k ∈ Z ∨ (g k).op ≠ GateOp.or
      · refine Finset.mem_biUnion.2 ⟨n + k, (hstops _).2 (Or.inr ⟨by omega, ?_, ?_⟩), hu⟩
        · rwa [Nat.add_sub_cancel_left]
        · rwa [Nat.add_sub_cancel_left]
      · have hkZ : k ∉ Z := fun h => hs (Or.inl h)
        have hor : (g k).op = GateOp.or := by
          by_contra h
          exact hs (Or.inr h)
        obtain ⟨w, hw, huw⟩ := (hf k hor u).1 hu
        by_cases hwn : w < n
        · exact Finset.mem_biUnion.2 ⟨w, (hstops _).2 (Or.inl ⟨hwn, k, hk, hkZ, hor, hw⟩), huw⟩
        · have hwk := hback k w hw
          have hweq : n + (w - n) = w := by omega
          have hwR : w - n ∈ R :=
            (hR _).2 (((hR k).1 hk).tail ⟨hkZ, hor, by rwa [hweq]⟩)
          exact ih (w - n) (by omega) hwR (by rwa [hweq])
  have hup : ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
    intro k hk
    have h := (hR k).1 hk
    clear hk
    induction h with
    | refl => exact Finset.Subset.refl _
    | tail _ hbc ih =>
      intro u hu
      exact ih ((hf _ hbc.2.1 u).2 ⟨_, hbc.2.2, hu⟩)
  exact ⟨hdown r ((hR r).2 Relation.ReflTransGen.refl), hup⟩

lemma cover_bound (n : ℕ) (H : SimpleGraph (Fin n)) (T : Finset ℕ) (c : ℕ → Fin n)
    (hcov : ∀ u v : Fin n, H.Adj u v → ∃ a, a ∈ T ∧ (c a = u ∨ c a = v))
    (K : Finset (Fin n)) (hK : IsMinCover H K) : K.card ≤ T.card := by
  classical
  refine (hK.2 (T.image c) ?_).trans Finset.card_image_le
  intro u v huv
  obtain ⟨a, ha, h | h⟩ := hcov u v huv
  · left
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha
  · right
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha

lemma four_split (N : ℕ) (isAnd isOr bel : ℕ → Prop)
    (hAO : ∀ k, k < N → (isAnd k ∧ ¬ isOr k) ∨ (isOr k ∧ ¬ isAnd k))
    (T J O Q : Finset ℕ)
    (hT : ∀ k, k ∈ T ↔ k < N ∧ isAnd k ∧ bel k)
    (hJ : ∀ k, k ∈ J ↔ k < N ∧ isAnd k ∧ ¬ bel k)
    (hO : ∀ k, k ∈ O ↔ k < N ∧ isOr k ∧ bel k)
    (hQ : ∀ k, k ∈ Q ↔ k < N ∧ isOr k ∧ ¬ bel k) :
    T.card + J.card + O.card + Q.card = N := by
  classical
  have h1 : Disjoint T J := by
    rw [Finset.disjoint_left]
    intro k h h'
    exact ((hJ k).1 h').2.2 ((hT k).1 h).2.2
  have h2 : Disjoint (T ∪ J) O := by
    rw [Finset.disjoint_left]
    intro k h h'
    have ho := (hO k).1 h'
    rcases hAO k ho.1 with ha | ha
    · exact ha.2 ho.2.1
    · rcases Finset.mem_union.1 h with h | h
      · exact ha.2 ((hT k).1 h).2.1
      · exact ha.2 ((hJ k).1 h).2.1
  have h3 : Disjoint (T ∪ J ∪ O) Q := by
    rw [Finset.disjoint_left]
    intro k h h'
    have hq := (hQ k).1 h'
    rcases Finset.mem_union.1 h with h | h
    · rcases hAO k hq.1 with ha | ha
      · exact ha.2 hq.2.1
      · rcases Finset.mem_union.1 h with h | h
        · exact ha.2 ((hT k).1 h).2.1
        · exact ha.2 ((hJ k).1 h).2.1
    · exact hq.2.2 ((hO k).1 h).2.2
  have h4 : T ∪ J ∪ O ∪ Q = Finset.range N := by
    ext k
    simp only [Finset.mem_union, Finset.mem_range, hT, hJ, hO, hQ]
    constructor
    · rintro (((h | h) | h) | h) <;> exact h.1
    · intro hk
      by_cases hb : bel k
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inl ⟨hk, ha.1, hb⟩))
        · exact Or.inl (Or.inr ⟨hk, ha.1, hb⟩)
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inr ⟨hk, ha.1, hb⟩))
        · exact Or.inr ⟨hk, ha.1, hb⟩
  have h5 := congrArg Finset.card h4
  rw [Finset.card_union_of_disjoint h3, Finset.card_union_of_disjoint h2,
    Finset.card_union_of_disjoint h1, Finset.card_range] at h5
  exact h5

def TwoNe {α : Type} (g : ℕ → Gate) (f : ℕ → Finset α) (k : ℕ) : Prop :=
  ∃ w1 ∈ (g k).inputs, ∃ w2 ∈ (g k).inputs, w1 ≠ w2 ∧ (f w1).Nonempty ∧ (f w2).Nonempty

lemma cone_count2 {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate) (f : ℕ → Finset α)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ)
    (hlen : ∀ k, k ∉ Z → (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)))
    (I : Finset ℕ)
    (hI : ∀ k, k ∈ R → k ∉ Z → (g k).op = GateOp.or → TwoNe g f k → k ∈ I) :
    (stops.filter (fun w => (f w).Nonempty)).card ≤ I.card + 1 := by
  classical
  set E : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or) with hE
  set N : ℕ → Finset ℕ := fun k => (g k).inputs.toFinset.filter (fun w => (f w).Nonempty)
    with hN
  set U : Finset ℕ := insert (n + r) (E.biUnion N) with hU
  set E2 := E.filter (fun k => 2 ≤ (N k).card) with hE2
  set Ene := E.filter (fun k => (f (n + k)).Nonempty) with hEne
  have hE2I : E2 ⊆ I := by
    intro k hk
    simp only [hE2, hE, Finset.mem_filter] at hk
    obtain ⟨⟨hkR, hkZ, hor⟩, h2⟩ := hk
    apply hI k hkR hkZ hor
    obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < (N k).card)
    simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw1 hw2
    exact ⟨w1, hw1.1, w2, hw2.1, hne, hw1.2, hw2.2⟩
  have hNk : ∀ k ∈ E, (N k).card ≤ (if 2 ≤ (N k).card then 1 else 0) +
      (if (f (n + k)).Nonempty then 1 else 0) := by
    intro k hk
    simp only [hE, Finset.mem_filter] at hk
    have hc : (N k).card ≤ 2 := (Finset.card_filter_le _ _).trans
      ((List.toFinset_card_le _).trans (hlen k hk.2.1 hk.2.2))
    have hne : 1 ≤ (N k).card → (f (n + k)).Nonempty := by
      intro h1
      obtain ⟨w, hw⟩ := Finset.card_pos.1 (by omega : 0 < (N k).card)
      simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw
      obtain ⟨u, hu⟩ := hw.2
      exact ⟨u, (hf2 k hk.2.2 u).2 ⟨w, hw.1, hu⟩⟩
    rcases Nat.lt_or_ge (N k).card 1 with h0 | h0
    · omega
    · rw [if_pos (hne h0)]
      split_ifs <;> omega
  have hsum : (E.biUnion N).card ≤ E2.card + Ene.card := by
    calc (E.biUnion N).card ≤ ∑ k ∈ E, (N k).card := Finset.card_biUnion_le
      _ ≤ ∑ k ∈ E, ((if 2 ≤ (N k).card then 1 else 0) +
          (if (f (n + k)).Nonempty then 1 else 0)) := Finset.sum_le_sum hNk
      _ = E2.card + Ene.card := by
        rw [Finset.sum_add_distrib, hE2, hEne, Finset.card_filter, Finset.card_filter]
  have hUcard : U.card ≤ E2.card + Ene.card + 1 := by
    have hins : U.card ≤ (E.biUnion N).card + 1 := Finset.card_insert_le (n + r) (E.biUnion N)
    omega
  have hmem : ∀ w, (f w).Nonempty → (w = n + r ∨ ∃ k' ∈ E, w ∈ (g k').inputs) → w ∈ U := by
    rintro w hw (h | ⟨k', hk', hin⟩)
    · rw [h]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨k', hk', ?_⟩)
      simp only [hN, Finset.mem_filter, List.mem_toFinset]
      exact ⟨hin, hw⟩
  have hRU : ∀ k, k ∈ R → n + k = n + r ∨ ∃ k' ∈ E, n + k ∈ (g k').inputs := by
    intro k hk
    rcases Relation.ReflTransGen.cases_tail ((hR k).1 hk) with h | ⟨b, hb, hb1, hb2, hb3⟩
    · left
      rw [h]
    · right
      refine ⟨b, ?_, hb3⟩
      rw [hE, Finset.mem_filter]
      exact ⟨(hR b).2 hb, hb1, hb2⟩
  set S2 : Finset ℕ := Ene.image (fun k => n + k) with hS2
  have hS2card : S2.card = Ene.card :=
    Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)
  have hdisj : Disjoint (stops.filter (fun w => (f w).Nonempty)) S2 := by
    rw [Finset.disjoint_left]
    intro w hw hw2
    rw [Finset.mem_filter] at hw
    rw [hS2, Finset.mem_image] at hw2
    obtain ⟨k, hk, rfl⟩ := hw2
    rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
    rcases (hstops _).1 hw.1 with ⟨h1, _⟩ | ⟨_, _, h3⟩
    · omega
    · rw [Nat.add_sub_cancel_left] at h3
      rcases h3 with h3 | h3
      · exact hk.1.2.1 h3
      · exact h3 hk.1.2.2
  have hsub : (stops.filter (fun w => (f w).Nonempty)) ∪ S2 ⊆ U := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · rw [Finset.mem_filter] at hw
      rcases (hstops _).1 hw.1 with ⟨_, k, hk, hk1, hk2, hk3⟩ | ⟨h1, h2, _⟩
      · refine hmem w hw.2 (Or.inr ⟨k, ?_, hk3⟩)
        rw [hE, Finset.mem_filter]
        exact ⟨hk, hk1, hk2⟩
      · have := hRU _ h2
        rw [Nat.add_sub_cancel' h1] at this
        exact hmem w hw.2 this
    · rw [hS2, Finset.mem_image] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
      exact hmem _ hk.2 (hRU k hk.1.1)
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hS2card] at h3
  have h4 := Finset.card_le_card hE2I
  omega

lemma top_step2 (n : ℕ) (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (Z : Finset ℕ) (ρ : ℕ) (c : Fin n) (E0 : Finset (Sym2 (Fin n)))
    (hZ : ∀ k, k ∈ Z → f (n + k) ⊆ f ρ →
      (∀ v, v ∈ f (n + k) → s(c, v) ∈ E0) ∨ (f (n + k)).card ≤ 1) :
    ∃ Znew : Finset ℕ, Disjoint Z Znew ∧
      (∀ k, k ∈ Znew → (g k).op = GateOp.or ∧ TwoNe g f k ∧ n ≤ ρ ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (ρ - n) k ∧ f (n + k) ⊆ f ρ) ∧
      (((f ρ).image (fun v => s(c, v))) \ E0).card ≤ Znew.card + 1 := by
  classical
  by_cases hρ : ρ < n
  · refine ⟨∅, Finset.disjoint_empty_right _, by simp, ?_⟩
    calc (((f ρ).image (fun v => s(c, v))) \ E0).card
        ≤ ((f ρ).image (fun v => s(c, v))).card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ (f ρ).card := Finset.card_image_le
      _ ≤ 1 := hf1 ρ hρ
      _ ≤ (∅ : Finset ℕ).card + 1 := by simp
  · have hρn : n ≤ ρ := Nat.le_of_not_lt hρ
    obtain ⟨r, rfl⟩ : ∃ r, ρ = n + r := ⟨ρ - n, by omega⟩
    have hle : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k → k ≤ r := by
      intro k h
      induction h with
      | refl => exact le_refl _
      | tail _ hbc ih =>
        have := hback _ _ hbc.2.2
        omega
    set R : Finset ℕ := (Finset.range (r + 1)).filter (fun k =>
      Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k) with hRdef
    have hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
      intro k
      rw [hRdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨Nat.lt_succ_of_le (hle k h), h⟩
    set stops : Finset ℕ := (Finset.range (n + r + 1)).filter (fun w =>
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) with hsdef
    have hstops : ∀ w, w ∈ stops ↔
        (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
        (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)) := by
      intro w
      rw [hsdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rcases h with ⟨h1, _⟩ | ⟨h1, h2, _⟩
        · omega
        · have := hle _ ((hR _).1 h2)
          omega
    set Znew : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or ∧ TwoNe g f k)
      with hZn
    obtain ⟨hcov, hup⟩ := cover_g n g hback f hf2 Z r R hR stops hstops
    have hcnt : (stops.filter (fun w => (f w).Nonempty)).card ≤ Znew.card + 1 :=
      cone_count2 n g f hf2 Z (fun k _ h => hlen k h) r R hR stops hstops Znew (by
        intro k hk hkZ hor htwo
        rw [hZn, Finset.mem_filter]
        exact ⟨hk, hkZ, hor, htwo⟩)
    refine ⟨Znew, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro k hk hk2
      rw [hZn, Finset.mem_filter] at hk2
      exact hk2.2.1 hk
    · intro k hk
      rw [hZn, Finset.mem_filter] at hk
      refine ⟨hk.2.2.1, hk.2.2.2, hρn, ?_, hup k hk.1⟩
      rw [Nat.add_sub_cancel_left]
      have hreach : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k →
          Relation.ReflTransGen (fun k k' : ℕ =>
            (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
        intro k h
        induction h with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hbc ih => exact ih.tail hbc.2
      exact hreach k ((hR k).1 hk.1)
    · have hsub : ((f (n + r)).image (fun v => s(c, v))) \ E0 ⊆
          (stops.filter (fun w => (f w).Nonempty)).biUnion
            (fun w => ((f w).image (fun v => s(c, v))) \ E0) := by
        intro e he
        rw [Finset.mem_sdiff, Finset.mem_image] at he
        obtain ⟨⟨v, hv, rfl⟩, he0⟩ := he
        obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.1 (hcov hv)
        refine Finset.mem_biUnion.2 ⟨w, Finset.mem_filter.2 ⟨hw, ⟨v, hvw⟩⟩, ?_⟩
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_image_of_mem _ hvw, he0⟩
      have hone : ∀ w, w ∈ stops.filter (fun w => (f w).Nonempty) →
          (((f w).image (fun v => s(c, v))) \ E0).card ≤ 1 := by
        intro w hw'
        have hw := (Finset.mem_filter.1 hw').1
        have himg : ∀ t : Finset (Fin n), t.card ≤ 1 →
            ((t.image (fun v => s(c, v))) \ E0).card ≤ 1 := fun t ht =>
          (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_image_le.trans ht)
        rcases (hstops w).1 hw with ⟨hwn, _⟩ | ⟨hwn, hwR, hw2⟩
        · exact himg _ (hf1 w hwn)
        · have hweq : n + (w - n) = w := by omega
          rcases hw2 with hz | hnor
          · have hsubw : f (n + (w - n)) ⊆ f (n + r) := hup _ hwR
            rcases hZ _ hz hsubw with hall | hc1
            · rw [hweq] at hall
              have hempty : ((f w).image (fun v => s(c, v))) \ E0 = ∅ := by
                rw [Finset.sdiff_eq_empty_iff_subset]
                intro e he
                obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
                exact hall v hv
              rw [hempty]
              simp
            · rw [hweq] at hc1
              exact himg _ hc1
          · have := hf3 _ hnor
            rw [hweq] at this
            exact himg _ this
      calc (((f (n + r)).image (fun v => s(c, v))) \ E0).card
          ≤ ((stops.filter (fun w => (f w).Nonempty)).biUnion
              (fun w => ((f w).image (fun v => s(c, v))) \ E0)).card :=
            Finset.card_le_card hsub
        _ ≤ (stops.filter (fun w => (f w).Nonempty)).card * 1 :=
            Finset.card_biUnion_le_card_mul _ _ _ hone
        _ ≤ Znew.card + 1 := by omega

lemma star_count2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (l : List (Fin n × ℕ))
    (hadj : ∀ p, p ∈ l → ∀ v, v ∈ f p.2 → G.Adj p.1 v) :
    ∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ p, p ∈ l ∧ n ≤ p.2 ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (p.2 - n) k ∧ f (n + k) ⊆ f p.2) ∧
      (l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v)))).card
        ≤ l.length + Z.card := by
  classical
  induction l with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨Z, hZ1, hZ2⟩ := ih (fun q hq => hadj q (List.mem_cons_of_mem _ hq))
    set E0 := l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v))) with hE0
    obtain ⟨Znew, hd, hn1, hn2⟩ := top_step2 n g hlen hback f hf1 hf2 hf3 (Z ∪ B) p.2 p.1 E0 (by
      intro k hk hsub
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨_, _, _, q, hq, _, _, hfq⟩ := hZ1 k hk
        by_cases hc : q.1 = p.1
        · left
          intro v hv
          rw [hE0]
          refine Finset.mem_biUnion.2 ⟨q, List.mem_toFinset.2 hq, ?_⟩
          rw [← hc]
          exact Finset.mem_image_of_mem _ (hfq hv)
        · right
          by_contra hcard
          have h2 : 1 < (f (n + k)).card := by omega
          obtain ⟨v, hv, v', hv', hne⟩ := Finset.one_lt_card.1 h2
          have a1 : G.Adj p.1 v := hadj p List.mem_cons_self v (hsub hv)
          have a2 : G.Adj p.1 v' := hadj p List.mem_cons_self v' (hsub hv')
          have b1 : G.Adj q.1 v := hadj q (List.mem_cons_of_mem _ hq) v (hfq hv)
          have b2 : G.Adj q.1 v' := hadj q (List.mem_cons_of_mem _ hq) v' (hfq hv')
          exact h4 p.1 v q.1 v' (fun h => hc h.symm) hne ⟨a1, b1.symm, b2, a2.symm⟩
      · exact Or.inr (hB k hk))
    have hd1 : Disjoint Z Znew := Finset.disjoint_of_subset_left Finset.subset_union_left hd
    refine ⟨Z ∪ Znew, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨h0, h1, ht, q, hq, h2⟩ := hZ1 k hk
        exact ⟨h0, h1, ht, q, List.mem_cons_of_mem _ hq, h2⟩
      · obtain ⟨h1, ht, h2, h3, h5⟩ := hn1 k hk
        refine ⟨?_, h1, ht, p, List.mem_cons_self, h2, h3, h5⟩
        intro hkB
        exact (Finset.disjoint_left.1 hd (Finset.mem_union_right _ hkB)) hk
    · rw [List.toFinset_cons, Finset.biUnion_insert, Finset.card_union_of_disjoint hd1,
        List.length_cons, ← hE0]
      have hsplit : (f p.2).image (fun v => s(p.1, v)) ∪ E0 =
          (((f p.2).image (fun v => s(p.1, v))) \ E0) ∪ E0 := by
        rw [Finset.sdiff_union_self_eq_union]
      have hle := Finset.card_union_le (((f p.2).image (fun v => s(p.1, v))) \ E0) E0
      rw [← hsplit] at hle
      omega

lemma assemble2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (T : Finset ℕ) (o : ℕ → Fin 2 → ℕ)
    (hstar : ∀ a, a ∈ T → (∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) → G.Adj u v) ∧
      ((f (o a 0)).card ≤ 1 ∨ (f (o a 1)).card ≤ 1))
    (Es : Finset (Sym2 (Fin n)))
    (hEs : ∀ e, e ∈ Es → ∃ a, a ∈ T ∧ ∃ u, u ∈ f (o a 0) ∧ ∃ v, v ∈ f (o a 1) ∧ e = s(u, v)) :
    (∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ a, a ∈ T ∧ ∃ b : Fin 2,
        n ≤ o a b ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (o a b - n) k ∧
        f (n + k) ⊆ f (o a b) ∧ (f (o a (1 - b))).card = 1) ∧
      Es.card ≤ T.card + Z.card) ∧
    ∀ (H : SimpleGraph (Fin n)) (K : Finset (Fin n)),
      (∀ u v : Fin n, H.Adj u v → s(u, v) ∈ Es) → IsMinCover H K → K.card ≤ T.card := by
  classical
  by_cases hEe : Es = ∅
  · subst hEe
    refine ⟨⟨∅, by simp, by simp⟩, ?_⟩
    intro H K hH hK
    have h0 := hK.2 ∅ (by
      intro u v huv
      exact absurd (hH u v huv) (Finset.notMem_empty _))
    simp only [Finset.card_empty] at h0
    omega
  · obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.2 hEe
    obtain ⟨_, _, v0, _, _⟩ := hEs e0 he0
    set c : ℕ → Fin n := fun a =>
      if (f (o a 0)).card ≤ 1 then (if h : (f (o a 0)).Nonempty then h.choose else v0)
      else (if h : (f (o a 1)).Nonempty then h.choose else v0) with hc
    set ρ : ℕ → ℕ := fun a => if (f (o a 0)).card ≤ 1 then o a 1 else o a 0 with hρ
    have hkey : ∀ a, a ∈ T → ∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) →
        (c a = u ∧ v ∈ f (ρ a)) ∨ (c a = v ∧ u ∈ f (ρ a)) := by
      intro a ha u hu v hv
      by_cases h0 : (f (o a 0)).card ≤ 1
      · left
        have hne : (f (o a 0)).Nonempty := ⟨u, hu⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h0 _ hne.choose_spec _ hu
        · simp only [hρ, h0, ↓reduceIte]
          exact hv
      · right
        have h1 : (f (o a 1)).card ≤ 1 := by
          rcases (hstar a ha).2 with h | h
          · exact absurd h h0
          · exact h
        have hne : (f (o a 1)).Nonempty := ⟨v, hv⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h1 _ hne.choose_spec _ hv
        · simp only [hρ, h0, ↓reduceIte]
          exact hu
    set T' : Finset ℕ := T.filter (fun a => (f (o a 0)).Nonempty ∧ (f (o a 1)).Nonempty)
      with hT'
    have hT'T : ∀ a, a ∈ T' → a ∈ T := fun a ha => (Finset.mem_filter.1 ha).1
    have hT'card : T'.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hadjc : ∀ a, a ∈ T' → ∀ v, v ∈ f (ρ a) → G.Adj (c a) v := by
      intro a ha' v hv
      have ha := hT'T a ha'
      have hnn := (Finset.mem_filter.1 ha').2
      by_cases h0 : (f (o a 0)).card ≤ 1
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.1
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact (hstar a ha).1 _ hne.choose_spec v hv
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.2
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact ((hstar a ha).1 v hv _ hne.choose_spec).symm
    have hEs' : ∀ e, e ∈ Es → ∃ a, a ∈ T' ∧ ∃ v, v ∈ f (ρ a) ∧ e = s(c a, v) := by
      intro e he
      obtain ⟨a, ha, u, hu, v, hv, rfl⟩ := hEs e he
      have ha' : a ∈ T' := Finset.mem_filter.2 ⟨ha, ⟨u, hu⟩, ⟨v, hv⟩⟩
      rcases hkey a ha u hu v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨a, ha', v, h2, by rw [h1]⟩
      · exact ⟨a, ha', u, h2, by rw [h1]; exact Sym2.eq_swap⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨Z, hZ1, hZ2⟩ := star_count2 n G h4 g hlen hback f hf1 hf2 hf3 B hB
        (T'.toList.map (fun a => (c a, ρ a))) (by
          intro p hp v hv
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
          exact hadjc a (Finset.mem_toList.1 ha) v hv)
      refine ⟨Z, ?_, ?_⟩
      · intro k hk
        obtain ⟨h1, h2, ht, p, hp, h3, h5, h6⟩ := hZ1 k hk
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
        have ha' := Finset.mem_toList.1 ha
        have hnn := (Finset.mem_filter.1 ha').2
        refine ⟨h1, h2, ht, a, hT'T a ha', ?_⟩
        by_cases h0 : (f (o a 0)).card ≤ 1
        · refine ⟨1, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 1 : Fin 2) = 0 := by decide
          rw [e]
          exact ⟨h3, h5, h6, le_antisymm h0 (Finset.card_pos.2 hnn.1)⟩
        · refine ⟨0, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 0 : Fin 2) = 1 := by decide
          rw [e]
          have h1' : (f (o a 1)).card ≤ 1 := by
            rcases (hstar a (hT'T a ha')).2 with h | h
            · exact absurd h h0
            · exact h
          exact ⟨h3, h5, h6, le_antisymm h1' (Finset.card_pos.2 hnn.2)⟩
      · have hsub : Es ⊆ (T'.toList.map (fun a => (c a, ρ a))).toFinset.biUnion
            (fun p => (f p.2).image (fun v => s(p.1, v))) := by
          intro e he
          obtain ⟨a, ha, v, hv, rfl⟩ := hEs' e he
          refine Finset.mem_biUnion.2 ⟨(c a, ρ a), ?_, Finset.mem_image_of_mem _ hv⟩
          exact List.mem_toFinset.2 (List.mem_map.2 ⟨a, Finset.mem_toList.2 ha, rfl⟩)
        have h1 := Finset.card_le_card hsub
        rw [List.length_map, Finset.length_toList] at hZ2
        omega
    · intro H K hH hK
      refine (cover_bound n H T' c ?_ K hK).trans hT'card
      intro u v huv
      obtain ⟨a, ha, w, hw, he⟩ := hEs' _ (hH u v huv)
      refine ⟨a, ha, ?_⟩
      have := Sym2.eq_iff.1 he
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1.symm
      · exact Or.inr h2.symm

lemma gateAt_ge {C : Circuit} {k : ℕ} (hk : C.gates.length ≤ k) :
    gateAt C k = ⟨GateOp.or, []⟩ := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk]

lemma orIn_iff_reach {n : ℕ} {C : Circuit} (p : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C p ↔ Relation.ReflTransGen (S90.OrStep n C) p u.val :=
  ⟨S90.mem_orIn_reach u, S90.reach_mem_orIn u⟩

lemma orIn_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [orIn_iff_reach] at ha hb
  have h1 : ∀ c : Fin n, Relation.ReflTransGen (S90.OrStep n C) w c.val → c.val = w := by
    intro c hc
    rcases Relation.ReflTransGen.cases_head hc with h | ⟨d, hd, _⟩
    · exact h.symm
    · obtain ⟨k, _, h3, _⟩ := hd
      omega
  exact Fin.ext ((h1 a ha).trans (h1 b hb).symm)

lemma orIn_gate {n : ℕ} (C : Circuit) (k : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔ k < C.gates.length ∧
      (gateAt C k).op = GateOp.or ∧ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧
        u ∈ PEqualNP.TopForm.orIn n C w := by
  rw [orIn_iff_reach]
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨d, hd, hr⟩
    · have := u.isLt
      omega
    · obtain ⟨k', hk', he, hop, hin, hlt⟩ := hd
      have hkk : k' = k := by omega
      subst hkk
      exact ⟨hk', hop, d, hin, hlt, (orIn_iff_reach d u).2 hr⟩
  · rintro ⟨hk, hop, w, hw, hlt, hu⟩
    exact Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hw, hlt⟩ ((orIn_iff_reach w u).1 hu)

lemma junk_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ PEqualNP.TopForm.BelowF G C k := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  simp only [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hc
    apply h3
    intro x hx
    by_contra hf
    exact hc ⟨x, hx, by simpa using hf⟩

lemma opnd_lt {n : ℕ} {C : Circuit} (h2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hRB : ReadsBack n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    PEqualNP.TopForm.opnd C a b < n + a := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (S90.gateAt_mem ha))
  have hp : p < n + a := hRB a ha p (by rw [hin]; simp)
  have hq : q < n + a := hRB a ha q (by rw [hin]; simp)
  fin_cases b
  · simpa [PEqualNP.TopForm.opnd, hin] using hp
  · simpa [PEqualNP.TopForm.opnd, hin] using hq

lemma rtg_conv {n : ℕ} (C : Circuit) (hRB : ReadsBack n C) (r k : ℕ)
    (h : Relation.ReflTransGen (fun k k' : ℕ =>
      (gateAt C k).op = GateOp.or ∧ n + k' ∈ (gateAt C k).inputs) r k)
    (hr : r < C.gates.length) :
    Relation.ReflTransGen (S90.OrStep n C) (n + r) (n + k) ∧ k < C.gates.length := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, hr⟩
  | tail _ hbc ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hlt := hRB _ ih2 _ hbc.2
    exact ⟨ih1.tail ⟨_, ih2, rfl, hbc.1, hbc.2, hlt⟩, by omega⟩

lemma two_facts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h2 : ∀ g ∈ C.gates, g.inputs.length = 2) (hRB : ReadsBack n C) {k : ℕ}
    (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or)
    (htwo : TwoNe (gateAt C) (PEqualNP.TopForm.orIn n C) k) :
    ¬ PEqualNP.TopForm.BelowF G C k ∧
      (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 0)).Nonempty ∧
      (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 1)).Nonempty := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (S90.gateAt_mem hk))
  have e0 : PEqualNP.TopForm.opnd C k 0 = p := by simp [PEqualNP.TopForm.opnd, hin]
  have e1 : PEqualNP.TopForm.opnd C k 1 = q := by simp [PEqualNP.TopForm.opnd, hin]
  obtain ⟨w1, hw1, w2, hw2, hne, hn1, hn2⟩ := htwo
  have hw1lt : w1 < n + k := hRB k hk w1 hw1
  have hw1m := hw1
  rw [hin] at hw1 hw2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1 hw2
  refine ⟨?_, ?_⟩
  · intro hbel
    obtain ⟨u, hu⟩ := hn1
    have hu2 : u ∈ PEqualNP.TopForm.orIn n C (n + k) :=
      (orIn_gate C k u).2 ⟨hk, hor, w1, hw1m, hw1lt, hu⟩
    have hr := (orIn_iff_reach _ u).1 hu2
    have hv := S90.reach_var_val (PEqualNP.EdgeOwnership.pairInput u u) (n + k) u hr
      (S90.pairInput_left u u)
    have hF := hbel _ (by rw [S90.gateVal_eq_val]; exact hv)
    exact G.irrefl ((S90.graphFun_pair G u u).1 hF)
  · rw [e0, e1]
    rcases hw1 with h1 | h1 <;> rcases hw2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1] at hn1
      rw [h2] at hn2
      exact ⟨hn1, hn2⟩
    · rw [h1] at hn1
      rw [h2] at hn2
      exact ⟨hn2, hn1⟩
    · exact absurd (h1.trans h2.symm) hne

lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : PEqualNP.TopForm.NoFourCycle G) (hne : G.edgeFinset.Nonempty)
    (hL : PEqualNP.TopForm.IsLeastAO G C) (hTF : PEqualNP.TopForm.TopForm G C) :
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  classical
  obtain ⟨⟨hAO, hRB, h2⟩, _, _⟩ := id hL
  have hlen : ∀ k, (gateAt C k).op = GateOp.or → (gateAt C k).inputs.length ≤ 2 := by
    intro k _
    by_cases hk : k < C.gates.length
    · rw [h2 _ (S90.gateAt_mem hk)]
    · rw [gateAt_ge (by omega)]
      simp
  have hback : ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n + k := by
    intro k i hi
    by_cases hk : k < C.gates.length
    · exact hRB k hk i hi
    · rw [gateAt_ge (by omega)] at hi
      simp at hi
  have hf2 : ∀ k, (gateAt C k).op = GateOp.or → ∀ u,
      u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔
        ∃ w ∈ (gateAt C k).inputs, u ∈ PEqualNP.TopForm.orIn n C w := by
    intro k hop u
    rw [orIn_gate]
    constructor
    · rintro ⟨_, _, w, hw, _, hu⟩
      exact ⟨w, hw, hu⟩
    · rintro ⟨w, hw, hu⟩
      have hk : k < C.gates.length := by
        by_contra hk
        rw [gateAt_ge (by omega)] at hw
        simp at hw
      exact ⟨hk, hop, w, hw, hRB k hk w hw, hu⟩
  have hf3 : ∀ k, (gateAt C k).op ≠ GateOp.or →
      (PEqualNP.TopForm.orIn n C (n + k)).card ≤ 1 := by
    intro k hop
    rw [Finset.card_le_one]
    intro a ha
    exact absurd ((orIn_gate C k a).1 ha).2.1 hop
  have h4' : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    rintro a b c d hac hbd ⟨h1, h2', h3, h5⟩
    have hsub : ({b, d} : Finset (Fin n)) ⊆
        Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact ⟨h1, h2'.symm⟩
      · exact ⟨h5.symm, h3⟩
    have := (Finset.card_le_card hsub).trans (h4 a c hac)
    rw [Finset.card_pair hbd] at this
    omega
  have hstar : ∀ a, a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C →
      (∀ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) →
        ∀ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) → G.Adj u v) ∧
      ((PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0)).card ≤ 1 ∨
        (PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1)).card ≤ 1) := by
    intro a ha
    have hf := S90.top_facts G C h4 hL a (Finset.mem_sdiff.1 ha).1
    exact ⟨hf.2.1, hf.2.2⟩
  have hEs : ∀ e, e ∈ G.edgeFinset \ PEqualNP.TopForm.Ustar G C →
      ∃ a, a ∈ PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C ∧
        ∃ u, u ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 0) ∧
        ∃ v, v ∈ PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C a 1) ∧ e = s(u, v) := by
    intro e he
    have he' : e ∈ PEqualNP.TopForm.starEdges G C := by
      simp only [PEqualNP.TopForm.Ustar, Finset.mem_sdiff, not_and, not_not] at he
      exact he.2 he.1
    simp only [PEqualNP.TopForm.starEdges, Finset.mem_biUnion, Finset.mem_image,
      Finset.mem_product] at he'
    obtain ⟨a, ha, p, hp, hpe⟩ := he'
    refine ⟨a, ?_, p.1, hp.1, p.2, hp.2, hpe.symm⟩
    rw [Finset.mem_sdiff]
    refine ⟨ha, fun hc => ?_⟩
    simp only [PEqualNP.TopForm.centreless, Finset.mem_filter] at hc
    rcases hc.2 with h | h
    · have := hp.1
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
    · have := hp.2
      rw [h] at this
      exact absurd this (Finset.notMem_empty _)
  obtain ⟨⟨Z, hZ1, hZ2⟩, hcov⟩ := assemble2 n G h4' (gateAt C) hlen hback
    (fun w => PEqualNP.TopForm.orIn n C w) (fun w hw => orIn_input C w hw) hf2 hf3 ∅ (by simp)
    (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C) (PEqualNP.TopForm.opnd C)
    hstar (G.edgeFinset \ PEqualNP.TopForm.Ustar G C) hEs
  refine ⟨?_, ?_⟩
  · have hZlam : Z ⊆ PEqualNP.TopForm.lam G C := by
      intro k hk
      obtain ⟨-, hor, htwo, a, ha, b, hnb, hrt, -, hcard⟩ := hZ1 k hk
      have hatop := (Finset.mem_sdiff.1 ha).1
      have halen : a < C.gates.length := by
        simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
          Finset.mem_range] at hatop
        exact hatop.1
      have hlt := opnd_lt h2 hRB halen b
      obtain ⟨hreach, hklen⟩ := rtg_conv C hRB _ k hrt (by omega)
      rw [show n + (PEqualNP.TopForm.opnd C a b - n) = PEqualNP.TopForm.opnd C a b by omega]
        at hreach
      have hOR := S90.reach_orReaches hreach k rfl hklen
      obtain ⟨hnbel, hn0, hn1⟩ := two_facts G C h2 hRB hklen hor htwo
      simp only [PEqualNP.TopForm.lam, PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range]
      exact ⟨⟨hklen, hor, hnbel⟩, hn0, hn1, a, hatop, b, hcard, hOR⟩
    have hAO' : ∀ k, k < C.gates.length →
        ((gateAt C k).op = GateOp.and ∧ ¬ (gateAt C k).op = GateOp.or) ∨
        ((gateAt C k).op = GateOp.or ∧ ¬ (gateAt C k).op = GateOp.and) := by
      intro k hk
      rcases hAO _ (S90.gateAt_mem hk) with h | h
      · exact Or.inl ⟨h, fun h' => by rw [h] at h'; cases h'⟩
      · exact Or.inr ⟨h, fun h' => by rw [h] at h'; cases h'⟩
    have hsplit := four_split C.gates.length (fun k => (gateAt C k).op = GateOp.and)
      (fun k => (gateAt C k).op = GateOp.or) (fun k => PEqualNP.TopForm.BelowF G C k) hAO'
      (PEqualNP.TopForm.tops G C) (PEqualNP.TopForm.junk G C) (PEqualNP.TopForm.orT G C)
      (PEqualNP.TopForm.orN G C)
      (fun k => by simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
      (fun k => junk_iff G C k)
      (fun k => by simp only [PEqualNP.TopForm.orT, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
      (fun k => by simp only [PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere,
        Finset.mem_filter, Finset.mem_range])
    have hm := (S98.main_real n G C hne hL hTF).2.2
    have hsize : C.size = C.gates.length := rfl
    have hU := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.Ustar G C ⊆ G.edgeFinset from Finset.sdiff_subset)
    have hTc := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.centreless G C ⊆ PEqualNP.TopForm.tops G C from
        Finset.filter_subset _ _)
    have hlam := Finset.card_sdiff_add_card_eq_card
      (show PEqualNP.TopForm.lam G C ⊆ PEqualNP.TopForm.orN G C from
        Finset.filter_subset _ _)
    have hZl := Finset.card_le_card hZlam
    omega
  · intro K hK
    refine hcov _ K ?_ hK
    intro u v huv
    rw [SimpleGraph.deleteEdges_adj] at huv
    rw [Finset.mem_sdiff, SimpleGraph.mem_edgeFinset]
    exact ⟨huv.1, fun h => huv.2 (Finset.mem_coe.2 h)⟩


lemma old_main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C →
    G.edgeFinset.card + (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card +
        2 * (PEqualNP.TopForm.centreless G C).card + (PEqualNP.TopForm.junk G C).card +
        (PEqualNP.TopForm.orN G C \ PEqualNP.TopForm.lam G C).card ≤
      C.size + (PEqualNP.TopForm.Ustar G C).card + 1 ∧
    ∀ K : Finset (Fin n),
      PEqualNP.MetaComplexity.NestedCover.IsMinCover (G.deleteEdges ↑(PEqualNP.TopForm.Ustar G C)) K →
      K.card ≤ (PEqualNP.TopForm.tops G C \ PEqualNP.TopForm.centreless G C).card := by
  intro n G _ C h4 hne hL hTF
  exact SafeLower.Source5781.main n G C h4 hne hL hTF

end SafeLower.Source5781

namespace SafeLower.Source7077

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Circuit evaluation and OR reachability follow L_meta_1490 and L_meta_4901.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
lemma junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩
lemma binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
lemma opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]
lemma opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)
lemma andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2
lemma andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩
lemma operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1
lemma operandReachLt (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) : h < a := by
  have hle := orStep_le (orReaches_reach h _ hr).1
  have hb := opndBound hAO ha b
  omega
lemma operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
    (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
  have hlen := (orReaches_reach h _ hr).2
  have hnb : ¬ BelowF G C h :=
    fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
  have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
    by_contra hne
    apply hnb
    intro x hx
    by_contra hf
    exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩
lemma reachVal {w h : ℕ} {x : Fin n → Bool} (hr : OrReaches n C w h)
    (hh : gateVal n C h x = true) : val C (List.ofFn x) w = true :=
  orStep_up (n := n) (by simp) (orReaches_reach h _ hr).1 hh
lemma eitherOperand (b c : Fin 2) : c = b ∨ c = 1 - b := by
  fin_cases b <;> fin_cases c <;> decide
lemma oppositeSideWmax (hAO : IsAO2 n C) {a j : ℕ} (ha : a ∈ tops G C) {b : Fin 2}
    (hr : OrReaches n C (opnd C a b) j) :
    side (n := n) C a (1 - b) ⊆ wmax G C j := by
  intro t ht
  obtain ⟨hal, hao, hab⟩ := topData ha
  simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
  intro x hj hx
  apply hab x
  apply (andValOperands hAO hal hao x).mpr
  intro c
  rcases eitherOperand b c with rfl | rfl
  · exact reachVal hr hj
  · exact reach_var_val x _ t (mem_orIn_reach t ht) hx
lemma orInTrans {w z : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w z) :
    orIn n C z ⊆ orIn n C w :=
  fun x hx => reach_mem_orIn x (hr.trans (mem_orIn_reach x hx))
lemma orStepOpnd (hAO : IsAO2 n C) {m : ℕ} (hm : m < C.gates.length)
    (hop : (gateAt C m).op = GateOp.or) (b : Fin 2) :
    OrStep n C (n + m) (opnd C m b) :=
  ⟨m, hm, rfl, hop, opndMem hAO hm b, opndBound hAO hm b⟩
lemma inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
    (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
  rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
  · exact ⟨0, by simp [opnd, hpq]⟩
  · have e : z = q := List.mem_singleton.mp hq
    exact ⟨1, by simpa [opnd, hpq] using e⟩
lemma orNOfRaw {m : ℕ} (hm : m < C.gates.length) (hop : (gateAt C m).op = GateOp.or)
    (hn : (orIn n C (n + m)).Nonempty) : m ∈ orN G C := by
  obtain ⟨t, ht⟩ := hn
  simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
  refine ⟨hm, hop, ?_⟩
  intro hb
  have hv : gateVal n C m (pairInput t t) = true :=
    reach_var_val (pairInput t t) _ t (mem_orIn_reach t ht) (pairInput_left t t)
  exact G.irrefl ((graphFun_pair G t t).mp (hb _ hv))
lemma lamAvoidsUstar {m : ℕ} (hm : m ∈ lam G C)
    (hstar : ∀ a ∈ tops G C, ∀ x ∈ side (n := n) C a 0, ∀ y ∈ side C a 1, G.Adj x y) :
    ∃ t : Fin n, ∀ x ∈ orIn n C (n + m), G.Adj t x ∧ s(t, x) ∉ Ustar G C := by
  obtain ⟨_, _, _, a, ha, b, hcard, hr⟩ := Finset.mem_filter.mp hm
  have hsub : orIn n C (n + m) ⊆ side (n := n) C a b :=
    orInTrans (orReaches_reach m _ hr).1
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcard
  refine ⟨t, fun x hx => ?_⟩
  have hts : t ∈ side (n := n) C a (1 - b) := by simp [ht]
  have hstar' : s(t, x) ∈ starEdges G C := by
    unfold starEdges
    refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr ?_⟩
    fin_cases b
    · exact ⟨(x, t), Finset.mem_product.mpr ⟨hsub hx, hts⟩, Sym2.eq_swap⟩
    · exact ⟨(t, x), Finset.mem_product.mpr ⟨hts, hsub hx⟩, rfl⟩
  refine ⟨?_, fun he => (Finset.mem_sdiff.mp he).2 hstar'⟩
  fin_cases b
  · exact (hstar a ha x (hsub hx) t hts).symm
  · exact hstar a ha t hts x (hsub hx)

lemma sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
    (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
    val C (List.ofFn x) (opnd C a b) = true :=
  reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
  (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

lemma topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  obtain ⟨hl, ho, hb⟩ := topData ha
  exact (graphFun_pair G u v).mp
    (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

lemma acceptedTop (hL : IsLeastAO G C) {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
  have hout (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hL.2.1 x
  obtain ⟨a, hl, ho, hr, hv⟩ :=
    edge_trace G (graphFun G ∅) (fun k l => (graphFun_pair G k l).mp)
      hout u v ((graphFun_pair G u v).mpr hadj)
  have hand := (hL.1.1 _ (gateAt_mem hl)).resolve_right ho
  have hb : BelowF G C a := fun x hx =>
    below_of_reach (graphFun G ∅) hout a hr x (gateVal_eq_val n C a x ▸ hx)
  refine ⟨a, ?_, hv⟩
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    And.intro hl (And.intro hand hb)

lemma operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
    {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
    (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
        gateVal n C j (pairInput u v) = true := by
  rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
  · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
  · have hr' := reach_orReaches hr j rfl hj
    exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
      ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩

lemma memJunkPair {j k a : ℕ} (hs : junk G C = {j,k}) (ha : a ∈ junk G C) :
    a = j ∨ a = k := by
  simpa only [hs, Finset.mem_insert, Finset.mem_singleton] using ha

lemma mem_gammaE_of_pair {u v : Fin n} (he : s(u, v) ∈ G.edgeFinset) {j : ℕ}
    (hv : gateVal n C j (pairInput u v) = true) :
    s(u, v) ∈ gammaE G C j :=
  Finset.mem_filter.mpr ⟨he, u, v, rfl, hv⟩

lemma biclique_star (h4 : NoFourCycle G) (A B : Finset (Fin n))
    (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  have hsub : ({b, d} : Finset (Fin n)) ⊆
      Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hw with rfl | rfl
    · exact ⟨hab a ha w hb, hab c hc w hb⟩
    · exact ⟨hab a ha w hd, hab c hc w hd⟩
  have hle := (Finset.card_le_card hsub).trans (h4 a c hac)
  rw [Finset.card_pair hbd] at hle
  omega

lemma conj1 (h4 : NoFourCycle G) (hL : IsLeastAO G C) :
    ∃ (S : Finset (Fin n)), S.card ≤ (tops G C \ centreless G C).card ∧
      ∀ e ∈ starEdges G C, ∃ v ∈ S, v ∈ e := by
  classical
  let pick : ℕ → Finset (Fin n) := fun a =>
    if (side (n := n) C a 0).card ≤ 1 then side (n := n) C a 0 else side (n := n) C a 1
  refine ⟨(tops G C \ centreless G C).biUnion pick, ?_, ?_⟩
  · have hle : ((tops G C \ centreless G C).biUnion pick).card ≤
        ∑ a ∈ tops G C \ centreless G C, (pick a).card := Finset.card_biUnion_le
    have hsum : ∑ a ∈ tops G C \ centreless G C, (pick a).card ≤
        ∑ _a ∈ tops G C \ centreless G C, 1 := by
      apply Finset.sum_le_sum
      intro a ha
      have hat : a ∈ tops G C := (Finset.mem_sdiff.mp ha).1
      dsimp only [pick]
      split_ifs with h0
      · exact h0
      · rcases biclique_star h4 (side (n := n) C a 0) (side (n := n) C a 1)
          (fun u hu v hv => topAdj hL.1 hat hu hv) with h | h
        · exact (h0 h).elim
        · exact h
    rw [Finset.sum_const, smul_eq_mul, mul_one] at hsum
    exact hle.trans hsum
  · intro e he
    simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product] at he
    obtain ⟨a, ha, ⟨u, v⟩, ⟨hu, hv⟩, rfl⟩ := he
    have hac : a ∉ centreless G C := by
      intro hc
      simp only [centreless, Finset.mem_filter] at hc
      rcases hc.2 with h0 | h1
      · rw [h0] at hu; exact Finset.notMem_empty u hu
      · rw [h1] at hv; exact Finset.notMem_empty v hv
    have has : a ∈ tops G C \ centreless G C := Finset.mem_sdiff.mpr ⟨ha, hac⟩
    dsimp only [pick]
    by_cases h0 : (side (n := n) C a 0).card ≤ 1
    · refine ⟨u, Finset.mem_biUnion.mpr ⟨a, has, ?_⟩, by simp⟩
      rw [if_pos h0]; exact hu
    · refine ⟨v, Finset.mem_biUnion.mpr ⟨a, has, ?_⟩, by simp⟩
      rw [if_neg h0]; exact hv

lemma conj2 (hL : IsLeastAO G C) (hT : TopForm G C) (hj : junk G C = ∅) :
    Ustar G C = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
    obtain ⟨a, ha, hv⟩ := acceptedTop hL hadj
    obtain ⟨hl, ho, _⟩ := topData ha
    have traces (b : Fin 2) := operandSupport hL.1 hT hl ho
      ((andValOperands hL.1 hl ho (pairInput u v)).mp hv b)
    rcases traces 0 with ⟨x, hx, hxe⟩ | ⟨g, hg, _⟩
    · rcases traces 1 with ⟨y, hy, hye⟩ | ⟨g, hg, _⟩
      · have hxy := G.ne_of_adj (topAdj hL.1 ha hx hy)
        have eq : s(u, v) = s(x, y) := by
          rcases hxe with rfl | rfl <;> rcases hye with rfl | rfl
          · exact (hxy rfl).elim
          · rfl
          · exact Sym2.eq_swap
          · exact (hxy rfl).elim
        exact (Finset.mem_sdiff.mp he).2 (eq ▸ Finset.mem_biUnion.mpr ⟨a, ha,
          Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩⟩)
      · rw [hj] at hg; exact Finset.notMem_empty g hg
    · rw [hj] at hg; exact Finset.notMem_empty g hg

end SafeLower.Source7077

namespace SafeLower
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

abbrev graph : SimpleGraph (Fin 10) := PEqualNP.EdgeOwnership.edgeGraph 10
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
   (5,7),(7,9),(9,6),(6,8),(8,5)]


lemma graph_card : graph.edgeFinset.card = 15 := by decide +kernel
lemma graph_nonempty : graph.edgeFinset.Nonempty := by decide +kernel
lemma graph_no_four_cycle : NoFourCycle graph := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cover_card : ∀ K : Finset (Fin 10),
    (∀ e ∈ graph.edgeFinset, ∃ v ∈ K, v ∈ e) → 6 ≤ K.card := by
  decide +kernel

def uncovered (K : Finset (Fin 10)) : Finset (Sym2 (Fin 10)) :=
  graph.edgeFinset.filter (fun e => Disjoint e.toFinset K)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma five_vertices_miss_two : ∀ K : Finset (Fin 10), K.card < 6 →
    2 ≤ (uncovered K).card := by
  decide +kernel

lemma one_uncovered_lower (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) (hu : (Ustar graph C).card ≤ 1) : 20 ≤ C.size := by
  obtain ⟨K, hk, hcover⟩ := Source7077.conj1 graph_no_four_cycle hl
  have miss_subset : uncovered K ⊆ Ustar graph C := by
    intro e he
    obtain ⟨hedge, hdisj⟩ := Finset.mem_filter.mp he
    apply Finset.mem_sdiff.mpr
    refine ⟨hedge, ?_⟩
    intro hstar
    obtain ⟨v, hvK, hve⟩ := hcover e hstar
    exact Finset.disjoint_left.mp hdisj (by simpa using hve) hvK
  have hc : 6 ≤ K.card := by
    by_contra hlt
    have hm := five_vertices_miss_two K (by omega)
    have hsub := Finset.card_le_card miss_subset
    omega
  have compensation : (Ustar graph C).card ≤ (junk graph C).card := by
    by_cases hj : junk graph C = ∅
    · rw [Source7077.conj2 hl ht hj, Finset.card_empty]
      omega
    · have positive : 0 < (junk graph C).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hj)
      omega
  have bound := (Source5781.old_main 10 graph C graph_no_four_cycle graph_nonempty hl ht).1
  rw [graph_card] at bound
  omega

lemma no_uncovered_lower (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) (hu : Ustar graph C = ∅) : 20 ≤ C.size := by
  obtain ⟨K, hk, hcover⟩ := Source7077.conj1 graph_no_four_cycle hl
  have hc : 6 ≤ K.card := cover_card K (by
    intro e he
    apply hcover e
    by_contra hnot
    have heU : e ∈ Ustar graph C := Finset.mem_sdiff.mpr ⟨he, hnot⟩
    simpa [hu] using heU)
  have bound := (Source5781.old_main 10 graph C graph_no_four_cycle graph_nonempty hl ht).1
  rw [graph_card, hu, Finset.card_empty] at bound
  omega

lemma safe_and_lower (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) (hsafe : junk graph C = ∅) : 20 ≤ C.size := by
  exact no_uncovered_lower C hl ht (Source7077.conj2 hl ht hsafe)

end SafeLower


namespace SafeLower.Source2695

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [if_neg hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [if_pos hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [if_pos hlt] at h'; exact ⟨hlt, h'⟩
    · rw [if_neg hlt] at h'; cases h'
  · intro h i hi
    rw [if_pos (h i hi).1]; exact (h i hi).2

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl


open PEqualNP.CleanedNonEdge

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩


open PEqualNP.TopForm PEqualNP.EdgeOwnership

lemma chain {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g → w = n + g ∨
      ∃ h, h < C.gates.length ∧ (gateAt C h).op = GateOp.or ∧
        n + g ∈ (gateAt C h).inputs ∧ g < h := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact Or.inl rfl
    · rcases ih i hlt hr with rfl | h4
      · exact Or.inr ⟨k, hk, hop, hi, by omega⟩
      · exact Or.inr h4

lemma orIn_and {n : ℕ} {C : Circuit} {g : ℕ} (hop : (gateAt C g).op = GateOp.and) :
    orIn n C (n + g) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro i hi
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with h | ⟨k, hk, hr, hko, _⟩
  · have := i.isLt; omega
  · obtain ⟨_, h3⟩ := (orReaches_iff n C g k).mp hr
    rcases h3 with rfl | ⟨ho, _⟩
    · rw [hop] at hko; cases hko
    · rw [hop] at ho; cases ho

lemma main : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x5 ∈ x4.gates, x5.inputs.length = (2 : ℕ)) → ∀ x6 ∈ PEqualNP.TopForm.tops x2 x4, ∀ (x8 : Fin (2 : ℕ)), ∀ x9 ∈ PEqualNP.TopForm.junk x2 x4, PEqualNP.CleanedNonEdge.OrReaches x1 x4 (PEqualNP.TopForm.opnd x4 x6 x8) x9 → x6 ∈ PEqualNP.TopForm.centreless x2 x4 ∨ (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).Nonempty := by
  intro n G _ C h2 a ha b g hg hr
  unfold junk gatesWhere at hg
  have hg := (Finset.mem_filter.mp hg).2
  unfold IsDirtyAnd IsDirty at hg
  obtain ⟨hgop, hgl, x, hx, hF⟩ := hg
  rcases chain g _ hr with hw | ⟨h, hh, hop, hin, hlt⟩
  · left
    have he : side (n := n) C a b = ∅ := by
      unfold side; rw [hw]; exact orIn_and hgop
    unfold centreless
    rw [Finset.mem_filter]
    refine ⟨ha, ?_⟩
    fin_cases b
    · exact Or.inl he
    · exact Or.inr he
  · right
    refine ⟨h, ?_⟩
    rw [Finset.mem_sdiff]
    constructor
    · simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
      refine ⟨hh, hop, ?_⟩
      intro hb
      have hv : gateVal n C h x = true := by
        rw [gateVal_eq_val]
        exact (val_or (n := n) (by simp) hh hop).mpr ⟨n + g, hin, by omega, hx⟩
      rw [hb x hv] at hF
      cases hF
    · intro hl
      unfold lam at hl
      rw [Finset.mem_filter] at hl
      obtain ⟨_, h0, h1, _⟩ := hl
      have hlen := h2 _ (gateAt_mem hh)
      have hE := orIn_and (n := n) hgop
      match hi : (gateAt C h).inputs, hlen with
      | [u0, u1], _ =>
        rw [hi] at hin
        simp only [opnd, hi] at h0 h1
        simp at hin h0 h1
        rcases hin with e | e
        · rw [← e, hE] at h0; simp at h0
        · rw [← e, hE] at h1; simp at h1

end SafeLower.Source2695
namespace SafeLower
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm Source7077

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma four_vertices_miss_three : ∀ K : Finset (Fin 10), K.card < 5 →
    3 ≤ (uncovered K).card := by
  decide +kernel

lemma uncovered_reaches_junk (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) (hu : (Ustar graph C).Nonempty) :
    ∃ a ∈ tops graph C, ∃ b : Fin 2, ∃ g ∈ junk graph C,
      PEqualNP.CleanedNonEdge.OrReaches 10 C (opnd C a b) g := by
  obtain ⟨e, he⟩ := hu
  induction e using Sym2.ind with
  | _ u v =>
    have hadj : graph.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
    obtain ⟨a, ha, hv⟩ := acceptedTop hl hadj
    obtain ⟨hal, ho, _⟩ := topData ha
    have traces (b : Fin 2) := operandSupport hl.1 ht hal ho
      ((andValOperands hl.1 hal ho (PEqualNP.EdgeOwnership.pairInput u v)).mp hv b)
    rcases traces 0 with ⟨x, hx, hxe⟩ | ⟨g, hg, hreach, _⟩
    · rcases traces 1 with ⟨y, hy, hye⟩ | ⟨g, hg, hreach, _⟩
      · have hxy := graph.ne_of_adj (topAdj hl.1 ha hx hy)
        have eq : s(u, v) = s(x, y) := by
          rcases hxe with rfl | rfl <;> rcases hye with rfl | rfl
          · exact (hxy rfl).elim
          · rfl
          · exact Sym2.eq_swap
          · exact (hxy rfl).elim
        exact False.elim ((Finset.mem_sdiff.mp he).2
          (eq ▸ Finset.mem_biUnion.mpr ⟨a, ha,
            Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩⟩))
      · exact ⟨a, ha, 1, g, hg, hreach⟩
    · exact ⟨a, ha, 0, g, hg, hreach⟩

lemma two_uncovered_parameters (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) (hu : (Ustar graph C).card = 2) (hs : C.size ≤ 19) :
    (tops graph C \ centreless graph C).card = 5 ∧
      centreless graph C = ∅ ∧ (junk graph C).card = 1 ∧
        (orN graph C \ lam graph C).card = 1 := by
  obtain ⟨K, hk, hcover⟩ := conj1 graph_no_four_cycle hl
  have miss_subset : uncovered K ⊆ Ustar graph C := by
    intro e he
    obtain ⟨hedge, hdisj⟩ := Finset.mem_filter.mp he
    apply Finset.mem_sdiff.mpr
    refine ⟨hedge, ?_⟩
    intro hstar
    obtain ⟨v, hvK, hve⟩ := hcover e hstar
    exact Finset.disjoint_left.mp hdisj (by simpa using hve) hvK
  have hc : 5 ≤ K.card := by
    by_contra hlt
    have hm := four_vertices_miss_three K (by omega)
    have hsub := Finset.card_le_card miss_subset
    omega
  have hU : (Ustar graph C).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha, b, g, hg, hreach⟩ := uncovered_reaches_junk C hl ht hU
  have hj : 0 < (junk graph C).card := Finset.card_pos.mpr ⟨g, hg⟩
  have bound := (Source5781.old_main 10 graph C graph_no_four_cycle graph_nonempty hl ht).1
  rw [graph_card, hu] at bound
  have hczero : (centreless graph C).card = 0 := by omega
  have hce : centreless graph C = ∅ := Finset.card_eq_zero.mp hczero
  have hr : 0 < (orN graph C \ lam graph C).card := by
    rcases Source2695.main 10 graph C hl.1.2.2 a ha b g hg hreach with hbad | good
    · simpa [hce] using hbad
    · exact Finset.card_pos.mpr good
  exact ⟨by omega, hce, by omega, by omega⟩

end SafeLower

namespace SafeLower
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover Source7077

lemma unsafe_or_reader {C : Circuit} (hao : IsAO2 10 C) {g m : Nat}
    (hg : g ∈ junk graph C) (hm : m < C.gates.length)
    (hop : (gateAt C m).op = GateOp.or) (hin : 10 + g ∈ (gateAt C m).inputs) :
    m ∈ orN graph C \ lam graph C := by
  obtain ⟨hgl, hgop, x, hx, hf⟩ := junkData hg
  have hbound := hao.2.1 m hm (10 + g) hin
  apply Finset.mem_sdiff.mpr
  constructor
  · simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
    refine ⟨hm, hop, ?_⟩
    intro hb
    have hv : gateVal 10 C m x = true := by
      rw [Source2695.gateVal_eq_val]
      exact (Source2695.val_or (n := 10) (by simp) hm hop).mpr
        ⟨10 + g, hin, hbound, hx⟩
    rw [hb x hv] at hf
    cases hf
  · intro hl
    obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
    have hlen := hao.2.2 _ (Source2695.gateAt_mem hm)
    have hE := Source2695.orIn_and (n := 10) hgop
    match hi : (gateAt C m).inputs, hlen with
    | [u0, u1], _ =>
      rw [hi] at hin
      simp only [opnd, hi] at h0 h1
      simp at hin h0 h1
      rcases hin with e | e
      · rw [← e, hE] at h0; simp at h0
      · rw [← e, hE] at h1; simp at h1

lemma one_nonlambda_later (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) (hu : (Ustar graph C).Nonempty)
    (hc : centreless graph C = ∅) {g : Nat} (hj : junk graph C = {g})
    (hr : (orN graph C \ lam graph C).card = 1) :
    ∃ m, g < m ∧ orN graph C \ lam graph C = {m} := by
  obtain ⟨a, ha, b, k, hk, hreach⟩ := uncovered_reaches_junk C hl ht hu
  have hkg : k = g := by simpa [hj] using hk
  subst k
  obtain ⟨hgl, hgop, _⟩ := junkData hk
  rcases Source2695.chain g _ hreach with he | ⟨m, hm, hop, hin, hgm⟩
  · have hs : side (n := 10) C a b = ∅ := by
      unfold side
      rw [he]
      exact Source2695.orIn_and hgop
    have hcentre : a ∈ centreless graph C := by
      apply Finset.mem_filter.mpr
      refine ⟨ha, ?_⟩
      fin_cases b
      · exact Or.inl hs
      · exact Or.inr hs
    simpa [hc] using hcentre
  · have hmem := unsafe_or_reader hl.1 hk hm hop hin
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hr
    have hmq : m = q := by simpa [hq] using hmem
    exact ⟨m, hgm, hmq ▸ hq⟩

lemma early_or_in_lambda (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) (hu : (Ustar graph C).Nonempty)
    (hc : centreless graph C = ∅) {g : Nat} (hj : junk graph C = {g})
    (hr : (orN graph C \ lam graph C).card = 1) {h : Nat}
    (hh : h ∈ orN graph C) (hbefore : h < g) : h ∈ lam graph C := by
  obtain ⟨m, hgm, heq⟩ := one_nonlambda_later C hl ht hu hc hj hr
  by_contra hnot
  have hm : h ∈ orN graph C \ lam graph C := Finset.mem_sdiff.mpr ⟨hh, hnot⟩
  have he : h = m := by simpa [heq] using hm
  omega

end SafeLower

namespace SafeLower
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover Source7077

lemma first_junk_operand (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) {g : Nat} (hj : junk graph C = {g})
    (b : Fin 2) (x : Fin 10 → Bool) :
    val C (List.ofFn x) (opnd C g b) = true ↔
      ∃ v ∈ side (n := 10) C g b, x v = true := by
  have hg : g ∈ junk graph C := by simp [hj]
  obtain ⟨hgl, hgop, _⟩ := junkData hg
  constructor
  · intro hv
    obtain ⟨w, hreach, hwval, hterm⟩ := or_trace (n := 10) (by simp) _ hv
    rcases hterm with hraw | ⟨a, hal, heq, hnotor⟩
    · let v : Fin 10 := ⟨w, hraw⟩
      refine ⟨v, reach_mem_orIn v hreach, ?_⟩
      change val C (List.ofFn x) v.val = true at hwval
      simpa only [val_ofFn] using hwval
    · rw [heq] at hreach
      have hr := reach_orReaches hreach a rfl hal
      have hop := (hl.1.1 _ (gateAt_mem hal)).resolve_right hnotor
      have ha := operandOrAndJunk hl.1 ht hgl hgop hr hop
      have hae : a = g := by simpa [hj] using ha
      have hbefore := operandReachLt hl.1 hgl hr
      omega
  · rintro ⟨v, hv, hx⟩
    exact sideVal hv hx

lemma first_junk_cone_has_input (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) {g : Nat} (hj : junk graph C = {g}) (b : Fin 2) :
    ∀ w, Relation.ReflTransGen (OrStep 10 C) (opnd C g b) w →
      (orIn 10 C w).Nonempty := by
  have hg : g ∈ junk graph C := by simp [hj]
  obtain ⟨hgl, hgop, _⟩ := junkData hg
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hpath
    have hle := orStep_le hpath
    have hb := opndBound hl.1 hgl b
    by_cases hraw : w < 10
    · let v : Fin 10 := ⟨w, hraw⟩
      exact ⟨v, reach_mem_orIn v Relation.ReflTransGen.refl⟩
    · obtain ⟨k, rfl⟩ : ∃ k, w = 10 + k := ⟨w - 10, by omega⟩
      have hkl : k < C.gates.length := by omega
      rcases hl.1.1 _ (gateAt_mem hkl) with hand | hor
      · have hr := reach_orReaches hpath k rfl hkl
        have hk := operandOrAndJunk hl.1 ht hgl hgop hr hand
        have hkg : k = g := by simpa [hj] using hk
        omega
      · let z := opnd C k 0
        have hstep : OrStep 10 C (10 + k) z := orStepOpnd hl.1 hkl hor 0
        have hz : z < 10 + k := opndBound hl.1 hkl 0
        have hsingle := Relation.ReflTransGen.single hstep
        obtain ⟨v, hv⟩ := ih z hz (hpath.trans hsingle)
        exact ⟨v, orInTrans hsingle hv⟩

lemma first_junk_or_in_lambda (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) (hu : (Ustar graph C).Nonempty)
    (hc : centreless graph C = ∅) {g : Nat} (hj : junk graph C = {g})
    (hr : (orN graph C \ lam graph C).card = 1) (b : Fin 2) {h : Nat}
    (hreach : PEqualNP.CleanedNonEdge.OrReaches 10 C (opnd C g b) h)
    (hop : (gateAt C h).op = GateOp.or) : h ∈ lam graph C := by
  have hg : g ∈ junk graph C := by simp [hj]
  obtain ⟨hgl, _, _⟩ := junkData hg
  have hpath := (orReaches_reach h _ hreach).1
  have hhl := (orReaches_reach h _ hreach).2
  have hraw := first_junk_cone_has_input C hl ht hj b (10 + h) hpath
  have hunsafe := orNOfRaw (G := graph) hhl hop hraw
  exact early_or_in_lambda C hl ht hu hc hj hr hunsafe (operandReachLt hl.1 hgl hreach)

end SafeLower

namespace SafeLower
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover Source7077

lemma least_distinct_wire (C : Circuit) (hl : IsLeastAO graph C) (i j : Nat)
    (hi : i < 10 + j) (hj : j < C.gates.length) :
    ∃ x : Fin 10 → Bool, val C (List.ofFn x) i ≠ val C (List.ofFn x) (10 + j) := by
  have hleast : Source5781.S98.Least 10 C :=
    ⟨Source5781.S98.AO_of_IsAO2 10 C hl.1, fun D hD hf =>
      hl.2.2 D (Source5781.S98.IsAO2_of_AO 10 D hD)
        (funext fun x => (hf x).trans (congrFun hl.2.1 x))⟩
  exact Source5781.S98.least_nodup 10 C hleast i j hi hj

lemma first_junk_sides_incomparable (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) {g : Nat} (hj : junk graph C = {g}) (b : Fin 2) :
    ¬ side (n := 10) C g b ⊆ side C g (1 - b) := by
  intro hsub
  have hg : g ∈ junk graph C := by simp [hj]
  obtain ⟨hgl, hgop, _⟩ := junkData hg
  obtain ⟨x, hne⟩ := least_distinct_wire C hl (opnd C g b) g
    (opndBound hl.1 hgl b) hgl
  have hiff : val C (List.ofFn x) (10 + g) = true ↔
      val C (List.ofFn x) (opnd C g b) = true := by
    constructor
    · intro h
      exact (andValOperands hl.1 hgl hgop x).mp h b
    · intro h
      apply (andValOperands hl.1 hgl hgop x).mpr
      intro d
      rcases eitherOperand b d with rfl | rfl
      · exact h
      · obtain ⟨v, hv, hx⟩ := (first_junk_operand C hl ht hj b x).mp h
        exact (first_junk_operand C hl ht hj (1 - b) x).mpr ⟨v, hsub hv, hx⟩
  apply hne
  cases ha : val C (List.ofFn x) (opnd C g b) <;>
    cases hg : val C (List.ofFn x) (10 + g) <;> simp_all

lemma orIn_raw {C : Circuit} {w : Nat} (hw : w < 10) :
    orIn 10 C w = {⟨w, hw⟩} := by
  ext v
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro (he | ⟨k, hk, hr, hop, hin⟩)
    · exact Fin.ext he
    · have := hr.1
      omega
  · intro he
    exact Or.inl (congrArg Fin.val he)

lemma large_first_junk_side_lambda (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) (hu : (Ustar graph C).Nonempty)
    (hc : centreless graph C = ∅) {g : Nat} (hj : junk graph C = {g})
    (hr : (orN graph C \ lam graph C).card = 1) (b : Fin 2)
    (hbig : 2 ≤ (side (n := 10) C g b).card) :
    ∃ h, opnd C g b = 10 + h ∧ h ∈ lam graph C ∧
      (gateAt C h).op = GateOp.or := by
  have hg : g ∈ junk graph C := by simp [hj]
  obtain ⟨hgl, hgop, _⟩ := junkData hg
  have hb := opndBound hl.1 hgl b
  have hn : 10 ≤ opnd C g b := by
    by_contra hnot
    have he := orIn_raw (C := C) (w := opnd C g b) (by omega)
    have hcside : (side (n := 10) C g b).card = 1 := by
      unfold side
      rw [he, Finset.card_singleton]
    omega
  obtain ⟨h, he⟩ : ∃ h, opnd C g b = 10 + h := ⟨opnd C g b - 10, by omega⟩
  have hhl : h < C.gates.length := by omega
  have hreach : OrReaches 10 C (opnd C g b) h := by
    rw [he]
    exact (Source2695.orReaches_iff 10 C h h).mpr ⟨hhl, Or.inl rfl⟩
  rcases hl.1.1 _ (gateAt_mem hhl) with hand | hor
  · have hmem := operandOrAndJunk hl.1 ht hgl hgop hreach hand
    have heg : h = g := by simpa [hj] using hmem
    omega
  · exact ⟨h, he, first_junk_or_in_lambda C hl ht hu hc hj hr b hreach hor, hor⟩

end SafeLower

namespace SafeLower
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover Source7077

-- Extracted from the local h_one_side argument in checked L_meta_7077.conj3.
lemma one_junk_filtered_edge (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) {g : Nat} (hj : junk graph C = {g})
    {u v : Fin 10} (he : s(u, v) ∈ Ustar graph C) :
    ∃ w ∈ wmax graph C g, (w = u ∨ w = v) ∧
      gateVal 10 C g (pairInput u v) = true := by
  have hg : g ∈ junk graph C := by simp [hj]
  obtain ⟨hgl, hgo, xd, hgd, hfd⟩ := junkData hg
  have hadj : graph.Adj u v := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
  obtain ⟨a, ha, hv⟩ := acceptedTop hl hadj
  obtain ⟨hal, ho, hb⟩ := topData ha
  have traces (b : Fin 2) := operandSupport hl.1 ht hal ho
    ((andValOperands hl.1 hal ho (pairInput u v)).mp hv b)
  rcases traces 0 with ⟨x, hx, hxe⟩ | ⟨j0, hj0, hr0, hv0⟩ <;>
    rcases traces 1 with ⟨y, hy, hye⟩ | ⟨j1, hj1, hr1, hv1⟩
  · have hxy := graph.ne_of_adj (topAdj hl.1 ha hx hy)
    have eq : s(u, v) = s(x, y) := by
      rcases hxe with rfl | rfl <;> rcases hye with rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hxy rfl).elim
    exact ((Finset.mem_sdiff.mp he).2 (eq ▸ Finset.mem_biUnion.mpr ⟨a, ha,
      Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩⟩)).elim
  · rw [hj, Finset.mem_singleton] at hj1
    subst hj1
    exact ⟨x, oppositeSideWmax hl.1 ha hr1 hx, hxe, hv1⟩
  · rw [hj, Finset.mem_singleton] at hj0
    subst hj0
    exact ⟨y, oppositeSideWmax hl.1 ha hr0 hy, hye, hv0⟩
  · rw [hj, Finset.mem_singleton] at hj0 hj1
    subst hj0
    subst hj1
    have hbel : graphFun graph ∅ xd = true :=
      hb xd ((andValBoth hl.1 hal ho xd).mpr
        ⟨reachVal hr0 hgd, reachVal hr1 hgd⟩)
    exact False.elim (Bool.false_ne_true (hfd.symm.trans hbel))

end SafeLower



namespace SingleUnsafe

def edges : Finset (Fin 10 × Fin 10) :=
  {(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
   (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)}

def adj (a b : Fin 10) : Bool := decide ((a, b) ∈ edges ∨ (b, a) ∈ edges)

def supports : Fin 50 → Finset (Fin 10) :=
  ![{0},
    {1},
    {2},
    {3},
    {4},
    {5},
    {6},
    {7},
    {8},
    {9},
    {1, 4},
    {1, 5},
    {4, 5},
    {1, 4, 5},
    {0, 2},
    {0, 6},
    {2, 6},
    {0, 2, 6},
    {1, 3},
    {1, 7},
    {3, 7},
    {1, 3, 7},
    {2, 4},
    {2, 8},
    {4, 8},
    {2, 4, 8},
    {0, 3},
    {0, 9},
    {3, 9},
    {0, 3, 9},
    {0, 7},
    {0, 8},
    {7, 8},
    {0, 7, 8},
    {1, 8},
    {1, 9},
    {8, 9},
    {1, 8, 9},
    {2, 5},
    {2, 9},
    {5, 9},
    {2, 5, 9},
    {3, 5},
    {3, 6},
    {5, 6},
    {3, 5, 6},
    {4, 6},
    {4, 7},
    {6, 7},
    {4, 6, 7}]

def centers : Fin 50 → Finset (Fin 10) :=
  ![∅,
    ∅,
    ∅,
    ∅,
    ∅,
    ∅,
    ∅,
    ∅,
    ∅,
    ∅,
    {0},
    {0},
    {0},
    {0},
    {1},
    {1},
    {1},
    {1},
    {2},
    {2},
    {2},
    {2},
    {3},
    {3},
    {3},
    {3},
    {4},
    {4},
    {4},
    {4},
    {5},
    {5},
    {5},
    {5},
    {6},
    {6},
    {6},
    {6},
    {7},
    {7},
    {7},
    {7},
    {8},
    {8},
    {8},
    {8},
    {9},
    {9},
    {9},
    {9}]

def filterable (A B : Finset (Fin 10)) (w : Fin 10) : Bool :=
  decide (∀ a ∈ A, ∀ b ∈ B, adj a b = true ∨ adj a w = true ∨ adj b w = true)

def accepted (A B : Finset (Fin 10)) (e : Fin 10 × Fin 10) : Bool :=
  decide ((e.1 ∈ A ∨ e.2 ∈ A) ∧ (e.1 ∈ B ∨ e.2 ∈ B))

def eligible (A B K : Finset (Fin 10)) : Finset (Fin 10 × Fin 10) :=
  edges.filter fun e => accepted A B e = true ∧
    (filterable A B e.1 = true ∨ filterable A B e.2 = true) ∧ e.1 ∉ K ∧ e.2 ∉ K

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma descriptor_pair_bound : ∀ i j : Fin 50,
    ¬ supports i ⊆ supports j → ¬ supports j ⊆ supports i →
    (eligible (supports i) (supports j) (centers i ∪ centers j)).card ≤ 1 := by
  decide +kernel

lemma raw_descriptor (v : Fin 10) :
    ∃ i : Fin 50, supports i = {v} ∧ centers i = ∅ := by
  fin_cases v <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma neighbor_descriptor : ∀ (v : Fin 10) (S : Finset (Fin 10)),
    2 ≤ S.card → (∀ a ∈ S, adj v a = true) →
    ∃ i : Fin 50, supports i = S ∧ centers i = {v} := by
  decide +kernel

lemma eligible_antitone (A B K L : Finset (Fin 10)) (hKL : K ⊆ L) :
    eligible A B L ⊆ eligible A B K := by
  intro e he
  obtain ⟨hedge, ha, hw, hK1, hK2⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨hedge, ha, hw, fun h => hK1 (hKL h), fun h => hK2 (hKL h)⟩

lemma descriptor_cover_bound (i j : Fin 50) (K : Finset (Fin 10))
    (hi : centers i ⊆ K) (hj : centers j ⊆ K)
    (hij : ¬ supports i ⊆ supports j) (hji : ¬ supports j ⊆ supports i) :
    (eligible (supports i) (supports j) K).card ≤ 1 := by
  have hs : centers i ∪ centers j ⊆ K := Finset.union_subset hi hj
  exact (Finset.card_le_card (eligible_antitone (supports i) (supports j) _ _ hs)).trans
    (descriptor_pair_bound i j hij hji)

end SingleUnsafe

namespace SingleUnsafe

def orValue (A : Finset (Fin 10)) (x : Fin 10 → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

def product (A B : Finset (Fin 10)) (x : Fin 10 → Bool) : Bool :=
  orValue A x && orValue B x

def edgeValue (x : Fin 10 → Bool) : Bool :=
  decide (∃ e ∈ edges, x e.1 = true ∧ x e.2 = true)

lemma adj_edgeValue {a b : Fin 10} (x : Fin 10 → Bool)
    (hab : adj a b = true) (ha : x a = true) (hb : x b = true) : edgeValue x = true := by
  simp only [adj, decide_eq_true_eq] at hab
  apply decide_eq_true
  rcases hab with hab | hab
  · exact ⟨(a, b), hab, ha, hb⟩
  · exact ⟨(b, a), hab, hb, ha⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma edgeValue_triple : ∀ a b w : Fin 10,
    edgeValue (fun v => decide (v = a ∨ v = b ∨ v = w)) =
      (adj a b || adj a w || adj b w) := by decide +kernel

lemma filterable_iff (A B : Finset (Fin 10)) (w : Fin 10) :
    filterable A B w = true ↔
      ∀ x : Fin 10 → Bool, product A B x = true → x w = true → edgeValue x = true := by
  constructor
  · intro hf x hx hw
    have hf' := of_decide_eq_true hf
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hx
    obtain ⟨a, ha, hxa⟩ := of_decide_eq_true ha
    obtain ⟨b, hb, hxb⟩ := of_decide_eq_true hb
    rcases hf' a ha b hb with hab | haw | hbw
    · exact adj_edgeValue x hab hxa hxb
    · exact adj_edgeValue x haw hxa hw
    · exact adj_edgeValue x hbw hxb hw
  · intro hf
    apply decide_eq_true
    intro a ha b hb
    have hp : product A B (fun v => decide (v = a ∨ v = b ∨ v = w)) = true := by
      apply Bool.and_eq_true_iff.mpr
      constructor
      · apply decide_eq_true
        exact ⟨a, ha, by simp⟩
      · apply decide_eq_true
        exact ⟨b, hb, by simp⟩
    have he := hf (fun v => decide (v = a ∨ v = b ∨ v = w)) hp (by simp)
    rw [edgeValue_triple] at he
    simpa only [Bool.or_eq_true, or_assoc] using he

lemma accepted_iff (A B : Finset (Fin 10)) (a b : Fin 10) :
    accepted A B (a, b) = true ↔ product A B (fun v => decide (v = a ∨ v = b)) = true := by
  simp only [accepted, product, orValue, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨ha, hb⟩
    constructor
    · rcases ha with ha | ha
      · exact ⟨a, ha, Or.inl rfl⟩
      · exact ⟨b, ha, Or.inr rfl⟩
    · rcases hb with hb | hb
      · exact ⟨a, hb, Or.inl rfl⟩
      · exact ⟨b, hb, Or.inr rfl⟩
  · rintro ⟨⟨u, hu, hua | hub⟩, ⟨v, hv, hva | hvb⟩⟩ <;> subst_vars <;> simp_all

end SingleUnsafe
namespace SafeLower.Source7077

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma conj1_with_lam (h4 : NoFourCycle G) (hL : IsLeastAO G C) :
    ∃ (S : Finset (Fin n)), S.card ≤ (tops G C \ centreless G C).card ∧
      (∀ e ∈ starEdges G C, ∃ v ∈ S, v ∈ e) ∧
      ∀ m ∈ lam G C, 2 ≤ (orIn n C (n + m)).card →
        ∃ t ∈ S, ∀ x ∈ orIn n C (n + m), G.Adj t x := by
  classical
  let pick : ℕ → Finset (Fin n) := fun a =>
    if (side (n := n) C a 0).card ≤ 1 then side (n := n) C a 0 else side (n := n) C a 1
  refine ⟨(tops G C \ centreless G C).biUnion pick, ?_, ?_, ?_⟩
  · have hle : ((tops G C \ centreless G C).biUnion pick).card ≤
        ∑ a ∈ tops G C \ centreless G C, (pick a).card := Finset.card_biUnion_le
    have hsum : ∑ a ∈ tops G C \ centreless G C, (pick a).card ≤
        ∑ _a ∈ tops G C \ centreless G C, 1 := by
      apply Finset.sum_le_sum
      intro a ha
      have hat : a ∈ tops G C := (Finset.mem_sdiff.mp ha).1
      dsimp only [pick]
      split_ifs with h0
      · exact h0
      · rcases biclique_star h4 (side (n := n) C a 0) (side (n := n) C a 1)
          (fun u hu v hv => topAdj hL.1 hat hu hv) with h | h
        · exact (h0 h).elim
        · exact h
    rw [Finset.sum_const, smul_eq_mul, mul_one] at hsum
    exact hle.trans hsum
  · intro e he
    simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product] at he
    obtain ⟨a, ha, ⟨u, v⟩, ⟨hu, hv⟩, rfl⟩ := he
    have hac : a ∉ centreless G C := by
      intro hc
      simp only [centreless, Finset.mem_filter] at hc
      rcases hc.2 with h0 | h1
      · rw [h0] at hu; exact Finset.notMem_empty u hu
      · rw [h1] at hv; exact Finset.notMem_empty v hv
    have has : a ∈ tops G C \ centreless G C := Finset.mem_sdiff.mpr ⟨ha, hac⟩
    dsimp only [pick]
    by_cases h0 : (side (n := n) C a 0).card ≤ 1
    · refine ⟨u, Finset.mem_biUnion.mpr ⟨a, has, ?_⟩, by simp⟩
      rw [ite_eq_left h0]; exact hu
    · refine ⟨v, Finset.mem_biUnion.mpr ⟨a, has, ?_⟩, by simp⟩
      rw [ite_eq_right h0]; exact hv

  · intro m hm htwo
    obtain ⟨_, _, _, a, ha, b, hcard, hr⟩ := Finset.mem_filter.mp hm
    have hsub : orIn n C (n + m) ⊆ side (n := n) C a b :=
      orInTrans (orReaches_reach m _ hr).1
    have hlarge : 2 ≤ (side (n := n) C a b).card := htwo.trans (Finset.card_le_card hsub)
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hcard
    have htother : t ∈ side (n := n) C a (1 - b) := by simp [ht]
    have hac : a ∉ centreless G C := by
      intro hc
      obtain ⟨_, hc⟩ := Finset.mem_filter.mp hc
      rcases hc with h0 | h1
      · fin_cases b <;> simp_all
      · fin_cases b <;> simp_all
    have has : a ∈ tops G C \ centreless G C := Finset.mem_sdiff.mpr ⟨ha, hac⟩
    refine ⟨t, Finset.mem_biUnion.mpr ⟨a, has, ?_⟩, ?_⟩
    · dsimp only [pick]
      fin_cases b
      · have hl : 2 ≤ (side (n := n) C a 0).card := by simpa using hlarge
        have hn : ¬ (side (n := n) C a 0).card ≤ 1 := by omega
        rw [ite_eq_right hn]
        simpa using htother
      · have hy : (side (n := n) C a 0).card ≤ 1 := by
          have hs : side (n := n) C a 0 = {t} := by simpa using ht
          rw [hs]
          simp
        rw [ite_eq_left hy]
        simpa using htother
    · intro x hx
      fin_cases b
      · exact (topAdj hL.1 ha (hsub hx) htother).symm
      · exact topAdj hL.1 ha htother (hsub hx)

end SafeLower.Source7077

namespace SafeLower
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.MetaComplexity.NestedCover Source7077

lemma finite_adj_bridge : ∀ a b : Fin 10, graph.Adj a b ↔ SingleUnsafe.adj a b = true := by
  decide +kernel

lemma finite_edges_bridge : graph.edgeFinset =
    SingleUnsafe.edges.image (fun e => s(e.1, e.2)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma finite_value_bridge : ∀ x : Fin 10 → Bool,
    graphFun graph ∅ x = SingleUnsafe.edgeValue x := by
  decide +kernel

lemma first_junk_product (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) {g : Nat} (hj : junk graph C = {g}) (x : Fin 10 → Bool) :
    gateVal 10 C g x = true ↔
      SingleUnsafe.product (side (n := 10) C g 0) (side C g 1) x = true := by
  have hg : g ∈ junk graph C := by simp [hj]
  obtain ⟨hgl, hgop, _⟩ := junkData hg
  rw [andValBoth hl.1 hgl hgop x]
  simp only [SingleUnsafe.product, SingleUnsafe.orValue, Bool.and_eq_true, decide_eq_true_eq]
  rw [first_junk_operand C hl ht hj 0 x, first_junk_operand C hl ht hj 1 x]

lemma two_uncovered_exclusion (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) (hu : (Ustar graph C).card = 2) (hs : C.size ≤ 19) : False := by
  obtain ⟨htops, hc, hjcard, hr⟩ := two_uncovered_parameters C hl ht hu hs
  obtain ⟨g, hj⟩ := Finset.card_eq_one.mp hjcard
  have hU : (Ustar graph C).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨K, hKcard, hKcover, hKlam⟩ := conj1_with_lam graph_no_four_cycle hl
  have descriptor (b : Fin 2) : ∃ i : Fin 50,
      SingleUnsafe.supports i = side (n := 10) C g b ∧ SingleUnsafe.centers i ⊆ K := by
    by_cases hsmall : (side (n := 10) C g b).card ≤ 1
    · have hnon : (side (n := 10) C g b).Nonempty :=
        first_junk_cone_has_input C hl ht hj b (opnd C g b) Relation.ReflTransGen.refl
      have hpos := Finset.card_pos.mpr hnon
      obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (show (side (n := 10) C g b).card = 1 by omega)
      obtain ⟨i, hi, hcenter⟩ := SingleUnsafe.raw_descriptor v
      exact ⟨i, hi.trans hv.symm, by simp [hcenter]⟩
    · have hbig : 2 ≤ (side (n := 10) C g b).card := by omega
      obtain ⟨m, hmwire, hmlam, _⟩ := large_first_junk_side_lambda C hl ht hU hc hj hr b hbig
      have hside : side (n := 10) C g b = orIn 10 C (10 + m) := by simp only [side, hmwire]
      obtain ⟨v, hvK, hvadj⟩ := hKlam m hmlam (by simpa only [← hside] using hbig)
      obtain ⟨i, hi, hcenter⟩ := SingleUnsafe.neighbor_descriptor v (side (n := 10) C g b) hbig
        (fun a ha => (finite_adj_bridge v a).mp (hvadj a (by simpa only [← hside] using ha)))
      exact ⟨i, hi, by simpa only [hcenter, Finset.singleton_subset_iff] using hvK⟩
  obtain ⟨i, hi, hiK⟩ := descriptor 0
  obtain ⟨j, hjS, hjK⟩ := descriptor 1
  have hanti : ¬ SingleUnsafe.supports i ⊆ SingleUnsafe.supports j := by
    rw [hi, hjS]
    exact first_junk_sides_incomparable C hl ht hj 0
  have hanti' : ¬ SingleUnsafe.supports j ⊆ SingleUnsafe.supports i := by
    rw [hi, hjS]
    simpa using first_junk_sides_incomparable C hl ht hj 1
  have helig := SingleUnsafe.descriptor_cover_bound i j K hiK hjK hanti hanti'
  rw [hi, hjS] at helig
  let A := side (n := 10) C g 0
  let B := side (n := 10) C g 1
  have miss_subset : uncovered K ⊆
      (SingleUnsafe.eligible A B K).image (fun e => s(e.1, e.2)) := by
    intro e he
    obtain ⟨hedge, hdisj⟩ := Finset.mem_filter.mp he
    rw [finite_edges_bridge] at hedge
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hedge
    have hp1 : p.1 ∉ K := fun h => Finset.disjoint_left.mp hdisj (by simp) h
    have hp2 : p.2 ∉ K := fun h => Finset.disjoint_left.mp hdisj (by simp) h
    have heU : s(p.1, p.2) ∈ Ustar graph C := by
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, ?_⟩
      · rw [finite_edges_bridge]
        exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
      · intro hstar
        obtain ⟨v, hvK, hve⟩ := hKcover _ hstar
        exact Finset.disjoint_left.mp hdisj (by simpa using hve) hvK
    obtain ⟨w, hw, hwe, hgv⟩ := one_junk_filtered_edge C hl ht hj heU
    have haccept : SingleUnsafe.accepted A B p = true := by
      rw [SingleUnsafe.accepted_iff]
      exact (first_junk_product C hl ht hj _).mp hgv
    have hfilter : SingleUnsafe.filterable A B w = true := by
      apply (SingleUnsafe.filterable_iff A B w).mpr
      intro x hprod hxw
      rw [← finite_value_bridge x]
      exact (Finset.mem_filter.mp hw).2 x ((first_junk_product C hl ht hj x).mpr hprod) hxw
    have hfend : SingleUnsafe.filterable A B p.1 = true ∨ SingleUnsafe.filterable A B p.2 = true := by
      rcases hwe with rfl | rfl
      · exact Or.inl hfilter
      · exact Or.inr hfilter
    exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, haccept, hfend, hp1, hp2⟩, rfl⟩
  have hmcard : (uncovered K).card ≤ 1 :=
    (Finset.card_le_card miss_subset).trans (Finset.card_image_le.trans helig)
  have hmiss := five_vertices_miss_two K (by omega)
  omega

lemma two_uncovered_lower (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) (hu : (Ustar graph C).card ≤ 2) : 20 ≤ C.size := by
  by_contra hsmall
  have hs : C.size ≤ 19 := by omega
  by_cases hlow : (Ustar graph C).card ≤ 1
  · have := one_uncovered_lower C hl ht hlow
    omega
  · exact two_uncovered_exclusion C hl ht (by omega) hs

end SafeLower


namespace LowOverheadFinite
open PEqualNP.MetaComplexity.NestedCover

def edge : Fin 15 → Fin 10 × Fin 10 := ![(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (4,9), (5,7), (7,9), (9,6), (6,8), (8,5)]
def edgeSym (i : Fin 15) : Sym2 (Fin 10) := s((edge i).1, (edge i).2)
abbrev graph : SimpleGraph (Fin 10) := PEqualNP.EdgeOwnership.edgeGraph 10 [(0,1), (1,2), (2,3), (3,4), (4,0), (0,5), (1,6), (2,7), (3,8), (4,9), (5,7), (7,9), (9,6), (6,8), (8,5)]
def edgeSet (S : Finset (Fin 15)) := S.image edgeSym
abbrev remaining (S : Finset (Fin 15)) := graph.deleteEdges (edgeSet S)
def neighbors (S : Finset (Fin 15)) (v : Fin 10) := Finset.univ.filter ((remaining S).Adj v)
abbrev covers (S : Finset (Fin 15)) (Q : Finset (Fin 10)) : Prop :=
  ∀ i ∈ S, (edge i).1 ∈ Q ∨ (edge i).2 ∈ Q

def independentInputs : Finset (Finset (Fin 10)) := {{1,4,5}, {0,2,6}, {3,5,6}, {2,4,5,6}, {1,3,7}, {0,3,6,7}, {4,6,7}, {2,4,8}, {0,7,8}, {1,4,7,8}, {0,3,9}, {2,5,9}, {1,3,5,9}, {1,8,9}, {0,2,8,9}}
abbrev good (S : Finset (Fin 15)) (w : Fin 10) : Prop :=
  ∀ I ∈ independentInputs, w ∈ I →
    (∃ v : Fin 10, v ∉ I ∧ covers S {v}) ∨
      ∃ t : Fin 10, covers S (neighbors S t \ I)

abbrev necessary (S : Finset (Fin 15)) : Prop :=
  ∃ z : Fin 10, covers S ((neighbors S z).filter (good S))


lemma edge_injective : Function.Injective edgeSym := by decide +kernel
lemma edges_cover : Finset.univ.image edgeSym = graph.edgeFinset := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma inputs_false : ∀ I ∈ independentInputs,
    graphFun graph ∅ (fun v => decide (v ∈ I)) = false := by decide +kernel




def baseNeighbors : Fin 10 → Finset (Fin 10) := ![{1,4,5}, {0,2,6}, {1,3,7}, {2,4,8}, {0,3,9}, {0,7,8}, {1,8,9}, {2,5,9}, {3,5,6}, {4,6,7}]
def edgeIndex : Fin 10 → Fin 10 → Fin 15 := ![![0,0,0,0,4,5,0,0,0,0],
![0,0,1,0,0,0,6,0,0,0],
![0,1,0,2,0,0,0,7,0,0],
![0,0,2,0,3,0,0,0,8,0],
![4,0,0,3,0,0,0,0,0,9],
![5,0,0,0,0,0,0,10,14,0],
![0,6,0,0,0,0,0,0,13,12],
![0,0,7,0,0,10,0,0,0,11],
![0,0,0,8,0,14,13,0,0,0],
![0,0,0,0,9,0,12,11,0,0]]

lemma baseNeighbors_iff : ∀ a b : Fin 10, b ∈ baseNeighbors a ↔ graph.Adj a b := by decide +kernel
lemma edgeIndex_spec : ∀ a b : Fin 10, graph.Adj a b → edgeSym (edgeIndex a b) = s(a,b) := by decide +kernel

def fastNeighbors (S : Finset (Fin 15)) (v : Fin 10) :=
  (baseNeighbors v).filter (fun w => edgeIndex v w ∉ S)

lemma neighbors_fast (S : Finset (Fin 15)) (v : Fin 10) : neighbors S v = fastNeighbors S v := by
  apply Finset.ext
  intro w
  change w ∈ Finset.univ.filter ((remaining S).Adj v) ↔
    w ∈ (baseNeighbors v).filter (fun q => edgeIndex v q ∉ S)
  rw [Finset.mem_filter, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  rw [baseNeighbors_iff]
  simp only [remaining, SimpleGraph.deleteEdges_adj]
  constructor
  · rintro ⟨ha, hn⟩
    refine ⟨ha, ?_⟩
    intro hmem
    apply hn
    exact Finset.mem_image.mpr ⟨edgeIndex v w, hmem, edgeIndex_spec v w ha⟩
  · rintro ⟨ha, hn⟩
    refine ⟨ha, ?_⟩
    intro hmem
    obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp hmem
    have he : i = edgeIndex v w := edge_injective (heq.trans (edgeIndex_spec v w ha).symm)
    exact hn (he ▸ hi)

abbrev fastGood (S : Finset (Fin 15)) (w : Fin 10) : Prop :=
  ∀ I ∈ independentInputs, w ∈ I →
    (∃ v : Fin 10, v ∉ I ∧ covers S {v}) ∨
      ∃ t : Fin 10, covers S (fastNeighbors S t \ I)

abbrev fastNecessary (S : Finset (Fin 15)) : Prop :=
  ∃ z : Fin 10, covers S ((fastNeighbors S z).filter (fastGood S))

lemma good_fast (S : Finset (Fin 15)) (w : Fin 10) : good S w ↔ fastGood S w := by
  simp only [good, fastGood, neighbors_fast]

lemma necessary_fast (S : Finset (Fin 15)) : necessary S ↔ fastNecessary S := by
  simp only [necessary, fastNecessary, neighbors_fast, good_fast]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_first_0 : ∀ b c : Fin 15, (0 : Fin 15) < b → b < c →
    ¬ fastNecessary {0,b,c} := by decide +kernel



set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_first_1 : ∀ b c : Fin 15, (1 : Fin 15) < b → b < c →
    ¬ fastNecessary {1,b,c} := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_first_2 : ∀ b c : Fin 15, (2 : Fin 15) < b → b < c →
    ¬ fastNecessary {2,b,c} := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_first_3 : ∀ b c : Fin 15, (3 : Fin 15) < b → b < c →
    ¬ fastNecessary {3,b,c} := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_first_4 : ∀ b c : Fin 15, (4 : Fin 15) < b → b < c →
    ¬ fastNecessary {4,b,c} := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_first_5 : ∀ b c : Fin 15, (5 : Fin 15) < b → b < c →
    ¬ fastNecessary {5,b,c} := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_first_6 : ∀ b c : Fin 15, (6 : Fin 15) < b → b < c →
    ¬ fastNecessary {6,b,c} := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_first_7 : ∀ b c : Fin 15, (7 : Fin 15) < b → b < c →
    ¬ fastNecessary {7,b,c} := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_first_8 : ∀ b c : Fin 15, (8 : Fin 15) < b → b < c →
    ¬ fastNecessary {8,b,c} := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_first_9 : ∀ b c : Fin 15, (9 : Fin 15) < b → b < c →
    ¬ fastNecessary {9,b,c} := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_first_10 : ∀ b c : Fin 15, (10 : Fin 15) < b → b < c →
    ¬ fastNecessary {10,b,c} := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_first_11 : ∀ b c : Fin 15, (11 : Fin 15) < b → b < c →
    ¬ fastNecessary {11,b,c} := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_first_12 : ∀ b c : Fin 15, (12 : Fin 15) < b → b < c →
    ¬ fastNecessary {12,b,c} := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_first_13 : ∀ b c : Fin 15, (13 : Fin 15) < b → b < c →
    ¬ fastNecessary {13,b,c} := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma fast_first_14 : ∀ b c : Fin 15, (14 : Fin 15) < b → b < c →
    ¬ fastNecessary {14,b,c} := by decide +kernel

lemma ordered_cases (P : Finset (Fin 15) → Prop)
    (h0 : ∀ b c : Fin 15, (0 : Fin 15) < b → b < c → ¬ P {0,b,c})
    (h1 : ∀ b c : Fin 15, (1 : Fin 15) < b → b < c → ¬ P {1,b,c})
    (h2 : ∀ b c : Fin 15, (2 : Fin 15) < b → b < c → ¬ P {2,b,c})
    (h3 : ∀ b c : Fin 15, (3 : Fin 15) < b → b < c → ¬ P {3,b,c})
    (h4 : ∀ b c : Fin 15, (4 : Fin 15) < b → b < c → ¬ P {4,b,c})
    (h5 : ∀ b c : Fin 15, (5 : Fin 15) < b → b < c → ¬ P {5,b,c})
    (h6 : ∀ b c : Fin 15, (6 : Fin 15) < b → b < c → ¬ P {6,b,c})
    (h7 : ∀ b c : Fin 15, (7 : Fin 15) < b → b < c → ¬ P {7,b,c})
    (h8 : ∀ b c : Fin 15, (8 : Fin 15) < b → b < c → ¬ P {8,b,c})
    (h9 : ∀ b c : Fin 15, (9 : Fin 15) < b → b < c → ¬ P {9,b,c})
    (h10 : ∀ b c : Fin 15, (10 : Fin 15) < b → b < c → ¬ P {10,b,c})
    (h11 : ∀ b c : Fin 15, (11 : Fin 15) < b → b < c → ¬ P {11,b,c})
    (h12 : ∀ b c : Fin 15, (12 : Fin 15) < b → b < c → ¬ P {12,b,c})
    (h13 : ∀ b c : Fin 15, (13 : Fin 15) < b → b < c → ¬ P {13,b,c})
    (h14 : ∀ b c : Fin 15, (14 : Fin 15) < b → b < c → ¬ P {14,b,c})
    : ∀ a b c : Fin 15, a < b → b < c → ¬ P {a,b,c} := by
  intro a
  fin_cases a
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14

lemma triple_of_ordered (P : Finset (Fin 15) → Prop)
    (hordered : ∀ a b c : Fin 15, a < b → b < c → ¬ P {a,b,c}) :
    ∀ S : Finset (Fin 15), S.card = 3 → ¬ P S := by
  intro S hcard
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hcard
  by_cases h1 : a < b
  · by_cases h2 : b < c
    · exact hordered a b c h1 h2
    · by_cases h3 : a < c
      · have hcb : c < b := by omega
        have he : ({a,b,c} : Finset (Fin 15)) = {a,c,b} := by
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [he]
        exact hordered a c b h3 hcb
      · have hca : c < a := by omega
        have he : ({a,b,c} : Finset (Fin 15)) = {c,a,b} := by
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [he]
        exact hordered c a b hca h1
  · have hba : b < a := by omega
    by_cases h2 : a < c
    · have he : ({a,b,c} : Finset (Fin 15)) = {b,a,c} := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [he]
      exact hordered b a c hba h2
    · by_cases h3 : b < c
      · have hca : c < a := by omega
        have he : ({a,b,c} : Finset (Fin 15)) = {b,c,a} := by
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [he]
        exact hordered b c a h3 hca
      · have hcb : c < b := by omega
        have he : ({a,b,c} : Finset (Fin 15)) = {c,b,a} := by
          ext x
          simp only [Finset.mem_insert, Finset.mem_singleton]
          tauto
        rw [he]
        exact hordered c b a hcb hba


lemma no_triple : ∀ S : Finset (Fin 15), S.card = 3 → ¬ necessary S := by
  have hordered := ordered_cases fastNecessary
    fast_first_0 fast_first_1 fast_first_2 fast_first_3 fast_first_4 fast_first_5 fast_first_6 fast_first_7 fast_first_8 fast_first_9 fast_first_10 fast_first_11 fast_first_12 fast_first_13 fast_first_14
  intro S hcard hn
  exact triple_of_ordered fastNecessary hordered S hcard ((necessary_fast S).mp hn)

end LowOverheadFinite

namespace LowOverheadFinite
open PEqualNP.MetaComplexity.NestedCover

def graphCondition (U : Finset (Sym2 (Fin 10))) : Prop :=
  ∃ z : Fin 10, ∀ u v : Fin 10, s(u,v) ∈ U →
    ∃ w : Fin 10, (w = u ∨ w = v) ∧ (graph.deleteEdges U).Adj z w ∧
      ∀ x : Fin 10 → Bool, x w = true → graphFun graph ∅ x = false →
        ∃ Q : Finset (Fin 10),
          (Q.card ≤ 1 ∨ ∃ t : Fin 10, ∀ q ∈ Q, (graph.deleteEdges U).Adj q t) ∧
          (∀ a b : Fin 10, s(a,b) ∈ U → a ∈ Q ∨ b ∈ Q) ∧
          ∀ q ∈ Q, x q = false

lemma remaining_adj {S : Finset (Fin 15)} {U : Finset (Sym2 (Fin 10))}
    (hsub : edgeSet S ⊆ U) {a b : Fin 10}
    (h : (graph.deleteEdges U).Adj a b) : (remaining S).Adj a b := by
  simp only [remaining, SimpleGraph.deleteEdges_adj, Finset.mem_coe] at h ⊢
  exact ⟨h.1, fun hm => h.2 (hsub hm)⟩

lemma graphCondition_restrict {U : Finset (Sym2 (Fin 10))}
    (hc : graphCondition U) {S : Finset (Fin 15)} (hS : S.Nonempty)
    (hsub : edgeSet S ⊆ U) : necessary S := by
  obtain ⟨z, hz⟩ := hc
  refine ⟨z, ?_⟩
  intro i hi
  have hei : edgeSym i ∈ U := hsub (Finset.mem_image.mpr ⟨i,hi,rfl⟩)
  obtain ⟨w, hew, hwz, hproperty⟩ := hz (edge i).1 (edge i).2 hei
  have hneighbor : w ∈ neighbors S z := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, remaining_adj hsub hwz⟩
  have hgood : good S w := by
    intro I hI hwI
    have hxw : (fun v : Fin 10 => decide (v ∈ I)) w = true := by simpa
    obtain ⟨Q, hshape, hcover, hdisjoint⟩ := hproperty (fun v => decide (v ∈ I)) hxw (inputs_false I hI)
    have hQI : ∀ q ∈ Q, q ∉ I := by
      intro q hq
      have hfalse := hdisjoint q hq
      simpa only [decide_eq_false_iff_not] using hfalse
    have hcoverS : covers S Q := by
      intro j hj
      exact hcover (edge j).1 (edge j).2 (hsub (Finset.mem_image.mpr ⟨j,hj,rfl⟩))
    rcases hshape with hcard | ⟨t, ht⟩
    · obtain ⟨j,hj⟩ := hS
      have hQnon : Q.Nonempty := by
        rcases hcoverS j hj with h | h
        · exact ⟨_,h⟩
        · exact ⟨_,h⟩
      have hpos := Finset.card_pos.mpr hQnon
      obtain ⟨q, hQ⟩ := Finset.card_eq_one.mp (show Q.card = 1 by omega)
      exact Or.inl ⟨q, hQI q (by simp [hQ]), by simpa only [hQ] using hcoverS⟩
    · refine Or.inr ⟨t, ?_⟩
      intro j hj
      have hmem : ∀ q ∈ Q, q ∈ neighbors S t \ I := by
        intro q hq
        apply Finset.mem_sdiff.mpr
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, (remaining_adj hsub (ht q hq)).symm⟩, hQI q hq⟩
      exact (hcoverS j hj).imp (hmem _) (hmem _)
  have hw : w ∈ (neighbors S z).filter (good S) := Finset.mem_filter.mpr ⟨hneighbor,hgood⟩
  rcases hew with rfl | rfl
  · exact Or.inl hw
  · exact Or.inr hw

lemma condition_card_le_two
    (finiteNo : ∀ S : Finset (Fin 15), S.card = 3 → ¬ necessary S)
    {U : Finset (Sym2 (Fin 10))} (hU : U ⊆ graph.edgeFinset)
    (hc : graphCondition U) : U.card ≤ 2 := by
  let indices : Finset (Fin 15) := Finset.univ.filter (fun i => edgeSym i ∈ U)
  have himage : indices.image edgeSym = U := by
    ext e
    constructor
    · rintro he
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
      exact (Finset.mem_filter.mp hi).2
    · intro he
      have hgraph := hU he
      rw [← edges_cover] at hgraph
      obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp hgraph
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, heq ▸ he⟩, heq⟩
  have hcard : indices.card = U.card := by
    calc
      indices.card = (indices.image edgeSym).card := (Finset.card_image_of_injective _ edge_injective).symm
      _ = U.card := congrArg Finset.card himage
  by_contra hnot
  have hthree : 3 ≤ indices.card := by omega
  obtain ⟨S,hsub,hScard⟩ := Finset.exists_subset_card_eq hthree
  have hSnon : S.Nonempty := Finset.card_pos.mp (by omega)
  have hSU : edgeSet S ⊆ U := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp (hsub hi)).2
  exact finiteNo S hScard (graphCondition_restrict hc hSnon hSU)

end LowOverheadFinite

namespace LowOverheadFinite
lemma graph_condition_small {U : Finset (Sym2 (Fin 10))}
    (hU : U ⊆ graph.edgeFinset) (hc : graphCondition U) : U.card ≤ 2 :=
  condition_card_le_two no_triple hU hc
end LowOverheadFinite

namespace LowOverhead.Source5869

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Circuit evaluation and OR reachability follow L_meta_1490 and L_meta_4901.
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
lemma junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩
lemma binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
lemma opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]
lemma opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)
lemma andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2
lemma andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩
lemma operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1
lemma operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
    (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
  have hlen := (orReaches_reach h _ hr).2
  have hnb : ¬ BelowF G C h :=
    fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
  have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
    by_contra hne
    apply hnb
    intro x hx
    by_contra hf
    exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩
lemma inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
    (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
  rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
  · exact ⟨0, by simp [opnd, hpq]⟩
  · have e : z = q := List.mem_singleton.mp hq
    exact ⟨1, by simpa [opnd, hpq] using e⟩
lemma sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
    (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
    val C (List.ofFn x) (opnd C a b) = true :=
  reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
  (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

lemma topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  obtain ⟨hl, ho, hb⟩ := topData ha
  exact (graphFun_pair G u v).mp
    (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

lemma acceptedTop (hL : IsLeastAO G C) {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
  have hout (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hL.2.1 x
  obtain ⟨a, hl, ho, hr, hv⟩ :=
    edge_trace G (graphFun G ∅) (fun k l => (graphFun_pair G k l).mp)
      hout u v ((graphFun_pair G u v).mpr hadj)
  have hand := (hL.1.1 _ (gateAt_mem hl)).resolve_right ho
  have hb : BelowF G C a := fun x hx =>
    below_of_reach (graphFun G ∅) hout a hr x (gateVal_eq_val n C a x ▸ hx)
  refine ⟨a, ?_, hv⟩
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    And.intro hl (And.intro hand hb)

lemma operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
    {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
    (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
        gateVal n C j (pairInput u v) = true := by
  rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
  · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
  · have hr' := reach_orReaches hr j rfl hj
    exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
      ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩


lemma andRawEmpty {j : ℕ} (hj : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with he | ⟨k, _, hr, ho, _⟩
  · have := v.isLt
    omega
  · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨hof, _⟩⟩
    · subst k
      rw [hj] at ho
      cases ho
    · rw [hj] at hof
      cases hof

lemma lastOrBefore {j w : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w (n + j)) :
    w = n + j ∨ ∃ m, m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
      n + j ∈ (gateAt C m).inputs ∧ n + j < n + m ∧
      Relation.ReflTransGen (OrStep n C) w (n + m) := by
  rcases Relation.ReflTransGen.cases_tail hr with eq | ⟨z, hz, hstep⟩
  · exact .inl eq.symm
  · obtain ⟨m, hm, rfl, ho, hi, hb⟩ := hstep
    exact .inr ⟨m, hm, ho, hi, hb, hz⟩

lemma lastOrOutside {j m : ℕ} (hAO : IsAO2 n C) (hj : j ∈ junk G C)
    (hm : m < C.gates.length) (ho : (gateAt C m).op = GateOp.or)
    (hi : n + j ∈ (gateAt C m).inputs) (hb : n + j < n + m) :
    m ∈ orN G C \ lam G C := by
  obtain ⟨_, hjop, x, hjx, hx⟩ := junkData hj
  have hNotBelow : ¬ BelowF G C m := by
    intro h
    have hvm : gateVal n C m x = true := (val_or (n := n) (by simp) hm ho).mpr
      ⟨n + j, hi, hb, hjx⟩
    exact Bool.noConfusion (hx.symm.trans (h x hvm))
  apply Finset.mem_sdiff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hm (And.intro ho hNotBelow)
  · intro hl
    obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
    obtain ⟨b, be⟩ := inputsAsOpnd hAO hm hi
    have hnonempty : (orIn n C (opnd C m b)).Nonempty := by
      fin_cases b
      · exact h0
      · exact h1
    rw [← be, andRawEmpty (n := n) hjop] at hnonempty
    exact Finset.not_nonempty_empty hnonempty

lemma residualTrace (hL : IsLeastAO G C) (hT : TopForm G C) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ j ∈ junk G C,
      gateVal n C a (pairInput u v) = true ∧ OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true := by
  obtain ⟨adj, miss⟩ := Finset.mem_sdiff.mp he
  have adj' : G.Adj u v := SimpleGraph.mem_edgeFinset.mp adj
  obtain ⟨a, ha, hv⟩ := acceptedTop hL adj'
  obtain ⟨hl, ho, _⟩ := topData ha
  have h := (andValOperands hL.1 hl ho _).mp hv
  rcases operandSupport hL.1 hT hl ho (b := 0) (h 0) with ⟨x, hx, hex⟩ | ⟨j, hj, hr, hjv⟩
  · rcases operandSupport hL.1 hT hl ho (b := 1) (h 1) with ⟨y, hy, hey⟩ | ⟨j, hj, hr, hjv⟩
    · have hxy : x ≠ y := (topAdj hL.1 ha hx hy).ne
      apply (miss ?_).elim
      unfold starEdges
      refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
        ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, ?_⟩⟩
      rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hxy rfl).elim
    · exact ⟨a, ha, 1, j, hj, hv, hr, hjv⟩
  · exact ⟨a, ha, 0, j, hj, hv, hr, hjv⟩


lemma opposite (b c : Fin 2) : c = b ∨ c = 1 - b := by
  revert b c
  decide

lemma topSides (empty : centreless G C = ∅) {a : ℕ} (ha : a ∈ tops G C)
    (b : Fin 2) : (side (n := n) C a b).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  have hc : a ∈ centreless G C := by
    apply Finset.mem_filter.mpr
    refine ⟨ha, ?_⟩
    fin_cases b
    · exact Or.inl he
    · exact Or.inr he
  rw [empty] at hc
  exact Finset.notMem_empty _ hc

lemma orData {m : ℕ} (hm : m ∈ orN G C \ lam G C) :
    m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G C m := by
  simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    (Finset.mem_sdiff.mp hm).1

lemma emptyInputOutside (ao : IsAO2 n C) {j m : ℕ}
    (dirty : ¬ BelowF G C j) (empty : orIn n C (n + j) = ∅)
    (hm : m < C.gates.length) (hop : (gateAt C m).op = GateOp.or)
    (hin : n + j ∈ (gateAt C m).inputs) :
    m ∈ orN G C \ lam G C := by
  have hbad : ¬ BelowF G C m := by
    intro hb
    apply dirty
    intro x hx
    exact hb x ((val_or (n := n) (by simp) hm hop).mpr
      ⟨_, hin, ao.2.1 _ hm _ hin, hx⟩)
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hm (And.intro hop hbad)
  · intro hl
    obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
    obtain ⟨b, hb⟩ := inputsAsOpnd ao hm hin
    have hne : (orIn n C (opnd C m b)).Nonempty := by
      fin_cases b
      · exact h0
      · exact h1
    rw [← hb, empty] at hne
    exact Finset.not_nonempty_empty hne

lemma residualPath (ao : IsAO2 n C) (empty : centreless G C = ∅)
    {a j : ℕ} {b : Fin 2} (ha : a ∈ tops G C) (hj : j ∈ junk G C)
    (path : OrReaches n C (opnd C a b) j) :
    ∃ m ∈ orN G C \ lam G C, n + j ∈ (gateAt C m).inputs ∧
      Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m) := by
  rcases lastOrBefore (orReaches_reach j _ path).1 with he | ⟨m, hm, hop, hin, hlt, hp⟩
  · have hne := topSides empty ha b
    change (orIn n C (opnd C a b)).Nonempty at hne
    rw [he, andRawEmpty (junkData hj).2.1] at hne
    exact (Finset.not_nonempty_empty hne).elim
  · exact ⟨m, lastOrOutside ao hj hm hop hin hlt, hin, hp⟩

lemma mixingRaw (ao : IsAO2 n C) (empty : centreless G C = ∅) {m a : ℕ} {b : Fin 2}
    (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
    (ha : a ∈ tops G C) (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m)) :
    (orIn n C (n + m)).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hz
  rcases lastOrBefore path with he | ⟨k, hk, hop, hin, hlt, _⟩
  · have hne := topSides empty ha b
    change (orIn n C (opnd C a b)).Nonempty at hne
    rw [he, hz] at hne
    exact Finset.not_nonempty_empty hne
  · have hk' := emptyInputOutside ao (orData hm).2.2 hz hk hop hin
    rw [only, Finset.mem_singleton] at hk'
    omega

lemma singleJunkInput (ao : IsAO2 n C) {m j k : ℕ}
    (hm : m ∈ orN G C \ lam G C) (hne : (orIn n C (n + m)).Nonempty)
    (hj : j ∈ junk G C) (hk : k ∈ junk G C)
    (hjin : n + j ∈ (gateAt C m).inputs) (hkin : n + k ∈ (gateAt C m).inputs) :
    j = k := by
  by_contra hjk
  obtain ⟨p, q, hpq⟩ := binaryInputs ao (orData hm).1
  have hinputs : ∀ w ∈ (gateAt C m).inputs, w = n + j ∨ w = n + k := by
    intro w hw
    simp only [hpq, List.mem_cons, List.not_mem_nil, or_false] at hjin hkin hw
    omega
  obtain ⟨t, ht⟩ := hne
  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach t ht) with he | ⟨w, hs, hrest⟩
  · have := t.isLt
    omega
  · obtain ⟨l, _, he, _, hin, _⟩ := hs
    have hl : l = m := by omega
    subst l
    have ht' := reach_mem_orIn t hrest
    rcases hinputs w hin with rfl | rfl
    · rw [andRawEmpty (junkData hj).2.1] at ht'
      exact Finset.notMem_empty _ ht'
    · rw [andRawEmpty (junkData hk).2.1] at ht'
      exact Finset.notMem_empty _ ht'

lemma cleanAdj (ao : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    {t w : Fin n} (ht : t ∈ side C a b) (hw : w ∈ side C a (1 - b)) :
    (G.deleteEdges ↑(Ustar G C)).Adj t w := by
  have cross {u v : Fin n} (hu : u ∈ side C a 0) (hv : v ∈ side C a 1) :
      (G.deleteEdges ↑(Ustar G C)).Adj u v := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨topAdj ao ha hu hv, ?_⟩
    intro he
    apply (Finset.mem_sdiff.mp (show s(u, v) ∈ Ustar G C from he)).2
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
      ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩⟩
  fin_cases b
  · exact cross ht hw
  · exact (cross hw ht).symm

lemma firingTop (ao : IsAO2 n C) {a m : ℕ} {b : Fin 2} {w : Fin n}
    (ha : a ∈ tops G C)
    (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m))
    (hw : w ∈ side C a (1 - b)) (x : Fin n → Bool)
    (hmx : gateVal n C m x = true) (hwx : x w = true) :
    graphFun G ∅ x = true := by
  obtain ⟨haLen, haOp, haBelow⟩ := topData ha
  apply haBelow x ((andValOperands ao haLen haOp x).mpr ?_)
  intro c
  rcases opposite b c with rfl | rfl
  · exact orStep_up (n := n) (by simp) path hmx
  · exact sideVal hw hwx

lemma oppositeEndpoint (least : IsLeastAO G C) (top : TopForm G C)
    (empty : centreless G C = ∅) {m a : ℕ} {b : Fin 2} {u v : Fin n}
    (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
    (ha : a ∈ tops G C) (hv : gateVal n C a (pairInput u v) = true)
    (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m)) :
    ∃ w ∈ side C a (1 - b), w = u ∨ w = v := by
  obtain ⟨al, aop, ab⟩ := topData ha
  have hv' := (andValOperands least.1 al aop _).mp hv (1 - b)
  rcases operandSupport least.1 top al aop hv' with h | ⟨j, hj, hr, _⟩
  · exact h
  · obtain ⟨k, hk, _, hp⟩ := residualPath least.1 empty ha hj hr
    rw [only, Finset.mem_singleton] at hk
    subst k
    exfalso
    apply (orData hm).2.2
    intro x hx
    apply ab x ((andValOperands least.1 al aop x).mpr ?_)
    intro c
    rcases opposite b c with rfl | rfl
    · exact orStep_up (n := n) (by simp) path hx
    · exact orStep_up (n := n) (by simp) hp hx

lemma rawCoverShape (ao : IsAO2 n C) {m w : ℕ}
    (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
    (hw : w < n + m) :
    (orIn n C w).card ≤ 1 ∨
      ∃ z : Fin n, ∀ t ∈ orIn n C w, (G.deleteEdges ↑(Ustar G C)).Adj t z := by
  by_cases hcard : (orIn n C w).card ≤ 1
  · exact Or.inl hcard
  have hne : (orIn n C w).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨u, hu⟩ := hne
  by_cases hi : w < n
  · exfalso
    apply hcard
    apply Finset.card_le_one.mpr
    intro t ht v hv
    have eq (z : Fin n) (hz : z ∈ orIn n C w) : (z : ℕ) = w := by
      rcases Relation.ReflTransGen.cases_head (mem_orIn_reach z hz) with he | ⟨_, hs, _⟩
      · exact he.symm
      · obtain ⟨k, _, he, _, _, _⟩ := hs
        omega
    exact Fin.ext ((eq t ht).trans (eq v hv).symm)
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  have hkm : k < m := by omega
  have hkl := hkm.trans (orData hm).1
  have hko : (gateAt C k).op = GateOp.or := by
    rcases ao.1 _ (gateAt_mem hkl) with h | h
    · rw [andRawEmpty h] at hu
      exact (Finset.notMem_empty _ hu).elim
    · exact h
  have hbelow : ¬ BelowF G C k := by
    intro hb
    have hv := reach_var_val (pairInput u u) _ u (mem_orIn_reach u hu) (pairInput_left u u)
    exact G.irrefl ((graphFun_pair G u u).mp (hb _ hv))
  have hkN : k ∈ orN G C := by
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hkl (And.intro hko hbelow)
  have hkL : k ∈ lam G C := by
    by_contra hn
    have hk := Finset.mem_sdiff.mpr ⟨hkN, hn⟩
    rw [only, Finset.mem_singleton] at hk
    omega
  obtain ⟨_, _, _, a, ha, b, hone, hr⟩ := Finset.mem_filter.mp hkL
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (side (n := n) C a (1 - b)).card)
  exact Or.inr ⟨z, fun t ht => cleanAdj ao ha b
    (reach_mem_orIn t ((orReaches_reach k _ hr).1.trans (mem_orIn_reach t ht))) hz⟩

lemma falseJunkCover (ao : IsAO2 n C) (top : TopForm G C) {m : ℕ}
    (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
    (x : Fin n → Bool) :
    ∀ j < m, j ∈ junk G C →
      (∀ u v : Fin n, s(u, v) ∈ Ustar G C → gateVal n C j (pairInput u v) = true) →
      gateVal n C j x = false →
      ∃ S : Finset (Fin n), (S.card ≤ 1 ∨
        ∃ z : Fin n, ∀ t ∈ S, (G.deleteEdges ↑(Ustar G C)).Adj t z) ∧
        (∀ u v : Fin n, s(u, v) ∈ Ustar G C → u ∈ S ∨ v ∈ S) ∧
        ∀ t ∈ S, x t = false := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hjm hj fires hx
    obtain ⟨jl, jo, _⟩ := junkData hj
    have hfalse : ∃ b : Fin 2, val C (List.ofFn x) (opnd C j b) = false := by
      by_contra hn
      have hv := (andValOperands ao jl jo x).mpr
        (fun b => by
          cases hval : val C (List.ofFn x) (opnd C j b) with
          | true => rfl
          | false => exact (hn ⟨b, hval⟩).elim)
      exact Bool.false_ne_true (hx.symm.trans hv)
    obtain ⟨b, hb⟩ := hfalse
    have firesOp (u v : Fin n) (he : s(u, v) ∈ Ustar G C) :
        val C (List.ofFn (pairInput u v)) (opnd C j b) = true :=
      (andValOperands ao jl jo _).mp (fires u v he) b
    have direct (k : ℕ) (hk : k ∈ junk G C) (hr : OrReaches n C (opnd C j b) k) :
        opnd C j b = n + k := by
      rcases lastOrBefore (orReaches_reach k _ hr).1 with h | ⟨r, rl, ro, ri, rb, rp⟩
      · exact h
      · have hr' := lastOrOutside ao hk rl ro ri rb
        rw [only, Finset.mem_singleton] at hr'
        have hle := orStep_le rp
        have hlt := opndBound ao jl b
        omega
    by_cases hd : ∃ k, k ∈ junk G C ∧ opnd C j b = n + k
    · obtain ⟨k, hk, he⟩ := hd
      have hbnd := opndBound ao jl b
      have hkj : k < j := by omega
      apply ih k hkj (hkj.trans hjm) hk
      · intro u v hu
        have hv := firesOp u v hu
        rw [he] at hv
        exact hv
      · rw [he] at hb
        exact hb
    · refine ⟨orIn n C (opnd C j b), rawCoverShape ao only hm (by
        have := opndBound ao jl b
        omega), ?_, ?_⟩
      · intro u v he
        rcases operandSupport ao top jl jo (firesOp u v he) with ⟨t, ht, rfl | rfl⟩ | ⟨k, hk, hr, _⟩
        · exact Or.inl ht
        · exact Or.inr ht
        · exact (hd ⟨k, hk, direct k hk hr⟩).elim
      · intro t ht
        apply Bool.eq_false_iff.mpr
        intro ht'
        exact Bool.false_ne_true (hb.symm.trans (reach_var_val x _ t (mem_orIn_reach t ht) ht'))

lemma finish (least : IsLeastAO G C) (top : TopForm G C)
    (hjunk : 2 ≤ (junk G C).card)
    (budget : 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ≤ 3)
    (nonempty : ∃ u v : Fin n, s(u, v) ∈ Ustar G C) :
    3 ≤ 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ∧
    ∃ t : Fin n, ∀ u v : Fin n, s(u, v) ∈ Ustar G C →
      ∃ w : Fin n, (w = u ∨ w = v) ∧ (G.deleteEdges ↑(Ustar G C)).Adj t w ∧
        ∀ x : Fin n → Bool, x w = true → graphFun G ∅ x = false →
          ∃ S : Finset (Fin n), (S.card ≤ 1 ∨
            ∃ z : Fin n, ∀ y ∈ S, (G.deleteEdges ↑(Ustar G C)).Adj y z) ∧
            (∀ p q : Fin n, s(p, q) ∈ Ustar G C → p ∈ S ∨ q ∈ S) ∧
            ∀ y ∈ S, x y = false := by
  have empty : centreless G C = ∅ := Finset.card_eq_zero.mp (by omega)
  obtain ⟨u, v, he⟩ := nonempty
  obtain ⟨a, ha, b, j, hj, _, hr, _⟩ := residualTrace least top he
  obtain ⟨m, hm, hin, path⟩ := residualPath least.1 empty ha hj hr
  have hpos := Finset.card_pos.mpr ⟨m, hm⟩
  have only : orN G C \ lam G C = {m} := by
    ext k
    rw [Finset.mem_singleton]
    exact ⟨fun hk => Finset.card_le_one.mp (by omega) k hk m hm, fun h => h.symm ▸ hm⟩
  obtain ⟨t, ht⟩ := mixingRaw least.1 empty only hm ha path
  refine ⟨by omega, t, ?_⟩
  have hml := (orData hm).1
  have hmo := (orData hm).2.1
  have hlt := least.1.2.1 m hml _ hin
  have uniform (p q : Fin n) (hpq : s(p, q) ∈ Ustar G C) :
      gateVal n C j (pairInput p q) = true := by
    obtain ⟨a', ha', b', k, hk, _, hr', hv⟩ := residualTrace least top hpq
    obtain ⟨l, hl, hkin, _⟩ := residualPath least.1 empty ha' hk hr'
    rw [only, Finset.mem_singleton] at hl
    subst l
    have heq := singleJunkInput least.1 hm ⟨t, ht⟩ hj hk hin hkin
    rwa [heq]
  intro p q hpq
  obtain ⟨a', ha', b', k, hk, hav, hr', _⟩ := residualTrace least top hpq
  obtain ⟨l, hl, _, hp⟩ := residualPath least.1 empty ha' hk hr'
  rw [only, Finset.mem_singleton] at hl
  subst l
  obtain ⟨w, hw, hend⟩ := oppositeEndpoint least top empty only hm ha' hav hp
  have ht' : t ∈ side C a' b' :=
    reach_mem_orIn t (hp.trans (mem_orIn_reach t ht))
  refine ⟨w, hend, cleanAdj least.1 ha' b' ht' hw, ?_⟩
  intro x hx hf
  have hjx : gateVal n C j x = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hmx : gateVal n C m x = true :=
      (val_or (n := n) (by simp) hml hmo).mpr ⟨_, hin, hlt, htrue⟩
    exact Bool.false_ne_true (hf.symm.trans (firingTop least.1 ha' hp hw x hmx hx))
  exact falseJunkCover least.1 top only hm x j (by omega) hj uniform hjx

end LowOverhead.Source5869

namespace SafeLower
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

lemma low_overhead_lower (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) (hj : 2 ≤ (junk graph C).card)
    (hcost : 2 * (centreless graph C).card + (junk graph C).card +
      (orN graph C \ lam graph C).card ≤ 3) : 20 ≤ C.size := by
  by_cases hempty : Ustar graph C = ∅
  · exact no_uncovered_lower C hl ht hempty
  · have hpairs : ∃ u v : Fin 10, s(u,v) ∈ Ustar graph C := by
      obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      induction e using Sym2.ind with
      | _ u v => exact ⟨u,v,he⟩
    have hcondition : LowOverheadFinite.graphCondition (Ustar graph C) :=
      (LowOverhead.Source5869.finish hl ht hj hcost hpairs).2
    have hcard := LowOverheadFinite.graph_condition_small
      (U := Ustar graph C) Finset.sdiff_subset hcondition
    exact two_uncovered_lower C hl ht hcard

lemma counterexample_overhead (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) (hs : C.size ≤ 19) (hj : 2 ≤ (junk graph C).card) :
    4 ≤ 2 * (centreless graph C).card + (junk graph C).card +
      (orN graph C \ lam graph C).card := by
  by_contra hsmall
  have bound := low_overhead_lower C hl ht hj (by omega)
  omega

end SafeLower



namespace Source8103

-- The circuit evaluation and wire-deletion lemmas adapt the existing one-junk argument.
namespace M1528
namespace P1
namespace S98
export PEqualNP.Outside.L_meta_2373.SafeLower.Source5781.S98
  (stepWire wires_eq_foldl foldl_stepWire_length foldl_stepWire_getD_lt getD_ge_length wires_length shiftDown wiresMatch wiresMatch_init wiresMatch_step wiresMatch_getD_shiftDown foldl_wiresMatch split_gates aliasWire aliasGate W eraseC gateAt_eq erase_wires erase_length erase_gateAt_lt erase_gateAt_ge prefix_W erase_W_lt W_gate W_input W_or W_and AO Least Bel alias_lt erase_AO least_nodup coneFold_length coneStep_getD_last coneStep_getD_lt coneFold_getD_lt inCone_iff inCone_c1 inCone_c2 AO_of_IsAO2 IsAO2_of_AO)
end S98
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
lemma junk_iff {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ PEqualNP.TopForm.BelowF G C k := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  simp only [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hc
    apply h3
    intro x hx
    by_contra hf
    exact hc ⟨x, hx, by simpa using hf⟩
end P1
namespace P2
open P1.S98 (W W_gate W_input W_or W_and AO gateAt_eq split_gates inCone_c1 inCone_c2 inCone_iff)
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
lemma fin2_sub : ∀ b : Fin 2, (b = 0 ∧ 1 - b = 1) ∨ (b = 1 ∧ 1 - b = 0) := by decide
lemma fin2_ne : ∀ b c : Fin 2, c ≠ b → c = 1 - b := by decide
lemma fin2_both (p : Fin 2 → Prop) (b : Fin 2) (h1 : p b) (h2 : p (1 - b)) : p 0 ∧ p 1 := by
  rcases fin2_sub b with ⟨h, h'⟩ | ⟨h, h'⟩
  · rw [h] at h1; rw [h'] at h2; exact ⟨h1, h2⟩
  · rw [h] at h1; rw [h'] at h2; exact ⟨h2, h1⟩
def OrStep (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ v ∈ (gateAt C k).inputs
def OrR (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (OrStep n C)
def Leaf (n : ℕ) (C : Circuit) (v : ℕ) : Prop :=
  v < n ∨ ∃ h, v = n + h ∧ h < C.gates.length ∧ (gateAt C h).op = GateOp.and
lemma orStep_lt (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrStep n C u v) : v < u := by
  obtain ⟨k, rfl, hk, _, hv⟩ := h
  obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
  rw [hin] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  omega
lemma orR_le (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrR n C u v) : v ≤ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => have := orStep_lt n C hA _ _ h2; omega
lemma orStep_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrStep n C u v) (hv : W n C x v = true) : W n C x u = true := by
  obtain ⟨k, rfl, hk, hop, hin⟩ := h
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
  rw [W_or n C x k hk hop a b hab ha hb]
  rw [hab] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl
  · simp [hv]
  · simp [hv]
lemma orR_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrR n C u v) (hv : W n C x v = true) : W n C x u = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head h1 _ ih => exact orStep_mono n C hA x _ _ h1 ih
lemma orR_leaf_true (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) :
    ∀ u, u < n + C.gates.length → W n C x u = true →
      ∃ v, OrR n C u v ∧ Leaf n C v ∧ W n C x v = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hx
    by_cases h1 : u < n
    · exact ⟨u, Relation.ReflTransGen.refl, Or.inl h1, hx⟩
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · exact ⟨n + k, Relation.ReflTransGen.refl, Or.inr ⟨k, rfl, hk, hop⟩, hx⟩
      · rw [W_or n C x k hk hop a b hab ha hb] at hx
        simp only [Bool.or_eq_true] at hx
        rcases hx with hx | hx
        · obtain ⟨v, hv1, hv2, hv3⟩ := ih a ha (by omega) hx
          exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2, hv3⟩
        · obtain ⟨v, hv1, hv2, hv3⟩ := ih b hb (by omega) hx
          exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2, hv3⟩
lemma orR_leaf (n : ℕ) (C : Circuit) (hA : AO n C) :
    ∀ u, u < n + C.gates.length → ∃ v, OrR n C u v ∧ Leaf n C v := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases h1 : u < n
    · exact ⟨u, Relation.ReflTransGen.refl, Or.inl h1⟩
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · exact ⟨n + k, Relation.ReflTransGen.refl, Or.inr ⟨k, rfl, hk, hop⟩⟩
      · obtain ⟨v, hv1, hv2⟩ := ih a ha (by omega)
        exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2⟩
open PEqualNP.EdgeOwnership in
lemma orR_cone (n : ℕ) (C : Circuit) (hA : AO n C) (h u : ℕ) (hr : OrR n C u (n + h)) :
    ∀ k, u = n + k → k < C.gates.length → h = k ∨ InCone n C h k := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => intro k hk _; left; omega
  | head h1 h2 ih =>
    rename_i u c
    intro k hk hlen
    have hle := orR_le n C hA _ _ h2
    have hlt := orStep_lt n C hA _ _ h1
    obtain ⟨k', hk', _, _, hin⟩ := h1
    have hkk : k' = k := by omega
    subst hkk
    have hc : c = n + (c - n) := by omega
    rcases ih (c - n) hc (by omega) with h3 | h3
    · right
      refine inCone_c1 n C hA h k' hlen ?_
      rw [h3, ← hc]
      exact hin
    · right
      refine inCone_c2 n C hA h (c - n) k' hlen h3 ?_
      rw [← hc]
      exact hin
lemma biclique_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hcon.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.mp hcon.2
  exact h4 a b c d hac hbd
    ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc d hd, (hab a ha d hd).symm⟩
lemma opnd_lt (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) : ∀ b : Fin 2, o b < n + a := by
  obtain ⟨_, a1, b1, hab, ha1, hb1⟩ := hA a ha
  rw [hin] at hab
  simp only [List.cons.injEq, and_true] at hab
  intro b
  rcases fin2_sub b with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> omega
lemma top_true (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) (x : Fin n → Bool)
    (h : ∀ b : Fin 2, W n C x (o b) = true) : W n C x (n + a) = true := by
  have hlt := opnd_lt n C hA a ha o hin
  rw [W_and n C x a ha hop (o 0) (o 1) hin (hlt 0) (hlt 1), h 0, h 1]
  rfl
open PEqualNP.EdgeOwnership in
lemma sem_adj (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and)
    (o : Fin 2 → ℕ) (hin : (gateAt C a).inputs = [o 0, o 1]) (u v : Fin n)
    (hu : OrR n C (o 0) u.val) (hv : OrR n C (o 1) v.val) :
    W n C (pairInput u v) (n + a) = true := by
  apply top_true n C hA a ha hop o hin
  intro b
  rcases fin2_sub b with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
  · refine orR_mono n C hA _ _ _ hu ?_
    rw [W_input n C _ u.val u.isLt]; simp [pairInput]
  · refine orR_mono n C hA _ _ _ hv ?_
    rw [W_input n C _ v.val v.isLt]; simp [pairInput]
open PEqualNP.EdgeOwnership in
open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]
open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w, (w ∈ g.inputs ∧ n ≤ w ∧ w < n + cs.length) ∧ x ∈ cs.getD (w - n) []) := by
  by_cases hop : g.op = GateOp.or
  · simp [orStep, List.getD_eq_getElem?_getD, hop]
  · simp [orStep, List.getD_eq_getElem?_getD, hop]
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk
lemma orReaches_iff (n : ℕ) (C : Circuit) (g k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ OrReaches n C w g) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : ∀ x, x ∈ (orSets n C).getD k [] ↔ x = k ∨ (gk.op = GateOp.or ∧
      ∃ w, (w ∈ gk.inputs ∧ n ≤ w ∧ w < n + k) ∧
        x ∈ (pre.foldl (orStep n) []).getD (w - n) []) := by
    intro x
    rw [hc, orFold_getD_lt n post _ k (by omega)]
    have h := orStep_mem_last n (pre.foldl (orStep n) []) gk x
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have e : n + k - n = k := by omega
  unfold OrReaches
  rw [e, h1 g]
  constructor
  · rintro ⟨_, h | ⟨hop, w, ⟨hw, hn, hlt⟩, h⟩⟩
    · exact Or.inl h
    · right
      refine ⟨hop, w, hw, hn, hlt, hn, ?_⟩
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro (h | ⟨hop, w, hw, hn, hlt, _, h⟩)
    · exact ⟨by omega, Or.inl h⟩
    · refine ⟨by omega, Or.inr ⟨hop, w, ⟨hw, hn, hlt⟩, ?_⟩⟩
      rw [← h2 (w - n) (by omega)]
      exact h
lemma orReaches_orR (n : ℕ) (C : Circuit) :
    ∀ w, w < n + C.gates.length → ∀ g, OrReaches n C w g → OrR n C w (n + g) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw g hr
    have hn : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (orReaches_iff n C g k hk).mp hr with h | ⟨hop, c, hc, hcn, hclt, hcr⟩
    · rw [h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head ⟨k, rfl, hk, hop, hc⟩ (ih c hclt (by omega) g hcr)
lemma orR_orReaches (n : ℕ) (C : Circuit) (hA : AO n C) (g : ℕ) (hg : g < C.gates.length) :
    ∀ w, w < n + C.gates.length → OrR n C w (n + g) → OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hr
    rcases Relation.ReflTransGen.cases_head hr with h | ⟨c, ⟨k, hk1, hk, hop, hc⟩, hcr⟩
    · rw [h]
      exact (orReaches_iff n C g g hg).mpr (Or.inl rfl)
    · subst hk1
      have hle := orR_le n C hA _ _ hcr
      have hclt : c < n + k := by
        obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
        rw [hab] at hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        omega
      exact (orReaches_iff n C g k hk).mpr
        (Or.inr ⟨hop, c, hc, by omega, hclt, ih c hclt (by omega) hcr⟩)
lemma mem_orIn (n : ℕ) (C : Circuit) (hA : AO n C) (w : ℕ) (hw : w < n + C.gates.length)
    (u : Fin n) : u ∈ orIn n C w ↔ OrR n C w u.val := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, hk, hr, hop, hu⟩)
    · rw [h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail (orReaches_orR n C w hw k hr) ⟨k, rfl, hk, hop, hu⟩
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, hc, ⟨k, rfl, hk, hop, hu⟩⟩
    · left
      exact h1
    · right
      exact ⟨k, hk, orR_orReaches n C hA k hk w hw hc, hop, hu⟩
lemma opnd_eq (n : ℕ) (C : Circuit) (hA : AO n C) (a : ℕ) (ha : a < C.gates.length) :
    (gateAt C a).inputs = [opnd C a 0, opnd C a 1] := by
  obtain ⟨_, p, q, hpq, _, _⟩ := hA a ha
  simp [opnd, hpq]
lemma nfc (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (h : NoFourCycle G) :
    ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
  rintro a b c d hac hbd ⟨h1, h2, h3, h4⟩
  have h0 := h a c hac
  have h5 : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj c w).card :=
    Finset.one_lt_card.mpr ⟨b, by simp [h1, h2.symm], d, by simp [h4.symm, h3], hbd⟩
  omega
end P2
end M1528
namespace M1529
lemma main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (P Q W : Finset (Fin n)),
    (∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) →
    (∀ w ∈ W, w ∈ P → w ∉ Q ∧ ∀ q ∈ Q, G.Adj w q) ∧
    (∀ w ∈ W, w ∈ Q → w ∉ P ∧ ∀ p ∈ P, G.Adj w p) ∧
    (∀ s ∈ P ∩ Q, ∀ w ∈ W, G.Adj s w) ∧ (∀ s ∈ P ∩ Q, s ∉ W) ∧
    (2 ≤ (P ∩ Q).card → W.card ≤ 1) := by
  intro n G _ hG P Q W hW
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw hwP
    have h := (hW w).1 hw
    refine ⟨?_, ?_⟩
    · intro hwQ
      rcases h w hwP w hwQ with h1 | h1 | h1 <;> exact G.irrefl h1
    · intro q hq
      rcases h w hwP q hq with h1 | h1 | h1
      · exact h1
      · exact absurd h1 G.irrefl
      · exact h1.symm
  · intro w hw hwQ
    have h := (hW w).1 hw
    refine ⟨?_, ?_⟩
    · intro hwP
      rcases h w hwP w hwQ with h1 | h1 | h1 <;> exact G.irrefl h1
    · intro p hp
      rcases h p hp w hwQ with h1 | h1 | h1
      · exact h1.symm
      · exact h1.symm
      · exact absurd h1 G.irrefl
  · intro s hs w hw
    have hsP := (Finset.mem_inter.1 hs).1
    have hsQ := (Finset.mem_inter.1 hs).2
    rcases (hW w).1 hw s hsP s hsQ with h1 | h1 | h1
    · exact absurd h1 G.irrefl
    · exact h1
    · exact h1
  · intro s hs hsW
    have hsP := (Finset.mem_inter.1 hs).1
    have hsQ := (Finset.mem_inter.1 hs).2
    rcases (hW s).1 hsW s hsP s hsQ with h1 | h1 | h1 <;> exact G.irrefl h1
  · intro h2
    obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.1 h2
    have key : ∀ u ∈ P ∩ Q, ∀ w ∈ W, G.Adj u w := by
      intro u hu w hw
      have huP := (Finset.mem_inter.1 hu).1
      have huQ := (Finset.mem_inter.1 hu).2
      rcases (hW w).1 hw u huP u huQ with h1 | h1 | h1
      · exact absurd h1 G.irrefl
      · exact h1
      · exact h1
    refine le_trans (Finset.card_le_card ?_) (hG s t hst)
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨key s hs w hw, key t ht w hw⟩
end M1529
lemma thm_1529 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (P Q W : Finset (Fin n)),
    (∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) →
    (∀ w ∈ W, w ∈ P → w ∉ Q ∧ ∀ q ∈ Q, G.Adj w q) ∧
    (∀ w ∈ W, w ∈ Q → w ∉ P ∧ ∀ p ∈ P, G.Adj w p) ∧
    (∀ s ∈ P ∩ Q, ∀ w ∈ W, G.Adj s w) ∧ (∀ s ∈ P ∩ Q, s ∉ W) ∧
    (2 ≤ (P ∩ Q).card → W.card ≤ 1) :=
  PEqualNP.Outside.L_meta_2373.Source8103.M1529.main_aux

namespace M1530
lemma core (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hno : ∀ s t w w' : Fin n, s ≠ t → w ≠ w' → G.Adj s w → G.Adj t w → G.Adj s w' →
      G.Adj t w' → False)
    (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) :
    (2 ≤ Q.card → (W ∩ P).card ≤ 1) ∧ (2 ≤ P.card → (W ∩ Q).card ≤ 1) ∧
    (∀ a b : Fin n, G.Adj a b → (a ∈ P ∨ b ∈ P) → (a ∈ Q ∨ b ∈ Q) → a ∈ W →
      (a ∈ P → b ∈ Q) ∧ (a ∈ Q → b ∈ P) ∧ (a ∉ P → a ∉ Q → b ∈ P ∩ Q)) ∧
    (∀ s, P ∩ Q = {s} → ∀ u, u ≠ s → ((Finset.univ.filter fun w => G.Adj u w) ∩ W).card ≤ 1) := by
  have kP : ∀ w ∈ W, w ∈ P → ∀ q ∈ Q, G.Adj w q := by
    intro w hw hwP q hq
    rcases (hW w).1 hw w hwP q hq with h | h | h
    · exact h
    · exact absurd h (G.loopless.irrefl w)
    · exact h.symm
  have kQ : ∀ w ∈ W, w ∈ Q → ∀ p ∈ P, G.Adj w p := by
    intro w hw hwQ p hp
    rcases (hW w).1 hw p hp w hwQ with h | h | h
    · exact h.symm
    · exact h.symm
    · exact absurd h (G.loopless.irrefl w)
  have h3 : ∀ s ∈ P ∩ Q, ∀ w ∈ W, G.Adj s w := by
    intro s hs w hw
    obtain ⟨hsP, hsQ⟩ := Finset.mem_inter.1 hs
    rcases (hW w).1 hw s hsP s hsQ with h | h | h
    · exact absurd h (G.loopless.irrefl s)
    · exact h
    · exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h2
    obtain ⟨q, hq, q', hq', hqq⟩ := Finset.one_lt_card.1 h2
    apply Finset.card_le_one.2
    intro w hw w' hw'
    rw [Finset.mem_inter] at hw hw'
    by_contra hne
    exact hno w w' q q' hne hqq (kP w hw.1 hw.2 q hq) (kP w' hw'.1 hw'.2 q hq)
      (kP w hw.1 hw.2 q' hq') (kP w' hw'.1 hw'.2 q' hq')
  · intro h2
    obtain ⟨p, hp, p', hp', hpp⟩ := Finset.one_lt_card.1 h2
    apply Finset.card_le_one.2
    intro w hw w' hw'
    rw [Finset.mem_inter] at hw hw'
    by_contra hne
    exact hno w w' p p' hne hpp (kQ w hw.1 hw.2 p hp) (kQ w' hw'.1 hw'.2 p hp)
      (kQ w hw.1 hw.2 p' hp') (kQ w' hw'.1 hw'.2 p' hp')
  · intro a b _ hP hQ haW
    have nPQ : a ∈ P → a ∉ Q := fun haP haQ => G.loopless.irrefl a (kP a haW haP a haQ)
    refine ⟨fun haP => ?_, fun haQ => ?_, fun haP haQ => ?_⟩
    · rcases hQ with h | h
      · exact absurd h (nPQ haP)
      · exact h
    · rcases hP with h | h
      · exact absurd haQ (nPQ h)
      · exact h
    · rcases hP with h | h
      · exact absurd h haP
      · rcases hQ with h' | h'
        · exact absurd h' haQ
        · exact Finset.mem_inter.2 ⟨h, h'⟩
  · intro s hs u hus
    have hsm : s ∈ P ∩ Q := by rw [hs]; simp
    apply Finset.card_le_one.2
    intro w hw w' hw'
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
    by_contra hne
    exact hno s u w w' (Ne.symm hus) hne (h3 s hsm w hw.2) hw.1 (h3 s hsm w' hw'.2) hw'.1
end M1530
lemma thm_1530 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (P Q W : Finset (Fin n)),
    (∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) →
    (2 ≤ Q.card → (W ∩ P).card ≤ 1) ∧ (2 ≤ P.card → (W ∩ Q).card ≤ 1) ∧
    (∀ a b : Fin n, G.Adj a b → (a ∈ P ∨ b ∈ P) → (a ∈ Q ∨ b ∈ Q) → a ∈ W →
      (a ∈ P → b ∈ Q) ∧ (a ∈ Q → b ∈ P) ∧ (a ∉ P → a ∉ Q → b ∈ P ∩ Q)) ∧
    (∀ s, P ∩ Q = {s} → ∀ u, u ≠ s → ((Finset.univ.filter fun w => G.Adj u w) ∩ W).card ≤ 1) := by
  intro n G _ hnf P Q W hW
  have hno : ∀ s t w w' : Fin n, s ≠ t → w ≠ w' → G.Adj s w → G.Adj t w → G.Adj s w' →
      G.Adj t w' → False := by
    intro s t w w' hst hww h1 h2 h3 h4
    exact hww (Finset.card_le_one.1 (hnf s t hst) w (by simp [h1, h2]) w' (by simp [h3, h4]))
  exact PEqualNP.Outside.L_meta_2373.Source8103.M1530.core n G hno P Q W hW

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
namespace Close
open M1528.P1.S98 (W AO Least Bel aliasWire aliasGate eraseC erase_length erase_AO
  erase_wires erase_W_lt erase_gateAt_lt erase_gateAt_ge W_gate W_input W_or W_and
  gateAt_eq AO_of_IsAO2 IsAO2_of_AO prefix_W)
open M1528.P2 (OrStep OrR Leaf orStep_lt orR_le orStep_mono orR_mono orR_leaf_true orR_leaf
  orR_cone pairInput_true graphFun_pair orReaches_orR orR_orReaches mem_orIn opnd_eq nfc)
def OrStepOut (n : ℕ) (C : Circuit) (B : Finset ℕ) (u v : ℕ) : Prop :=
  ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ k ∉ B ∧
    v ∈ (gateAt C k).inputs
def OrROut (n : ℕ) (C : Circuit) (B : Finset ℕ) : ℕ → ℕ → Prop :=
  Relation.ReflTransGen (OrStepOut n C B)
lemma orROut_to_orR {n : ℕ} {C : Circuit} {B : Finset ℕ} {u v : ℕ}
    (h : OrROut n C B u v) : OrR n C u v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ h2 ih =>
    obtain ⟨k, rfl, hk, hop, _, hin⟩ := h2
    exact Relation.ReflTransGen.tail ih ⟨k, rfl, hk, hop, hin⟩
lemma orStepOut_lt {n : ℕ} {C : Circuit} (hA : AO n C) {B : Finset ℕ} {u v : ℕ}
    (h : OrStepOut n C B u v) : v < u := by
  obtain ⟨k, rfl, hk, hop, _, hin⟩ := h
  exact orStep_lt n C hA (n + k) v ⟨k, rfl, hk, hop, hin⟩
lemma orROut_le {n : ℕ} {C : Circuit} (hA : AO n C) {B : Finset ℕ} {u v : ℕ}
    (h : OrROut n C B u v) : v ≤ u :=
  orR_le n C hA u v (orROut_to_orR h)
open Classical in
lemma or_dag_leaf_bound {n : ℕ} (C : Circuit) (hA : AO n C)
    (T : Finset (Fin n)) (B : Finset ℕ)
    (hB : ∀ h ∈ B, ((orIn n C (n + h)) ∩ T).card ≤ 1)
    (R : Finset ℕ)
    (hR_lt : ∀ w ∈ R, w < n + C.gates.length)
    (hnoAnd : ∀ w ∈ R, ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ OrR n C w (n + h)) :
    let F := (Finset.range C.gates.length).filter fun h =>
      (gateAt C h).op = GateOp.or ∧ h ∉ B ∧ ∃ w ∈ R, OrR n C w (n + h)
    ((R.biUnion fun w => orIn n C w) ∩ T).card ≤ R.card + F.card := by
  classical
  intro F
  let Fout : Finset ℕ → Finset ℕ := fun R0 =>
    (Finset.range C.gates.length).filter fun h =>
      (gateAt C h).op = GateOp.or ∧ h ∉ B ∧ ∃ w ∈ R0, OrROut n C B w (n + h)
  have hFout_sub : Fout R ⊆ F := by
    intro h hh
    simp only [Fout, F, Finset.mem_filter] at hh ⊢
    obtain ⟨hrng, hop, hnotB, w, hwR, hr⟩ := hh
    exact ⟨hrng, hop, hnotB, w, hwR, orROut_to_orR hr⟩
  suffices hmain : ∀ m : ℕ, ∀ R0 : Finset ℕ,
      (∀ w ∈ R0, w < n + C.gates.length) →
      (∀ w ∈ R0, ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ OrR n C w (n + h)) →
      (Fout R0).card = m →
      ((R0.biUnion fun w => orIn n C w) ∩ T).card ≤ R0.card + m by
    exact (hmain (Fout R).card R hR_lt hnoAnd rfl).trans
      (Nat.add_le_add_left (Finset.card_le_card hFout_sub) R.card)
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro R0 hR0_lt hR0_noAnd hm
    by_cases hFempty : Fout R0 = ∅
    · have hm0 : m = 0 := by rw [← hm, hFempty, Finset.card_empty]
      rw [hm0, add_zero]
      calc ((R0.biUnion fun w => orIn n C w) ∩ T).card
          = (R0.biUnion fun w => (orIn n C w) ∩ T).card := by
              congr 1
              ext u
              simp only [Finset.mem_inter, Finset.mem_biUnion]
              constructor
              · rintro ⟨⟨w,hw,hu⟩,ht⟩
                exact ⟨w,hw,hu,ht⟩
              · rintro ⟨w,hw,hu,ht⟩
                exact ⟨⟨w,hw,hu⟩,ht⟩
        _ ≤ ∑ w ∈ R0, ((orIn n C w) ∩ T).card := Finset.card_biUnion_le
        _ ≤ ∑ _w ∈ R0, 1 := by
              refine Finset.sum_le_sum fun w hw => ?_
              by_cases hwn : w < n
              · have hsub : (orIn n C w) ∩ T ⊆ {⟨w, hwn⟩} := by
                  intro u hu
                  have hu1 := (mem_orIn n C hA w (hR0_lt w hw) u).mp (Finset.mem_inter.mp hu).1
                  rcases Relation.ReflTransGen.cases_head hu1 with heq | ⟨c, ⟨k, hk, _⟩, _⟩
                  · exact Finset.mem_singleton.mpr (Fin.ext heq.symm)
                  · omega
                exact (Finset.card_le_card hsub).trans (by simp)
              · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
                have hk : k < C.gates.length := by have := hR0_lt (n + k) hw; omega
                rcases (hA k hk).1 with hop | hop
                · exact absurd Relation.ReflTransGen.refl (hR0_noAnd (n + k) hw k hk hop)
                · have hkB : k ∈ B := by
                    by_contra hkNotB
                    have : k ∈ Fout R0 := Finset.mem_filter.mpr
                      ⟨Finset.mem_range.mpr hk, hop, hkNotB, n + k, hw, Relation.ReflTransGen.refl⟩
                    rw [hFempty] at this
                    exact Finset.notMem_empty _ this
                  exact hB k hkB
        _ = R0.card := by simp
    · have hFne : (Fout R0).Nonempty := Finset.nonempty_iff_ne_empty.mpr hFempty
      let h := (Fout R0).max' hFne
      have hhF : h ∈ Fout R0 := Finset.max'_mem (Fout R0) hFne
      have hh_lt : h < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp hhF).1
      have hh_op : (gateAt C h).op = GateOp.or := (Finset.mem_filter.mp hhF).2.1
      have hh_notB : h ∉ B := (Finset.mem_filter.mp hhF).2.2.1
      obtain ⟨w0, hw0R, hw0_reach⟩ := (Finset.mem_filter.mp hhF).2.2.2
      have hreach_eq : ∀ w ∈ R0, OrROut n C B w (n + h) → w = n + h := by
        intro w hw hr
        rcases Relation.ReflTransGen.cases_head hr with heq | ⟨c, hstep, hrest⟩
        · exact heq
        · obtain ⟨k, rfl, hk, hkop, hkB, hkin⟩ := hstep
          have hlt1 := orStepOut_lt hA ⟨k, rfl, hk, hkop, hkB, hkin⟩
          have hle2 := orROut_le hA hrest
          have hkF : k ∈ Fout R0 := Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr hk, hkop, hkB, n + k, hw, Relation.ReflTransGen.refl⟩
          have hk_le : k ≤ h := Finset.le_max' (Fout R0) k hkF
          omega
      have hhR : n + h ∈ R0 := by
        have := hreach_eq w0 hw0R hw0_reach
        rwa [← this]
      obtain ⟨_, a, b, hab, ha_lt, hb_lt⟩ := hA h hh_lt
      let R' := (R0.erase (n + h)) ∪ {a, b}
      have hstep_a : OrStep n C (n + h) a := ⟨h, rfl, hh_lt, hh_op, by rw [hab]; simp⟩
      have hstep_b : OrStep n C (n + h) b := ⟨h, rfl, hh_lt, hh_op, by rw [hab]; simp⟩
      have hstepOut_a : OrStepOut n C B (n + h) a :=
        ⟨h, rfl, hh_lt, hh_op, hh_notB, by rw [hab]; simp⟩
      have hstepOut_b : OrStepOut n C B (n + h) b :=
        ⟨h, rfl, hh_lt, hh_op, hh_notB, by rw [hab]; simp⟩
      have hR'_lt : ∀ w ∈ R', w < n + C.gates.length := by
        intro w hw
        simp only [R', Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
          Finset.mem_singleton] at hw
        rcases hw with ⟨_, hwR⟩ | rfl | rfl
        · exact hR0_lt w hwR
        · omega
        · omega
      have hR'_noAnd : ∀ w ∈ R', ∀ k, k < C.gates.length → (gateAt C k).op = GateOp.and →
          ¬ OrR n C w (n + k) := by
        intro w hw k hk hop hr
        simp only [R', Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
          Finset.mem_singleton] at hw
        rcases hw with ⟨_, hwR⟩ | rfl | rfl
        · exact hR0_noAnd w hwR k hk hop hr
        · exact hR0_noAnd (n + h) hhR k hk hop (Relation.ReflTransGen.head hstep_a hr)
        · exact hR0_noAnd (n + h) hhR k hk hop (Relation.ReflTransGen.head hstep_b hr)
      have hF'_sub : Fout R' ⊆ (Fout R0).erase h := by
        intro k hk
        simp only [Fout, Finset.mem_filter] at hk
        obtain ⟨hkrng, hkop, hkB, w, hwR', hwk⟩ := hk
        have hwk_orig : ∃ w' ∈ R0, OrROut n C B w' (n + k) := by
          simp only [R', Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
            Finset.mem_singleton] at hwR'
          rcases hwR' with ⟨_, hwR⟩ | rfl | rfl
          · exact ⟨w, hwR, hwk⟩
          · exact ⟨n + h, hhR, Relation.ReflTransGen.head hstepOut_a hwk⟩
          · exact ⟨n + h, hhR, Relation.ReflTransGen.head hstepOut_b hwk⟩
        have hkF0 : k ∈ Fout R0 := Finset.mem_filter.mpr ⟨hkrng, hkop, hkB, hwk_orig⟩
        refine Finset.mem_erase.mpr ⟨?_, hkF0⟩
        intro hkh
        subst hkh
        simp only [R', Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
          Finset.mem_singleton] at hwR'
        rcases hwR' with ⟨hne, hwR⟩ | rfl | rfl
        · exact hne (hreach_eq w hwR hwk)
        · have := orROut_le hA hwk; omega
        · have := orROut_le hA hwk; omega
      have hF'_lt : (Fout R').card < m := by
        have h1 : (Fout R').card ≤ ((Fout R0).erase h).card := Finset.card_le_card hF'_sub
        have h2 : ((Fout R0).erase h).card + 1 = (Fout R0).card := Finset.card_erase_add_one hhF
        omega
      have hR'_card : R'.card ≤ R0.card + 1 := by
        have h1 : R'.card ≤ (R0.erase (n + h)).card + ({a, b} : Finset ℕ).card :=
          Finset.card_union_le _ _
        have h2 : ({a, b} : Finset ℕ).card ≤ 2 := Finset.card_le_two
        have h3 : (R0.erase (n + h)).card + 1 = R0.card := Finset.card_erase_add_one hhR
        omega
      have hunion_sub : R0.biUnion (fun w => orIn n C w) ⊆ R'.biUnion (fun w => orIn n C w) := by
        intro u hu
        simp only [Finset.mem_biUnion] at hu ⊢
        obtain ⟨w, hwR, huw⟩ := hu
        by_cases hwh : w = n + h
        · subst hwh
          have hr := (mem_orIn n C hA (n + h) (by omega) u).mp huw
          rcases Relation.ReflTransGen.cases_head hr with heq | ⟨c, hst, hrest⟩
          · have := u.isLt; omega
          · obtain ⟨k, hk_eq, _, _, hc⟩ := hst
            have hkh : k = h := by omega
            subst hkh
            rw [hab] at hc
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · exact ⟨c, Finset.mem_union_right _ (by simp),
                (mem_orIn n C hA c (by omega) u).mpr hrest⟩
            · exact ⟨c, Finset.mem_union_right _ (by simp),
                (mem_orIn n C hA c (by omega) u).mpr hrest⟩
        · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwh, hwR⟩), huw⟩
      have hih := ih (Fout R').card hF'_lt R' hR'_lt hR'_noAnd rfl
      have hsub_card : ((R0.biUnion fun w => orIn n C w) ∩ T).card ≤
          ((R'.biUnion fun w => orIn n C w) ∩ T).card :=
        Finset.card_le_card (Finset.inter_subset_inter_right hunion_sub)
      omega
lemma opnd_lt' {n : ℕ} {C : Circuit} (hA : AO n C) (a : ℕ) (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  M1528.P2.opnd_lt n C hA a ha (opnd C a) (opnd_eq n C hA a ha) b
lemma W_eq_gateVal {n : ℕ} (C : Circuit) (k : ℕ) (x : Fin n → Bool) :
    W n C x (n + k) = gateVal n C k x := rfl
lemma W_mono_input {n : ℕ} (C : Circuit) (hA : AO n C) (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ u, u < n + C.gates.length → W n C x u = true → W n C y u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hx
    by_cases h1 : u < n
    · rw [W_input n C x u h1] at hx
      rw [W_input n C y u h1]
      exact hxy ⟨u, h1⟩ hx
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · rw [W_and n C x k hk hop a b hab ha hb, Bool.and_eq_true] at hx
        rw [W_and n C y k hk hop a b hab ha hb, Bool.and_eq_true]
        exact ⟨ih a ha (by omega) hx.1, ih b hb (by omega) hx.2⟩
      · rw [W_or n C x k hk hop a b hab ha hb, Bool.or_eq_true] at hx
        rw [W_or n C y k hk hop a b hab ha hb, Bool.or_eq_true]
        rcases hx with hx | hx
        · exact Or.inl (ih a ha (by omega) hx)
        · exact Or.inr (ih b hb (by omega) hx)
lemma least_of_isLeastAO {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) : Least n C := by
  refine ⟨AO_of_IsAO2 n C hL.1, fun D hAD hDeq => ?_⟩
  have hfun : circuitFun n D = graphFun G ∅ := by
    funext x
    rw [← hL.2.1]
    exact hDeq x
  exact hL.2.2 D (IsAO2_of_AO n D hAD) hfun
lemma graphFun_single_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) : graphFun G ∅ (pairInput u u) = false := by
  rw [Bool.eq_false_iff, ne_eq, graphFun_pair]
  exact G.irrefl
lemma junk_single_props {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) :
    g < C.gates.length ∧ (gateAt C g).op = GateOp.and ∧ ¬ BelowF G C g ∧
    (∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = g) ∧
    (∀ h < C.gates.length, (gateAt C h).op = GateOp.and → InCone n C h g → False) ∧
    (∀ a ∈ tops G C, ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → InCone n C h a → h = g) := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  have hmem_iff : ∀ k, k ∈ junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ ¬ BelowF G C k := by
    intro k
    have h1 := M1528.P1.junk_iff G C k
    simpa [BelowF] using h1
  have hgmem : g ∈ junk G C := by rw [hg]; simp
  obtain ⟨hg_lt, hg_op, hg_notB⟩ := (hmem_iff g).mp hgmem
  have huniq : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = g := by
    intro k hk hop hnotB
    have : k ∈ junk G C := (hmem_iff k).mpr ⟨hk, hop, hnotB⟩
    rw [hg, Finset.mem_singleton] at this
    exact this
  have hno_in_g : ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → InCone n C h g → False := by
    intro h hh hop hc
    by_cases hB : BelowF G C h
    · exact hT h hh g hg_lt hop hB hg_op hc
    · have heq := huniq h hh hop hB
      subst heq
      have hlt : ∀ i k, k < C.gates.length → InCone n C i k → i < k := by
        intro i k
        induction k using Nat.strong_induction_on with
        | _ k ihk =>
          intro hk hic
          rw [M1528.P1.S98.inCone_iff n C i k hk] at hic
          obtain ⟨w, hwin, hnw, hwlt, hcase⟩ := hic
          rcases hcase with rfl | hc'
          · omega
          · have hlt' := ihk (w - n) (by omega) (by omega) hc'
            omega
      exact Nat.lt_irrefl h (hlt h h hg_lt hc)
  have htop_cone : ∀ a ∈ tops G C, ∀ h < C.gates.length, (gateAt C h).op = GateOp.and →
      InCone n C h a → h = g := by
    intro a ha h hh hop hc
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
    by_cases hB : BelowF G C h
    · exact absurd hc (hT h hh a ha.1 hop hB ha.2.1)
    · exact huniq h hh hop hB
  exact ⟨hg_lt, hg_op, hg_notB, huniq, hno_in_g, htop_cone⟩
lemma no_and_in_g_opnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (b : Fin 2) :
    opnd C g b < n + g ∧
    ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C (opnd C g b) (n + h) := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  obtain ⟨hg_lt, hg_op, _, _, hno_in_g, _⟩ := junk_single_props G C hL hT g hg
  have hlt := opnd_lt' hA g hg_lt b
  refine ⟨hlt, fun h hh hop hr => ?_⟩
  have hmem : opnd C g b ∈ (gateAt C g).inputs := by
    have := M1528.P2.opnd_eq n C hA g hg_lt
    fin_cases b <;> rw [this] <;> simp
  have hic : InCone n C h g := by
    by_cases hw : opnd C g b < n
    · have := orR_le n C hA _ _ hr; omega
    · obtain ⟨k, hk_eq⟩ : ∃ k, opnd C g b = n + k := ⟨opnd C g b - n, by omega⟩
      rcases orR_cone n C hA h (opnd C g b) hr k hk_eq (by omega) with rfl | hc
      · exact M1528.P1.S98.inCone_c1 n C hA h g hg_lt (hk_eq ▸ hmem)
      · exact M1528.P1.S98.inCone_c2 n C hA h k g hg_lt hc (hk_eq ▸ hmem)
  exact hno_in_g h hh hop hic
lemma pure_or_wire_eval {n : ℕ} (C : Circuit) (hA : AO n C) (w : ℕ) (hw : w < n + C.gates.length)
    (hnoAnd : ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C w (n + h)) :
    (orIn n C w).Nonempty ∧
    ∀ x : Fin n → Bool, W n C x w = true ↔ ∃ u ∈ orIn n C w, x u = true := by
  constructor
  · obtain ⟨v, hrv, hleaf⟩ := orR_leaf n C hA w hw
    rcases hleaf with hvn | ⟨h, rfl, hh, hop⟩
    · exact ⟨⟨v, hvn⟩, (mem_orIn n C hA w hw ⟨v, hvn⟩).mpr hrv⟩
    · exact absurd hrv (hnoAnd h hh hop)
  · intro x
    constructor
    · intro hW
      obtain ⟨v, hrv, hleaf, hWv⟩ := orR_leaf_true n C hA x w hw hW
      rcases hleaf with hvn | ⟨h, rfl, hh, hop⟩
      · rw [M1528.P1.S98.W_input n C x v hvn] at hWv
        exact ⟨⟨v, hvn⟩, (mem_orIn n C hA w hw ⟨v, hvn⟩).mpr hrv, hWv⟩
      · exact absurd hrv (hnoAnd h hh hop)
    · rintro ⟨u, hu, hxu⟩
      have hru := (mem_orIn n C hA w hw u).mp hu
      refine orR_mono n C hA x w u.val hru ?_
      rw [M1528.P1.S98.W_input n C x u.val u.isLt]
      exact hxu
lemma g_semantics {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) :
    let P := side (n := n) C g 0
    let Q := side (n := n) C g 1
    let Wg := wmax G C g
    P.Nonempty ∧ Q.Nonempty ∧
    (∀ x : Fin n → Bool, W n C x (n + g) = true ↔
      (∃ p ∈ P, x p = true) ∧ (∃ q ∈ Q, x q = true)) ∧
    (∀ w : Fin n, w ∈ Wg ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) ∧
    (∃ p ∈ P, ∃ q ∈ Q, ¬ G.Adj p q) := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  obtain ⟨hg_lt, hg_op, hg_notB, _, _, _⟩ := junk_single_props G C hL hT g hg
  obtain ⟨h0_lt, h0_no⟩ := no_and_in_g_opnd G C hL hT g hg 0
  obtain ⟨h1_lt, h1_no⟩ := no_and_in_g_opnd G C hL hT g hg 1
  obtain ⟨hPne, hPeval⟩ := pure_or_wire_eval C hA (opnd C g 0) (by omega) h0_no
  obtain ⟨hQne, hQeval⟩ := pure_or_wire_eval C hA (opnd C g 1) (by omega) h1_no
  have hgeval : ∀ x : Fin n → Bool, W n C x (n + g) = true ↔
      (∃ p ∈ side (n := n) C g 0, x p = true) ∧ (∃ q ∈ side (n := n) C g 1, x q = true) := by
    intro x
    rw [W_and n C x g hg_lt hg_op (opnd C g 0) (opnd C g 1) (opnd_eq n C hA g hg_lt) h0_lt h1_lt,
      Bool.and_eq_true, hPeval x, hQeval x]
    rfl
  refine ⟨hPne, hQne, hgeval, ?_, ?_⟩
  · intro w
    simp only [wmax, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hw p hp q hq
      let x : Fin n → Bool := fun i => decide (i = p ∨ i = q ∨ i = w)
      have hgx : gateVal n C g x = true := by
        rw [← W_eq_gateVal, hgeval x]
        exact ⟨⟨p, hp, by simp [x]⟩, ⟨q, hq, by simp [x]⟩⟩
      have hxw : x w = true := by simp [x]
      have hF := hw x hgx hxw
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq] at hF
      obtain ⟨a, b, hab, hxa, hxb⟩ := hF
      simp only [x, decide_eq_true_eq] at hxa hxb
      rcases hxa with rfl | rfl | rfl <;> rcases hxb with rfl | rfl | rfl
      · exact (G.irrefl hab).elim
      · exact Or.inl hab
      · exact Or.inr (Or.inl hab)
      · exact Or.inl hab.symm
      · exact (G.irrefl hab).elim
      · exact Or.inr (Or.inr hab)
      · exact Or.inr (Or.inl hab.symm)
      · exact Or.inr (Or.inr hab.symm)
      · exact (G.irrefl hab).elim
    · intro hcond x hgx hxw
      rw [← W_eq_gateVal, hgeval x] at hgx
      obtain ⟨⟨p, hp, hxp⟩, ⟨q, hq, hxq⟩⟩ := hgx
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_eq]
      rcases hcond p hp q hq with h | h | h
      · exact ⟨p, q, h, hxp, hxq⟩
      · exact ⟨p, w, h, hxp, hxw⟩
      · exact ⟨q, w, h, hxq, hxw⟩
  · simp only [BelowF, not_forall] at hg_notB
    obtain ⟨x, hx⟩ := hg_notB
    push Not at hx
    obtain ⟨hgx, hFx⟩ := hx
    rw [← W_eq_gateVal, hgeval x] at hgx
    obtain ⟨⟨p, hp, hxp⟩, ⟨q, hq, hxq⟩⟩ := hgx
    refine ⟨p, hp, q, hq, fun hadj => hFx ?_⟩
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨p, q, hadj, hxp, hxq⟩
lemma lam_has_center {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (h : ℕ) (hh : h ∈ lam G C) :
    ∃ c : Fin n, ∀ u ∈ orIn n C (n + h), G.Adj c u ∧ s(c, u) ∈ starEdges G C := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  simp only [lam, Finset.mem_filter] at hh
  obtain ⟨_, _, _, a, ha, b, hcard1, hreach⟩ := hh
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcard1
  refine ⟨c, fun u hu => ?_⟩
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  have hreach_orR := orReaches_orR n C (opnd C a b) (by have := opnd_lt' hA a ha.1 b; omega) h hreach
  have hhu : OrR n C (n + h) u.val := (mem_orIn n C hA (n + h) (by
    have hlt := orR_le n C hA _ _ hreach_orR
    have := opnd_lt' hA a ha.1 b
    omega) u).mp hu
  have hu_side : u ∈ side (n := n) C a b :=
    (mem_orIn n C hA (opnd C a b) (by have := opnd_lt' hA a ha.1 b; omega) u).mpr
      (hreach_orR.trans hhu)
  have hc_side : c ∈ side (n := n) C a (1 - b) := by rw [hc]; simp
  have hadj : G.Adj c u := by
    have hr_c := (mem_orIn n C hA (opnd C a (1 - b))
      (by have := opnd_lt' hA a ha.1 (1 - b); omega) c).mp hc_side
    have hr_u := (mem_orIn n C hA (opnd C a b)
      (by have := opnd_lt' hA a ha.1 b; omega) u).mp hu_side
    have hpair : W n C (pairInput c u) (n + a) = true := by
      have h0 : W n C (pairInput c u) (opnd C a b) = true :=
        orR_mono n C hA _ _ _ hr_u (by rw [M1528.P1.S98.W_input n C _ u.val u.isLt]; simp [pairInput])
      have h1 : W n C (pairInput c u) (opnd C a (1 - b)) = true :=
        orR_mono n C hA _ _ _ hr_c (by rw [M1528.P1.S98.W_input n C _ c.val c.isLt]; simp [pairInput])
      rw [W_and n C _ a ha.1 ha.2.1 (opnd C a 0) (opnd C a 1) (opnd_eq n C hA a ha.1)
        (opnd_lt' hA a ha.1 0) (opnd_lt' hA a ha.1 1), Bool.and_eq_true]
      fin_cases b <;> simp_all
    have hF := ha.2.2 (pairInput c u) hpair
    rwa [graphFun_pair] at hF
  have hstar : s(c, u) ∈ starEdges G C := by
    simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
    refine ⟨a, by simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]; exact ha, ?_⟩
    fin_cases b
    · exact ⟨(u, c), ⟨hu_side, by simpa using hc_side⟩, Sym2.eq_swap⟩
    · exact ⟨(c, u), ⟨by simpa using hc_side, hu_side⟩, rfl⟩
  exact ⟨hadj, hstar⟩
lemma lam_card_le_one_of_common_nbr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (C : Circuit) (hL : IsLeastAO G C)
    (z : Fin n) (T : Finset (Fin n))
    (hadj : ∀ u ∈ T, G.Adj z u)
    (hnotStar : ∀ u v, u ∈ T → v ∈ T → u ≠ v → s(z, u) ∉ starEdges G C ∨ s(z, v) ∉ starEdges G C)
    (h : ℕ) (hh : h ∈ lam G C) :
    ((orIn n C (n + h)) ∩ T).card ≤ 1 := by
  obtain ⟨c, hc⟩ := lam_has_center G C hL h hh
  refine Finset.card_le_one.mpr fun u hu v hv => ?_
  by_contra hne
  have hu1 := (Finset.mem_inter.mp hu).1
  have huT := (Finset.mem_inter.mp hu).2
  have hv1 := (Finset.mem_inter.mp hv).1
  have hvT := (Finset.mem_inter.mp hv).2
  have hcz : c = z := by
    by_contra hcz_ne
    exact nfc n G h4 c u z v hcz_ne hne
      ⟨(hc u hu1).1, (hadj u huT).symm, hadj v hvT, (hc v hv1).1.symm⟩
  subst hcz
  rcases hnotStar u v huT hvT hne with hns | hns
  · exact hns (hc u hu1).2
  · exact hns (hc v hv1).2
lemma pure_or_gate_in_orN_not_mixing {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (w : ℕ) (hw : w < n + C.gates.length)
    (hnoAnd : ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C w (n + h))
    (k : ℕ) (hk : k < C.gates.length) (hkop : (gateAt C k).op = GateOp.or)
    (hr : OrR n C w (n + k)) :
    k ∈ orN G C ∧ k ∉ mixing G C := by
  have hA : AO n C := AO_of_IsAO2 n C hL.1
  have hk_noAnd : ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C (n + k) (n + h) :=
    fun h hh hop hkr => hnoAnd h hh hop (hr.trans hkr)
  have hkne : (orIn n C (n + k)).Nonempty := (pure_or_wire_eval C hA (n + k) (by omega) hk_noAnd).1
  have hnotB : ¬ BelowF G C k := by
    intro hB
    obtain ⟨u, hu⟩ := hkne
    have hWu : W n C (pairInput u u) (n + k) = true :=
      (pure_or_wire_eval C hA (n + k) (by omega) hk_noAnd).2 (pairInput u u) |>.mpr
        ⟨u, hu, by simp [pairInput]⟩
    have hF := hB (pairInput u u) hWu
    rw [graphFun_single_false G u] at hF
    exact Bool.noConfusion hF
  have horN : k ∈ orN G C := by
    simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨hk, hkop, hnotB⟩
  have hnotMix : k ∉ mixing G C := by
    simp only [mixing, Finset.mem_filter, not_and]
    intro _
    have hop_ne : ∀ b : Fin 2, (orIn n C (opnd C k b)).Nonempty := by
      intro b
      have hlt := opnd_lt' hA k hk b
      have hmem : opnd C k b ∈ (gateAt C k).inputs := by
        have := opnd_eq n C hA k hk
        fin_cases b <;> rw [this] <;> simp
      have hstep : OrStep n C (n + k) (opnd C k b) := ⟨k, rfl, hk, hkop, hmem⟩
      exact (pure_or_wire_eval C hA (opnd C k b) (by omega) (fun h hh hop hbr =>
        hk_noAnd h hh hop (Relation.ReflTransGen.head hstep hbr))).1
    have h0 := Finset.nonempty_iff_ne_empty.mp (hop_ne 0)
    have h1 := Finset.nonempty_iff_ne_empty.mp (hop_ne 1)
    simp [h0, h1]
  exact ⟨horN, hnotMix⟩
lemma crossPair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    {a : ℕ} (ha : a ∈ tops G C) {b : Fin 2} {u v : Fin n}
    (hu : u ∈ side C a b) (hv : v ∈ side C a (1-b)) : s(u,v) ∈ starEdges G C := by
  apply Finset.mem_biUnion.mpr
  refine ⟨a, ha, Finset.mem_image.mpr ?_⟩
  fin_cases b
  · exact ⟨(u,v), Finset.mem_product.mpr ⟨hu,hv⟩, rfl⟩
  · exact ⟨(v,u), Finset.mem_product.mpr ⟨hv,hu⟩, Sym2.eq_swap⟩

lemma coverAssemble {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (K X : Finset (Fin n))
    (hK : ∀ e ∈ starEdges G C, ∃ z ∈ K, z ∈ e)
    (hX : ∀ e ∈ Ustar G C, ∃ z ∈ K ∪ X, z ∈ e) :
    PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G (K ∪ X) := by
  intro u v hadj
  have hE : s(u,v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hadj
  have h : ∃ z ∈ K ∪ X, z ∈ s(u,v) := by
    by_cases hs : s(u,v) ∈ starEdges G C
    · obtain ⟨z,hz,he⟩ := hK _ hs
      exact ⟨z, Finset.mem_union_left _ hz, he⟩
    · exact hX _ (Finset.mem_sdiff.mpr ⟨hE,hs⟩)
  obtain ⟨z,hz,he⟩ := h
  rcases Sym2.mem_iff.mp he with rfl | rfl
  · exact Or.inl hz
  · exact Or.inr hz

lemma bothStar {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hA : AO n C) (h4 : NoFourCycle G) {a : ℕ}
    (ha : a ∈ tops G C \ centreless G C) :
    ∃ b : Fin 2, ∃ u : Fin n, side C a b = {u} := by
  have ht := (Finset.mem_sdiff.mp ha).1
  obtain ⟨hl, ho, hb⟩ : a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
    simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ht
  have hn : ∀ b : Fin 2, (side (n := n) C a b).Nonempty := by
    intro b
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    apply (Finset.mem_sdiff.mp ha).2
    refine Finset.mem_filter.mpr ⟨ht, ?_⟩
    fin_cases b
    · exact Or.inl he
    · exact Or.inr he
  have hc : ∀ u ∈ side C a 0, ∀ v ∈ side C a 1, G.Adj u v := by
    intro u hu v hv
    have h := M1528.P2.sem_adj n C hA a hl ho (opnd C a) (opnd_eq n C hA a hl) u v
      ((mem_orIn n C hA _ (by have := opnd_lt' hA a hl 0; omega) u).mp hu)
      ((mem_orIn n C hA _ (by have := opnd_lt' hA a hl 1; omega) v).mp hv)
    exact (graphFun_pair G u v).mp (hb _ h)
  rcases M1528.P2.biclique_star G (nfc n G h4) (side C a 0) (side C a 1) hc with h | h
  · obtain ⟨u,hu⟩ := Finset.card_eq_one.mp (le_antisymm h (Finset.card_pos.mpr (hn 0)))
    exact ⟨0,u,hu⟩
  · obtain ⟨u,hu⟩ := Finset.card_eq_one.mp (le_antisymm h (Finset.card_pos.mpr (hn 1)))
    exact ⟨1,u,hu⟩

lemma coverSelected {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (centres : ℕ → Fin n)
    (hcentres : ∀ a ∈ tops G C \ centreless G C, ∃ b : Fin 2, side C a b = {centres a}) :
    ∀ e ∈ starEdges G C, ∃ z ∈ (tops G C \ centreless G C).image centres, z ∈ e := by
  intro e he
  obtain ⟨a,ha,hcross⟩ := Finset.mem_biUnion.mp he
  obtain ⟨⟨u,v⟩, huv, rfl⟩ := Finset.mem_image.mp hcross
  obtain ⟨hu,hv⟩ := Finset.mem_product.mp huv
  have has : a ∈ tops G C \ centreless G C := by
    refine Finset.mem_sdiff.mpr ⟨ha, fun hf => ?_⟩
    rcases (Finset.mem_filter.mp hf).2 with h | h
    · rw [h] at hu
      exact Finset.notMem_empty _ hu
    · rw [h] at hv
      exact Finset.notMem_empty _ hv
  refine ⟨centres a, Finset.mem_image.mpr ⟨a,has,rfl⟩, ?_⟩
  obtain ⟨b,hb⟩ := hcentres a has
  fin_cases b
  · change side C a 0 = {centres a} at hb
    change u ∈ side C a 0 at hu
    rw [hb, Finset.mem_singleton] at hu
    exact hu ▸ Sym2.mem_mk_left u v
  · change side C a 1 = {centres a} at hb
    change v ∈ side C a 1 at hv
    rw [hb, Finset.mem_singleton] at hv
    exact hv ▸ Sym2.mem_mk_right u v

lemma ntMixSubset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    mixing G C ⊆ orN G C \ lam G C := by
  intro h hm
  obtain ⟨hor, hx⟩ := Finset.mem_filter.mp hm
  refine Finset.mem_sdiff.mpr ⟨hor, fun hl => ?_⟩
  obtain ⟨_,h0,h1,_⟩ := Finset.mem_filter.mp hl
  exact hx (propext ⟨fun h => (h0.ne_empty h).elim, fun h => (h1.ne_empty h).elim⟩)

-- Count only OR gates whose support contains at least two selected leaves.
noncomputable def pureBudget {n : ℕ} (C : Circuit)
    (R : Finset ℕ) (T : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun h =>
    (gateAt C h).op = GateOp.or ∧ 1 < (orIn n C (n+h) ∩ T).card ∧
    ∃ r ∈ R, OrR n C r (n+h)

lemma pureBudget_le {n : ℕ} (C : Circuit) (hA : AO n C)
    (R : Finset ℕ) (T : Finset (Fin n))
    (hR : ∀ r ∈ R, r < n + C.gates.length)
    (hno : ∀ r ∈ R, ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C r (n+h))
    (hT : T ⊆ R.biUnion (fun r => orIn n C r)) :
    T.card ≤ R.card + (pureBudget C R T).card := by
  classical
  let B := (Finset.range C.gates.length).filter fun h => (orIn n C (n+h) ∩ T).card ≤ 1
  have hb := or_dag_leaf_bound C hA T B (fun h hh => (Finset.mem_filter.mp hh).2) R hR hno
  rw [Finset.inter_eq_right.mpr hT] at hb
  have hP : ((Finset.range C.gates.length).filter fun h =>
      (gateAt C h).op = GateOp.or ∧ h ∉ B ∧ ∃ r ∈ R, OrR n C r (n+h)) = pureBudget C R T := by
    ext j
    by_cases h : j < C.gates.length <;> simp [pureBudget,B,h]
  rwa [hP] at hb

lemma pureBudget_sub {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (R : Finset ℕ) (T : Finset (Fin n))
    (hR : ∀ r ∈ R, r < n + C.gates.length)
    (hno : ∀ r ∈ R, ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C r (n+h))
    (hlam : ∀ h ∈ lam G C, (orIn n C (n+h) ∩ T).card ≤ 1) :
    pureBudget C R T ⊆ (orN G C \ lam G C) \ mixing G C := by
  classical
  intro h hh
  obtain ⟨hl, ho, hbig, r, hr, hreach⟩ := Finset.mem_filter.mp hh
  obtain ⟨hN, hM⟩ := pure_or_gate_in_orN_not_mixing G C hL r (hR r hr)
    (hno r hr) h (Finset.mem_range.mp hl) ho hreach
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hN, fun hL => (Nat.not_le_of_lt hbig) (hlam h hL)⟩, hM⟩

lemma budgetScoped {n : ℕ} (C : Circuit) (hA : AO n C) {R : Finset ℕ} {T : Finset (Fin n)}
    {h : ℕ} (hh : h ∈ pureBudget C R T) {S : Finset (Fin n)}
    (hR : ∀ r ∈ R, r < n + C.gates.length ∧ orIn n C r ⊆ S) :
    orIn n C (n+h) ⊆ S := by
  classical
  obtain ⟨_,_,_,r,hr,hreach⟩ := Finset.mem_filter.mp hh
  intro u hu
  obtain ⟨hrl,hrs⟩ := hR r hr
  have hhl := orR_le n C hA _ _ hreach
  exact hrs ((mem_orIn n C hA r hrl u).mpr
    (hreach.trans ((mem_orIn n C hA (n+h) (by omega) u).mp hu)))

lemma bigBudget {n : ℕ} (C : Circuit) {R : Finset ℕ} {T : Finset (Fin n)}
    {h : ℕ} (hh : h ∈ pureBudget C R T) : 1 < (orIn n C (n+h)).card := by
  classical
  exact (Finset.mem_filter.mp hh).2.2.1.trans_le (Finset.card_le_card Finset.inter_subset_left)



lemma topProps {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha

lemma topAnd {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hA : AO n C) {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2) (x : Fin n → Bool)
    (hx : W n C x (opnd C a b) = true) (hy : W n C x (opnd C a (1-b)) = true) :
    graphFun G ∅ x = true := by
  obtain ⟨hl,ho,hbel⟩ := topProps ha
  apply hbel
  rw [← W_eq_gateVal, W_and n C x a hl ho (opnd C a 0) (opnd C a 1)
    (opnd_eq n C hA a hl) (opnd_lt' hA a hl 0) (opnd_lt' hA a hl 1), Bool.and_eq_true]
  fin_cases b
  · exact ⟨hx,hy⟩
  · exact ⟨hy,hx⟩

lemma sideImp {n : ℕ} {C : Circuit} (hA : AO n C) {w : ℕ} (hw : w < n + C.gates.length)
    {u : Fin n} {x : Fin n → Bool} (hu : u ∈ orIn n C w) (hx : x u = true) :
    W n C x w = true :=
  orR_mono n C hA x w u.val ((mem_orIn n C hA w hw u).mp hu)
    ((W_input n C x u.val u.isLt).trans hx)

lemma topAdj {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hA : AO n C) {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2) {u v : Fin n}
    (hu : u ∈ side C a b) (hv : v ∈ side C a (1-b)) :
    G.Adj u v := by
  have hl := (topProps ha).1
  exact (graphFun_pair G u v).mp (topAnd hA ha b (pairInput u v)
    (sideImp hA ((opnd_lt' hA a hl b).trans (by omega)) hu (by simp [pairInput]))
    (sideImp hA ((opnd_lt' hA a hl (1-b)).trans (by omega)) hv (by simp [pairInput])))

def mixTarget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (g m : ℕ) (w : Fin n) : Prop :=
  m ∈ mixing G C ∧ n + g ∈ (gateAt C m).inputs ∧
  ∃ a ∈ tops G C \ centreless G C, ∃ b : Fin 2,
    OrReaches n C (opnd C a b) m ∧ OrReaches n C (opnd C a b) g ∧
    w ∈ side C a (1-b) ∧ side (n := n) C a (1-b) ⊆ wmax G C g

def filterTarget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (g : ℕ) (w : Fin n) : Prop :=
  ∃ a ∈ centreless G C, ∃ b : Fin 2,
    opnd C a b = n + g ∧ w ∈ side C a (1-b)



lemma reachableAnd {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    {a j : ℕ} (ha : a ∈ tops G C) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (b : Fin 2) (hr : OrR n C (opnd C a b) (n+j)) : j = g := by
  have hA := AO_of_IsAO2 n C hL.1
  have ha' := (topProps ha).1
  have hl := opnd_lt' hA a ha' b
  have hr' := orR_le n C hA _ _ hr
  have hm : opnd C a b ∈ (gateAt C a).inputs := by
    rw [opnd_eq n C hA a ha']
    fin_cases b <;> simp
  let k := opnd C a b - n
  have hk : opnd C a b = n+k := by dsimp [k]; omega
  have hc : InCone n C j a := by
    rcases orR_cone n C hA j (opnd C a b) hr k hk (by omega) with h | h
    · rw [← h] at hk
      exact M1528.P1.S98.inCone_c1 n C hA j a ha' (hk ▸ hm)
    · exact M1528.P1.S98.inCone_c2 n C hA j k a ha' h (hk ▸ hm)
  exact (junk_single_props G C hL hT g hg).2.2.2.2.2 a ha j hj hop hc

lemma emptyOrIsJunk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hrg : OrR n C (opnd C a b) (n+g)) (he : side (n := n) C a b = ∅) :
    opnd C a b = n+g := by
  have hA := AO_of_IsAO2 n C hL.1
  have hle := orR_le n C hA _ _ hrg
  have hal := (topProps ha).1
  have hl := opnd_lt' hA a hal b
  by_contra hne
  let j := opnd C a b - n
  have hj : opnd C a b = n+j := by dsimp [j]; omega
  have hbound : j < C.gates.length := by omega
  obtain ⟨x,hx⟩ := M1528.P1.S98.least_nodup n C (least_of_isLeastAO G C hL) (n+g) j
    (by omega) hbound
  rw [← hj] at hx
  apply hx
  cases hf : W n C x (n+g)
  · cases hval : W n C x (opnd C a b)
    · rfl
    · obtain ⟨w,hp,hs,hw⟩ := orR_leaf_true n C hA x _ (by omega) hval
      rcases hs with hlt | ⟨k,rfl,hk,hkop⟩
      · have hn : (⟨w,hlt⟩ : Fin n) ∈ side C a b :=
          (mem_orIn n C hA _ (by omega) _).mpr hp
        rw [he] at hn
        exact (Finset.notMem_empty _ hn).elim
      · have hkg := reachableAnd G C hL hT g hg ha hk hkop b hp
        subst k
        rw [hf] at hw
        contradiction
  · exact (orR_mono n C hA x _ _ hrg hf).symm
lemma directInputWitness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    {m a : ℕ} {b : Fin 2} (ha : a ∈ tops G C) (hrm : OrReaches n C (opnd C a b) m)
    (hm_lt : m < C.gates.length) (hmop : (gateAt C m).op = GateOp.or)
    (hgm : n+g ∈ (gateAt C m).inputs) :
    ∃ y ∈ (gateAt C m).inputs, y < n+m ∧ ∃ u ∈ orIn n C y,
      gateVal n C g (pairInput u u) = false ∧
      ∀ a ∈ tops G C, ∀ b : Fin 2, OrReaches n C (opnd C a b) m →
        u ∈ side C a b := by
  have hA := AO_of_IsAO2 n C hL.1
  obtain ⟨_, p, q, hin, hp, hq⟩ := hA m hm_lt
  have hGlt : n+g < n+m := by
    rw [hin] at hgm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgm
    omega
  obtain ⟨y,hy,hylt,hmor⟩ : ∃ y ∈ (gateAt C m).inputs, y < n+m ∧
      ∀ x : Fin n → Bool, W n C x (n+m) = (W n C x (n+g) || W n C x y) := by
    rw [hin] at hgm ⊢
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hgm ⊢
    rcases hgm with h | h
    · exact ⟨q,Or.inr rfl,hq,fun x => (W_or n C x m hm_lt hmop p q hin hp hq).trans (by rw [h])⟩
    · exact ⟨p,Or.inl rfl,hp,fun x => (W_or n C x m hm_lt hmop p q hin hp hq).trans (by rw [h,Bool.or_comm])⟩
  have hx : ∃ x : Fin n → Bool, W n C x (n+m) = true ∧ W n C x (n+g) = false := by
    obtain ⟨x,hx⟩ := M1528.P1.S98.least_nodup n C (least_of_isLeastAO G C hL) (n+g) m hGlt hm_lt
    refine ⟨x,?_⟩
    rw [hmor]
    cases hgx : W n C x (n+g) <;> cases hyx : W n C x y <;> simp_all
  obtain ⟨x,hx,hgx⟩ := hx
  have hxy : W n C x y = true := by simpa only [hmor,hgx,Bool.false_or] using hx
  have hmPath : OrR n C (n+m) y := Relation.ReflTransGen.single ⟨m,rfl,hm_lt,hmop,hy⟩
  obtain ⟨w,hw,hl,hval⟩ := orR_leaf_true n C hA x y (by omega) hxy
  have hlo : ∀ a ∈ tops G C, ∀ b : Fin 2, opnd C a b < n+C.gates.length := by
    intro d hd i
    have hd' := (topProps hd).1
    have := opnd_lt' hA d hd' i
    omega
  rcases hl with hlt | ⟨j,rfl,hj,hjop⟩
  · let u : Fin n := ⟨w,hlt⟩
    have xu : x u = true := by rwa [W_input n C _ _ hlt] at hval
    refine ⟨y,hy,hylt,u,(mem_orIn n C hA _ (by omega) u).mpr hw,?_,?_⟩
    · cases hh : gateVal n C g (pairInput u u)
      · rfl
      · have himp (t : Fin n) (ht : pairInput u u t = true) : x t = true := by
          rcases (pairInput_true u u t).mp ht with rfl | rfl <;> exact xu
        have hp := W_mono_input C hA _ x himp (n+g) (by omega) hh
        exact (Bool.false_ne_true (hgx.symm.trans hp)).elim
    · intro d hd i hmi
      exact (mem_orIn n C hA _ (hlo d hd i) u).mpr
        ((orReaches_orR n C _ (hlo d hd i) _ hmi).trans (hmPath.trans hw))
  · have hjg : j = g := reachableAnd G C hL hT g hg ha hj hjop b
      ((orReaches_orR n C _ (hlo a ha b) _ hrm).trans (hmPath.trans hw))
    subst j
    rw [hgx] at hval
    contradiction





lemma junkWireEmpty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) :
    orIn n C (n+g) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨hgl,hgop,_⟩ := junk_single_props G C hL hT g hg
  have hr := (mem_orIn n C (AO_of_IsAO2 n C hL.1) (n+g) (by omega) u).mp hu
  rcases Relation.ReflTransGen.cases_head hr with he | ⟨_,⟨i,hi,_,hop,_⟩,_⟩
  · have := u.isLt
    omega
  · have hi' : i = g := by omega
    subst i
    rw [hgop] at hop
    contradiction

lemma firstMix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hrg : OrR n C (opnd C a b) (n+g)) (hs : (side (n := n) C a b).Nonempty) :
    ∃ m ∈ mixing G C, OrReaches n C (opnd C a b) m ∧ n+g ∈ (gateAt C m).inputs := by
  have hA := AO_of_IsAO2 n C hL.1
  have ha' := (topProps ha).1
  have hlo := opnd_lt' hA a ha' b
  have hge := junkWireEmpty G C hL hT g hg
  rcases Relation.ReflTransGen.cases_tail hrg with he | ⟨w,hw,hstep⟩
  · change (orIn n C (opnd C a b)).Nonempty at hs
    have he' : opnd C a b = n+g := by omega
    rw [he',hge] at hs
    exact (Finset.not_nonempty_empty hs).elim
  · obtain ⟨m,rfl,hm,hmor,hgm⟩ := hstep
    have hmr := orR_orReaches n C hA m hm (opnd C a b) (by omega) hw
    obtain ⟨y,hy,hylt,u,hu,_,_⟩ := directInputWitness G C hL hT g hg ha hmr hm hmor hgm
    have hye : orIn n C y ≠ ∅ := (show (orIn n C y).Nonempty from ⟨u,hu⟩).ne_empty
    have hyne : y ≠ n+g := fun h => hye (h.symm ▸ hge)
    refine ⟨m,Finset.mem_filter.mpr ⟨?_,?_⟩,hmr,hgm⟩
    · letI : DecidableEq GateOp := gateOpDecEq
      unfold orN gatesWhere
      rw [Finset.mem_filter,Finset.mem_range]
      refine ⟨hm,hmor,fun hB => ?_⟩
      have htrue : W n C (pairInput u u) (n+m) = true :=
        orR_mono n C hA _ _ _ (Relation.ReflTransGen.single ⟨m,rfl,hm,hmor,hy⟩)
          (sideImp hA (by omega) hu (by simp [pairInput]))
      have hh := hB (pairInput u u) htrue
      rw [graphFun_single_false] at hh
      contradiction
    · obtain ⟨_,p,q,hin,_,_⟩ := hA m hm
      have hp : opnd C m 0 = p := by simp [opnd,hin]
      have hq : opnd C m 1 = q := by simp [opnd,hin]
      rw [hp,hq]
      rw [hin] at hgm hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hgm hy
      rcases hgm with hg' | hg' <;> rcases hy with hy' | hy'
      · exact (hyne (hy'.trans hg'.symm)).elim
      · rw [← hg',← hy',hge]
        simp [hye]
      · rw [← hg',← hy',hge]
        simp [hye]
      · exact (hyne (hy'.trans hg'.symm)).elim

lemma mixedWitness {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    {m a : ℕ} {b : Fin 2} (ha : a ∈ tops G C) (hrm : OrReaches n C (opnd C a b) m)
    (hm : m ∈ mixing G C) (hgm : n+g ∈ (gateAt C m).inputs) :
    ∃ u : Fin n, gateVal n C g (pairInput u u) = false ∧
      ∀ a ∈ tops G C, ∀ b : Fin 2, OrReaches n C (opnd C a b) m →
        u ∈ side C a b := by
  have hmdata : m < C.gates.length ∧ (gateAt C m).op = GateOp.or := by
    simp only [mixing,orN,gatesWhere,Finset.mem_filter,Finset.mem_range] at hm
    exact ⟨hm.1.1,hm.1.2.1⟩
  obtain ⟨_,_,_,u,_,hx,hs⟩ :=
    directInputWitness G C hL hT g hg ha hrm hmdata.1 hmdata.2 hgm
  exact ⟨u,hx,hs⟩

lemma residualToward {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    {u v : Fin n} (he : s(u,v) ∈ Ustar G C) :
    (∀ b : Fin 2, u ∈ side C g b ∨ v ∈ side C g b) ∧
    ∃ w ∈ wmax G C g, w ∈ s(u,v) ∧
      (filterTarget G C g w ∨ ∃ m, mixTarget G C g m w) := by
  have hadj := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp he).1
  let x := pairInput u v
  have hA := AO_of_IsAO2 n C hL.1
  have hcalc (z : Fin n → Bool) : W n C z C.output = graphFun G ∅ z := congrFun hL.2.1 z
  have hx : W n C x C.output = true := (hcalc x).trans ((graphFun_pair G u v).mpr hadj)
  have hOut : C.output < n + C.gates.length := by
    by_contra! hh
    rw [W, M1528.P1.S98.getD_ge_length _ _ (by rw [M1528.P1.S98.wires_length]; exact hh)] at hx
    contradiction
  obtain ⟨w,hr,hl,hw⟩ := orR_leaf_true n C hA x C.output hOut hx
  rcases hl with hlt | ⟨a,rfl,ha,hop⟩
  · exfalso
    let t : Fin n := ⟨w,hlt⟩
    have ht : W n C (pairInput t t) w = true := by
      rw [W_input n C _ _ hlt]
      simp [pairInput,t]
    have hout := orR_mono n C hA _ _ _ hr ht
    rw [hcalc,graphFun_single_false] at hout
    contradiction
  have hb : BelowF G C a := by
    intro y hy
    rw [← hcalc]
    exact orR_mono n C hA y _ _ hr hy
  have htop : a ∈ tops G C := by
    simpa only [tops,gatesWhere,Finset.mem_filter,Finset.mem_range] using And.intro ha ⟨hop,hb⟩
  have hbound (i : Fin 2) : opnd C a i < n+C.gates.length := by
    have := opnd_lt' hA a ha i
    omega
  rw [W_and n C x a ha hop (opnd C a 0) (opnd C a 1)
    (opnd_eq n C hA a ha) (opnd_lt' hA a ha 0) (opnd_lt' hA a ha 1), Bool.and_eq_true] at hw
  have trace (i : Fin 2) :
      (∃ z ∈ side C a i, x z = true) ∨
      (OrR n C (opnd C a i) (n+g) ∧ gateVal n C g x = true) := by
    have hi : W n C x (opnd C a i) = true := by
      fin_cases i
      · exact hw.1
      · exact hw.2
    obtain ⟨r,hp,hl,hv⟩ := orR_leaf_true n C hA x _ (hbound i) hi
    rcases hl with hlt | ⟨j,rfl,hj,hjop⟩
    · refine Or.inl ⟨⟨r,hlt⟩,(mem_orIn n C hA _ (hbound i) _).mpr hp,?_⟩
      rwa [W_input n C _ _ hlt] at hv
    · have heq := reachableAnd G C hL hT g hg htop hj hjop i hp
      subst j
      exact Or.inr ⟨hp,hv⟩
  have done (b : Fin 2) (hrg : OrR n C (opnd C a b) (n+g)) (hgx : gateVal n C g x = true)
      (z : Fin n) (hz : z ∈ side C a (1-b)) (hxz : x z = true) :
      ∃ w ∈ wmax G C g, w ∈ s(u,v) ∧
        (filterTarget G C g w ∨ ∃ m, mixTarget G C g m w) := by
    have hset : side (n := n) C a (1-b) ⊆ wmax G C g := by
      intro t ht
      simp only [wmax,Finset.mem_filter,Finset.mem_univ,true_and]
      intro y hgval htval
      exact topAnd hA htop b y (orR_mono n C hA y _ _ hrg hgval) (sideImp hA (hbound (1-b)) ht htval)
    by_cases hc : a ∈ centreless G C
    · have he : side (n := n) C a b = ∅ := by
        rcases M1528.P2.fin2_sub b with ⟨rfl,hopp⟩ | ⟨rfl,hopp⟩
        · rcases (Finset.mem_filter.mp hc).2 with hh | hh
          · exact hh
          · rw [hopp,hh] at hz
            exact (Finset.notMem_empty _ hz).elim
        · rcases (Finset.mem_filter.mp hc).2 with hh | hh
          · rw [hopp,hh] at hz
            exact (Finset.notMem_empty _ hz).elim
          · exact hh
      have hgz := emptyOrIsJunk G C hL hT g hg htop b hrg he
      exact ⟨z,hset hz,Sym2.mem_iff.mpr ((pairInput_true u v z).mp hxz),
        Or.inl ⟨a,hc,b,hgz,hz⟩⟩
    · have hn : (side (n := n) C a b).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hs
        apply hc
        refine Finset.mem_filter.mpr ⟨htop,?_⟩
        fin_cases b
        · exact Or.inl hs
        · exact Or.inr hs
      have hgl := (junk_single_props G C hL hT g hg).1
      have hrg' := orR_orReaches n C hA g hgl _ (hbound b) hrg
      obtain ⟨m,hm,hrm,hgm⟩ := firstMix G C hL hT g hg htop b hrg hn
      exact ⟨z,hset hz,Sym2.mem_iff.mpr ((pairInput_true u v z).mp hxz),
        Or.inr ⟨m,hm,hgm,a,Finset.mem_sdiff.mpr ⟨htop,hc⟩,b,hrm,hrg',hz,hset⟩⟩
  have both (hgtrue : gateVal n C g x = true) :
      ∀ b : Fin 2, u ∈ side C g b ∨ v ∈ side C g b := by
    have hsem := (g_semantics G C hL hT g hg).2.2.1 x
    rw [W_eq_gateVal] at hsem
    obtain ⟨⟨z,hzs,hzx⟩,⟨r,hrs,hrx⟩⟩ := hsem.mp hgtrue
    change pairInput u v z = true at hzx
    change pairInput u v r = true at hrx
    rw [pairInput_true] at hzx hrx
    intro i
    fin_cases i
    · rcases hzx with rfl | rfl
      · exact Or.inl hzs
      · exact Or.inr hzs
    · rcases hrx with rfl | rfl
      · exact Or.inl hrs
      · exact Or.inr hrs
  rcases trace 0 with ⟨y,hy,hyx⟩ | ⟨hyg,hyx⟩ <;> rcases trace 1 with ⟨z,hz,hzx⟩ | ⟨hzg,hzx⟩
  · exfalso
    have hne := (topAdj hA htop 0 hy hz).ne
    change pairInput u v y = true at hyx
    change pairInput u v z = true at hzx
    rw [pairInput_true] at hyx hzx
    apply (Finset.mem_sdiff.mp he).2
    rcases hyx with rfl | rfl <;> rcases hzx with rfl | rfl
    · exact (hne rfl).elim
    · exact crossPair G C htop (b := 0) hy hz
    · rw [Sym2.eq_swap]
      exact crossPair G C htop (b := 0) hy hz
    · exact (hne rfl).elim
  · exact ⟨both hzx,done 1 hzg hzx y hy hyx⟩
  · exact ⟨both hyx,done 0 hyg hyx z hz hzx⟩
  · exact ((junk_single_props G C hL hT g hg).2.2.1 (fun y hgy =>
      topAnd hA htop 0 y (orR_mono n C hA y _ _ hyg hgy) (orR_mono n C hA y _ _ hzg hgy))).elim


lemma notTwoCommon {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h4 : NoFourCycle G) {a b v w : Fin n} (hab : a ≠ b) (hvw : v ≠ w)
    (hav : G.Adj a v) (hbv : G.Adj b v) (haw : G.Adj a w) (hbw : G.Adj b w) : False :=
  hvw (Finset.card_le_one.mp (h4 a b hab) v (by simp [hav,hbv]) w (by simp [haw,hbw]))

lemma mixedTargetUnique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) {v : Fin n}
    (hv0 : v ∈ side C g 0) (hv1 : v ∈ side C g 1) {m : ℕ} {x y : Fin n}
    (hx : mixTarget G C g m x) (hy : mixTarget G C g m y) :
    x = y := by
  obtain ⟨hm,hgm,a,ha,b,hmb,_,hxs,hxW⟩ := hx
  obtain ⟨_,_,a',ha',b',hmb',_,hys,hyW⟩ := hy
  obtain ⟨u,huf,hux⟩ := mixedWitness G C hL hT g hg (Finset.mem_sdiff.mp ha).1 hmb hm hgm
  have hA := AO_of_IsAO2 n C hL.1
  have hs := g_semantics G C hL hT g hg
  have hne : u ≠ v := by
    rintro rfl
    have hgv := (hs.2.2.1 (pairInput u u)).mpr
      ⟨⟨u,hv0,by simp [pairInput]⟩,⟨u,hv1,by simp [pairInput]⟩⟩
    rw [W_eq_gateVal,huf] at hgv
    contradiction
  have hvW := (thm_1529 n G h4 _ _ _ hs.2.2.2.1).2.2.1
    v (Finset.mem_inter.mpr ⟨hv0,hv1⟩)
  by_contra hxy
  exact notTwoCommon h4 hne hxy
    (topAdj hA (Finset.mem_sdiff.mp ha).1 b (hux a (Finset.mem_sdiff.mp ha).1 b hmb) hxs) (hvW x (hxW hxs))
    (topAdj hA (Finset.mem_sdiff.mp ha').1 b' (hux a' (Finset.mem_sdiff.mp ha').1 b' hmb') hys) (hvW y (hyW hys))

lemma mixedForcesCentre {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) {v : Fin n}
    (hv0 : v ∈ side C g 0) (hv1 : v ∈ side C g 1)
    {a m : ℕ} {b : Fin 2} {w : Fin n} (ha : a ∈ tops G C \ centreless G C)
    (hm : m ∈ mixing G C) (hgm : n + g ∈ (gateAt C m).inputs)
    (hrm : OrReaches n C (opnd C a b) m) (hrg : OrReaches n C (opnd C a b) g)
    (hw : w ∈ side C a (1-b)) (hs : side (n := n) C a (1-b) ⊆ wmax G C g) :
    side C a (1-b) = {w} := by
  ext x
  rw [Finset.mem_singleton]
  refine ⟨fun hx => ?_, fun h => h.symm ▸ hw⟩
  exact mixedTargetUnique G C h4 hE hL hT g hg hv0 hv1
    ⟨hm,hgm,a,ha,b,hrm,hrg,hx,hs⟩ ⟨hm,hgm,a,ha,b,hrm,hrg,hw,hs⟩



lemma filterWireUnique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    {a : ℕ} (ha : a ∈ tops G C) {b d : Fin 2}
    (hb : opnd C a b = n+g) (hd : opnd C a d = n+g) : b = d := by
  by_contra hne
  have hd' : d = 1-b := M1528.P2.fin2_ne b d (Ne.symm hne)
  subst d
  exact (junk_single_props G C hL hT g hg).2.2.1 (fun x hx =>
    topAnd (AO_of_IsAO2 n C hL.1) ha b x (by rwa [hb]) (by rwa [hd]))

noncomputable def filterRoots {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) : Finset ℕ :=
  (centreless G C).biUnion fun a =>
    ((Finset.univ : Finset (Fin 2)).filter fun b => opnd C a b = n + g).image fun b => opnd C a (1-b)

lemma filterRootsCard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) :
    (filterRoots G C g).card ≤ (centreless G C).card := by
  unfold filterRoots
  refine Finset.card_biUnion_le.trans ?_
  trans ∑ _a ∈ centreless G C, (1 : ℕ)
  · refine Finset.sum_le_sum fun a ha => Finset.card_image_le.trans (Finset.card_le_one.mpr ?_)
    intro x hx y hy
    exact filterWireUnique G C hL hT g hg (Finset.mem_filter.mp ha).1
      (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2
  · simp

lemma filterRootsData {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) {r : ℕ}
    (hr : r ∈ filterRoots G C g) :
    r < n + C.gates.length ∧ orIn n C r ⊆ wmax G C g ∧
    (∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C r (n+h)) := by
  obtain ⟨a,ha,hr⟩ := Finset.mem_biUnion.mp hr
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hr
  have hb := (Finset.mem_filter.mp hb).2
  have ht := (Finset.mem_filter.mp ha).1
  have hl := (topProps ht).1
  have hA := AO_of_IsAO2 n C hL.1
  have hlt := opnd_lt' hA a hl (1-b)
  refine ⟨by omega,?_,?_⟩
  · intro w hw
    simp only [wmax,Finset.mem_filter,Finset.mem_univ,true_and]
    intro x hx hwx
    exact topAnd hA ht b x (by rwa [hb]) (sideImp hA (by omega) hw hwx)
  · intro h hh hop hpath
    have hhg := reachableAnd G C hL hT g hg ht hh hop (1-b) hpath
    subst h
    exact (junk_single_props G C hL hT g hg).2.2.1 (fun x hx =>
      topAnd hA ht b x (by rwa [hb]) (orR_mono n C hA x _ _ hpath hx))
lemma filterTarget_leaves {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (g : ℕ) {w : Fin n} (hw : filterTarget G C g w) :
    w ∈ (filterRoots G C g).biUnion (fun r => orIn n C r) := by
  obtain ⟨a,ha,b,hb,hw⟩ := hw
  exact Finset.mem_biUnion.mpr ⟨opnd C a (1-b), Finset.mem_biUnion.mpr
    ⟨a,ha,Finset.mem_image.mpr ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,rfl⟩⟩,hw⟩

lemma residualLamBound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (v : Fin n) (T : Finset (Fin n))
    (hadj : ∀ x ∈ T, G.Adj v x) (hpair : ∀ x y, x ∈ T → y ∈ T → x ≠ y →
      s(v,x) ∈ Ustar G C ∨ s(v,y) ∈ Ustar G C) :
    ∀ h ∈ lam G C, (orIn n C (n+h) ∩ T).card ≤ 1 := by
  apply lam_card_le_one_of_common_nbr G h4 C hL v T hadj
  intro x y hx hy hxy
  rcases hpair x y hx hy hxy with hx' | hy'
  · exact Or.inl (Finset.mem_sdiff.mp hx').2
  · exact Or.inr (Finset.mem_sdiff.mp hy').2

lemma oneRoot {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h4 : NoFourCycle G) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (b : Fin 2) (v : Fin n) (T : Finset (Fin n)) (hsub : T ⊆ side C g b)
    (hadj : ∀ x ∈ T, G.Adj v x)
    (hpair : ∀ x y, x ∈ T → y ∈ T → x ≠ y → s(v,x) ∈ Ustar G C ∨ s(v,y) ∈ Ustar G C) :
    let P := pureBudget C {opnd C g b} T
    T.card ≤ P.card + 1 ∧ P ⊆ (orN G C \ lam G C) \ mixing G C ∧
      ∀ h ∈ P, orIn n C (n+h) ⊆ side C g b := by
  intro P
  have hA := AO_of_IsAO2 n C hL.1
  obtain ⟨hbound,hno⟩ := no_and_in_g_opnd G C hL hT g hg b
  have hl := (junk_single_props G C hL hT g hg).1
  have hR (r : ℕ) (hr : r ∈ ({opnd C g b} : Finset ℕ)) : r < n+C.gates.length := by
    rw [Finset.mem_singleton] at hr
    omega
  have hN (r : ℕ) (hr : r ∈ ({opnd C g b} : Finset ℕ)) :
      ∀ h < C.gates.length, (gateAt C h).op = GateOp.and → ¬ OrR n C r (n+h) := by
    rwa [Finset.mem_singleton.mp hr]
  refine ⟨?_, pureBudget_sub G C hL _ T hR hN (residualLamBound G C h4 hL v T hadj hpair), ?_⟩
  · have hh := pureBudget_le C hA {opnd C g b} T hR hN (by simpa only [Finset.singleton_biUnion,side] using hsub)
    simpa [P,Nat.add_comm] using hh
  · intro h hh
    exact budgetScoped C hA hh (fun r hr => ⟨hR r hr, by rw [Finset.mem_singleton.mp hr]; exact Finset.Subset.rfl⟩)

lemma filterBudget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) (v : Fin n)
    (T : Finset (Fin n)) (he : ∀ w ∈ T, s(v,w) ∈ Ustar G C)
    (hcert : ∀ w ∈ T, filterTarget G C g w ∨ ∃ m, mixTarget G C g m w)
    (hv0 : v ∈ side C g 0) (hv1 : v ∈ side C g 1) :
    ∃ P ⊆ (orN G C \ lam G C) \ mixing G C,
      T.card ≤ P.card + (centreless G C).card + (mixing G C).card ∧
      ∀ h ∈ P, 1 < (orIn n C (n+h)).card ∧ orIn n C (n+h) ⊆ wmax G C g := by
  classical
  have hA := AO_of_IsAO2 n C hL.1
  let S := T.filter (filterTarget G C g)
  let R := filterRoots G C g
  let P := pureBudget C R S
  have hR r (hr : r ∈ R) := filterRootsData G C hE hL hT g hg hr
  have hR' r (hr : r ∈ R) := (hR r hr).1
  have hN r (hr : r ∈ R) := (hR r hr).2.2
  have hSE : ∀ w ∈ S, s(v,w) ∈ Ustar G C := fun w hw => he w (Finset.mem_filter.mp hw).1
  have ha : ∀ w ∈ S, G.Adj v w := fun w hw =>
    SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hSE w hw)).1
  have hcut := residualLamBound G C h4 hL v S ha (fun x _ hx _ _ => Or.inl (hSE x hx))
  have hp := pureBudget_sub G C hL R S hR' hN hcut
  have hc := pureBudget_le C hA R S hR' hN
    (fun w hw => filterTarget_leaves G C g (Finset.mem_filter.mp hw).2)
  have hc' := filterRootsCard G C hL hT g hg
  have hmex (w : Fin n) (hw : w ∈ T \ S) : ∃ m, mixTarget G C g m w := by
    obtain ⟨hwT,hwS⟩ := Finset.mem_sdiff.mp hw
    exact (hcert w hwT).resolve_left (fun hf => hwS (Finset.mem_filter.mpr ⟨hwT,hf⟩))
  have hmc : (T \ S).card ≤ (mixing G C).card := by
    let f (w : Fin n) := if h : w ∈ T \ S then (hmex w h).choose else 0
    refine Finset.card_le_card_of_injOn f ?_ ?_
    · intro w hw
      change f w ∈ mixing G C
      rw [show f w = (hmex w hw).choose by dsimp only [f]; split_ifs <;> first | rfl | contradiction]
      exact (hmex w hw).choose_spec.1
    · intro w hw z hz heq
      have hf (w : Fin n) (hw : w ∈ T \ S) : f w = (hmex w hw).choose := by
        dsimp only [f]; split_ifs <;> first | rfl | contradiction
      rw [hf w hw,hf z hz] at heq
      exact mixedTargetUnique G C h4 hE hL hT g hg hv0 hv1
        (hmex w hw).choose_spec (heq.symm ▸ (hmex z hz).choose_spec)
  have hsplit := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (filterTarget G C g) T)
  change (T \ S).card + S.card = T.card at hsplit
  change R.card ≤ (centreless G C).card at hc'
  change S.card ≤ R.card + P.card at hc
  refine ⟨P,hp,by omega,?_⟩
  intro h hh
  exact ⟨bigBudget C hh, budgetScoped C hA hh (fun r hr => ⟨(hR r hr).1,(hR r hr).2.1⟩)⟩



lemma edgeAdj {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {u v : Fin n} (h : s(u,v) ∈ Ustar G C) : G.Adj u v :=
  SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp h).1

lemma reverseEdge {n : ℕ} {E : Finset (Sym2 (Fin n))} {u v : Fin n}
    (h : s(u,v) ∈ E) : s(v,u) ∈ E := Sym2.eq_swap ▸ h

lemma assignCover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hA : AO n C) (h4 : NoFourCycle G) (fallback : Fin n) (X : Finset (Fin n))
    (hU : ∀ e ∈ Ustar G C, ∃ z ∈ X, z ∈ e) :
    ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧
      K.card ≤ (tops G C \ centreless G C).card + X.card := by
  classical
  let f a := if ha : a ∈ tops G C \ centreless G C then
    (bothStar G C hA h4 ha).choose_spec.choose else fallback
  let K := (tops G C \ centreless G C).image f
  have hK : ∀ e ∈ starEdges G C, ∃ z ∈ K, z ∈ e := by
    apply coverSelected G C f
    intro a ha
    exact ⟨(bothStar G C hA h4 ha).choose, by
      have he : f a = (bothStar G C hA h4 ha).choose_spec.choose := by
        dsimp only [f]; split_ifs <;> first | rfl | contradiction
      rw [he]
      exact (bothStar G C hA h4 ha).choose_spec.choose_spec⟩
  refine ⟨K ∪ X, coverAssemble G C K X hK ?_, ?_⟩
  · intro e he
    obtain ⟨z,hz,he⟩ := hU e he
    exact ⟨z,Finset.mem_union_right _ hz,he⟩
  · exact Nat.le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right Finset.card_image_le _)

lemma budgetCombine {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (S : Finset ℕ) (hS : S ⊆ (orN G C \ lam G C) \ mixing G C) :
    S.card + (mixing G C).card ≤ (orN G C \ lam G C).card := by
  rw [← Finset.card_union_of_disjoint (show Disjoint S (mixing G C) from Finset.disjoint_left.mpr (fun i hi hm => (Finset.mem_sdiff.mp (hS hi)).2 hm))]
  exact Finset.card_le_card (Finset.union_subset (hS.trans Finset.sdiff_subset) (ntMixSubset G C))

lemma residualResourcePositive {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) (hU : (Ustar G C).Nonempty) :
    1 ≤ 2 * (centreless G C).card + (mixing G C).card := by
  obtain ⟨e,he⟩ := hU
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨_,w,_,_,hw⟩ := residualToward G C h4 hE hL hT g hg he
    rcases hw with ⟨a,ha,_⟩ | ⟨m,hm,_⟩
    · have := Finset.card_pos.mpr ⟨a,ha⟩
      omega
    · have := Finset.card_pos.mpr ⟨m,hm⟩
      omega

lemma singleStarCase {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) (hU : (Ustar G C).Nonempty)
    (c : Fin n) (b : Fin 2)
    (hs : ∀ e ∈ Ustar G C, ∃ x ∈ side C g b, e = s(c,x)) :
    ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧
      K.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2*(centreless G C).card + 1 + (orN G C \ lam G C).card := by
  let T := (side (n := n) C g b).filter fun x => s(c,x) ∈ Ustar G C
  have he (x : Fin n) (hx : x ∈ T) := (Finset.mem_filter.mp hx).2
  have hu : (Ustar G C).card ≤ T.card := by
    calc
      (Ustar G C).card ≤ (T.image fun x => s(c,x)).card := by
        apply Finset.card_le_card
        intro e hem
        obtain ⟨x,hx,rfl⟩ := hs e hem
        exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hem⟩,rfl⟩
      _ ≤ T.card := Finset.card_image_le
  obtain ⟨hc,hsub,_⟩ := oneRoot G C h4 hL hT g hg b c T
    (Finset.filter_subset _ _) (fun x hx => edgeAdj (he x hx)) (fun x _ hx _ _ => Or.inl (he x hx))
  have hr := residualResourcePositive G C h4 hE hL hT g hg hU
  have hb := budgetCombine G C _ hsub
  obtain ⟨K,hK,hKc⟩ := assignCover G C (AO_of_IsAO2 n C hL.1) h4 c {c} (by
    intro e hem
    obtain ⟨x,_,rfl⟩ := hs e hem
    exact ⟨c,by simp,Sym2.mem_mk_left _ _⟩)
  rw [Finset.card_singleton] at hKc
  exact ⟨K,hK,by omega⟩

lemma scopedDisjoint {n : ℕ} (C : Circuit)
    {R S : Finset ℕ} {T U A B : Finset (Fin n)}
    (hAB : (A ∩ B).card ≤ 1)
    (hA : ∀ h ∈ pureBudget C R T, orIn n C (n+h) ⊆ A)
    (hB : ∀ h ∈ pureBudget C S U, orIn n C (n+h) ⊆ B) :
    Disjoint (pureBudget C R T) (pureBudget C S U) := by
  apply Finset.disjoint_left.mpr
  intro h h1 h2
  exact (Nat.not_le_of_lt (bigBudget C h1))
    ((Finset.card_le_card (Finset.subset_inter (hA h h1) (hB h h2))).trans hAB)



lemma witnessSelected {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) (v : Fin n)
    (hv0 : v ∈ side C g 0) (hv1 : v ∈ side C g 1) (hcl : (centreless G C).card = 0) :
    ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧
      K.card ≤ (tops G C \ centreless G C).card := by
  classical
  let A := tops G C \ centreless G C
  let Cert (a : ℕ) (b : Fin 2) := ∃ m ∈ mixing G C, n+g ∈ (gateAt C m).inputs ∧
    OrReaches n C (opnd C a b) m ∧ OrReaches n C (opnd C a b) g ∧
    (side (n := n) C a (1-b)).Nonempty ∧ side (n := n) C a (1-b) ⊆ wmax G C g
  have hneq (a : ℕ) (ha : a ∈ A) (b d : Fin 2) (hb : Cert a b) (hd : Cert a d) : b = d := by
    by_contra hn
    have hd' := M1528.P2.fin2_ne b d (Ne.symm hn)
    subst d
    obtain ⟨_,_,_,_,hrb,_,_⟩ := hb
    obtain ⟨_,_,_,_,hrd,_,_⟩ := hd
    have hA := AO_of_IsAO2 n C hL.1
    have htop := (Finset.mem_sdiff.mp ha).1
    have hbound (i : Fin 2) : opnd C a i < n+C.gates.length := by
      have hlt := opnd_lt' hA a (topProps htop).1 i
      have hh := (topProps htop).1
      omega
    exact (junk_single_props G C hL hT g hg).2.2.1 (fun x hx =>
      topAnd hA htop b x (orR_mono n C hA x _ _ (orReaches_orR n C _ (hbound b) _ hrb) hx)
        (orR_mono n C hA x _ _ (orReaches_orR n C _ (hbound (1-b)) _ hrd) hx))
  have hsingleton (a : ℕ) (ha : a ∈ A) (b : Fin 2) (hb : Cert a b) :
      ∃ w : Fin n, side C a (1-b) = {w} := by
    obtain ⟨m,hm,hgm,hrm,hrg,⟨w,hw⟩,hs⟩ := hb
    exact ⟨w,mixedForcesCentre G C h4 hE hL hT g hg hv0 hv1 ha hm hgm hrm hrg hw hs⟩
  have hchoose (a : ℕ) (ha : a ∈ A) :
      ∃ w : Fin n, (∃ b : Fin 2, side C a b = {w}) ∧
        ∀ b, Cert a b → side C a (1-b) = {w} := by
    by_cases hh : ∃ b, Cert a b
    · obtain ⟨b,hb⟩ := hh
      obtain ⟨w,hw⟩ := hsingleton a ha b hb
      exact ⟨w,⟨1-b,hw⟩,fun d hd => hneq a ha b d hb hd ▸ hw⟩
    · obtain ⟨b,w,hw⟩ := bothStar G C (AO_of_IsAO2 n C hL.1) h4 ha
      exact ⟨w,⟨b,hw⟩,fun d hd => (hh ⟨d,hd⟩).elim⟩
  let f a := if ha : a ∈ A then (hchoose a ha).choose else v
  have hf (a : ℕ) (ha : a ∈ A) : f a = (hchoose a ha).choose := by
    dsimp only [f]; split_ifs <;> first | rfl | contradiction
  let K := A.image f
  have hK := coverSelected G C f (fun a ha => by
    rw [hf a ha]; exact (hchoose a ha).choose_spec.1)
  have hKU : ∀ e ∈ Ustar G C, ∃ z ∈ K ∪ ∅, z ∈ e := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨_,w,_,hwe,hc⟩ := residualToward G C h4 hE hL hT g hg he
      rcases hc with ⟨a,ha,_⟩ | ⟨m,hm,hgm,a,ha,b,hrm,hrg,hw,hs⟩
      · have := Finset.card_pos.mpr ⟨a,ha⟩
        omega
      · have hh := (hchoose a ha).choose_spec.2 b ⟨m,hm,hgm,hrm,hrg,⟨w,hw⟩,hs⟩
        rw [hh,Finset.mem_singleton] at hw
        rw [← hf a ha] at hw
        subst w
        exact ⟨f a,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩),hwe⟩
  exact ⟨K,by simpa using coverAssemble G C K ∅ hK hKU,Finset.card_image_le⟩

lemma specialTwoCover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hA : AO n C) (h4 : NoFourCycle G) (p q : Fin n)
    (hU : ∀ e ∈ Ustar G C, p ∈ e ∨ q ∈ e)
    (hcan : (∃ a ∈ tops G C \ centreless G C, ∃ b : Fin 2, side C a b = {p} ∨ side C a b = {q}) ∨
      ∃ a ∈ tops G C \ centreless G C, ∃ b : Fin 2, side (n := n) C a b ⊆ {p,q}) :
    ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧
      K.card ≤ (tops G C \ centreless G C).card + 1 := by
  classical
  let A := tops G C \ centreless G C
  have ex (a : ℕ) (ha : a ∈ A) : ∃ w : Fin n, ∃ b : Fin 2, side C a b = {w} := by
    obtain ⟨b,w,hw⟩ := bothStar G C hA h4 ha
    exact ⟨w,b,hw⟩
  let f a := if ha : a ∈ A then (ex a ha).choose else p
  have hf (a : ℕ) (ha : a ∈ A) : ∃ b : Fin 2, side C a b = {f a} := by
    have he : f a = (ex a ha).choose := by dsimp only [f]; split_ifs <;> first | rfl | contradiction
    rw [he]
    exact (ex a ha).choose_spec
  obtain ⟨a,ha,b,hb,hmode⟩ : ∃ a ∈ A, ∃ b : Fin 2, side (n := n) C a b ⊆ {p,q} ∧
      ((∃ z ∈ ({p,q} : Finset (Fin n)), side C a b = {z}) ∨ True) := by
    rcases hcan with ⟨a,ha,b,hb | hb⟩ | ⟨a,ha,b,hb⟩
    · exact ⟨a,ha,b,by simp [hb],Or.inr trivial⟩
    · exact ⟨a,ha,b,by simp [hb],Or.inr trivial⟩
    · exact ⟨a,ha,b,hb,Or.inr trivial⟩
  let K := (A.erase a).image f ∪ {p,q}
  have hK : ∀ e ∈ starEdges G C, ∃ z ∈ K, z ∈ e := by
    intro e he
    obtain ⟨d,hd,hcross⟩ := Finset.mem_biUnion.mp he
    obtain ⟨⟨u,v⟩, huv, rfl⟩ := Finset.mem_image.mp hcross
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp huv
    change u ∈ side C d 0 at hu
    change v ∈ side C d 1 at hv
    have hdA : d ∈ A := by
      refine Finset.mem_sdiff.mpr ⟨hd,fun hc => ?_⟩
      rcases (Finset.mem_filter.mp hc).2 with h | h
      · rw [h] at hu; exact Finset.notMem_empty _ hu
      · rw [h] at hv; exact Finset.notMem_empty _ hv
    by_cases hda : d = a
    · subst d
      fin_cases b
      · exact ⟨u,Finset.mem_union_right _ (hb hu),Sym2.mem_mk_left _ _⟩
      · exact ⟨v,Finset.mem_union_right _ (hb hv),Sym2.mem_mk_right _ _⟩
    · have hfK : f d ∈ K := Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨d,Finset.mem_erase.mpr ⟨hda,hdA⟩,rfl⟩)
      obtain ⟨i,hi⟩ := hf d hdA
      fin_cases i
      · change side C d 0 = {f d} at hi
        rw [hi,Finset.mem_singleton] at hu
        exact ⟨f d,hfK,hu ▸ Sym2.mem_mk_left _ _⟩
      · change side C d 1 = {f d} at hi
        rw [hi,Finset.mem_singleton] at hv
        exact ⟨f d,hfK,hv ▸ Sym2.mem_mk_right _ _⟩
  have hKU : ∀ e ∈ Ustar G C, ∃ z ∈ K ∪ ∅, z ∈ e := by
    intro e he
    rcases hU e he with hh | hh
    · exact ⟨p,by simp [K],hh⟩
    · exact ⟨q,by simp [K],hh⟩
  refine ⟨K,by simpa using coverAssemble G C K ∅ hK hKU,?_⟩
  have hb := (Finset.card_union_le (s := (A.erase a).image f) (t := {p,q})).trans
    (Nat.add_le_add Finset.card_image_le Finset.card_le_two)
  have hcard := Finset.card_erase_add_one ha
  change K.card ≤ A.card + 1
  change K.card ≤ (A.erase a).card + 2 at hb
  omega



lemma residualCases {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (p q : Fin n)
    (hp : ∀ w ∈ wmax G C g, w ∈ side C g 0 → w = p)
    (hq : ∀ w ∈ wmax G C g, w ∈ side C g 1 → w = q)
    {e : Sym2 (Fin n)} (he : e ∈ Ustar G C) :
    (p ∈ wmax G C g ∩ side C g 0 ∧ ∃ y ∈ side C g 1, e = s(p,y)) ∨
    (q ∈ wmax G C g ∩ side C g 1 ∧ ∃ y ∈ side C g 0, e = s(q,y)) ∨
    ∃ w ∈ wmax G C g, ∃ z ∈ side C g 0 ∩ side C g 1,
      (filterTarget G C g w ∨ ∃ m, mixTarget G C g m w) ∧
      w ∉ side C g 0 ∧ w ∉ side C g 1 ∧ e = s(z,w) := by
  have hsem := (g_semantics G C hL hT g hg).2.2.2.1
  have hc := (thm_1530 n G h4 _ _ _ hsem).2.2.1
  induction e using Sym2.ind with
  | _ u v =>
    obtain ⟨hs,w,hw,hm,hcert⟩ := residualToward G C h4 hE hL hT g hg he
    have step (x y : Fin n) (hxy : G.Adj x y) (hW : x ∈ wmax G C g)
        (s0 : x ∈ side C g 0 ∨ y ∈ side C g 0) (s1 : x ∈ side C g 1 ∨ y ∈ side C g 1)
        (hc' : filterTarget G C g x ∨ ∃ m, mixTarget G C g m x) :
        (p ∈ wmax G C g ∩ side C g 0 ∧ ∃ t ∈ side C g 1, s(x,y) = s(p,t)) ∨
        (q ∈ wmax G C g ∩ side C g 1 ∧ ∃ t ∈ side C g 0, s(x,y) = s(q,t)) ∨
        ∃ z ∈ wmax G C g, ∃ t ∈ side C g 0 ∩ side C g 1,
          (filterTarget G C g z ∨ ∃ m, mixTarget G C g m z) ∧ z ∉ side C g 0 ∧ z ∉ side C g 1 ∧ s(x,y)=s(t,z) := by
      obtain ⟨h0,h1,h2⟩ := hc x y hxy s0 s1 hW
      by_cases hx0 : x ∈ side C g 0
      · obtain rfl := hp x hW hx0
        exact Or.inl ⟨Finset.mem_inter.mpr ⟨hW,hx0⟩,y,h0 hx0,rfl⟩
      by_cases hx1 : x ∈ side C g 1
      · obtain rfl := hq x hW hx1
        exact Or.inr (Or.inl ⟨Finset.mem_inter.mpr ⟨hW,hx1⟩,y,h1 hx1,rfl⟩)
      exact Or.inr (Or.inr ⟨x,hW,y,h2 hx0 hx1,hc',hx0,hx1,Sym2.eq_swap⟩)
    rcases Sym2.mem_iff.mp hm with h | h
    · subst w
      exact step u v (edgeAdj he) hw (hs 0) (hs 1) hcert
    · subst w
      exact Sym2.eq_swap ▸ step v u (edgeAdj he).symm hw (hs 0).symm (hs 1).symm hcert

-- If the central edge is residual and there is just one mixing gate,
-- a centred top can be covered by the two residual centres instead of its usual centre.
lemma rareMixCover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (p q x y : Fin n) (hpW : p ∈ wmax G C g ∩ side C g 0) (hqW : q ∈ wmax G C g ∩ side C g 1)
    (hx : x ∈ side C g 0) (hy : y ∈ side C g 1) (hxp : x ≠ p) (hyq : y ≠ q)
    (hxe : s(q,x) ∈ Ustar G C) (hye : s(p,y) ∈ Ustar G C) (hpq : s(p,q) ∈ Ustar G C)
    (hrep0 : ∀ w ∈ wmax G C g, w ∈ side C g 0 → w = p)
    (hrep1 : ∀ w ∈ wmax G C g, w ∈ side C g 1 → w = q)
    (hcl : (centreless G C).card = 0) (hmc : (mixing G C).card ≤ 1)
    (hU : ∀ e ∈ Ustar G C, p ∈ e ∨ q ∈ e) :
    ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧
      K.card ≤ (tops G C \ centreless G C).card + 1 := by
  have hA := AO_of_IsAO2 n C hL.1
  have hps := (Finset.mem_inter.mp hpW).2
  have hqs := (Finset.mem_inter.mp hqW).2
  have hsem := (g_semantics G C hL hT g hg).2.2.2.1
  have cert {a b : Fin n} (he : s(a,b) ∈ Ustar G C)
      (hb : b ∉ wmax G C g) : ∃ m, mixTarget G C g m a := by
    obtain ⟨_,w,hw,hm,hc⟩ := residualToward G C h4 hE hL hT g hg he
    have hwa : w = a := (Sym2.mem_iff.mp hm).resolve_right (fun h => hb (h ▸ hw))
    subst w
    rcases hc with ⟨i,hi,_⟩ | hm
    · have := Finset.card_pos.mpr ⟨i,hi⟩
      omega
    · exact hm
  obtain ⟨m,hm,hgm,a,ha,b,hrm,_,hpb,hpsub⟩ := cert hye (fun h => hyq (hrep1 y h hy))
  obtain ⟨k,hk,_,a',ha',b',hrk,_,hqb,_⟩ := cert hxe (fun h => hxp (hrep0 x h hx))
  have heq := Finset.card_le_one.mp hmc k hk m hm
  subst k
  have hat := (Finset.mem_sdiff.mp ha).1
  have hat' := (Finset.mem_sdiff.mp ha').1
  obtain ⟨u,_,hu⟩ := mixedWitness G C hL hT g hg hat hrm hm hgm
  have hua := hu a hat b hrm
  have hua' := hu a' hat' b' hrk
  have hup := topAdj hA hat b hua hpb
  have huq := topAdj hA hat' b' hua' hqb
  have hux : u ≠ x := fun h => (Finset.mem_sdiff.mp hxe).2
    (reverseEdge (h ▸ crossPair G C hat' hua' hqb))
  have huy : u ≠ y := fun h => (Finset.mem_sdiff.mp hye).2
    (reverseEdge (h ▸ crossPair G C hat hua hpb))
  have hxy : ¬ G.Adj x y := fun h =>
    notTwoCommon h4 hxp hyq.symm (edgeAdj hxe).symm (edgeAdj hpq) h (edgeAdj hye)
  apply specialTwoCover G C hA h4 p q hU
  right
  refine ⟨a,ha,1-b,?_⟩
  intro r hr
  by_cases hrp : r = p
  · simp [hrp]
  by_cases hrq : r = q
  · simp [hrq]
  have hur := topAdj hA hat b hua hr
  rcases (hsem r).mp (hpsub hr) x hx y hy with hh | hh | hh
  · exact (hxy hh).elim
  · exact (notTwoCommon h4 hrq hux hur.symm huq.symm hh.symm (edgeAdj hxe)).elim
  · exact (notTwoCommon h4 hrp huy hur.symm hup.symm hh.symm (edgeAdj hye)).elim



lemma noOverlapCase {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) (hU : (Ustar G C).Nonempty)
    (p q : Fin n)
    (hp : ∀ w ∈ wmax G C g, w ∈ side C g 0 → w = p)
    (hq : ∀ w ∈ wmax G C g, w ∈ side C g 1 → w = q)
    (hd : side (n := n) C g 0 ∩ side C g 1 = ∅) :
    ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧
      K.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2*(centreless G C).card + 1 + (orN G C \ lam G C).card := by
  classical
  let E := Ustar G C
  have hs (e : Sym2 (Fin n)) (he : e ∈ E) :
      (p ∈ wmax G C g ∩ side C g 0 ∧ ∃ y ∈ side C g 1, e = s(p,y)) ∨
      (q ∈ wmax G C g ∩ side C g 1 ∧ ∃ x ∈ side C g 0, e = s(q,x)) := by
    rcases residualCases G C h4 hE hL hT g hg p q hp hq he with h | h | ⟨_,_,z,hz,_⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact (Finset.notMem_empty z (hd ▸ hz)).elim
  by_cases hpAll : ∀ e ∈ E, ∃ y ∈ side C g 1, e = s(p,y)
  · exact singleStarCase G C h4 hE hL hT g hg hU p 1 hpAll
  by_cases hqAll : ∀ e ∈ E, ∃ x ∈ side C g 0, e = s(q,x)
  · exact singleStarCase G C h4 hE hL hT g hg hU q 0 hqAll
  push Not at hpAll hqAll
  obtain ⟨e,he,hno⟩ := hpAll
  obtain ⟨f,hf,hno'⟩ := hqAll
  obtain ⟨hqW,x,hx,rfl⟩ := (hs e he).resolve_left (fun ⟨_,z,hz,heq⟩ => hno z hz heq)
  obtain ⟨hpW,y,hy,rfl⟩ := (hs f hf).resolve_right (fun ⟨_,z,hz,heq⟩ => hno' z hz heq)
  have hps := (Finset.mem_inter.mp hpW).2
  have hqs := (Finset.mem_inter.mp hqW).2
  have hxp : x ≠ p := fun h => hno q hqs (by rw [h,Sym2.eq_swap])
  have hyq : y ≠ q := fun h => hno' p hps (by rw [h,Sym2.eq_swap])
  have hsem := (g_semantics G C hL hT g hg).2.2.2.1
  have hpfill : ∀ z ∈ side C g 1, G.Adj p z :=
    (thm_1529 n G h4 _ _ _ hsem).1 p (Finset.mem_inter.mp hpW).1 hps |>.2
  have hqfill : ∀ z ∈ side C g 0, G.Adj q z :=
    (thm_1529 n G h4 _ _ _ hsem).2.1 q (Finset.mem_inter.mp hqW).1 hqs |>.2
  let X := (side (n := n) C g 0).filter fun z => s(q,z) ∈ E ∧ z ≠ p
  let Y := (side (n := n) C g 1).filter fun z => s(p,z) ∈ E
  let T := insert p X
  let V := insert q Y
  have hxE (z : Fin n) (hz : z ∈ X) := (Finset.mem_filter.mp hz).2.1
  have hyE (z : Fin n) (hz : z ∈ Y) := (Finset.mem_filter.mp hz).2
  have hT : T ⊆ side C g 0 := Finset.insert_subset hps (Finset.filter_subset _ _)
  have hV : V ⊆ side C g 1 := Finset.insert_subset hqs (Finset.filter_subset _ _)
  obtain ⟨ht,htsub,htsc⟩ := oneRoot G C h4 hL ‹TopForm G C› g hg 0 q T hT
    (fun z hz => hqfill z (hT hz)) (by
      intro u v hu hv hne
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Or.inr (hxE _ ((Finset.mem_insert.mp hv).resolve_left (Ne.symm hne)))
      · exact Or.inl (hxE _ hu))
  obtain ⟨hv,hvsub,hvsc⟩ := oneRoot G C h4 hL ‹TopForm G C› g hg 1 p V hV
    (fun z hz => hpfill z (hV hz)) (by
      intro u v hu hv hne
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact Or.inr (hyE _ ((Finset.mem_insert.mp hv).resolve_left (Ne.symm hne)))
      · exact Or.inl (hyE _ hu))
  have hid : (side (n := n) C g 0 ∩ side C g 1).card ≤ 1 := by simp [hd]
  have hdisj := scopedDisjoint C hid htsc hvsc
  have hsum := budgetCombine G C _ (Finset.union_subset htsub hvsub)
  rw [Finset.card_union_of_disjoint hdisj] at hsum
  have hpc : T.card = X.card + 1 :=
    Finset.card_insert_of_notMem (fun hh => (Finset.mem_filter.mp hh).2.2 rfl)
  rw [hpc] at ht
  have hyV : Y.card ≤ V.card := Finset.card_le_card (Finset.subset_insert q Y)
  have hcount : E.card ≤ X.card + Y.card := by
    apply (Finset.card_le_card (show E ⊆ (X.image fun z => s(q,z)) ∪ (Y.image fun z => s(p,z)) from ?_)).trans
      (Nat.le_trans (Finset.card_union_le _ _) (Nat.add_le_add Finset.card_image_le Finset.card_image_le))
    intro e he
    rcases hs e he with ⟨_,z,hz,rfl⟩ | ⟨_,z,hz,rfl⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨hz,he⟩,rfl⟩)
    · by_cases hzp : z = p
      · subst z
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨q,Finset.mem_filter.mpr ⟨hqs,reverseEdge he⟩,Sym2.eq_swap⟩)
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨z,Finset.mem_filter.mpr ⟨hz,he,hzp⟩,rfl⟩)
  have hcv (e : Sym2 (Fin n)) (he : e ∈ E) : p ∈ e ∨ q ∈ e := by
    rcases hs e he with ⟨_,z,_,rfl⟩ | ⟨_,z,_,rfl⟩
    · exact Or.inl (Sym2.mem_mk_left _ _)
    · exact Or.inr (Sym2.mem_mk_left _ _)
  obtain ⟨K,hK,hKc⟩ := assignCover G C (AO_of_IsAO2 n C hL.1) h4 p {p,q} (by
    intro e he
    rcases hcv e he with h | h
    · exact ⟨p,by simp,h⟩
    · exact ⟨q,by simp,h⟩)
  have hK2 := hKc.trans (Nat.add_le_add_left Finset.card_le_two _)
  have hpos := residualResourcePositive G C h4 hE hL ‹TopForm G C› g hg hU
  by_cases hcen : s(p,q) ∈ E
  · by_cases hbig : 2 ≤ 2*(centreless G C).card + (mixing G C).card
    · exact ⟨K,hK,by change K.card + E.card ≤ _; omega⟩
    have hzero : (centreless G C).card = 0 := by omega
    have hm : (mixing G C).card ≤ 1 := by omega
    obtain ⟨K',hK',hKc'⟩ := rareMixCover G C h4 hE hL ‹TopForm G C› g hg p q x y hpW hqW
      hx hy hxp hyq he hf hcen hp hq hzero hm hcv
    exact ⟨K',hK',by change K'.card + E.card ≤ _; omega⟩
  · have hvc : V.card = Y.card + 1 :=
      Finset.card_insert_of_notMem (fun hh => hcen (hyE q hh))
    have hYc : Y.card ≤ (pureBudget C {opnd C g 1} V).card := by
      rw [hvc] at hv
      omega
    exact ⟨K,hK,by change K.card + E.card ≤ _; omega⟩



lemma rootWithPad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g})
    (b : Fin 2) (c v : Fin n) (S : Finset (Fin n)) (hv : v ∈ side C g b)
    (hS : S ⊆ side C g b) (hres : ∀ z ∈ S, s(c,z) ∈ Ustar G C)
    (ha : S.Nonempty → G.Adj c v) :
    ∃ P ⊆ (orN G C \ lam G C) \ mixing G C,
      S.card ≤ P.card + (if v ∈ S then 1 else 0) ∧
      ∀ i ∈ P, 1 < (orIn n C (n+i)).card ∧ orIn n C (n+i) ⊆ side C g b := by
  by_cases hn : S.Nonempty
  · let T := insert v S
    have ht : T ⊆ side C g b := Finset.insert_subset hv hS
    have he : ∀ x ∈ T, G.Adj c x := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha hn
      · exact edgeAdj (hres x hx)
    obtain ⟨hb,hsub,hsc⟩ := oneRoot G C h4 hL hT g hg b c T ht he (by
      intro x y hx hy hxy
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inr (hres y ((Finset.mem_insert.mp hy).resolve_left (Ne.symm hxy)))
      · exact Or.inl (hres x hx))
    refine ⟨pureBudget C {opnd C g b} T,hsub,?_,fun i hi => ⟨bigBudget C hi,hsc i hi⟩⟩
    by_cases hvm : v ∈ S
    · rw [ite_eq_left hvm]
      have ht' : T = S := Finset.insert_eq_of_mem hvm
      simpa only [ht'] using hb
    · rw [ite_eq_right hvm]
      have ht' : T.card = S.card + 1 := Finset.card_insert_of_notMem hvm
      omega
  · have hS0 := Finset.not_nonempty_iff_eq_empty.mp hn
    refine ⟨∅, by simp, by simp [hS0],by simp⟩

lemma overlapFilter {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) {v : Fin n}
    (hv0 : v ∈ side C g 0) (hv1 : v ∈ side C g 1) :
    let T := (wmax G C g).filter (fun w => s(v,w) ∈ Ustar G C)
    ∃ P ⊆ (orN G C \ lam G C) \ mixing G C,
      T.card ≤ P.card + (centreless G C).card + (mixing G C).card ∧
      ∀ i ∈ P, 1 < (orIn n C (n+i)).card ∧ orIn n C (n+i) ⊆ wmax G C g := by
  intro T
  have hs := (g_semantics G C hL hT g hg).2.2.2.1
  have hvW := (thm_1529 n G h4 _ _ _ hs).2.2.2.1 v (Finset.mem_inter.mpr ⟨hv0,hv1⟩)
  apply filterBudget G C h4 hE hL hT g hg v T (fun w hw => (Finset.mem_filter.mp hw).2) _ hv0 hv1
  intro w hw
  obtain ⟨_,z,hz,hm,hc⟩ := residualToward G C h4 hE hL hT g hg (Finset.mem_filter.mp hw).2
  rcases Sym2.mem_iff.mp hm with rfl | rfl
  · exact (hvW hz).elim
  · exact hc

lemma overlapSmallSide {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) (v : Fin n)
    (hv0 : v ∈ side C g 0) (hv1 : v ∈ side C g 1) (b : Fin 2) (hb : side C g b = {v}) :
    ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧
      K.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2*(centreless G C).card + 1 + (orN G C \ lam G C).card := by
  let T := (wmax G C g).filter (fun w => s(v,w) ∈ Ustar G C)
  have hs := (g_semantics G C hL hT g hg).2.2.2.1
  have hvW := (thm_1529 n G h4 _ _ _ hs).2.2.2.1 v (Finset.mem_inter.mpr ⟨hv0,hv1⟩)
  have hsplit (e : Sym2 (Fin n)) (he : e ∈ Ustar G C) : ∃ w ∈ T, e = s(v,w) := by
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨hh,w,hw,hm,_⟩ := residualToward G C h4 hE hL hT g hg he
      have ht := hh b
      rw [hb,Finset.mem_singleton,Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · have hwy := (Sym2.mem_iff.mp hm).resolve_left (fun h => hvW (h ▸ hw))
        subst w
        exact ⟨y,Finset.mem_filter.mpr ⟨hw,he⟩,rfl⟩
      · have hwx := (Sym2.mem_iff.mp hm).resolve_right (fun h => hvW (h ▸ hw))
        subst w
        exact ⟨x,Finset.mem_filter.mpr ⟨hw,reverseEdge he⟩,Sym2.eq_swap⟩
  have hc : (Ustar G C).card ≤ T.card := (Finset.card_le_card
    (show Ustar G C ⊆ T.image (fun w => s(v,w)) from by
      intro e he
      obtain ⟨w,hw,rfl⟩ := hsplit e he
      exact Finset.mem_image.mpr ⟨w,hw,rfl⟩)).trans Finset.card_image_le
  obtain ⟨P,hP,hcard,_⟩ := overlapFilter G C h4 hE hL hT g hg hv0 hv1
  change T.card ≤ _ at hcard
  have hsum := budgetCombine G C P hP
  obtain ⟨K,hK,hKc⟩ := assignCover G C (AO_of_IsAO2 n C hL.1) h4 v {v} (by
    intro e he
    obtain ⟨w,_,rfl⟩ := hsplit e he
    exact ⟨v,by simp,Sym2.mem_mk_left _ _⟩)
  rw [Finset.card_singleton] at hKc
  exact ⟨K,hK,by omega⟩



-- Separate edges using internal filter vertices from edges through the common operand vertex.
lemma overlapSingleton {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) (v p q : Fin n)
    (hv0 : v ∈ side C g 0) (hv1 : v ∈ side C g 1)
    (hv : side (n := n) C g 0 ∩ side C g 1 = {v})
    (hp : ∀ w ∈ wmax G C g, w ∈ side C g 0 → w = p)
    (hq : ∀ w ∈ wmax G C g, w ∈ side C g 1 → w = q) :
    ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧
      K.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2*(centreless G C).card + 1 + (orN G C \ lam G C).card := by
  classical
  let A := side (n := n) C g 0
  let B := side (n := n) C g 1
  let E := Ustar G C
  let W' := wmax G C g
  let T := W'.filter (fun w => s(v,w) ∈ E)
  let Z := T.filter (fun w => w ∉ A ∧ w ∉ B)
  let X := A.filter (fun x => s(q,x) ∈ E ∧ q ∈ W' ∩ B ∧ ¬(p ∈ W' ∩ A ∧ x = p))
  let Y := B.filter (fun y => s(p,y) ∈ E ∧ p ∈ W' ∩ A)
  have hsem := (g_semantics G C hL hT g hg).2.2.2.1
  have hi := thm_1529 n G h4 _ _ _ hsem
  have hvA : v ∈ A ∩ B := Finset.mem_inter.mpr ⟨hv0,hv1⟩
  have hvW : v ∉ W' := hi.2.2.2.1 v hvA
  have hcommon : ∀ w ∈ W', G.Adj v w := hi.2.2.1 v hvA
  have hI : (A ∩ B).card ≤ 1 := by change (side (n := n) C g 0 ∩ side C g 1).card ≤ 1; simp [hv]
  have hwq : (W' ∩ B).card ≤ 1 := Finset.card_le_one.mpr (fun x hx y hy =>
    (hq x (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2).trans
      (hq y (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2).symm)
  have hwp : (W' ∩ A).card ≤ 1 := Finset.card_le_one.mpr (fun x hx y hy =>
    (hp x (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2).trans
      (hp y (Finset.mem_inter.mp hy).1 (Finset.mem_inter.mp hy).2).symm)
  have hcases (e : Sym2 (Fin n)) (he : e ∈ E) :
      (∃ x ∈ X, e = s(q,x)) ∨ (∃ y ∈ Y, e = s(p,y)) ∨ (∃ w ∈ Z, e = s(v,w)) := by
    rcases residualCases G C h4 hE hL hT g hg p q hp hq he with
      ⟨hpW,y,hy,rfl⟩ | ⟨hqW,x,hx,rfl⟩ | ⟨w,hw,t,ht,_,hwA,hwB,rfl⟩
    · exact Or.inr (Or.inl ⟨y,Finset.mem_filter.mpr ⟨hy,he,hpW⟩,rfl⟩)
    · by_cases ht : p ∈ W' ∩ A ∧ x = p
      · rcases ht with ⟨hpW,rfl⟩
        exact Or.inr (Or.inl ⟨q,Finset.mem_filter.mpr
          ⟨(Finset.mem_inter.mp hqW).2,reverseEdge he,hpW⟩,Sym2.eq_swap⟩)
      · exact Or.inl ⟨x,Finset.mem_filter.mpr ⟨hx,he,hqW,ht⟩,rfl⟩
    · rw [hv,Finset.mem_singleton] at ht
      subst t
      exact Or.inr (Or.inr ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hw,he⟩,hwA,hwB⟩,rfl⟩)
  have hX (x : Fin n) (hx : x ∈ X) := (Finset.mem_filter.mp hx).2
  have hY (y : Fin n) (hy : y ∈ Y) := (Finset.mem_filter.mp hy).2
  have hpic (h : p ∈ W' ∩ A) : p ∈ T → p ∉ Z := fun _ hz => (Finset.mem_filter.mp hz).2.1 (Finset.mem_inter.mp h).2
  have hqic (h : q ∈ W' ∩ B) : q ∈ T → q ∉ Z := fun _ hz => (Finset.mem_filter.mp hz).2.2 (Finset.mem_inter.mp h).2
  have hsumT : Z.card + (if v ∈ X then 1 else 0) + (if v ∈ Y then 1 else 0) ≤ T.card := by
    have hpT (hy : v ∈ Y) : p ∈ T :=
      Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp (hY v hy).2).1,reverseEdge (hY v hy).1⟩
    have hqT (hx : v ∈ X) : q ∈ T :=
      Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp (hX v hx).2.1).1,reverseEdge (hX v hx).1⟩
    have hzT : Z ⊆ T := Finset.filter_subset _ _
    by_cases hx : v ∈ X <;> by_cases hy : v ∈ Y <;> simp only [hx,hy,ite_true,ite_false,Nat.add_zero]
    · have hpZ := hpic (hY v hy).2 (hpT hy)
      have hqZ := hqic (hX v hx).2.1 (hqT hx)
      have hpq : p ≠ q := by
        intro h
        have hpB := (Finset.mem_inter.mp (hX v hx).2.1).2
        rw [← h] at hpB
        have hh : p ∈ A ∩ B := Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (hY v hy).2).2,hpB⟩
        rw [hv,Finset.mem_singleton] at hh
        exact hvW (hh ▸ (Finset.mem_inter.mp (hY v hy).2).1)
      have hh : insert p (insert q Z) ⊆ T := Finset.insert_subset (hpT hy) (Finset.insert_subset (hqT hx) hzT)
      have hc := Finset.card_le_card hh
      rw [Finset.card_insert_of_notMem (by simp [hpq,hpZ]),Finset.card_insert_of_notMem hqZ] at hc
      exact hc
    · have hh := Finset.card_le_card (Finset.insert_subset (hqT hx) hzT)
      rwa [Finset.card_insert_of_notMem (hqic (hX v hx).2.1 (hqT hx))] at hh
    · have hh := Finset.card_le_card (Finset.insert_subset (hpT hy) hzT)
      rwa [Finset.card_insert_of_notMem (hpic (hY v hy).2 (hpT hy))] at hh
    · exact Finset.card_le_card hzT
  have hcount : E.card ≤ X.card + Y.card + Z.card := by
    refine (Finset.card_le_card (show E ⊆
      ((X.image fun x => s(q,x)) ∪ (Y.image fun y => s(p,y))) ∪ (Z.image fun w => s(v,w)) from ?_)).trans ?_
    · intro e he
      rcases hcases e he with ⟨x,hx,rfl⟩ | ⟨y,hy,rfl⟩ | ⟨w,hw,rfl⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y,hy,rfl⟩))
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w,hw,rfl⟩)
    · exact Nat.le_trans (Finset.card_union_le _ _) (Nat.add_le_add
        (Nat.le_trans (Finset.card_union_le _ _) (Nat.add_le_add Finset.card_image_le Finset.card_image_le))
        Finset.card_image_le)
  obtain ⟨D,hD,hDc,hDs⟩ := rootWithPad G C h4 hL hT g hg 0 q v X hv0
    (Finset.filter_subset _ _) (fun x hx => (hX x hx).1)
    (fun ⟨x,hx⟩ => (hcommon q (Finset.mem_inter.mp (hX x hx).2.1).1).symm)
  obtain ⟨F,hF,hFc,hFs⟩ := rootWithPad G C h4 hL hT g hg 1 p v Y hv1
    (Finset.filter_subset _ _) (fun y hy => (hY y hy).1)
    (fun ⟨y,hy⟩ => (hcommon p (Finset.mem_inter.mp (hY y hy).2).1).symm)
  obtain ⟨L,hLp,hLc,hLs⟩ := overlapFilter G C h4 hE hL hT g hg hv0 hv1
  change T.card ≤ _ at hLc
  have hdis (S R : Finset ℕ) (a b : Finset (Fin n)) (hs : (a ∩ b).card ≤ 1)
      (hp : ∀ i ∈ S, 1 < (orIn n C (n+i)).card ∧ orIn n C (n+i) ⊆ a)
      (hq : ∀ i ∈ R, orIn n C (n+i) ⊆ b) : Disjoint S R := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Nat.not_le_of_lt (hp i hi).1)
      ((Finset.card_le_card (Finset.subset_inter (hp i hi).2 (hq i hj))).trans hs)
  have df := hdis D F A B hI hDs (fun i hi => (hFs i hi).2)
  have dl := hdis D L A W' (by simpa [Finset.inter_comm] using hwp) hDs (fun i hi => (hLs i hi).2)
  have fl := hdis F L B W' (by simpa [Finset.inter_comm] using hwq) hFs (fun i hi => (hLs i hi).2)
  have hcards := budgetCombine G C _ (Finset.union_subset (Finset.union_subset hD hF) hLp)
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨dl,fl⟩),
    Finset.card_union_of_disjoint df] at hcards
  have hbound : E.card ≤ (orN G C \ lam G C).card + (centreless G C).card := by omega
  by_cases hcl : (centreless G C).card = 0
  · obtain ⟨K,hK,hKc⟩ := witnessSelected G C h4 hE hL hT g hg v hv0 hv1 hcl
    exact ⟨K,hK,by change K.card + E.card ≤ _; omega⟩
  have hsmall : ∃ R : Finset (Fin n), R.card ≤ 2 ∧ ∀ e ∈ E, ∃ w ∈ R, w ∈ e := by
    by_cases hz : Z.Nonempty
    · by_cases hx : X.Nonempty
      · by_cases hy : Y.Nonempty
        · obtain ⟨x0,hx0⟩ := hx
          obtain ⟨y0,hy0⟩ := hy
          obtain ⟨w,hw⟩ := hz
          have hqW := (hX x0 hx0).2.1
          have hpW := (hY y0 hy0).2
          have hwm := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).1
          have hwA := (Finset.mem_filter.mp hw).2.1
          have hwB := (Finset.mem_filter.mp hw).2.2
          have hsp : ∀ y ∈ B, G.Adj p y :=
            (hi.1 p (Finset.mem_inter.mp hpW).1 (Finset.mem_inter.mp hpW).2).2
          have hsq : ∀ x ∈ A, G.Adj q x :=
            (hi.2.1 q (Finset.mem_inter.mp hqW).1 (Finset.mem_inter.mp hqW).2).2
          have hh : A ⊆ {p,v} ∨ B ⊆ {q,v} := by
            by_contra! hn
            obtain ⟨x,hx,hxp⟩ := Finset.not_subset.mp hn.1
            obtain ⟨y,hy,hyq⟩ := Finset.not_subset.mp hn.2
            simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hxp hyq
            have hpq := hsp q (Finset.mem_inter.mp hqW).2
            have hnxy : ¬ G.Adj x y := fun h =>
              notTwoCommon h4 hxp.1 (Ne.symm hyq.1) (hsq x hx).symm hpq h (hsp y hy)
            have hnx : ¬ G.Adj x w := fun h =>
              notTwoCommon h4 (fun e : q = w => hwB (e ▸ (Finset.mem_inter.mp hqW).2))
                hxp.2 (hsq x hx) h.symm (hcommon q (Finset.mem_inter.mp hqW).1).symm (hcommon w hwm).symm
            have hny : ¬ G.Adj y w := fun h =>
              notTwoCommon h4 (fun e : p = w => hwA (e ▸ (Finset.mem_inter.mp hpW).2))
                hyq.2 (hsp y hy) h.symm (hcommon p (Finset.mem_inter.mp hpW).1).symm (hcommon w hwm).symm
            exact ((hsem w).mp hwm x hx y hy).elim hnxy (Or.elim · hnx hny)
          rcases hh with hA | hB
          · refine ⟨{p,v},Finset.card_le_two,?_⟩
            intro e he
            rcases hcases e he with ⟨x,hx,rfl⟩ | ⟨y,_,rfl⟩ | ⟨w,_,rfl⟩
            · exact ⟨x,hA (Finset.mem_filter.mp hx).1,Sym2.mem_mk_right _ _⟩
            · exact ⟨p,by simp,Sym2.mem_mk_left _ _⟩
            · exact ⟨v,by simp,Sym2.mem_mk_left _ _⟩
          · refine ⟨{q,v},Finset.card_le_two,?_⟩
            intro e he
            rcases hcases e he with ⟨x,_,rfl⟩ | ⟨y,hy,rfl⟩ | ⟨w,_,rfl⟩
            · exact ⟨q,by simp,Sym2.mem_mk_left _ _⟩
            · exact ⟨y,hB (Finset.mem_filter.mp hy).1,Sym2.mem_mk_right _ _⟩
            · exact ⟨v,by simp,Sym2.mem_mk_left _ _⟩
        · refine ⟨{q,v},Finset.card_le_two,?_⟩
          intro e he
          rcases hcases e he with ⟨x,_,rfl⟩ | ⟨y,hyw,_⟩ | ⟨w,_,rfl⟩
          · exact ⟨q,by simp,Sym2.mem_mk_left _ _⟩
          · exact (hy ⟨y,hyw⟩).elim
          · exact ⟨v,by simp,Sym2.mem_mk_left _ _⟩
      · refine ⟨{p,v},Finset.card_le_two,?_⟩
        intro e he
        rcases hcases e he with ⟨x,hxw,_⟩ | ⟨y,_,rfl⟩ | ⟨w,_,rfl⟩
        · exact (hx ⟨x,hxw⟩).elim
        · exact ⟨p,by simp,Sym2.mem_mk_left _ _⟩
        · exact ⟨v,by simp,Sym2.mem_mk_left _ _⟩
    · refine ⟨{p,q},Finset.card_le_two,?_⟩
      intro e he
      rcases hcases e he with ⟨x,_,rfl⟩ | ⟨y,_,rfl⟩ | ⟨w,hw,_⟩
      · exact ⟨q,by simp,Sym2.mem_mk_left _ _⟩
      · exact ⟨p,by simp,Sym2.mem_mk_left _ _⟩
      · exact (hz ⟨w,hw⟩).elim
  obtain ⟨R,hRc,hR⟩ := hsmall
  obtain ⟨K,hK,hKc⟩ := assignCover G C (AO_of_IsAO2 n C hL.1) h4 v R hR
  exact ⟨K,hK,by change K.card + E.card ≤ _; omega⟩



lemma largeOverlap {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) (hU : (Ustar G C).Nonempty)
    (hI : 2 ≤ (side (n := n) C g 0 ∩ side C g 1).card) :
    ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧
      K.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2*(centreless G C).card + 1 + (orN G C \ lam G C).card := by
  have hs := (g_semantics G C hL hT g hg).2.2.2.1
  have hl := (thm_1529 n G h4 _ _ _ hs).2.2.2.2 hI
  obtain ⟨w,hw⟩ : (wmax G C g).Nonempty := by
    obtain ⟨e,he⟩ := hU
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨_,w,hw,_,_⟩ := residualToward G C h4 hE hL hT g hg he
      exact ⟨w,hw⟩
  have hu (x : Fin n) (hx : x ∈ wmax G C g) : x = w := Finset.card_le_one.mp hl x hx w hw
  have hrep (e : Sym2 (Fin n)) (he : e ∈ Ustar G C) :=
    residualCases G C h4 hE hL hT g hg w w (fun x hx _ => hu x hx) (fun x hx _ => hu x hx) he
  by_cases hw0 : w ∈ side C g 0
  · apply singleStarCase G C h4 hE hL hT g hg hU w 1
    intro e he
    rcases hrep e he with ⟨_,x,hx,rr⟩ | ⟨hm,_⟩ | ⟨u,hU',_,_,_,hn,_,_⟩
    · exact ⟨x,hx,rr⟩
    · exact ((thm_1529 n G h4 _ _ _ hs).1 w hw hw0).1 (Finset.mem_inter.mp hm).2 |>.elim
    · exact (hn ((hu u hU').symm ▸ hw0)).elim
  · apply singleStarCase G C h4 hE hL hT g hg hU w 0
    intro e he
    rcases hrep e he with ⟨hm,_⟩ | ⟨_,x,hx,rr⟩ | ⟨u,hU',x,hx,_,_,_,rr⟩
    · exact (hw0 (Finset.mem_inter.mp hm).2).elim
    · exact ⟨x,hx,rr⟩
    · exact ⟨x,(Finset.mem_inter.mp hx).1,by simpa only [hu u hU'] using rr.trans Sym2.eq_swap⟩

lemma thinSide {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) (hU : (Ustar G C).Nonempty)
    (b : Fin 2) (v : Fin n) (hv : side C g b = {v}) :
    ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧
      K.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2*(centreless G C).card + 1 + (orN G C \ lam G C).card := by
  by_cases hv' : v ∈ side C g (1-b)
  · have hvs : v ∈ side C g b := by simp [hv]
    rcases M1528.P2.fin2_both (fun d => v ∈ side C g d) b hvs hv' with ⟨h0,h1⟩
    exact overlapSmallSide G C h4 hE hL hT g hg v h0 h1 b hv
  · apply singleStarCase G C h4 hE hL hT g hg hU v (1-b)
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨hs,_⟩ := residualToward G C h4 hE hL hT g hg he
      have hh := hs b
      rw [hv,Finset.mem_singleton,Finset.mem_singleton] at hh
      rcases hh with rfl | rfl
      · exact ⟨y,(hs (1-b)).resolve_left hv',rfl⟩
      · exact ⟨x,(hs (1-b)).resolve_right hv',Sym2.eq_swap⟩

lemma finalCover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : NoFourCycle G) (hE : G.edgeFinset.Nonempty) (hL : IsLeastAO G C)
    (hT : TopForm G C) (g : ℕ) (hg : junk G C = {g}) (hU : (Ustar G C).Nonempty) :
    ∃ K : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G K ∧
      K.card + (Ustar G C).card ≤ (tops G C \ centreless G C).card +
        2*(centreless G C).card + 1 + (orN G C \ lam G C).card := by
  classical
  obtain ⟨hP,hQ,_,hW,_⟩ := g_semantics G C hL hT g hg
  by_cases hP' : (side (n := n) C g 0).card ≤ 1
  · obtain ⟨p,hp⟩ := Finset.card_eq_one.mp (le_antisymm hP' (Finset.card_pos.mpr hP))
    exact thinSide G C h4 hE hL hT g hg hU 0 p hp
  by_cases hQ' : (side (n := n) C g 1).card ≤ 1
  · obtain ⟨q,hq⟩ := Finset.card_eq_one.mp (le_antisymm hQ' (Finset.card_pos.mpr hQ))
    exact thinSide G C h4 hE hL hT g hg hU 1 q hq
  let I := side (n := n) C g 0 ∩ side C g 1
  by_cases hBig : 2 ≤ I.card
  · exact largeOverlap G C h4 hE hL hT g hg hU hBig
  obtain ⟨fallback,_⟩ := hP
  have hCard := thm_1530 n G h4 _ _ _ hW
  have rep (b : Fin 2) (h : (wmax G C g ∩ side C g b).card ≤ 1) :
      ∃ z : Fin n, ∀ w ∈ wmax G C g, w ∈ side C g b → w = z := by
    by_cases hn : (wmax G C g ∩ side C g b).Nonempty
    · obtain ⟨z,hz⟩ := hn
      exact ⟨z,fun w hw hs => Finset.card_le_one.mp h w (Finset.mem_inter.mpr ⟨hw,hs⟩) z hz⟩
    · exact ⟨fallback,fun w hw hs => (hn ⟨w,Finset.mem_inter.mpr ⟨hw,hs⟩⟩).elim⟩
  obtain ⟨p,hp⟩ := rep 0 (hCard.1 (by omega))
  obtain ⟨q,hq⟩ := rep 1 (hCard.2.1 (by omega))
  by_cases hne : I.Nonempty
  · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp (le_antisymm (by omega) (Finset.card_pos.mpr hne))
    have hvm : v ∈ I := by rw [hv]; simp
    exact overlapSingleton G C h4 hE hL hT g hg v p q
      (Finset.mem_inter.mp hvm).1 (Finset.mem_inter.mp hvm).2 hv hp hq
  · exact noOverlapCase G C h4 hE hL hT g hg hU p q hp hq (Finset.not_nonempty_iff_eq_empty.mp hne)

end Close
end Source8103

lemma Source8103 :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle x2 → x2.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO x2 x4 → PEqualNP.TopForm.TopForm x2 x4 → (PEqualNP.TopForm.Ustar x2 x4).Nonempty → (PEqualNP.TopForm.junk x2 x4).card = (1 : ℕ) → ∃ (x11 : Finset (Fin x1)), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover x2 x11 ∧ x11.card + (PEqualNP.TopForm.Ustar x2 x4).card ≤ (PEqualNP.TopForm.tops x2 x4 \ PEqualNP.TopForm.centreless x2 x4).card + (2 : ℕ) * (PEqualNP.TopForm.centreless x2 x4).card + (PEqualNP.TopForm.junk x2 x4).card + (PEqualNP.TopForm.orN x2 x4 \ PEqualNP.TopForm.lam x2 x4).card := by
  intro n G _ C h4 hE hL hT hU hj
  obtain ⟨g,hg⟩ := Finset.card_eq_one.mp hj
  rw [hj]
  exact PEqualNP.Outside.L_meta_2373.Source8103.Close.finalCover G C h4 hE hL hT g hg hU

namespace SafeLower
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
lemma one_junk_lower (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) (hj : (junk graph C).card = 1) : 20 ≤ C.size := by
  by_cases hu : Ustar graph C = ∅
  · exact no_uncovered_lower C hl ht hu
  have hU := Finset.nonempty_iff_ne_empty.mpr hu
  obtain ⟨K, hcover, hcharge⟩ := PEqualNP.Outside.L_meta_2373.Source8103
    10 graph C graph_no_four_cycle graph_nonempty hl ht hU hj
  have hc : 6 ≤ K.card := cover_card K (by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hadj : graph.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      rcases hcover u v hadj with hu | hv
      · exact ⟨u, hu, by simp⟩
      · exact ⟨v, hv, by simp⟩)
  have bound := (Source5781.old_main 10 graph C graph_no_four_cycle graph_nonempty hl ht).1
  rw [graph_card] at bound
  omega

lemma at_most_one_junk_lower (C : Circuit) (hl : IsLeastAO graph C)
    (ht : TopForm graph C) (hj : (junk graph C).card ≤ 1) : 20 ≤ C.size := by
  by_cases he : junk graph C = ∅
  · exact safe_and_lower C hl ht he
  · have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
    exact one_junk_lower C hl ht (by omega)

end SafeLower

end PEqualNP.Outside.L_meta_2373
