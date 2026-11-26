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


namespace AndLower.Source635

open PEqualNP.AndCount

abbrev V := Fin 10

def edges : Finset (Sym2 V) := {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0), s(0, 5), s(1, 6), s(2, 7), s(3, 8),
      s(4, 9), s(5, 7), s(6, 8), s(7, 9), s(8, 5), s(9, 6)}

def related (v w : V) : Bool := decide (s(v, w) ∈ edges)

def Good (I : Finset V) : Prop :=
  (∀ v ∈ I, ∀ w ∈ I, related v w = false) ∧
  (∀ u : V, u ∉ I → ∃ v ∈ I, related u v = true)

def center : Fin 6 → V := ![0, 1, 3, 7, 8, 9]

def circuit : AndCountCircuit 10 where
  size := 6
  leftVars i := {center i}
  rightVars i := Finset.univ.filter (fun w => related (center i) w)
  leftGates _ := ∅
  rightGates _ := ∅
  outVars := ∅
  outGates := Finset.univ

lemma covered : ∀ a b : V, related a b = true →
    (∃ i, center i = a) ∨ (∃ i, center i = b) := by decide +kernel

lemma symmetric : ∀ a b : V, related a b = related b a := by decide +kernel

lemma gateEq (I : Finset V) (i : Fin 6) : circuit.gateVal I i = true ↔
    center i ∈ I ∧ ∃ v ∈ I, related (center i) v = true := by
  simp [AndCountCircuit.gateVal, AndCountCircuit.gateValFuel, AndCountCircuit.sideTrue,
    circuit, and_comm]

lemma evalEq (I : Finset V) : circuit.eval I = true ↔
    ∃ a ∈ I, ∃ b ∈ I, related a b = true := by
  rw [AndCountCircuit.eval, decide_eq_true_eq]
  change ((∃ v ∈ (∅ : Finset V), v ∈ I) ∨ ∃ i ∈ (Finset.univ : Finset (Fin 6)),
    circuit.gateVal I i = true) ↔ _
  simp only [Finset.notMem_empty, false_and, exists_const, false_or, Finset.mem_univ,
    true_and, gateEq]
  constructor
  · rintro ⟨i, hi, b, hb, hab⟩
    exact ⟨_, hi, b, hb, hab⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    rcases covered a b hab with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨i, ha, b, hb, hab⟩
    · exact ⟨i, hb, a, ha, (symmetric _ _).trans hab⟩

lemma upper (I : Finset V) (h : Good I) :
    circuit.eval I = false ∧ ∀ u, u ∉ I → circuit.eval (insert u I) = true := by
  constructor
  · apply Bool.eq_false_iff.mpr
    rintro ht
    obtain ⟨a, ha, b, hb, hr⟩ := (evalEq _).mp ht
    simp [h.1 a ha b hb] at hr
  · intro u hu
    obtain ⟨v, hv, hr⟩ := h.2 u hu
    exact (evalEq _).mpr ⟨u, Finset.mem_insert_self .., v, Finset.mem_insert_of_mem hv, hr⟩

lemma good_iff (G : SimpleGraph V) (he : G.edgeSet = {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0), s(0, 5), s(1, 6), s(2, 7), s(3, 8),
      s(4, 9), s(5, 7), s(6, 8), s(7, 9), s(8, 5), s(9, 6)}) (I : Finset V) :
    Good I ↔ (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) ∧ (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) := by
  have hr (v w : V) : related v w = true ↔ G.Adj v w := by
    rw [← SimpleGraph.mem_edgeSet, he]
    simp [related, edges]
  have hn (v w : V) : related v w = false ↔ ¬G.Adj v w := by
    rw [← hr, Bool.eq_false_iff]
  simp only [Good, hn, hr]


def rows : Fin 15 → Finset V := ![{1, 4, 5}, {0, 2, 6}, {3, 5, 6}, {2, 4, 5, 6}, {1, 3, 7}, {0, 3, 6, 7}, {4, 6, 7}, {2, 4, 8}, {0, 7, 8}, {1, 4, 7, 8}, {0, 3, 9}, {2, 5, 9}, {1, 3, 5, 9}, {1, 8, 9}, {0, 2, 8, 9}]

def through : V → Fin 5 → Fin 15 := ![![1, 5, 8, 10, 14],
    ![0, 4, 9, 12, 13],
    ![1, 3, 7, 11, 14],
    ![2, 4, 5, 10, 12],
    ![0, 3, 6, 7, 9],
    ![0, 2, 3, 11, 12],
    ![1, 2, 3, 5, 6],
    ![4, 5, 6, 8, 9],
    ![7, 8, 9, 13, 14],
    ![10, 11, 12, 13, 14]]

lemma rowsGood : ∀ i, Good (rows i) := by
  unfold Good
  decide +kernel

lemma rowContains : ∀ v i, v ∈ rows (through v i) := by decide +kernel

lemma rowDiff : ∀ v i j, i ≠ j → ∃ w ∈ rows (through v i), w ∉ rows (through v j) := by
  decide +kernel

lemma orderedPair : ∀ v w : V, v ≠ w → ∃ i, v ∈ rows i ∧ w ∉ rows i := by decide +kernel

open PEqualNP.AndCount.AndCountCircuit

private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma sideTrue_mono_U {n k : ℕ} {U V : Finset (Fin n)} (hUV : U ⊆ V)
    (B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (hv : ∀ j, j < i → v1 j = true → v2 j = true)
    (hs : sideTrue U B F i v1 = true) :
    sideTrue V B F i v2 = true := by
  unfold sideTrue at hs ⊢
  rw [decide_eq_true_eq] at hs ⊢
  rcases hs with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
  · exact Or.inl ⟨v, hvB, hUV hvU⟩
  · exact Or.inr ⟨j, hjF, hji, hv j hji hvj⟩

private lemma gateValFuel_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel V d i = true := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp [gateValFuel] at hi
  | succ d ih =>
    intro i hi
    simp only [gateValFuel, Bool.and_eq_true] at hi ⊢
    exact ⟨sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.1,
           sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.2⟩

private lemma gateVal_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal V i = true :=
  gateValFuel_mono_U C hUV C.size i h

def Free (C : AndCountCircuit 10) (v : V) : Finset (Fin C.size) :=
  Finset.univ.filter (fun i => v ∉ C.leftVars i ∧ v ∉ C.rightVars i)

def sideL (C : AndCountCircuit 10) (I : Finset V) (i : Fin C.size) : Bool :=
  sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I)

def sideR (C : AndCountCircuit 10) (I : Finset V) (i : Fin C.size) : Bool :=
  sideTrue I (C.rightVars i) (C.rightGates i) i (C.gateVal I)

def Separates (C : AndCountCircuit 10) : Prop :=
  ∀ I, Good I → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true

lemma unionSide (C : AndCountCircuit 10) (U I J B : Finset V)
    (F : Finset (Fin C.size)) (i : Fin C.size) (hU : U ⊆ I ∪ J)
    (ih : ∀ j < i, C.gateVal U j = true → C.gateVal I j = true ∨ C.gateVal J j = true) :
    sideTrue U B F i (C.gateVal U) = true →
    sideTrue I B F i (C.gateVal I) = true ∨ sideTrue J B F i (C.gateVal J) = true := by
  simp only [sideTrue, decide_eq_true_eq]
  rintro (⟨v, hv, hu⟩ | ⟨j, hj, hji, ht⟩)
  · rcases Finset.mem_union.mp (hU hu) with h | h
    · exact Or.inl (Or.inl ⟨v, hv, h⟩)
    · exact Or.inr (Or.inl ⟨v, hv, h⟩)
  · rcases ih j hji ht with h | h
    · exact Or.inl (Or.inr ⟨j, hj, hji, h⟩)
    · exact Or.inr (Or.inr ⟨j, hj, hji, h⟩)

lemma mergeInput (C : AndCountCircuit 10) (I J U : Finset V) (v : V)
    (hi : v ∈ I) (hj : v ∈ J) (hU : U ⊆ I ∪ J)
    (hs : ∀ i ∈ Free C v, sideL C I i = sideL C J i) :
    C.eval U = true → C.eval I = true ∨ C.eval J = true := by
  have gate (i : Fin C.size) : C.gateVal U i = true →
      C.gateVal I i = true ∨ C.gateVal J i = true := by
    induction i using ((wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction) with
    | h i ih =>
      intro ht
      rw [gateVal_unfold, Bool.and_eq_true] at ht
      rw [gateVal_unfold C I, gateVal_unfold C J]
      change (sideL C I i && sideR C I i) = true ∨ (sideL C J i && sideR C J i) = true
      have hl : sideL C I i = true ∨ sideL C J i = true := unionSide C U I J _ _ i hU ih ht.1
      have hr : sideR C I i = true ∨ sideR C J i = true := unionSide C U I J _ _ i hU ih ht.2
      simp only [Bool.and_eq_true]
      by_cases h₁ : v ∈ C.leftVars i
      · have a : sideL C I i = true := decide_eq_true (Or.inl ⟨v, h₁, hi⟩)
        have b : sideL C J i = true := decide_eq_true (Or.inl ⟨v, h₁, hj⟩)
        tauto
      by_cases h₂ : v ∈ C.rightVars i
      · have a : sideR C I i = true := decide_eq_true (Or.inl ⟨v, h₂, hi⟩)
        have b : sideR C J i = true := decide_eq_true (Or.inl ⟨v, h₂, hj⟩)
        tauto
      have hh := hs i (by simp [Free, h₁, h₂])
      rw [hh] at hl ⊢
      tauto
  simp only [eval, decide_eq_true_eq]
  rintro (⟨w, hw, h⟩ | ⟨i, hi', h⟩)
  · rcases Finset.mem_union.mp (hU h) with h | h
    · exact Or.inl (Or.inl ⟨_, hw, h⟩)
    · exact Or.inr (Or.inl ⟨_, hw, h⟩)
  · rcases gate i h with h | h
    · exact Or.inl (Or.inr ⟨i, hi', h⟩)
    · exact Or.inr (Or.inr ⟨i, hi', h⟩)

lemma free_bound (C : AndCountCircuit 10) (h : Separates C) (v : V) :
    3 ≤ (Free C v).card := by
  let code (a : Fin 5) (i : ↥(Free C v)) := sideL C (rows (through v a)) i
  have hinj : Function.Injective code := by
    intro a b hab
    by_contra hne
    obtain ⟨w, hwa, hwb⟩ := rowDiff v a b hne
    let A := rows (through v a)
    let B := rows (through v b)
    have ha := h A (rowsGood _)
    have hb := h B (rowsGood _)
    have he := mergeInput C A B (insert w B) v (rowContains ..) (rowContains ..)
      (Finset.insert_subset (Finset.mem_union_left B hwa) Finset.subset_union_right)
      (fun i hi => congrFun hab ⟨i, hi⟩) (hb.2 w hwb)
    simp [ha.1, hb.1] at he
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hc
  by_contra! hbad
  have hp : 2 ^ (Free C v).card ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

def MaskLe (C : AndCountCircuit 10) (v w : V) : Prop :=
  ∀ i, (v ∈ C.leftVars i → w ∈ C.leftVars i) ∧ (v ∈ C.rightVars i → w ∈ C.rightVars i)

lemma bare_out_empty (C : AndCountCircuit 10) (h : Separates C) (v : V) : v ∉ C.outVars := by
  intro hv
  have he := (h _ (rowsGood (through v 0))).1
  have ht : C.eval (rows (through v 0)) = true :=
    decide_eq_true (Or.inl ⟨v, hv, rowContains v 0⟩)
  simp [he] at ht

lemma sideMasked (I : Finset V) (v w : V) (hw : w ∈ I) (B : Finset V)
    (hp : v ∈ B → w ∈ B) {k : ℕ} (F : Finset (Fin k)) (i : Fin k) (vals : Fin k → Bool) :
    sideTrue (insert v I) B F i vals = sideTrue I B F i vals := by
  unfold sideTrue
  apply decide_eq_decide.mpr
  constructor
  · rintro (⟨u, hu, hi⟩ | h)
    · rcases Finset.mem_insert.mp hi with rfl | hi
      · exact Or.inl ⟨w, hp hu, hw⟩
      · exact Or.inl ⟨u, hu, hi⟩
    · exact Or.inr h
  · rintro (⟨u, hu, hi⟩ | h)
    · exact Or.inl ⟨u, hu, Finset.mem_insert_of_mem hi⟩
    · exact Or.inr h

lemma notMasked (C : AndCountCircuit 10) (h : Separates C) {v w : V} (hne : v ≠ w) :
    ¬ MaskLe C v w := by
  intro hm
  obtain ⟨j, hw, hv⟩ := orderedPair w v hne.symm
  let I := rows j
  have hf (d : ℕ) : C.gateValFuel (insert v I) d = C.gateValFuel I d := by
    induction d with
    | zero => rfl
    | succ d ih =>
      funext i
      simp only [gateValFuel, ih, sideMasked I v w hw _ (hm i).1,
        sideMasked I v w hw _ (hm i).2]
  have a := (h I (rowsGood j)).1
  have b := (h I (rowsGood j)).2 v hv
  rw [eval, decide_eq_true_eq] at b
  rcases b with ⟨u, hu, _⟩ | ⟨i, hi, ht⟩
  · exact bare_out_empty C h u hu
  · rw [gateVal, hf] at ht
    have he : C.eval I = true := decide_eq_true (Or.inr ⟨i, hi, ht⟩)
    simp [a] at he

lemma atLeastFive (C : AndCountCircuit 10) (h : Separates C) : 5 ≤ C.size := by
  classical
  by_contra! hs
  let occ (v : V) := Finset.univ \ Free C v
  have memOcc (i : Fin C.size) (v : V) : i ∈ occ v ↔ v ∈ C.leftVars i ∨ v ∈ C.rightVars i := by
    simp [occ, Free]
    tauto
  have unique (v : V) {i j : Fin C.size} (hi : i ∈ occ v) (hj : j ∈ occ v) : i = j := by
    have ha := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (Free C v))
    have hb := free_bound C h v
    change (occ v).card + _ = _ at ha
    simp only [Finset.card_univ, Fintype.card_fin] at ha
    exact Finset.card_le_one.mp (by omega : (occ v).card ≤ 1) _ hi _ hj
  have occupied (v : V) : ∃ i, i ∈ occ v := by
    by_contra! he
    obtain ⟨w, hw⟩ := exists_ne v
    apply notMasked C h hw.symm
    intro i
    specialize he i
    rw [memOcc, not_or] at he
    exact ⟨fun hv => (he.1 hv).elim, fun hv => (he.2 hv).elim⟩
  choose gate hg using occupied
  let code (v : V) := (gate v, decide (v ∈ C.leftVars (gate v)))
  have inj : Function.Injective code := by
    intro a b heq
    by_contra hne
    have he : gate a = gate b := congrArg Prod.fst heq
    have hl : a ∈ C.leftVars (gate a) ↔ b ∈ C.leftVars (gate a) := by
      have hh := congrArg Prod.snd heq
      change decide (_ ∈ _) = decide (_ ∈ _) at hh
      rw [← he] at hh
      exact decide_eq_decide.mp hh
    have other (v : V) {i : Fin C.size} (hi : i ≠ gate v) :
        v ∉ C.leftVars i ∧ v ∉ C.rightVars i := by
      have hh : i ∉ occ v := fun hm => hi (unique v hm (hg v))
      rwa [memOcc, not_or] at hh
    have comp {x y : V} (hx : gate x = gate y)
        (hlx : x ∈ C.leftVars (gate x) → y ∈ C.leftVars (gate x))
        (hrx : x ∈ C.rightVars (gate x) → y ∈ C.rightVars (gate x)) : MaskLe C x y := by
      intro i
      by_cases hi : i = gate x
      · simpa [hi] using And.intro hlx hrx
      · exact ⟨fun h' => ((other x hi).1 h').elim, fun h' => ((other x hi).2 h').elim⟩
    by_cases hr : b ∈ C.rightVars (gate a)
    · exact notMasked C h hne (comp he hl.mp (fun _ => hr))
    · apply notMasked C h (Ne.symm hne)
      apply comp he.symm <;> rw [← he]
      · exact hl.mpr
      · exact fun h' => (hr h').elim
  have hc := Fintype.card_le_of_injective _ inj
  simp [V, Fintype.card_prod] at hc
  omega

lemma jointlyPresent : ∀ a b : V, related a b = false → ∃ i, a ∈ rows i ∧ b ∈ rows i := by
  decide +kernel

lemma noSquare : ∀ a b c d : V, related a c = true → related a d = true →
    related b c = true → related b d = true → a = b ∨ c = d := by decide +kernel

lemma isolatedEdge : ∀ a b : V, related a b = true → ∃ i, a ∉ rows i ∧
    ∀ x ∈ insert a (rows i), ∀ y ∈ insert a (rows i), related x y = true →
      (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by decide +kernel

set_option maxHeartbeats 2000000 in
lemma largeHasEdge : ∀ I : Finset V, 5 ≤ I.card → ∃ x ∈ I, ∃ y ∈ I, related x y = true := by
  decide +kernel

lemma starCenter (L R : Finset V) (h : ∀ a ∈ L, ∀ b ∈ R, related a b = true) :
    ∃ t : V, ∀ a ∈ L, ∀ b ∈ R, a = t ∨ b = t := by
  rcases L.eq_empty_or_nonempty with he | ⟨a, ha⟩
  · exact ⟨0, by simp [he]⟩
  rcases R.eq_empty_or_nonempty with he | ⟨b, hb⟩
  · exact ⟨0, by simp [he]⟩
  by_cases hl : ∀ x ∈ L, x = a
  · exact ⟨a, fun x hx _ _ => Or.inl (hl x hx)⟩
  push Not at hl
  obtain ⟨x, hx, hn⟩ := hl
  exact ⟨b, fun _ _ y hy => Or.inr ((noSquare x a y b
    (h x hx y hy) (h x hx b hb) (h a ha y hy) (h a ha b hb)).resolve_left hn)⟩

lemma firstTrue (C : AndCountCircuit 10) (h : Separates C) (U : Finset V) (hu : C.eval U = true) :
    ∃ i, (∃ a ∈ C.leftVars i, a ∈ U) ∧ (∃ b ∈ C.rightVars i, b ∈ U) := by
  by_contra hn
  have hz (d : ℕ) (i : Fin C.size) : C.gateValFuel U d i = false := by
    induction d generalizing i with
    | zero => rfl
    | succ d ih =>
      apply Bool.eq_false_iff.mpr
      simp only [gateValFuel, sideTrue, ih, Bool.false_eq_true,
        and_false, exists_false, or_false]
      exact fun ht => hn ⟨i, by simpa only [Bool.and_eq_true, decide_eq_true_eq] using ht⟩
  rw [eval, decide_eq_true_eq] at hu
  rcases hu with ⟨v, hv, _⟩ | ⟨i, _, ht⟩
  · exact bare_out_empty C h v hv
  · simp [gateVal, hz] at ht

lemma safe_bound (C : AndCountCircuit 10) (h : Separates C)
    (safe : ∀ i j, C.gateVal (rows j) i = false) : 6 ≤ C.size := by
  classical
  have rect (i : Fin C.size) (a : V) (ha : a ∈ C.leftVars i) (b : V) (hb : b ∈ C.rightVars i) :
      related a b = true := by
    by_contra! hn
    obtain ⟨j, hja, hjb⟩ := jointlyPresent a b (Bool.eq_false_iff.mpr hn)
    have ht : C.gateVal (rows j) i = true := by
      rw [gateVal_unfold, Bool.and_eq_true]
      exact ⟨decide_eq_true (Or.inl ⟨a, ha, hja⟩), decide_eq_true (Or.inl ⟨b, hb, hjb⟩)⟩
    simp [safe] at ht
  choose center hc using fun i => starCenter _ _ (rect i)
  let T := Finset.univ.image center
  have covers (a b : V) (hab : related a b = true) : a ∈ T ∨ b ∈ T := by
    obtain ⟨j, ha, he⟩ := isolatedEdge a b hab
    have hp := (h _ (rowsGood j)).2 a ha
    obtain ⟨i, ⟨x, hx, hx'⟩, ⟨y, hy, hy'⟩⟩ := firstTrue C h _ hp
    have hi : center i ∈ T := Finset.mem_image_of_mem _ (Finset.mem_univ _)
    rcases he x hx' y hy' (rect i x hx y hy) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hc i x hx y hy with h₁ | h₂ <;> grind
  have hsmall : (Finset.univ \ T).card < 5 := by
    by_contra! hh
    obtain ⟨a, ha, b, hb, hab⟩ := largeHasEdge _ hh
    exact (covers a b hab).elim (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).2
  have htotal := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  have hbound : T.card ≤ C.size := (Finset.card_image_le).trans_eq (by simp)
  simp [V] at htotal
  omega


private def singSet {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) : Finset (Fin n) :=
  Finset.univ.filter (fun v => C.gateVal {v} i = true)

private lemma mem_singSet {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ singSet C i ↔ C.gateVal {v} i = true := by
  unfold singSet
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ v)

private def stripCircuit {n : ℕ} (C : AndCountCircuit n) : AndCountCircuit n where
  size := C.size
  leftVars i := (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  leftGates := C.leftGates
  rightVars i := (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  rightGates := C.rightGates
  outVars := C.outVars ∪ C.outGates.biUnion (singSet C)
  outGates := C.outGates

private lemma mem_strip_leftVars {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).leftVars i ↔
      (v ∈ C.leftVars i ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  change v ∈ (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i ↔ _
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    mem_singSet, and_assoc]

private lemma mem_strip_rightVars {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).rightVars i ↔
      (v ∈ C.rightVars i ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  change v ∈ (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i ↔ _
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    mem_singSet, and_assoc]

private lemma mem_strip_outVars {n : ℕ} (C : AndCountCircuit n) (v : Fin n) :
    v ∈ (stripCircuit C).outVars ↔
      v ∈ C.outVars ∨ ∃ j ∈ C.outGates, C.gateVal {v} j = true := by
  change v ∈ C.outVars ∪ C.outGates.biUnion (singSet C) ↔ _
  simp only [Finset.mem_union, Finset.mem_biUnion, mem_singSet]

private lemma strip_singleton_false {n : ℕ} (C : AndCountCircuit n) (v : Fin n) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m → (stripCircuit C).gateVal {v} i = false := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi
    cases h : (stripCircuit C).gateVal {v} i
    · rfl
    · exfalso
      rw [gateVal_unfold (stripCircuit C) {v} i, Bool.and_eq_true] at h
      have hL := h.1
      have hR := h.2
      unfold sideTrue at hL hR
      rw [decide_eq_true_eq] at hL hR
      have hvL : v ∈ (stripCircuit C).leftVars i := by
        rcases hL with ⟨w, hwB, hwv⟩ | ⟨j, _, hji, hjv⟩
        · rw [Finset.mem_singleton] at hwv
          rwa [← hwv]
        · rw [ih j (by omega)] at hjv
          exact absurd hjv Bool.false_ne_true
      have hvR : v ∈ (stripCircuit C).rightVars i := by
        rcases hR with ⟨w, hwB, hwv⟩ | ⟨j, _, hji, hjv⟩
        · rw [Finset.mem_singleton] at hwv
          rwa [← hwv]
        · rw [ih j (by omega)] at hjv
          exact absurd hjv Bool.false_ne_true
      rw [mem_strip_leftVars] at hvL
      rw [mem_strip_rightVars] at hvR
      apply hvL.2
      rw [gateVal_unfold C {v} i, Bool.and_eq_true]
      constructor
      · unfold sideTrue
        rw [decide_eq_true_eq]
        rcases hvL.1 with hvB | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvB, Finset.mem_singleton_self v⟩
        · exact Or.inr ⟨j, hjF, hji, hjv⟩
      · unfold sideTrue
        rw [decide_eq_true_eq]
        rcases hvR.1 with hvB | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvB, Finset.mem_singleton_self v⟩
        · exact Or.inr ⟨j, hjF, hji, hjv⟩

private lemma strip_disjoint {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) :
    Disjoint ((stripCircuit C).leftVars i) ((stripCircuit C).rightVars i) := by
  rw [Finset.disjoint_left]
  intro v hvL hvR
  have hf := strip_singleton_false C v C.size i i.isLt
  have ht : (stripCircuit C).gateVal {v} i = true := by
    rw [gateVal_unfold (stripCircuit C) {v} i, Bool.and_eq_true]
    constructor
    · unfold sideTrue
      rw [decide_eq_true_eq]
      exact Or.inl ⟨v, hvL, Finset.mem_singleton_self v⟩
    · unfold sideTrue
      rw [decide_eq_true_eq]
      exact Or.inl ⟨v, hvR, Finset.mem_singleton_self v⟩
  rw [hf] at ht
  exact Bool.false_ne_true ht

private lemma strip_gateVal_le {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      (stripCircuit C).gateVal U i = true → C.gateVal U i = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    rw [gateVal_unfold (stripCircuit C) U i, Bool.and_eq_true] at hval
    rw [gateVal_unfold C U i, Bool.and_eq_true]
    constructor
    · have hL := hval.1
      unfold sideTrue at hL ⊢
      rw [decide_eq_true_eq] at hL ⊢
      rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · rw [mem_strip_leftVars] at hvB
        rcases hvB.1 with hvC | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvC, hvU⟩
        · exact Or.inr ⟨j, hjF, hji, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hjv⟩
      · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩
    · have hR := hval.2
      unfold sideTrue at hR ⊢
      rw [decide_eq_true_eq] at hR ⊢
      rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
      · rw [mem_strip_rightVars] at hvB
        rcases hvB.1 with hvC | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, hvC, hvU⟩
        · exact Or.inr ⟨j, hjF, hji, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hjv⟩
      · exact Or.inr ⟨j, hjF, hji, ih j (by omega) hjv⟩

private lemma strip_gateVal_ge {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      C.gateVal U i = true →
        (∃ v ∈ U, C.gateVal {v} i = true) ∨ (stripCircuit C).gateVal U i = true := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi hval
    by_cases hsing : ∃ v ∈ U, C.gateVal {v} i = true
    · exact Or.inl hsing
    · right
      have hno : ∀ v ∈ U, C.gateVal {v} i ≠ true := fun v hvU hv => hsing ⟨v, hvU, hv⟩
      rw [gateVal_unfold C U i, Bool.and_eq_true] at hval
      rw [gateVal_unfold (stripCircuit C) U i, Bool.and_eq_true]
      constructor
      · have hL := hval.1
        unfold sideTrue at hL ⊢
        rw [decide_eq_true_eq] at hL ⊢
        rcases hL with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, (mem_strip_leftVars C i v).mpr ⟨Or.inl hvB, hno v hvU⟩, hvU⟩
        · rcases ih j (by omega) hjv with ⟨v, hvU, hvs⟩ | hj'
          · exact Or.inl ⟨v, (mem_strip_leftVars C i v).mpr ⟨Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
          · exact Or.inr ⟨j, hjF, hji, hj'⟩
      · have hR := hval.2
        unfold sideTrue at hR ⊢
        rw [decide_eq_true_eq] at hR ⊢
        rcases hR with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hjv⟩
        · exact Or.inl ⟨v, (mem_strip_rightVars C i v).mpr ⟨Or.inl hvB, hno v hvU⟩, hvU⟩
        · rcases ih j (by omega) hjv with ⟨v, hvU, hvs⟩ | hj'
          · exact Or.inl ⟨v, (mem_strip_rightVars C i v).mpr ⟨Or.inr ⟨j, hjF, hji, hvs⟩, hno v hvU⟩, hvU⟩
          · exact Or.inr ⟨j, hjF, hji, hj'⟩

private lemma strip_eval_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    (stripCircuit C).eval U = C.eval U := by
  unfold AndCountCircuit.eval
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
    · rw [mem_strip_outVars] at hvO
      rcases hvO with hvC | ⟨j, hjO, hvs⟩
      · exact Or.inl ⟨v, hvC, hvU⟩
      · exact Or.inr ⟨j, hjO, gateVal_mono_U C (Finset.singleton_subset_iff.mpr hvU) j hvs⟩
    · exact Or.inr ⟨j, hjO, strip_gateVal_le C U C.size j j.isLt hjv⟩
  · rintro (⟨v, hvO, hvU⟩ | ⟨j, hjO, hjv⟩)
    · exact Or.inl ⟨v, (mem_strip_outVars C v).mpr (Or.inl hvO), hvU⟩
    · rcases strip_gateVal_ge C U C.size j j.isLt hjv with ⟨v, hvU, hvs⟩ | hj'
      · exact Or.inl ⟨v, (mem_strip_outVars C v).mpr (Or.inr ⟨j, hjO, hvs⟩), hvU⟩
      · exact Or.inr ⟨j, hjO, hj'⟩


def vars (C : AndCountCircuit 10) (i : Fin C.size) (d : Bool) : Finset V :=
  if d then C.rightVars i else C.leftVars i

def refs (C : AndCountCircuit 10) (i : Fin C.size) (d : Bool) : Finset (Fin C.size) :=
  (if d then C.rightGates i else C.leftGates i).filter (· < i)

def fires (A B U : Finset V) : Prop :=
  (∃ v ∈ A, v ∈ U) ∧ (∃ v ∈ B, v ∈ U)

def raw (C : AndCountCircuit 10) (p : Fin C.size) (U : Finset V) : Prop :=
  fires (C.leftVars p) (C.rightVars p) U

def onSide (C : AndCountCircuit 10) (i : Fin C.size) (d : Bool) (U : Finset V) : Prop :=
  (∃ v ∈ vars C i d, v ∈ U) ∨ ∃ j ∈ refs C i d, C.gateVal U j = true

lemma gate_iff (C : AndCountCircuit 10) (i : Fin C.size) (U : Finset V) :
    C.gateVal U i = true ↔ ∀ d, onSide C i d U := by
  rw [gateVal_unfold, Bool.and_eq_true]
  simp [Bool.forall_bool, onSide, sideTrue, refs, vars, and_assoc]

lemma raw_gate (C : AndCountCircuit 10) (p : Fin C.size) (U : Finset V) (hg : raw C p U) :
    C.gateVal U p = true := (gate_iff ..).2 (by
      rintro (_ | _)
      · exact Or.inl hg.1
      · exact Or.inl hg.2)

def Early (C : AndCountCircuit 10) (p : Fin C.size) : Prop :=
  ∀ j < p, ∀ r, C.gateVal (rows r) j = false

lemma earliest_raw (C : AndCountCircuit 10) (p : Fin C.size) (h : Early C p) (r : Fin 15) :
    C.gateVal (rows r) p = true ↔ raw C p (rows r) := by
  refine ⟨fun ht => ?_, raw_gate C p (rows r)⟩
  have hs (d) := (gate_iff ..).1 ht d
  have hv (d) : ∃ v ∈ vars C p d, v ∈ rows r := by
    rcases hs d with hv | ⟨j, hj, ht'⟩
    · exact hv
    · simp [h j (Finset.mem_filter.mp hj).2 r] at ht'
  exact ⟨hv false, hv true⟩

lemma blocked (C : AndCountCircuit 10) (p : Fin C.size) (early : Early C p)
    (sep : Separates C) (nout : p ∉ C.outGates) (T : Finset (Fin 15)) (U : Finset V)
    (blockSide : ∀ i, i ≠ p → (∀ r ∈ T, C.gateVal (rows r) i = false) →
      ∃ d, (∀ v ∈ vars C i d, v ∉ U) ∧ (∀ j ∈ refs C i d, ∀ r ∈ T, C.gateVal (rows r) j = false) ∧
        (p ∈ refs C i d → ¬ raw C p U)) : C.eval U = false := by
  have guard (i : Fin C.size) : C.gateVal U i = true →
      (∃ r ∈ T, C.gateVal (rows r) i = true) ∨ (i = p ∧ raw C p U) := by
    induction i using ((wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction) with
    | h i ih =>
      intro ht
      by_cases hp : i = p
      · subst i
        right
        refine ⟨rfl, ?_⟩
        have get (d) : ∃ v ∈ vars C p d, v ∈ U := by
          rcases (gate_iff ..).mp ht d with hv | ⟨j, hj, hjt⟩
          · exact hv
          have lt' : j < p := (Finset.mem_filter.mp hj).2
          rcases ih j lt' hjt with ⟨r, _, hrt⟩ | ⟨he, _⟩
          · simp [early j lt' r] at hrt
          · exact (lt_irrefl _ (he ▸ lt')).elim
        exact ⟨get false, get true⟩
      left
      by_contra! no
      have hz : ∀ r ∈ T, C.gateVal (rows r) i = false := by simpa using no
      obtain ⟨d, hv, href, hraw⟩ := blockSide i hp hz
      rcases (gate_iff ..).mp ht d with ⟨v, hvi, hvU⟩ | ⟨j, hj, hjt⟩
      · exact hv v hvi hvU
      · rcases ih j (Finset.mem_filter.mp hj).2 hjt with ⟨r, hr, hrt⟩ | ⟨rfl, hrt⟩
        · simp [href j hj r hr] at hrt
        · exact hraw hj hrt
  apply Bool.eq_false_iff.mpr
  intro ht
  rw [eval, decide_eq_true_eq] at ht
  rcases ht with ⟨v, hv, _⟩ | ⟨i, hi, hit⟩
  · exact bare_out_empty C sep v hv
  · rcases guard i hit with ⟨r, hr, hrt⟩ | ⟨rfl, _⟩
    · have he := (sep _ (rowsGood r)).1
      have het : C.eval (rows r) = true := decide_eq_true (Or.inr ⟨i, hi, hrt⟩)
      simp [he] at het
    · exact nout hi

abbrev X := Option V

def present (A B I : Finset V) : X → Prop
  | none => fires A B I
  | some v => v ∈ I

def wire (C : AndCountCircuit 10) (p i : Fin C.size) (d : Bool) : X → Prop
  | none => p ∈ refs C i d
  | some v => v ∈ vars C i d

lemma wire_on (C : AndCountCircuit 10) (p i : Fin C.size) (d : Bool) (I : Finset V) (z : X)
    (hw : wire C p i d z) (hz : present (C.leftVars p) (C.rightVars p) I z) : onSide C i d I := by
  cases z with
  | none => exact Or.inr ⟨p, hw, raw_gate C p I hz⟩
  | some v => exact Or.inl ⟨v, hw, hz⟩

def Dir (A B : Finset V) (r s : Fin 15) : Prop := ∃ u ∈ rows s, u ∉ rows r ∧
  (fires A B (insert u (rows r)) → fires A B (rows r) ∨ fires A B (rows s))

def Apart (A B : Finset V) (r s : Fin 15) : Prop := Dir A B r s ∨ Dir A B s r

lemma dir_block (C : AndCountCircuit 10) (p : Fin C.size) (early : Early C p)
    (sep : Separates C) (nout : p ∉ C.outGates) (r s : Fin 15)
    (hd : Dir (C.leftVars p) (C.rightVars p) r s)
    (agree : ∀ i, i ≠ p → C.gateVal (rows r) i = false → C.gateVal (rows s) i = false →
      ∃ d, ¬ onSide C i d (rows r) ∧ ¬ onSide C i d (rows s)) : False := by
  obtain ⟨u, hus, hur, hg⟩ := hd
  have hh := blocked C p early sep nout {r,s} (insert u (rows r)) (by
    intro i hne hz
    obtain ⟨d, dr, ds⟩ := agree i hne (hz r (by simp)) (hz s (by simp))
    refine ⟨d, ?_, ?_, ?_⟩
    · intro v hv hu
      rcases Finset.mem_insert.mp hu with rfl | hvr
      · exact ds (Or.inl ⟨_, hv, hus⟩)
      · exact dr (Or.inl ⟨_, hv, hvr⟩)
    · intro j hj t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Bool.eq_false_iff.mpr (fun h => dr (Or.inr ⟨j, hj, h⟩))
      · exact Bool.eq_false_iff.mpr (fun h => ds (Or.inr ⟨j, hj, h⟩))
    · intro hp hu
      rcases hg hu with h | h
      · exact dr (Or.inr ⟨_, hp, raw_gate C p _ h⟩)
      · exact ds (Or.inr ⟨_, hp, raw_gate C p _ h⟩))
  simp [(sep _ (rowsGood r)).2 u hur] at hh

noncomputable def idle (C : AndCountCircuit 10) (p : Fin C.size) (z : X) : Finset (Fin C.size) := by
  classical
  exact Finset.univ.filter (fun i => i ≠ p ∧ ¬ wire C p i false z ∧ ¬ wire C p i true z)

noncomputable def pick (C : AndCountCircuit 10) (p i : Fin C.size) (z : X) (r : Fin 15) : Bool := by
  classical
  exact if wire C p i false z then true else if wire C p i true z then false
    else decide (onSide C i false (rows r))

lemma pick_off (C : AndCountCircuit 10) (p i : Fin C.size) (z : X) (r : Fin 15)
    (hr : present (C.leftVars p) (C.rightVars p) (rows r) z) (hi : C.gateVal (rows r) i = false) :
    ¬ onSide C i (pick C p i z r) (rows r) := by
  classical
  have h := (Bool.eq_false_iff.mp hi)
  simp only [ne_eq, gate_iff] at h
  by_cases hl : wire C p i false z
  · simp only [pick, hl, ↓reduceIte]
    have := wire_on C p i false _ z hl hr
    exact fun ht => h (by rintro (_ | _) <;> assumption)
  by_cases hh : wire C p i true z
  · simp only [pick, hl, hh, ↓reduceIte]
    have := wire_on C p i true _ z hh hr
    exact fun ht => h (by rintro (_ | _) <;> assumption)
  by_cases ht : onSide C i false (rows r)
  · simp only [pick, hl, hh, ↓reduceIte, decide_eq_true ht]
    exact fun ht' => h (by rintro (_ | _) <;> assumption)
  · simp [pick, hl, hh, ht]

lemma three_idle (C : AndCountCircuit 10) (p : Fin C.size) (early : Early C p)
    (sep : Separates C) (nout : p ∉ C.outGates) (z : X) (rs : Fin 5 → Fin 15)
    (hz : ∀ a, present (C.leftVars p) (C.rightVars p) (rows (rs a)) z)
    (apart : ∀ a b, a ≠ b → Apart (C.leftVars p) (C.rightVars p) (rs a) (rs b)) :
    3 ≤ (idle C p z).card := by
  classical
  let code (a : Fin 5) (j : ↥(idle C p z)) := pick C p j z (rs a)
  have hinj : Function.Injective code := by
    intro a b hab
    by_contra hne
    have ag (i : Fin C.size) (hi : i ≠ p) (ha : C.gateVal (rows (rs a)) i = false)
        (hb : C.gateVal (rows (rs b)) i = false) :
        ∃ d, ¬onSide C i d (rows (rs a)) ∧ ¬onSide C i d (rows (rs b)) := by
      have he : pick C p i z (rs a) = pick C p i z (rs b) := by
        by_cases hl : wire C p i false z
        · simp [pick, hl]
        by_cases hr : wire C p i true z
        · simp [pick, hl, hr]
        exact congrFun hab ⟨i, by simp [idle, hi, hl, hr]⟩
      exact ⟨_, pick_off C p i z (rs a) (hz a) ha, he ▸ pick_off C p i z (rs b) (hz b) hb⟩
    rcases apart a b hne with hd | hd
    · exact dir_block C p early sep nout _ _ hd ag
    · exact dir_block C p early sep nout _ _ hd fun i hi hb ha => by
        obtain ⟨d, hd, he⟩ := ag i hi ha hb
        exact ⟨d, he, hd⟩
  have hc := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_bool, Fintype.card_coe] at hc
  by_contra! hbad
  have hp : 2 ^ (idle C p z).card ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

abbrev Slot := Fin 4 × Bool

def Consistent (M : Finset Slot) : Prop :=
  ∀ q ∈ M, ∀ s ∈ M, q.1 = s.1 → q.2 = s.2

def Cover (A B : Finset V) (pos : X → Finset Slot) : Prop :=
  ∀ r : Fin 15, ∃ M : Finset Slot, Consistent M ∧
    (∀ z, present A B (rows r) z → Disjoint M (pos z)) ∧
    ∀ u : V, u ∉ rows r → (∃ s ∈ M, s ∈ pos (some u)) ∨
      (¬fires A B (rows r) ∧ fires A B (insert u (rows r)) ∧ ∃ s ∈ M, s ∈ pos none)

def Strong (A B : Finset V) (v : V) : Prop :=
  ∀ a b : Fin 5, a ≠ b → Apart A B (through v a) (through v b)

def Cap (A B : Finset V) (pos : X → Finset Slot) : Prop :=
  (∀ v, Consistent (pos (some v)) ∧ (pos (some v)).card ≤ 2) ∧
  (∀ v, Strong A B v → (pos (some v)).card ≤ 1) ∧
  (∀ rs : Fin 5 → Fin 15, (∀ a, fires A B (rows (rs a))) →
    (∀ a b, a ≠ b → Apart A B (rs a) (rs b)) → ((pos none).image Prod.fst).card ≤ 1)

lemma lift_slots (C : AndCountCircuit 10) (p : Fin C.size) (early : Early C p)
    (sep : Separates C) (nout : p ∉ C.outGates) (dis : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (size : C.size = 5) : ∃ pos, Cover (C.leftVars p) (C.rightVars p) pos ∧
      Cap (C.leftVars p) (C.rightVars p) pos := by
  classical
  let D := Finset.univ.erase p
  have hD : D.card = 4 := by simp [D, Finset.card_erase_of_mem, size]
  let e := D.orderEmbOfFin hD
  have de (i) : e i ≠ p := Finset.ne_of_mem_erase (D.orderEmbOfFin_mem hD i)
  have onto (i) (hp : i ≠ p) : ∃ j, e j = i := by
    have hh : i ∈ D := by simp [D, hp]
    change i ∈ Set.range (D.orderEmbOfFin hD)
    rwa [Finset.range_orderEmbOfFin]
  let pos (z : X) : Finset Slot := Finset.univ.filter (fun s => wire C p (e s.1) s.2 z)
  have pm {z : X} {s : Slot} : s ∈ pos z ↔ wire C p (e s.1) s.2 z := by simp [pos]
  refine ⟨pos, ?_, ?_⟩
  · intro r
    let d (j : Fin 4) := decide (onSide C (e j) false (rows r))
    let M : Finset Slot := Finset.univ.filter (fun s => C.gateVal (rows r) (e s.1) = false ∧ s.2 = d s.1)
    have off {s : Slot} (hs : s ∈ M) : ¬onSide C (e s.1) s.2 (rows r) := by
      obtain ⟨hg, hd⟩ := (Finset.mem_filter.mp hs).2
      have hn : ¬∀ b, onSide C (e s.1) b (rows r) := fun h => by
        simpa [hg] using (gate_iff ..).2 h
      rw [hd]
      by_cases h₀ : onSide C (e s.1) false (rows r)
      · simpa [d, h₀] using (fun ht => hn (by rintro (_ | _) <;> assumption) :
          ¬onSide C (e s.1) true (rows r))
      · simp [d, h₀]
    refine ⟨M, ?_, ?_, ?_⟩
    · intro q hq s hs he
      exact ((Finset.mem_filter.mp hq).2.2).trans (he ▸ (Finset.mem_filter.mp hs).2.2.symm)
    · intro z hz
      exact Finset.disjoint_left.mpr fun s hs hp => off hs (wire_on C p _ _ _ z (pm.mp hp) hz)
    · intro u hu
      by_contra! bad
      have hb := blocked C p early sep nout {r} (insert u (rows r)) (by
        intro i hi hz
        obtain ⟨j, rfl⟩ := onto i hi
        let s : Slot := (j, d j)
        have hs : s ∈ M := by simpa [M, s] using hz _ (Finset.mem_singleton_self r)
        have hf := off hs
        refine ⟨d j, ?_, ?_, ?_⟩
        · intro v hv he
          rcases Finset.mem_insert.mp he with rfl | he
          · exact bad.1 s hs (pm.mpr hv)
          · exact hf (Or.inl ⟨_, hv, he⟩)
        · intro k hk a ha
          have h' := Finset.mem_singleton.mp ha
          subst a
          exact Bool.eq_false_iff.mpr fun ht => hf (Or.inr ⟨_, hk, ht⟩)
        · intro hp hU
          have hrow : ¬fires (C.leftVars p) (C.rightVars p) (rows r) :=
            fun h => hf (Or.inr ⟨_, hp, raw_gate C p _ h⟩)
          exact bad.2 hrow hU s hs (pm.mpr hp))
      simp [(sep _ (rowsGood r)).2 u hu] at hb
  · have cEq (v : V) : Consistent (pos (some v)) := by
      rintro ⟨j, b⟩ hs ⟨k,c⟩ ht rfl
      have h₁ := pm.mp hs
      have h₂ := pm.mp ht
      cases b <;> cases c <;> first | rfl | exact False.elim (Finset.disjoint_left.mp (dis _) h₁ h₂) |
        exact False.elim (Finset.disjoint_left.mp (dis _) h₂ h₁)
    have cardEq (v : V) : (pos (some v)).card = ((pos (some v)).image Prod.fst).card := by
      symm
      exact Finset.card_image_of_injOn (fun a ha b hb hab => Prod.ext hab (cEq v a ha b hb hab))
    have bd (z : X) (hz : 3 ≤ (idle C p z).card) : ((pos z).image Prod.fst).card ≤ 1 := by
      let O := ((pos z).image Prod.fst).map e.toEmbedding
      have hdis : Disjoint O (insert p (idle C p z)) := by
        refine Finset.disjoint_left.mpr ?_
        simp only [O, Finset.mem_map, Finset.mem_image, Finset.mem_insert, not_or]
        rintro _ ⟨j, ⟨s, hs, rfl⟩, rfl⟩
        have hh := pm.mp hs
        refine ⟨de _, ?_⟩
        intro hx
        obtain ⟨_, h₀, h₁⟩ := (Finset.mem_filter.mp hx).2
        cases h : s.2
        · exact h₀ (h ▸ hh)
        · exact h₁ (h ▸ hh)
      have hh := Finset.card_le_card (Finset.subset_univ (O ∪ insert p (idle C p z)))
      rw [Finset.card_union_of_disjoint hdis, Finset.card_insert_of_notMem (by simp [idle])] at hh
      simp only [O, Finset.card_map, Finset.card_univ, Fintype.card_fin, size] at hh
      omega
    refine ⟨fun v => ⟨cEq v, ?_⟩, fun v hv => (cardEq v).trans_le
      (bd _ (three_idle C p early sep nout _ (through v) (rowContains v) hv)), ?_⟩
    · let O := ((pos (some v)).image Prod.fst).map e.toEmbedding
      have hdis : Disjoint O (Free C v) := by
        refine Finset.disjoint_left.mpr ?_
        simp only [O, Finset.mem_map, Finset.mem_image]
        rintro _ ⟨j, ⟨s, hs, rfl⟩, rfl⟩
        have hh := pm.mp hs
        intro hfree
        obtain ⟨hl, hr⟩ := (Finset.mem_filter.mp hfree).2
        cases h : s.2
        · exact hl (show wire C p (e s.1) false (some v) from h ▸ hh)
        · exact hr (show wire C p (e s.1) true (some v) from h ▸ hh)
      have hh := Finset.card_le_card (Finset.subset_univ (O ∪ Free C v))
      rw [Finset.card_union_of_disjoint hdis] at hh
      simp only [O, Finset.card_map, Finset.card_univ, Fintype.card_fin, size] at hh
      have := free_bound C sep v
      rw [cardEq]
      omega
    · exact fun rs hz ha => bd _ (three_idle C p early sep nout none rs hz ha)

def Stable (A B : Finset V) (r : Fin 15) (v : V) : Prop :=
  v ∉ rows r ∧ (fires A B (insert v (rows r)) → fires A B (rows r))

def Conflict (A B : Finset V) (v w : V) : Prop :=
  (∃ r, Stable A B r v ∧ Stable A B r w) ∧
  ((∃ r, Stable A B r v ∧ w ∈ rows r) ∨ (∃ r, Stable A B r w ∧ v ∈ rows r))

def Clique {n : ℕ} (A B : Finset V) (a : Fin n → V) : Prop :=
  (∀ j, Strong A B (a j)) ∧ (∀ j, ∃ r, Stable A B r (a j)) ∧
    ∀ j k, j ≠ k → Conflict A B (a j) (a k)

lemma fromStable {A B : Finset V} {pos : X → Finset Slot} {r : Fin 15}
    {M : Finset Slot} (hit : ∀ u : V, u ∉ rows r → (∃ s ∈ M, s ∈ pos (some u)) ∨
      (¬fires A B (rows r) ∧ fires A B (insert u (rows r)) ∧ ∃ s ∈ M, s ∈ pos none))
    {v : V} (hh : Stable A B r v) : ∃ s ∈ M, s ∈ pos (some v) :=
  (hit v hh.1).resolve_right fun h => h.1 (hh.2 h.2.1)

lemma clique_places {n : ℕ} {A B : Finset V} {pos : X → Finset Slot} (cv : Cover A B pos)
    (cap : Cap A B pos) {a : Fin n → V} (hc : Clique A B a) :
    ∃ q : Fin n → Slot, (∀ j, pos (some (a j)) = {q j}) ∧ Function.Injective (fun j => (q j).1) := by
  have single (j) : ∃ s, pos (some (a j)) = {s} := by
    obtain ⟨r, hr⟩ := hc.2.1 j
    obtain ⟨M, _, _, hit⟩ := cv r
    obtain ⟨s, _, hs⟩ := fromStable hit hr
    exact Finset.card_eq_one.mp (le_antisymm (cap.2.1 _ (hc.1 j)) (Finset.card_pos.mpr ⟨s, hs⟩))
  choose q hq using single
  refine ⟨q, hq, ?_⟩
  intro j k hgate
  by_contra hne
  obtain ⟨⟨r, hrv, hrw⟩, hm⟩ := hc.2.2 j k hne
  have inM {r' i} {M : Finset Slot}
      (hit : ∀ u : V, u ∉ rows r' → (∃ s ∈ M, s ∈ pos (some u)) ∨
        (¬fires A B (rows r') ∧ fires A B (insert u (rows r')) ∧ ∃ s ∈ M, s ∈ pos none))
      (hr : Stable A B r' (a i)) : q i ∈ M := by
    simpa [hq] using fromStable hit hr
  obtain ⟨M, con, _, hit⟩ := cv r
  have eqSlot : q j = q k := Prod.ext hgate (con _ (inM hit hrv) _ (inM hit hrw) hgate)
  have contra {j k : Fin n} (eq : q j = q k) (r' : Fin 15)
      (hj : Stable A B r' (a j)) (hk : a k ∈ rows r') : False := by
    obtain ⟨N, _, avo, hh⟩ := cv r'
    have hdis := avo (some (a k)) hk
    exact Finset.disjoint_left.mp hdis (inM hh hj) (by simp [hq, eq])
  rcases hm with ⟨r', hj, hk⟩ | ⟨r', hk, hj⟩
  · exact contra eqSlot r' hj hk
  · exact contra eqSlot.symm r' hk hj

lemma noFiveClique {A B : Finset V} {pos : X → Finset Slot} (cv : Cover A B pos)
    (cap : Cap A B pos) (a : Fin 5 → V) (hc : Clique A B a) : False := by
  obtain ⟨q, _, h⟩ := clique_places cv cap hc
  have ht := Fintype.card_le_of_injective _ h
  simp at ht

lemma normalize_places {n : ℕ} (hn : n ≤ 4) {A B : Finset V} {pos : X → Finset Slot}
    (cv : Cover A B pos) (cap : Cap A B pos) {a : Fin n → V} (hc : Clique A B a) :
    ∃ pos' : X → Finset Slot, Cover A B pos' ∧ Cap A B pos' ∧
      ∀ j, pos' (some (a j)) = {(Fin.castLE hn j, false)} := by
  classical
  obtain ⟨q, hq, inj⟩ := clique_places cv cap hc
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_extending_pair _ (Fin.castLE hn) inj
    (show Function.Injective (Fin.castLE hn) from (Fin.castLEEmb hn).injective)
  let b (k : Fin 4) := decide (∃ j, (q j).1 = k ∧ (q j).2 = true)
  have hbit (j) : b (q j).1 = (q j).2 := by
    cases hh : (q j).2 with
    | true => exact decide_eq_true ⟨j,rfl,hh⟩
    | false =>
      apply decide_eq_false
      rintro ⟨k,hk,ht⟩
      have := inj hk
      subst k
      simp [hh] at ht
  let f (s : Slot) : Slot := (σ s.1, xor s.2 (b s.1))
  have fi : Function.Injective f := by
    rintro ⟨i,x⟩ ⟨j,y⟩ eq
    have hij := σ.injective (congrArg Prod.fst eq)
    change i = j at hij
    subst j
    have eq' := congrArg Prod.snd eq
    change xor x (b i) = xor y (b i) at eq'
    cases b i <;> cases x <;> cases y <;> simp_all
  let move (S : Finset Slot) := S.image f
  have mc {S : Finset Slot} (h : Consistent S) : Consistent (move S) := by
    intro t ht y hy he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    have hf : x.1 = z.1 := σ.injective he
    exact congrArg (fun s : Slot => (f s).2) (Prod.ext hf (h _ hx _ hz hf))
  have sz (S : Finset Slot) : (move S).card = S.card := Finset.card_image_of_injective S fi
  refine ⟨fun z => move (pos z), ?_, ?_, ?_⟩
  · intro r
    obtain ⟨M,hm,hd,hh⟩ := cv r
    refine ⟨move M, mc hm, ?_, ?_⟩
    · intro z hz
      apply Finset.disjoint_left.mpr
      rintro s hs ht
      obtain ⟨x,hx,he⟩ := Finset.mem_image.mp hs
      obtain ⟨y,hy,he'⟩ := Finset.mem_image.mp ht
      exact Finset.disjoint_left.mp (hd z hz) hx (fi (he.trans he'.symm) ▸ hy)
    · intro u hu
      have tr {z} : (∃ s ∈ M, s ∈ pos z) → ∃ s ∈ move M, s ∈ move (pos z) := by
        rintro ⟨s,hs,ht⟩
        exact ⟨_,Finset.mem_image_of_mem f hs,Finset.mem_image_of_mem f ht⟩
      rcases hh u hu with h | ⟨h₁,h₂,h₃⟩
      · exact Or.inl (tr h)
      · exact Or.inr ⟨h₁,h₂,tr h₃⟩
  · refine ⟨fun v => ⟨mc (cap.1 v).1, (sz _).trans_le (cap.1 v).2⟩,
      fun v h => (sz _).trans_le (cap.2.1 v h), ?_⟩
    intro rs h₁ h₂
    have eq : (move (pos none)).image Prod.fst = ((pos none).image Prod.fst).image σ := by
      simp [move, Finset.image_image, f, Function.comp_def]
    rw [eq, Finset.card_image_of_injective _ σ.injective]
    exact cap.2.2 rs h₁ h₂
  · intro j
    simp [move,hq,f,hσ,hbit]

def slotId (s : Slot) := 2*s.1.val + s.2.toNat

def slots (m : ℕ) : Finset Slot := Finset.univ.filter (fun s => m.testBit (slotId s))

def slotBits (M : Finset Slot) := ∑ s ∈ M, 2 ^ slotId s

set_option maxRecDepth 4000 in
lemma slotsSurj (S : Finset Slot) : ∃ m : Fin 256, slots m.val = S := by
  have round : ∀ m : Fin 256, slotBits (slots m.val) = m.val := by decide +kernel
  have inj : Function.Injective (fun m : Fin 256 => slots m.val) := by
    intro a b eq
    exact Fin.ext ((round a).symm.trans ((congrArg slotBits eq).trans (round b)))
  exact ((Fintype.bijective_iff_injective_and_card _).mpr ⟨inj, by decide⟩).surjective S

def fitsMask (m : ℕ) : Bool := (m &&& (m >>> 1) &&& 85) == 0

lemma fitsSpec : ∀ m : Fin 256, Consistent (slots m.val) → fitsMask m.val = true := by
  unfold Consistent
  decide +kernel

def meets (m n : ℕ) : Bool := (m &&& n) != 0

lemma meetSpec (m n : Fin 256) : meets m.val n.val = true ↔ ∃ s ∈ slots m.val, s ∈ slots n.val := by
  unfold meets
  simp only [bne_iff_ne, ne_eq]
  constructor
  · intro h
    have ex : ∃ j, (m.val &&& n.val).testBit j = true := by
      by_contra! hn
      apply h
      apply Nat.eq_of_testBit_eq
      simpa using hn
    obtain ⟨j,hj⟩ := ex
    rw [Nat.testBit_and, Bool.and_eq_true] at hj
    have lt : j < 8 := by
      by_contra! he
      have b : m.val < 2 ^ j := lt_of_lt_of_le m.isLt
        (by exact Nat.pow_le_pow_right (by decide) he : 2 ^ 8 ≤ 2 ^ j)
      simp [Nat.testBit_lt_two_pow b] at hj
    have rep : ∀ a : Fin 8, ∃ s : Slot, slotId s = a.val := by decide +kernel
    obtain ⟨s,hs⟩ := rep ⟨j,lt⟩
    exact ⟨s,by simpa [slots,hs] using hj.1,by simpa [slots,hs] using hj.2⟩
  · rintro ⟨s,hs,ht⟩ h
    have h₁ := (Finset.mem_filter.mp hs).2
    have h₂ := (Finset.mem_filter.mp ht).2
    have hx : (m.val &&& n.val).testBit (slotId s) = true := by simp [h₁,h₂]
    simp [h] at hx

abbrev Marks := List (X × Fin 256)

def hot (A B I : Finset V) : Bool :=
  decide (∃ v ∈ A, v ∈ I) && decide (∃ v ∈ B, v ∈ I)

lemma hotSpec {A B I : Finset V} : hot A B I = true ↔ fires A B I := by simp [hot,fires]

def admiss (A B : Finset V) (r : Fin 15) (L : Marks) (m : Fin 256) : Bool :=
  fitsMask m.val &&
  let gOK := L.all fun t => t.1.isSome || meets m.val t.2.val
  L.all fun t =>
    let hit := meets m.val t.2.val
    match t.1 with
    | none => !(hot A B (rows r)) || !hit
    | some u => if u ∈ rows r then !hit else
        hit || (!(hot A B (rows r)) && hot A B (insert u (rows r)) && gOK)

def Pass (A B : Finset V) (L : Marks) : Prop :=
  ∀ r : Fin 15, ∃ m : Fin 256, admiss A B r L m = true

lemma pass_marks {A B : Finset V} {pos : X → Finset Slot} (cv : Cover A B pos)
    (L : Marks) (assigned : ∀ t ∈ L, pos t.1 = slots t.2.val) : Pass A B L := by
  intro r
  obtain ⟨M,hm,ha,hp⟩ := cv r
  obtain ⟨m,rfl⟩ := slotsSurj M
  have hh {z : X} {w : Fin 256} (ht : (z,w) ∈ L) :
      meets m.val w.val = true ↔ ∃ s ∈ slots m.val, s ∈ pos z := by
    rw [meetSpec, assigned _ ht]
  refine ⟨m, ?_⟩
  simp only [admiss, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fitsSpec m hm, ?_⟩
  rintro ⟨(_ | u),w⟩ ht
  · simp only [Bool.or_eq_true, Bool.not_eq_true']
    by_cases h : fires A B (rows r)
    · right
      apply Bool.eq_false_iff.mpr
      rintro he
      obtain ⟨s,hs,h'⟩ := (hh ht).mp he
      exact Finset.disjoint_left.mp (ha none h) hs h'
    · exact Or.inl (Bool.eq_false_iff.mpr (fun hv => h (hotSpec.mp hv)))
  · by_cases hu : u ∈ rows r
    · simp only [hu,↓reduceIte,Bool.not_eq_true']
      apply Bool.eq_false_iff.mpr
      rintro he
      obtain ⟨s,hs,h'⟩ := (hh ht).mp he
      exact Finset.disjoint_left.mp (ha (some u) hu) hs h'
    · simp only [hu,↓reduceIte,Bool.or_eq_true,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true]
      rcases hp u hu with he | ⟨h₀,h₁,he⟩
      · exact Or.inl ((hh ht).mpr he)
      · refine Or.inr ⟨⟨Bool.eq_false_iff.mpr (fun ht => h₀ (hotSpec.mp ht)),hotSpec.mpr h₁⟩, ?_⟩
        rintro ⟨(_ | z),w'⟩ hw
        · simpa using (hh hw).mpr he
        · simp

def Autom (f : V → V) : Prop := ∀ v w, related (f v) (f w) = related v w

lemma good_image (f : Equiv.Perm V) (ha : Autom f) (I : Finset V) : Good (I.image f) ↔ Good I := by
  constructor
  · rintro ⟨hi,hm⟩
    refine ⟨fun v hv w hw => ?_, fun u hu => ?_⟩
    · rw [← ha v w]
      exact hi _ (Finset.mem_image_of_mem f hv) _ (Finset.mem_image_of_mem f hw)
    · obtain ⟨v,hv,hh⟩ := hm (f u) (by simpa using hu)
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨x,hx,(ha u x).symm ▸ hh⟩
  · rintro ⟨hi,hm⟩
    constructor
    · intro v hv w hw
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hw
      exact (ha x y).trans (hi x hx y hy)
    · intro u hu
      obtain ⟨z,rfl⟩ := f.surjective u
      obtain ⟨x,hx,hr⟩ := hm z (by simpa using hu)
      exact ⟨f x,Finset.mem_image_of_mem f hx,(ha z x).trans hr⟩

def rename (C : AndCountCircuit 10) (f : Equiv.Perm V) (sw : Bool) : AndCountCircuit 10 where
  size := C.size
  leftVars i := (vars C i sw).image f
  rightVars i := (vars C i (!sw)).image f
  leftGates i := if sw then C.rightGates i else C.leftGates i
  rightGates i := if sw then C.leftGates i else C.rightGates i
  outVars := C.outVars.image f
  outGates := C.outGates

lemma renameGate (C : AndCountCircuit 10) (f : Equiv.Perm V) (sw : Bool) (I : Finset V) (i : Fin C.size) :
    (rename C f sw).gateVal (I.image f) i = C.gateVal I i := by
  have hs (B : Finset V) (F : Finset (Fin C.size)) (j : Fin C.size) (v : Fin C.size → Bool) :
      sideTrue (I.image f) (B.image f) F j v = sideTrue I B F j v := by simp [sideTrue]
  have hf (d : ℕ) (j : Fin C.size) : (rename C f sw).gateValFuel (I.image f) d j = C.gateValFuel I d j := by
    induction d generalizing j with
    | zero => rfl
    | succ d ih =>
      have he : (rename C f sw).gateValFuel (I.image f) d = C.gateValFuel I d := funext ih
      simp only [gateValFuel,he]
      cases sw <;> simp only [rename,vars,Bool.not_true,Bool.not_false,
        Bool.false_eq_true,↓reduceIte,hs,Bool.and_comm]
  exact hf _ i

lemma renameEval (C : AndCountCircuit 10) (f : Equiv.Perm V) (sw : Bool) (I : Finset V) :
    (rename C f sw).eval (I.image f) = C.eval I := by
  unfold eval
  apply decide_eq_decide.mpr
  change ((∃ v ∈ C.outVars.image f, v ∈ I.image f) ∨
    ∃ i ∈ C.outGates, (rename C f sw).gateVal (I.image f) i = true) ↔ _
  simp [renameGate]

lemma allRows : ∀ I : Finset V, Good I → ∃ r, I = rows r := by
  unfold Good
  decide +kernel

def Bad (A B : Finset V) : Prop := ∃ (C : AndCountCircuit 10) (p : Fin C.size),
  C.leftVars p = A ∧ C.rightVars p = B ∧ C.size = 5 ∧ Separates C ∧ Early C p ∧
  (∃ r, C.gateVal (rows r) p = true) ∧ ∀ i, Disjoint (C.leftVars i) (C.rightVars i)

lemma bad_rename {A B : Finset V} (h : Bad A B) (f : Equiv.Perm V) (hf : Autom f) (sw : Bool) :
    Bad ((if sw then B else A).image f) ((if sw then A else B).image f) := by
  obtain ⟨C,p,hA,hB,sz,sp,er,⟨r,hr⟩,dis⟩ := h
  have pre (I : Finset V) : (I.image f.symm).image f = I := by simp [Finset.image_image]
  have gp (I : Finset V) (hi : Good I) : Good (I.image f.symm) := by
    apply (good_image f hf _).mp
    rwa [pre]
  refine ⟨rename C f sw,p,?_,?_,sz,?_,?_,?_,?_⟩
  · cases sw <;> simp [rename,vars,hA,hB]
  · cases sw <;> simp [rename,vars,hA,hB]
  · intro I hi
    have hh := sp _ (gp I hi)
    constructor
    · simpa [pre] using (renameEval C f sw (I.image f.symm)).trans hh.1
    · intro u hu
      have hm : f.symm u ∉ I.image f.symm := by simpa using hu
      simpa [pre] using (renameEval C f sw (insert (f.symm u) (I.image f.symm))).trans (hh.2 _ hm)
  · intro j hj k
    obtain ⟨t,ht⟩ := allRows _ (gp _ (rowsGood k))
    have eq := renameGate C f sw (rows t) j
    rw [← ht,pre] at eq
    exact eq.trans (ht ▸ er j hj t)
  · obtain ⟨t,ht⟩ := allRows _ ((good_image f hf _).mpr (rowsGood r))
    refine ⟨t, ?_⟩
    rw [← ht, renameGate]
    exact hr
  · intro i
    have tr {L R : Finset V} (h : Disjoint L R) : Disjoint (L.image f) (R.image f) := by
      apply Finset.disjoint_left.mpr
      intro z hz hzr
      rcases Finset.mem_image.mp hz with ⟨x,hx,rfl⟩
      exact Finset.disjoint_left.mp h hx (by simpa using hzr)
    cases sw
    · exact tr (dis i)
    · exact tr (dis i).symm

lemma bad_frame {A B : Finset V} (h : Bad A B) :
    (∃ r, fires A B (rows r)) ∧ Disjoint A B ∧ ∃ pos, Cover A B pos ∧ Cap A B pos := by
  obtain ⟨C,p,rfl,rfl,sz,sp,er,⟨r,hr⟩,dis⟩ := h
  have no : p ∉ C.outGates := by
    intro hp
    have ht : C.eval (rows r) = true := decide_eq_true (Or.inr ⟨p,hp,hr⟩)
    simp [(sp _ (rowsGood r)).1] at ht
  exact ⟨⟨r,(earliest_raw C p er r).mp hr⟩,dis p,lift_slots C p er sp no dis sz⟩

def decode (m : ℕ) : Finset V := Finset.univ.filter (fun v => m.testBit v.val)

def encode (S : Finset V) : ℕ := ∑ v ∈ S, 2 ^ v.val

set_option maxRecDepth 8000 in
lemma roundTrip : ∀ m : Fin 1024, encode (decode m.val) = m.val := by decide +kernel

lemma decodeSurj (S : Finset V) : ∃ m : Fin 1024, decode m.val = S := by
  have hi : Function.Injective (fun m : Fin 1024 => decode m.val) := by
    intro a b he
    apply Fin.ext
    exact (roundTrip a).symm.trans ((congrArg encode he).trans (roundTrip b))
  exact ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hi, by simp [V]⟩).surjective S

def digit (w i : ℕ) (t : List ℕ) : ℕ :=
  (t[i / 16]?.getD 0 >>> (w * (i % 16))) % (2 ^ w)

def permWord (i : ℕ) : ℕ := digit 40 i ([126226149157589975746341902316111795087821178652033608920161735958946923079870511985886294867129905945234916616031849721433987644004584800004927027771687814726114274588084853161905303621743120, 2660427616327399435269531481718178401646082027935301662405787220980513690381215809495705737399288358085788155882573235272057163748261904316948553213991739791448677035952218303664639833339474945, 1239776632479440460244602490183314676691547349958322777359778274831490461234906931871140444825865134744593906462442277757210676840076939554254334611650596719953180810767997775417393455447621720, 680685397305202844481730047074739049850684476135515465580967989292822686912974557059058932175023691582793193531654587653421625127084123126121360498644757611592746733010595291706279375578552370, 2359441078723314407906557783535630859696363947135212612127674429424469707800345139931796134771291749332960158557197026408827764011363104189937445598002369409681521431006698551114156449727010595, 1791754269936980387159954496114408964656880037637619497637505127712020123491113231000397111323065666707872711214067982177652391611727069481362886028575371653022816591766911860414686323241216320, 1541088152341823624237729883312090527910832664816948779100557851341024978419659269577389250850737176470168489800182385030007969897233769982389941546953591982700802455662121076718277292290230645, 835185793909363909917313300847005245958202268679457184379754624500360860895227543323517272014935] : List ℕ)

def permV (k : Fin 120) (v : V) : V := ⟨((permWord k.val >>> (4*v.val)) % 16) % 10, by omega⟩

lemma permVgood : ∀ k : Fin 120, Autom (permV k) := by
  unfold Autom
  decide +kernel

lemma permVinj : ∀ k : Fin 120, Function.Injective (permV k) := by
  unfold Function.Injective
  decide +kernel

noncomputable def permEquiv (k : Fin 120) : Equiv.Perm V :=
  Equiv.ofBijective (permV k) (Finite.injective_iff_bijective.mp (permVinj k))

lemma imageBits (m t : ℕ) (k : Fin 120) (h : ∀ v : V, m.testBit v.val = t.testBit (permV k v).val) :
    (decode m).image (permEquiv k) = decode t := by
  ext u
  obtain ⟨v,rfl⟩ := (permEquiv k).surjective u
  have hh : permEquiv k v ∈ (decode m).image (permEquiv k) ↔ v ∈ decode m := by simp
  rw [hh]
  simpa [decode,permEquiv] using congrArg (· = true) (h v)

def singleRep (i : ℕ) : ℕ := digit 10 i ([78573957597998152557647779226802614155160323072, 546991629132700528092428079876994142004277476414, 1048063] : List ℕ)

def pairRep (i : ℕ) : ℕ := digit 20 i ([114725973609074075000109491161865487118005356286619033226030857900160287287629696631213748387840, 798909720900755881392578020957696775616100896332323364951706747266773848636547461320279710562304, 112642077850045298223365682517299979906470552628187816107166864065793705836134846598243011787776, 229453984256074743788803436817666581333535581202370550316096375986347712285595268220241002428417, 454734061901752821338900217318648017394800379034731200287931485646358104220288215684051444551681, 976215781102861010724132099112869098907358634470140234189129700761173837233142500104207823237121, 91786883635254566250442256158247979551287849636035534012753119879714032982154566221848303327233, 425535176285071611199243124491270125494560598463673205079543300572722184222679198779418413678595, 892782762123292537875602494762105965511123054530527967088740716797095820491697117046651554586627, 100134661048767288662001606443536093421122630241271050134999550493193607572178676794496673832963, 517319915460527399153542731733057727340251353007180791540617471963804698114081336659201376700421, 705053449433732465196883486905035713828352563218206134831846963438562958421921923094750313048069, 972052083553555746919745480852950244425295252749153865051347631934959474311055954922255504728069, 1722985742015674452268653352516374510664173386440959037641832008192252123144838072723290782654469, 2123483693195348666392168155063319091534131838337374672167452718450361192064993877159384784371717, 784322731078129172857075797867995314276176257025944539227766275533094659951824809230513443233799, 1835629852925037687307807514049250639733529195212002372389960356618258467439236581838128279863303, 508988545750877914282531661988708573254704065486404406265908701840969586814089657445892138852359, 1034642090759996194937848229185681912929981514206898021093676364958310750198226605597960439091211, 2069261734316994065343227939560153819485705669740193667927879854290948740430257144460799808884747, 2069269747196506948868016243547885524890652897137129335365177242922692921504972932000023259877387, 1243297915873653007623639622160307920794292766343880756717276381678808002902247101217003565727759, 1243299728121315487252875818795286580776177337246719939861738008569637652565651205259831450096682, 1501962548446404530492584436117676736333220250781125481761285943459308959809495823912904284651563, 1754373699398992320769270333980718569775861332313352362362948890435848587813254746429572267327535, 1177501491751842185137460920265352246] : List ℕ)

abbrev Rep := Fin 406

def leftRep (k : Rep) := (pairRep k.val) % 1024

def rightRep (k : Rep) := (pairRep k.val) / 1024

def firstCode (i : ℕ) : ℕ := digit 13 i ([38569952502296343774028938675791859572722333804570002496421888, 44999421199332912466623356848920006908097583714364730957381788, 70712483764290731533902964007979957444196155207414167179092121, 109284342337125418501515229976704159649863491732327637512454636, 98882100008364961827176112222275590180943889750998339260948650, 110084336079905545841241882793409679485541800773162147956195808, 122139884071268758178376947171510346372898858270792309605179874, 154284199199274909489020768965429131384000509642905945252676680, 97631834546760360861700649514380080678311775681644474373005444, 110589863044103915482514881491849272269937309261839306296066436, 110489447808528902785898747538343086094881033190861099107901729, 167137018812612387829021058165696941485440086632296879259099809, 142628129891441296396486448275971268127797306887634510082580882, 155587047237749206715552177391246023168499415581101059262006792, 155486631998432749883120794797312123190470723382303537774240423, 192854685064642007692928673097023761753713848072149432067548937, 73170643296686033274634140032038033063295823294179671641817222, 112045819977949499872929533395642400153362280155712159122768267, 163916349363607570667694053757272394247218153114148972448317721, 170651680100466351449103325670702442363730476351548370671174299, 111737941703029512538224389933296066494037840368451389113237804, 169595656016738468732084798261526233060493823622548377628189358, 170348810133296343362683351128353847162581938891642228976501346, 199279187872962888406995160592764597420914437870029131172349128, 124599870260447629990408874083342051808445369117568250459398581, 157045424847743536774450916601817883161676623516256570155303939, 172759364145559934130889874843329219598368740830344072584700469, 200785839600531277359289996922495935960420212632766733226968219, 156740237910390548875984478576576458264518471164135323967701694, 195312243858753228312983580126977221631974304944710322674534204, 200485960699492451765858045402170992522064037186805414636569427, 205711648451009789768883332942555850581231328667306280368015369, 104559076536345216142592437868273272339207176966334501247926408, 110988459384430145389815217570576735471478084243639874785526044, 152575355922889074596121119731066099760482204306909925767405961, 155991668638171877451573569412147998708782298759869468829631133, 127107995601527220260422541302583390528894244826838605481091370, 167643391600641919499335689293654119747356160792986980234953312, 180497511291940442980704309110518801338184513632616583193027243, 193357539686647365759659119145695074007905960063046840212866250, 124750532964306286480800201097466409542395102441605629272424708, 172608725966120029944617083965143751604454065646994404371628548, 157196087551602193264843604579255974486717208164667653200405001, 200886285490506840403570637455083388399466007064465267579978525, 156890900610507761174808693953946660741276345646334819551011346, 200586406589468014810131880453491806619602755532836706291435144, 195462906562611884803376268104416773712638546358485330114503463, 205812094340985352813163973475142884565104763527697123849136009, 151115218951074087676882203980902740368063754153139740250735036, 157847024452792154748955877038123560215976791028309109398831795, 189637277602722748689446292786117378487347707924154102371336885, 196369837063769105656213913732600732819748425603358304923125001, 157543755975371232295523029437136034320758141629439423960367676, 201339732367228684392640419328811942523483334788695332092642134, 196065545114340549888985783919767146996934244507725931355063124, 206515203300373193867785569123722447759145196161684972130870740, 184963840472626978213391404225691358773355098539671001026011785, 198325436249964754270469136676769215515097090949153707994129545, 198476098953075121922547041230619754952743427721101681131528969, 210231529619173361220483096796229030265293206853363292746032521, 197825040150487172375472871321418903100956622161808610166104850, 209378444439099649558096809754491664296953864981191761187309500, 209529107142210017210174714308344031150787292869803728325370761, 212141006876512945821654650128192829023921600745380775307847817] : List ℕ)

def firstPerm (m : Fin 1024) : Fin 120 := ⟨(firstCode m.val % 128) % 120, by omega⟩

def firstRep (m : Fin 1024) : Fin 34 := ⟨(firstCode m.val / 128) % 34, by omega⟩

set_option maxRecDepth 8000 in
lemma firstCheck : ∀ (m : Fin 1024) (v : V), m.val.testBit v.val =
    (singleRep (firstRep m).val).testBit (permV (firstPerm m) v).val := by decide +kernel

def second0 (i : ℕ) : ℕ := digit 17 i ([88928798495482919922597495328054612487350783573425957412674327071265225923624960, 103750422676360236468925428090398345083543053175439590755109110521419389366173980, 163036289959760120791429331164061781224492923536170049322362144977078283466047769, 251965395441601116460341838034025302627266016121292828404931768340740327561757548, 225158430898706965890169185708548038013013581178060755175131293370402481770201386, 252891199013448580849965780515626954045261087183261067836012374155380935925695328, 281608172942346939086867544105135041453255705018265792433789095142536385881834338, 355715906023145624232554490406995266013371472603163342790826007919984024856823880, 223711797032487215743594248278887525518569366441597083675712287300674529391935748, 253470627670127346560634334501603751937278594172857085104566263971052601270600452, 253354836906035438877576782463334749426472311201403400161465261342176640676266529, 385358261243446058449524733394279961337378302178864902193196247680090871181215009, 327461768283975265336978532090311001989271751739051989079034698043163821660046098, 357220776048040411849681491239337405722227777750505317245002773334278633154677768, 357104985283931654199957950848342879077880262794914973776935005497488842399810855, 444644799487335643933611347740245358506328083855975907226928874123106002399006217, 165872848959766783127747823581177672151799664003684524875802823909050565502435590, 255149589114935694086996975236878621160247912750713188182452711096525172241072907, 374241278935103456114742761077133427397639296263251577409452258950714119539393049, 389410947256065412629502564763713036091026477863617163124091222687665061127783707, 254801286578438568698512156137458905475861134047081330730793430577692591217705516, 388194911231816917026839864364404113231016019874298534307216373049184431456257326, 389063344833654609125289172309475215655581147806105634131302211183651651623584866, 459465726641741514071768601126827088724285012176405627590277753751228427533289800, 284444976649890189473311773756244498172945932239296009814909493866725590718087989, 358900081579861038753710274100552668361212184531280149430205153508367560550647811, 391842365574787977005886237978975328129673378691209027676192850489879028357530677, 461202618583109049401357400303840081559975239366836553618874418751676373781711131, 358552142574681743962288338940286122933672765241407059109954898411611225386648894, 447481258660483127393623817941454221206623825251974997791838739812141927370853948, 460855457869094447262676607382838463401914217664092323568333221924678632126809683, 474287792538567184961320516700414192361925980105660883784958380810723628694900745, 239111725720884269138677712150842171462882147896560987341167837110669726191976712, 253933343717665420838866154180836085087829569326470990090385892823366291809370652, 346336527701890123438801549189834112644112264739749248181070417440382782361961225, 357684378604434132061143324505341085384021082085361001094389092475092241288004893, 287339357047980341152402622660774636034835823792817770398202675666725192228012586, 385937863933617125723477923536397256203804640660221918379621467782730706103305312, 415580425879961287282785207579920825928221975505476835605284839347464814041367851, 445223865943577753416403257867566391539936850277545264625121176206354904413112650, 284618665667179806187061886253468620629104956121287810211201462190182400174588420, 391668678324365645133365637521173386862274810439953329433590583464862474022945796, 359073770597150655467460386599273357076016305320213471386249398871915699034260489, 461318411555780008017395727308559848644227287565372646055843904836824276111197725, 358725831591954510709371482287638567087421324105821275505653214339553501068002322, 460971250841765405878714934380075353520664807100992016215359601674834350692371720, 447654947677772744107373930440174909921428678445305772003437807817262481595565607, 474403585511238143577358843705133959446177830912663205151116993933007271116017417, 344656982319892934839669533851112057000589629433343647765823881972238381263881020, 359826113956671215422176217272918294934073969861766321297672575222856706926052659, 433528221794189391516142181454322244863021962580441806720578240961644461765690677, 448697520839598978172404699340767438177765473570199394691917440299736969562819081, 359478482822287883261269481896168077203283364497518340545456816222325780549207100, 461839696811630281747254333674985521950266460412810647320586172060725983938872918, 448349702863490828554843321506445198084085285538420215886185377994913822376461908, 475214135436464141388124892152741513513241594719177592147373124963539446630845268, 420732733902830419897759493777336164394271957770619545772375792305048441426412809, 450955034585693433540406324058389145155951142618903645968184172301875567078279433, 451128723602979680260823042725638922817242738758710660236353478217398606765360649, 479498463057922958295005355020285907670862945969138691049949432391148585168800521, 450376314876712852626778071698752722649562100609703165151871061320243643092436498, 478514330125462871813604405119195149501761874125169747523523410641718799413284668, 478688019142749118534021123786444927163054471181187406169769968778888417026901769, 489109408769370769423905459720280279891152340695715442479987037477370995431051529] : List ℕ)

def second1 (i : ℕ) : ℕ := digit 17 i ([4410050273936963979366909464015676027135942319059009602782701755476488487296, 4749284910383412623696426103543842482886787719741875910341631403125408539298, 5088519546851355671304903392624018038576438721714173281040743543043344310943, 5427754183297804315634384114288013746089338136604971812734015849515425212470, 6106223456222943209211894285536773750565791131502386851482217997418805338901, 6671614516984936285826889226043718690082761782274339043092185027197288850768, 7123927365594530747118885178449422662892587329287976937655424238309729117518, 7689318426356523823733880118956367602409561864141368454643572825734785280846, 7915474850661321054376893919271714669844712805610888176146608950732275065667, 8141631274966118285022511764744640194204633798943077354509468954580456842552, 8142514698498558899204716708028475568335750219205120925647031072888113341507, 8367787699270915515669656119447813954576206678238277339896315296005637548355, 8820100547880509976963869999970504183437232065138042566073299311423261782786, 9159335184337705822932866964274680764343788331533203098347547271391921323010, 9160218607870146437115077893869222645853256416014106890963150922402012083278, 9498569820794901668901863928578896894228152424783482360813085929443380182350, 8070073968831229453818872537531573572402042443940330147074663731982134944688, 8183152180983628069141895470875806430415017372744407769817482018015617754438, 8285629310747356378486987604844688157753248891150019924067202620356481262646, 8398707522899754993810752840716571138375813297377710203274989488940372732214, 9724726245099698899542998027332402909779923105225947977559971701123952158231, 9950882669404496130188960085670974734915769991735230865164407289116054531095, 9961042040027563193284004148700646229742084036061654730173548876245239867214, 10177039093709293360834574937988546831361941342326174638067073160816518769998, 9878000227970612134601104820288375240151145090326507320012737132197832569142, 10087813316926209310199606666265030432165069876687926906668570939234132703030, 9991078440123010749924103808389780674854122877200621699074002444612458787382, 10200891529078607925522605654366435866868047663562041285729836251648758921270, 10629351942318887822127373056028862859618373812578236637503617933875274069326, 11081664790928482283418949966685006781200379068936316205363010808183783439950, 11307821215201757817387267011966070474633936999386416084729855239142785431118, 11533977639519719084492181842527120826190021720795987158535868254437674860366, 6600057210830918464150260556238574427734899815323783576773284820510348157874, 6713135422983317079473259544339979862437882794494756512207975755721811698744, 7617761120202506002057215531286917393555986531562939545798363609765150467395, 7730839332354904617380214519388322828258969510733912481233054544564297148728, 10404078941546531205655923531715776250179691571860732174642493274513240761877, 11195626426575217798009148527700530650208211131920522254068167144183649281872, 10856391790156125666949835103547591853790549796627908802282295491370126683157, 11421782850893179065116398019437252683793151417887619655068403767275079871824, 9879325363269247344865711574258103199738735840084266880954615212316012062264, 9992403575421645960188710562359508634441714803338138347370628839585536288568, 10088696740458649924381817595859572662123693370877749888752751714911666579267, 10201774952611048539704816583960978096826672334131621355168765350788305267256, 10630235365851328436309583985623405089576983038092902400501408975072683640120, 11308704638734198431569477941560612704592539830871454361766232175606201599544, 11082548214460922897601160896279549011158985698302552549831260101105739122488, 11534861063052159698674392772121663056148624455939579661503272995716654450744, 9087777878196234973500050666485512085711116806645627431255113278848023671619, 9200856090348633588823049654586917520414097189668171092192440210350642574406, 9416411432264760513492314093555748424644661508787779745005445634767366140995, 9529489644417159128815313081657153859347641881669118740770417469877364209987, 10639511312941954885225449185431582442083812067859773188624643280273512875285, 11317980585824644903424386134457929357345027852159611749465688958788782016277, 11091824161551549346516663924289960366530263286930675557254588741930866198295, 11544137010142606170528938793221213711765561122289230089039937804313988974869, 11008782349482385558703574142433155092045245189037504655344590076454524433731, 11123185696933445095299888028348697157729276783760199307183090618976876640835, 11121860561634784174026573130534560526748222975911619034405855388869150651971, 11574173410257542671777521855162705393470776686305478290851914509475641310019, 11760134063842873975360044804239568407316322056490594953722036752183401141571, 11873212275996712407170702840783212867967789763946244050655467287217914795843, 11874095699529050177318075208689413556525002840172799507760330502079015573059, 11986290488149059600477431919696208452339829596558761348202110622118283597891] : List ℕ)

def second2 (i : ℕ) : ℕ := digit 17 i ([704275950533476186043190180000415691937128404904717502904874828416, 717439986992045834381954137127822505012571665503088634370656838818, 730604023450615482719259399027301992757911814190878988198075180191, 756932096367754779393828108929013723330202108113129678670588309504, 750761454277800256735659165310204444607896978234476811600747570349, 757343472507085080904301342785632377250969533858591220868029901834, 770096132826324427731112463879869588616347068540778950555858922503, 783260169284894076068375911882101831443297212889795571662895214869, 796424205743463724405681173781581319188636530441084940432755926714, 809588242202033372742965528732437184474781791034153779719850454530, 809639664219449660431783045743963965198555643662026382327257525005, 822752278660603021080249883683293049760927051627222619006944965122, 835916315119172669417534238634148915047071937677599785695303462413, 849080351577742317754818593585004780333217119466177942095193469954, 849131773595158605443636110596531561056990975340677501675481624333, 862244388036311966092102948535860645619362228943519329553641141517, 875408424494881614429387303486716510905506508760099257851295311536, 881990442724166438598030874758719351712525787270480621674730384919, 888572460953451262766649967478375367890236533328600788762548529927, 901736497412020911103956013388428241477796954388373210511160930839, 895334456243693093846131937759521888285596536182421999279061101335, 902147873551351212614473848735443956644847453341267480507731439383, 901916474472977918014772721438374912764722744938700652485690813703, 908318515641305735272600194446432604606542457034596188405937238807, 921482552099875383609882545814712039407014771491000174603596232711, 934646588558445031947166900765567904693160183199796465719337582087, 941228606787729856115765086536600298411675739522036024968243869959, 954392643246299504453093433191851702622377696300081095078362251015, 947990602077971687195267963766370441266230779225122960418904504839, 967556679704869152790377788142707567908522728448671325546369548295, 954572620307256511363910141241798373909303333963793654148128340743, 974138697934153976959020575404137022873321809554638537004228313351, 803417600112078850084840663930309376437279853143797099356401706674, 809999618341363674253482841405737309080352407882467793085625559818, 842909709487787795096693728782876972295715181575821261731744738837, 849491727717072619265335906258304904938787736314491955460968575509, 816427370518399635355672990520300490113582982249462790531307301653, 823009388747684459524315167995728422756655536988133484260531137802, 855919479894108580367526055372868085972018087254522732136561143573, 862501498123393404536168232848296018615090714304430194807227314965, 921533974117291671298700062826238820130789603124474257124326671362, 941280028805146143804582690660413010895697293337273335935959860490, 934698010575861319635984417777094685416934637043951918668450923789, 954444065263715792141910950203378483346152301259963999856122431490, 948067735104096118728494239283660612351892692420331468582924879125, 954649753333380942897136416759088544994965247159002162312148715018, 967608101722285440479195305154234348632297262868204892458804348685, 974190119951570264647838179527949735357342987351444649476444162325, 928475946468490509289042558637155687217138049494973074637538228245, 935057964697775333457684736112583619860210679791507494281085483541, 961386037614914630132187153564701280884802516317509748543509789207, 967968055844199454300873932530526274774158217460293654551363353621, 948222001156344981794925099359043946221799017526008925002185865493, 954804019385629805963611268538867417789428192891792123640110152469, 968148032905156461211690030794471423739357557791484115070287379223, 974550074073484278469516110005954207417230772198964348280587189525, 987302734392723625296304320568991365837740998898480645124745366285, 993884752622008449464947369167278616083280322107601267837884206357, 993936174639424737153764450617375738005820790500248905953333775373, 1007048789080578097802230852995275163766958889788083904055387131925, 1000646747912250280544428903886995477677406714052606336119469018133, 1007305899167659536246296137307710536762687375148994769308973305365, 1007228766141535104713069861790420365677026216056683994391422996237, 1013630807309862921970874859828707663375211023628644150970515755285] : List ℕ)

def second3 (i : ℕ) : ℕ := digit 17 i ([59384202209394262382057092483447634614923272181728150400, 59767326096195481302317261647230593890578534951456613794, 60533573867703826901324015405658320521746670192217302431, 62066069408658918740476484925374772578456024338340552448, 62832317179136464660052719685232998606810482797566767533, 63598564949614010579628954445091224635165374945410720538, 64364812720091556499205189204949450663520041195154744088, 65897308261046648338357658724665902720229399739324475648, 61335739502422507785880386169884900895180461080431306170, 62104980428253481619204965596773823118958400973846912258, 62101987272900053705456620929743126923535131762581597381, 66663556031524194257933893484524128748584030873415885058, 65166978354810237383761559969176031036953832083368747778, 65936219280641211217086139396064953260731776374830835458, 65933226125287783303337794729034257065308507163565532418, 67429803802001740177510128244382354776938741137984760578, 67812927685779901439080421568787524868157055240807396241, 68962299342956832016662597764098806833648100060111610769, 69728547113434377936238832523957032862002762358485708441, 71261042654389469775391302043673484918712125300701968128, 72410414310105788654755654183460823961244137920997128384, 73942909851060880493908123703177276017953488081390714368, 74709157621538426413484358463035502046308145981718314008, 76241653162493518252636827982751954103017513321981068288, 70530712748153058820795203288183613235436558022703358925, 77774148703448610091789297502468406159726863482374637568, 71296960518630604740371438048041839263791233102900146968, 78540396473926156011365532262326632188081538974888282648, 75511323256257107298040729227262082419741946043982462488, 80072892014881247850518001782043084244790888722964991488, 76277571026734653217616963987120308448096621124179247128, 80839139785358793770094236541901310273145564215478636568, 68234962591777057417645336515314583720190610111832535951, 69001210362551394895391078435497857374150481505981329052, 77010894088324492085961407409640876326795356492733129615, 77813059723043172970517778173867456700229174147183326978, 73215573100177897453060369614718100530101189636700272829, 73981820870655443372636604374576326558455865129213934618, 79309637399757129844690111689215554411859412519649066498, 80111803034475810729246482453442134785293230174099260418, 70533705903506486734543547955214309430859813661871992452, 71299953673984032654119782715072535459214501936208327938, 77777141858802038005537642169499102355150031572929917698, 78543389629279583925113876929357328383504724245312747778, 75514316411610535211789073894292778615165197285104598018, 76280564182088081131365308654151004643519889957487428098, 80075885170234675764266346449073780440214087599845851138, 80842132940712221683842581208932006468568780272228681218, 82371635326313885609246706061617762329854913963555345408, 83137883096791431528822940821475988358209589490428728858, 83904130867268977448399175581334214386564255740172752408, 85436626408224069287551645101050666443273614284342483968, 86969121949179161126704114620767118499982964444736053248, 87735369719656707046280349380625344528337639971609436698, 88501617490134252965856584140483570556692306221353460248, 90034113031089344805009053660200022613401664765523191808, 84706296501987658332955546345560794759998046628386756098, 85475537427818632166280125772449716983775990919848843778, 85472544272465204252531781105419020788352721708583540738, 90800360801566890724585288420058248641756287103521578498, 89303783124852933850412954904710150930126097109567463938, 90073024050683907683737534331599073153904041401029551618, 90070030895330479769989189664568376958480772189764248578, 91566608572044436644161523179916474670111006164183476738] : List ℕ)

def second4 (i : ℕ) : ℕ := digit 17 i ([885670611068206427656225186242249575903528064, 2448116571540258211510071447719675403916289954, 4047672365819239860435379490385180145997588383, 5352178847647349553968572385435606761435347954, 4004900233426745579331887155729436608890417837, 5374479592845880177110108103708255122941326305, 5396780338044410800251643821980903484447306724, 5441381828441472046534715258526200207459283712, 4189229830458350261236143327076795721963284410, 5354443767081575320381384606822672610650797444, 5354269542509711799888091359023667545326513605, 5463682573640002669676250976798848568965263362, 5421171778105303669312698513841612629844472723, 5443646747875697812947527479913266056674734594, 5443472523303834292454234232114260991350468866, 5485983318838533292817786695071496930471244802, 2977672157719428750874898132795571457021199808, 5508284064037063915959322413344145291977211025, 5530584809235594539100858131616793653483177392, 5575186299632655785383929568162090376495167744, 5521350906926827952956315998269525191297104320, 5619787790029717031667001004707387099507129088, 5642088535228247654808536722980035461013108708, 5686690025625308901091608159525332184025071104, 5554976249296487408161912823477502798880357581, 5731291516022370147374679596070628907037032448, 5577276994495018031303448541750151160386352920, 5753592261220900770516215314343277268543013144, 5666479975289140523869591414840744606410275608, 5798193751617962016799286750888573991554974464, 5688780720487671147011127133113392967916256280, 5820494496816492639940822469161222353060955160, 4210223891367904480677979686856906093537281469, 5510548983471289682372134634731211141192648114, 5709164995395703044726437125596985610855300239, 5733556435456595913787491817457694756252481794, 5599751964265412174938277507821804587216566717, 5622052709463942798079813226094452948722579425, 5776067230991294914151044280414930695373257474, 5800458671052187783212098972275639840770424322, 5555150473868350928655206071276507864204608904, 5577451219066881551796741789549156225710618626, 5731465740594233667867972843869633972361295618, 5753766485792764291009508562142282333867276802, 5666654199861004044362884662639749671734540179, 5688954945059534667504420380912398033240521986, 5798367976189825537292579998687579056879238146, 5820668721388356160434115716960227418385219330, 5842795242015023263082358187433870714566926524, 5865095987213553886223893905706519076072916506, 5887396732412084509365429623979167437578896920, 5931998222809145755648501060524464160590858496, 5976599713206207001931572497069760883602819840, 5998900458404737625073108215342409245108800538, 6021201203603268248214643933615057606614780952, 6065802694000329494497715370160354329626742528, 5911788172472977378426484315839876582976062978, 5934263142243371522061313281911530009806309378, 5934088917671508001568020034112524944482043650, 6088103439198860117639251088433002691132721666, 6045592643664161117275698625475766752011947010, 6068067613434555260910527591547420178842193410, 6067893388862691740417234343748415113517927682, 6110404184397390740780786806705651052638703618] : List ℕ)

def second5 (i : ℕ) : ℕ := digit 17 i ([3143325190160107595367808, 11857567090580499778775458, 12237422444546326865655026, 20778412524626438940304626, 12460259112956738249176297, 20783134891109308585517537, 20853970388352353263724004, 20929528252078267587171344, 8686202849428353664955834, 21005086115804181910566812, 18206493678893558415784689, 21156201843256010557429504, 21231759706981924880832147, 21382875434433753527687680, 21533991161885582174526464, 21685106889337410821365248, 13413291698780868523863216, 21760664753063325144756625, 21836222616789239468158896, 21911780480515153791620808, 21068838063322922120933312, 21916502846998023436837136, 21987338344241068115030500, 22062896207966982438462224, 21151479476773140912193229, 22214011935418811085300992, 22289569799144725408709581, 22440685526596554055559168, 22516243390322468378975466, 22667359117774297025817344, 22818474845226125672656128, 22969590572677954319494912, 13874312726671017637852594, 21009808482287051555762913, 21312039937190708849464975, 21387597800916623172901136, 21085366346012965879184102, 21160924209738880202633441, 21614271392094366143159312, 21689829255820280466578704, 18861131732581362983537540, 23045148436403868642900380, 23120706300129782966322831, 23271822027581611613172480, 23200986530338566934955667, 23276544394064481258385936, 23422937755033440260011264, 23498495618759354583430672, 22143176438175766407069398, 22218734301901680730511328, 22596523620531252347608290, 22672081484257166671030800, 22369850029353509377342422, 22445407893079423700772624, 22898755075434909641288976, 22974312939160823964708368, 23649611346211183230269440, 23725169209937097553688848, 23876284937388926200527616, 24027400664840754847366400, 23956565167597710169160464, 24032123031323624492579856, 24178516392292583494205184, 24254074256018497817624592] : List ℕ)

def second6 (i : ℕ) : ℕ := digit 17 i ([1664, 10914, 18417, 48626, 14057, 47585, 49380, 82432, 14010, 47516, 31729, 75741, 55443, 82688, 77267, 82944, 18392, 48529, 34713, 78235, 31704, 75694, 64740, 83200, 49357, 82487, 64717, 83255, 77290, 82999, 83456, 83712, 21938, 34972, 57999, 78749, 36053, 64225, 80811, 83968, 35976, 64156, 68751, 84224, 67475, 84480, 84736, 84992, 58044, 78816, 79285, 85248, 68796, 84279, 84962, 85504, 80786, 84023, 84917, 85559, 84791, 85047, 85760, 86016] : List ℕ)

def second7 (i : ℕ) : ℕ := digit 17 i ([1920, 0, 22175, 0, 22191, 0, 58596, 0, 22202, 0, 36829, 0, 58515, 0, 81831, 0, 22150, 0, 36761, 0, 36782, 0, 69092, 0, 58555, 0, 69051, 0, 81854, 0, 85971, 0, 22194, 0, 58511, 0, 36821, 0, 81835, 0, 36740, 0, 69007, 0, 69011, 0, 85927, 0, 58556, 0, 81845, 0, 69052, 0, 85972, 0, 81801, 0, 85897, 0, 85906, 0, 86272, 0] : List ℕ)

def second8 (i : ℕ) : ℕ := digit 17 i ([1569711263664483990151085688960, 2732069816471063101771308873634, 0, 0, 3347403383116281762154590123948, 3367222520972037432690540071136, 0, 0, 2732993359353941237010586286010, 3377121346073444881744989309060, 0, 0, 3368146277837146822960527493266, 3406836911544174229451299706368, 0, 0, 3416726486119937547223286426502, 3426643569070759391047461941905, 0, 0, 3426870984663770754910722748864, 3436547240500769885077496730798, 0, 0, 3427567333019418505621916398285, 3437707816371149653389649728286, 0, 0, 3437475771088097646197960938730, 3446451063046507830934084081414, 0, 0, 3363573274493468051390906518408, 3456350774181926628402335350450, 0, 0, 3466254298628280343114151657148, 3486065671437798650054285787360, 0, 0, 3457275452498795988611420946056, 3495967047797698469434548617348, 0, 0, 3486991984283766893518599028882, 3525680062009935446813899317760, 0, 0, 3535582417080288840927629322686, 3545486719536520608412123080160, 0, 0, 3545718757736022891299342447550, 3555390390966531102440096350934, 0, 0, 3546415106091670642008474592658, 3556550966836910870752249339678, 0, 0, 3556318921553858863560560558782, 3565294213512269048296683692806, 0, 0] : List ℕ)

def second9 (i : ℕ) : ℕ := digit 17 i ([3444966349253406183393664, 13672136411623160952141986, 0, 0, 14499140841935707570191080, 26429019169285148791327462, 0, 0, 8761760713154267988376250, 22052270883380525736708740, 0, 0, 21595972221973246267939475, 27351946668780985077819648, 0, 0, 13791081017410440140959152, 27427504532506899401192593, 0, 0, 21219953790774750767772608, 27503062396232813724640174, 0, 0, 21227037340499055235612621, 27519000383112498777251227, 0, 0, 27578620259958728048057834, 27654178123684642371496502, 0, 0, 14856564955107903842307506, 22411170736078618772930482, 0, 0, 23712477850014385382133222, 27729735987410556694888934, 0, 0, 19238921051210934600633732, 24603529375750851563422084, 0, 0, 24831973854359670650636435, 27880851714862385341755392, 0, 0, 26571575607486776206214358, 27956409578588299665156320, 0, 0, 27780501427101405380935382, 28031967442314213988582870, 0, 0, 27787584976825709848770953, 28047905429193899041189686, 0, 0, 28107525306040128312002750, 28183083169766042635432246, 0, 0] : List ℕ)

def second10 (i : ℕ) : ℕ := digit 17 i ([253162552298112, 732549622020514, 0, 0, 548673482152878, 1313624337472736, 0, 0, 733271176526266, 1501967243324804, 0, 0, 1314655129623698, 1649267441759744, 0, 0, 764160581319057, 1503135474427537, 0, 0, 1080819930135744, 1608276273867438, 0, 0, 1503857028933307, 1653665488262531, 0, 0, 1609307066018538, 1658063534782209, 0, 0, 970851587480456, 1313675877055644, 0, 0, 1168763680495018, 1468243160140256, 0, 0, 1312954322549892, 1607623438824836, 0, 0, 1467074929035666, 1666859627805184, 0, 0, 1646484302912702, 1650882349443763, 0, 0, 1664076488968638, 1668474535497174, 0, 0, 1651294666304137, 1659678442483081, 0, 0, 1668886852357522, 1671257674316545, 0, 0] : List ℕ)

def second11 (i : ℕ) : ℕ := digit 17 i ([2944, 15266, 0, 0, 23727, 57057, 0, 0, 15290, 52356, 0, 0, 56979, 97536, 0, 0, 18880, 49553, 0, 0, 32192, 77486, 0, 0, 49613, 90499, 0, 0, 77546, 97792, 0, 0, 23944, 37020, 0, 0, 38589, 68321, 0, 0, 36996, 66180, 0, 0, 68243, 98048, 0, 0, 59582, 81376, 0, 0, 69566, 85718, 0, 0, 81298, 95369, 0, 0, 85694, 98304, 0, 0] : List ℕ)

def second12 (i : ℕ) : ℕ := digit 17 i ([249080344840925340159755138123272056364872534322542401317026686088252544, 0, 0, 0, 333011121578390789200722627215681911758216882048831613767409003672517803, 0, 0, 0, 313987247319047917842412686936204440386720856371998886336463107837541523, 0, 0, 0, 334737078144528543648832224024388574347831673092948654566654178418665363, 0, 0, 0, 313603065919316289741108310102514624920216996370605363171207860913454214, 0, 0, 0, 335599546321184651298874662251385712391754844203666889809976040053830830, 0, 0, 0, 335781525344123709122102589725265268117146740455704437790142452421547445, 0, 0, 0, 337325364047875381770154904060155689574121701989892386820975827735091902, 0, 0, 0, 333327901723060070462762884609033586699353438006963095392803598741027976, 0, 0, 0, 336469339718487761379187183912741769918124456651824390328558005956277419, 0, 0, 0, 335788265382212514198338968132517117846953744250492751126314904912950408, 0, 0, 0, 337332104085964186846391282467407539303928922152582437723879821719564947, 0, 0, 0, 334972977266489972416731924785743140384202061255544053630012512357885908, 0, 0, 0, 337402874100231509524718431842149927743968788332418517531520677104644820, 0, 0, 0, 337632034829608690537592959757223186117391366480037303963651209674824338, 0, 0, 0, 339050869437232325709950274121951170273595819509682250891682895115010962, 0, 0, 0] : List ℕ)

def second13 (i : ℕ) : ℕ := digit 17 i ([886695557317756762123428734365912358679926946693423614746068782464, 0, 0, 0, 2019419756963741971394616669311435653564894226298642331076556506797, 0, 0, 0, 1670855611907435872746264511572972750823363213069732173249792460485, 0, 0, 0, 2426399313804950884543043404775033441030262809170123699241858679443, 0, 0, 0, 1668695887175951789814590316815506464235134197746805958114916976304, 0, 0, 0, 2176282621092127566133236584884123888938058318058164531903504352960, 0, 0, 0, 2175665556883132113868608755802754302080504906406461478798452908469, 0, 0, 0, 2524512523035227794806845652717794893613845354720177878931691614954, 0, 0, 0, 2020191087224986286727570660473205881978642873942960869626255263410, 0, 0, 0, 2491653853906219961651188892869313692265135557524866675355802437309, 0, 0, 0, 2175716978900548401557426272814281082804274874887901921122671691396, 0, 0, 0, 2524563945052644082495663169729321674337615739360164624143394864531, 0, 0, 0, 2425987937665620583031434139597578701732980371990721592800015598292, 0, 0, 0, 2524718211104892945561268292446357852829562265676017355176030567892, 0, 0, 0, 2525900917505467562405141096807287688825678179428958989057116942985, 0, 0, 0, 2593315182338220722444788994231176795442398451383453844606061464210, 0, 0, 0] : List ℕ)

def second14 (i : ℕ) : ℕ := digit 17 i ([476062701733393773738498804324642724832911705509504, 0, 0, 0, 995469129221283088662079031285287820012869619698861, 0, 0, 0, 1014137468063276891674148759128957564623892193361372, 0, 0, 0, 1154593956933431294193329014643550622331551277034387, 0, 0, 0, 849146490131030786094169964422556463578866992823942, 0, 0, 0, 1065634253749107569150393701650858904247839546704044, 0, 0, 0, 1157515620072686325830101972646913241408390437984205, 0, 0, 0, 1163363388380880621422144893299521912707573488888766, 0, 0, 0, 1130133789373215705090401728917457255282992359685768, 0, 0, 0, 1160461820303744328239068378497296537865233221976234, 0, 0, 0, 1157538456209994193051719398515672232335634661406088, 0, 0, 0, 1163386224518188488643762319168280903634819848533139, 0, 0, 0, 1162368329827020472471651542723187538837436393639612, 0, 0, 0, 1166285544924123170548954857780651314129408547947452, 0, 0, 0, 1169209689543955254308113791512415162351660573859474, 0, 0, 0, 1172132848401159734268321672048132239914307053503634, 0, 0, 0] : List ℕ)

def second15 (i : ℕ) : ℕ := digit 17 i ([1622988999194625155273249871631686028195008384, 0, 0, 0, 4428614392198827419021065802909755477504052909, 0, 0, 0, 4367635792046595246368429073257982614011136197, 0, 0, 0, 7931050960371179895695226306308583691212867219, 0, 0, 0, 3066439577083892442207807886388652239734462353, 0, 0, 0, 5699756868515072938088601744450712083344953024, 0, 0, 0, 6880041230604492519903708958810527122581414861, 0, 0, 0, 8241170698288246373757207388537599968405437674, 0, 0, 0, 5079952954110598783197872699490192192270522255, 0, 0, 0, 7067158420785913529700657094941967280842510013, 0, 0, 0, 6880215455176356040397002206609532187905657220, 0, 0, 0, 8241344922860109894250500636336605033729687443, 0, 0, 0, 6925339619289007848159953386551844106890438356, 0, 0, 0, 7416740024230067399493558803645630853981212372, 0, 0, 0, 8468882213713867658491482261837220347220407945, 0, 0, 0, 8579863265990930212719281109803446958777519250, 0, 0, 0] : List ℕ)

def second16 (i : ℕ) : ℕ := digit 17 i ([1627394176, 0, 0, 0, 6630035628, 0, 0, 0, 6269845468, 0, 0, 0, 11829694634, 0, 0, 0, 6264995718, 0, 0, 0, 9990865324, 0, 0, 0, 13073570235, 0, 0, 0, 13418180542, 0, 0, 0, 6634360974, 0, 0, 0, 10560901802, 0, 0, 0, 9983000974, 0, 0, 0, 12467504298, 0, 0, 0, 11842408636, 0, 0, 0, 12479169724, 0, 0, 0, 13409398674, 0, 0, 0, 13488965522, 0, 0, 0] : List ℕ)

def second17 (i : ℕ) : ℕ := digit 17 i ([4480, 0, 0, 0, 24239, 0, 0, 0, 22714, 0, 0, 0, 60051, 0, 0, 0, 22673, 0, 0, 0, 37312, 0, 0, 0, 58811, 0, 0, 0, 82154, 0, 0, 0, 24242, 0, 0, 0, 38845, 0, 0, 0, 37252, 0, 0, 0, 69779, 0, 0, 0, 60118, 0, 0, 0, 69846, 0, 0, 0, 82057, 0, 0, 0, 86162, 0, 0, 0] : List ℕ)

def second18 (i : ℕ) : ℕ := digit 17 i ([292744970900096, 758937901092770, 0, 0, 0, 0, 0, 0, 759968693243834, 1515161382858628, 0, 0, 0, 0, 0, 0, 768558627832465, 1528699119774865, 0, 0, 0, 0, 0, 0, 1530039149571277, 1772412744063107, 0, 0, 0, 0, 0, 0, 975249633992584, 1322471970079388, 0, 0, 0, 0, 0, 0, 1321750415573636, 1612021485336196, 0, 0, 0, 0, 0, 0, 1718227436625342, 1763169974430899, 0, 0, 0, 0, 0, 0, 1762139182279817, 1776810790579849, 0, 0, 0, 0, 0, 0] : List ℕ)

def second19 (i : ℕ) : ℕ := digit 17 i ([4992, 20898, 0, 0, 0, 0, 0, 0, 20922, 53892, 0, 0, 0, 0, 0, 0, 19136, 51089, 0, 0, 0, 0, 0, 0, 51149, 91267, 0, 0, 0, 0, 0, 0, 24968, 37810, 0, 0, 0, 0, 0, 0, 37768, 66948, 0, 0, 0, 0, 0, 0, 59838, 81632, 0, 0, 0, 0, 0, 0, 81554, 95625, 0, 0, 0, 0, 0, 0] : List ℕ)

def second20 (i : ℕ) : ℕ := digit 17 i ([13935243125943394426619523949767032810372645245352017223750784, 0, 0, 0, 0, 0, 0, 0, 19865606214534663389313649957082375035718313526964055248879748, 0, 0, 0, 0, 0, 0, 0, 18916152406256523582045378645697446976907596419397199327150214, 0, 0, 0, 0, 0, 0, 0, 20272051625981558373759304621347195114641691762167951018609077, 0, 0, 0, 0, 0, 0, 0, 19867556424447293777166154080953921708878693911819391152177288, 0, 0, 0, 0, 0, 0, 0, 20272443947833209648679583049567958023352149460203393111324292, 0, 0, 0, 0, 0, 0, 0, 20275190197801453367429361515671391345720923496964945245948348, 0, 0, 0, 0, 0, 0, 0, 20337964304115213658035176439804829905552514966661677317297545, 0, 0, 0, 0, 0, 0, 0] : List ℕ)

def second21 (i : ℕ) : ℕ := digit 17 i ([78048022415271959534520885358350868383573930088532546944, 0, 0, 0, 0, 0, 0, 0, 148879547275741353314983558972187901142263540729310626692, 0, 0, 0, 0, 0, 0, 0, 112072715894542909998493911025638732852474942193823400849, 0, 0, 0, 0, 0, 0, 0, 152719765595474708433032889211842055507467205243878559669, 0, 0, 0, 0, 0, 0, 0, 137495080889369940210703811989858142902055938522030818191, 0, 0, 0, 0, 0, 0, 0, 152722758750828136346781233878872751702890173807433119620, 0, 0, 0, 0, 0, 0, 0, 152743710838301434844732192466114452079657399300462271444, 0, 0, 0, 0, 0, 0, 0, 155063406239083595515810107525205816088973793220802715529, 0, 0, 0, 0, 0, 0, 0] : List ℕ)

def second22 (i : ℕ) : ℕ := digit 17 i ([1996003807554422531414093409301530887447385728, 0, 0, 0, 0, 0, 0, 0, 5170462619193697679463714931073323628226435460, 0, 0, 0, 0, 0, 0, 0, 3088740322282423065349343604661300601240443270, 0, 0, 0, 0, 0, 0, 0, 6946943466200084389328316113628472207099357133, 0, 0, 0, 0, 0, 0, 0, 5169155934904721275764015572580785638294444424, 0, 0, 0, 0, 0, 0, 0, 6947117690771947909821609361427477272423598724, 0, 0, 0, 0, 0, 0, 0, 6947640364487538471301489104824492468396419028, 0, 0, 0, 0, 0, 0, 0, 8489876274623421877933318621617330718794397577, 0, 0, 0, 0, 0, 0, 0] : List ℕ)

def second23 (i : ℕ) : ℕ := digit 17 i ([301541063923584, 0, 0, 0, 0, 0, 0, 0, 922387176510340, 0, 0, 0, 0, 0, 0, 0, 904898069677201, 0, 0, 0, 0, 0, 0, 0, 1582815707713979, 0, 0, 0, 0, 0, 0, 0, 984458043875506, 0, 0, 0, 0, 0, 0, 0, 1339342601618308, 0, 0, 0, 0, 0, 0, 0, 1722625483136982, 0, 0, 0, 0, 0, 0, 0, 1766537228791945, 0, 0, 0, 0, 0, 0, 0] : List ℕ)

def second24 (i : ℕ) : ℕ := digit 17 i ([6272, 0, 0, 0, 0, 0, 0, 0, 25274, 0, 0, 0, 0, 0, 0, 0, 23174, 0, 0, 0, 0, 0, 0, 0, 60365, 0, 0, 0, 0, 0, 0, 0, 25266, 0, 0, 0, 0, 0, 0, 0, 38020, 0, 0, 0, 0, 0, 0, 0, 60374, 0, 0, 0, 0, 0, 0, 0, 82313, 0, 0, 0, 0, 0, 0, 0] : List ℕ)

def second25 (i : ℕ) : ℕ := digit 17 i ([437725886945664, 0, 0, 0, 671784424728490, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1041237511529350, 0, 0, 0, 1203965232453822, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1041185971921800, 0, 0, 0, 1203913692846268, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1726954810174652, 0, 0, 0, 1735750903206332, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ)

def second26 (i : ℕ) : ℕ := digit 17 i ([6784, 0, 0, 0, 26797, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25734, 0, 0, 0, 39360, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25736, 0, 0, 0, 39357, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61116, 0, 0, 0, 70332, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ)

def second27 (i : ℕ) : ℕ := digit 17 i ([1747977576078264060396481551232, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3451428852887702929512478036614, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3451544910356681744271955743368, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4017180450335457434563017486524, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ)

def second28 (i : ℕ) : ℕ := digit 17 i ([6391723034564064796744832, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15982259065461955520124080, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 15982849361272314225775794, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27243922535485341943518164, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ)

def second29 (i : ℕ) : ℕ := digit 17 i ([446521979968896, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1045635558040966, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1045584018433416, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1731352856686012, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ)

def second30 (i : ℕ) : ℕ := digit 17 i ([7808, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26246, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26248, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 61372, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ)

def second31 (i : ℕ) : ℕ := digit 17 i ([8064, 0, 0, 0, 0, 0, 0, 0, 27066, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27058, 0, 0, 0, 0, 0, 0, 0, 39556, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ)

def second32 (i : ℕ) : ℕ := digit 17 i ([8320, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 27272, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ)

def second33 (i : ℕ) : ℕ := digit 17 i ([8576, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ)

def secondCode (i : Fin 34) (m : Fin 1024) : ℕ := (![second0, second1, second2, second3, second4, second5, second6, second7, second8, second9, second10, second11, second12, second13, second14, second15, second16, second17, second18, second19, second20, second21, second22, second23, second24, second25, second26, second27, second28, second29, second30, second31, second32, second33] : Fin 34 → ℕ → ℕ) i m.val

def nextPerm (i : Fin 34) (m : Fin 1024) : Fin 120 := ⟨(secondCode i m % 128) % 120, by omega⟩

def nextSwap (i : Fin 34) (m : Fin 1024) := (secondCode i m).testBit 7

def nextRep (i : Fin 34) (m : Fin 1024) : Rep := ⟨(secondCode i m / 256) % 406, by omega⟩

def NextOK (i : Fin 34) (m : Fin 1024) : Prop :=
    Disjoint (decode (singleRep i.val)) (decode m.val) → ∀ v : V,
    let k := nextRep i m
    let w := permV (nextPerm i m) v
    ((if nextSwap i m then m.val else singleRep i.val).testBit v.val = (leftRep k).testBit w.val) ∧
    ((if nextSwap i m then singleRep i.val else m.val).testBit v.val = (rightRep k).testBit w.val)

set_option maxRecDepth 8000 in
lemma nextCheck0 : ∀ m, NextOK 0 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck1 : ∀ m, NextOK 1 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck2 : ∀ m, NextOK 2 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck3 : ∀ m, NextOK 3 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck4 : ∀ m, NextOK 4 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck5 : ∀ m, NextOK 5 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck6 : ∀ m, NextOK 6 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck7 : ∀ m, NextOK 7 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck8 : ∀ m, NextOK 8 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck9 : ∀ m, NextOK 9 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck10 : ∀ m, NextOK 10 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck11 : ∀ m, NextOK 11 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck12 : ∀ m, NextOK 12 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck13 : ∀ m, NextOK 13 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck14 : ∀ m, NextOK 14 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck15 : ∀ m, NextOK 15 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck16 : ∀ m, NextOK 16 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck17 : ∀ m, NextOK 17 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck18 : ∀ m, NextOK 18 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck19 : ∀ m, NextOK 19 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck20 : ∀ m, NextOK 20 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck21 : ∀ m, NextOK 21 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck22 : ∀ m, NextOK 22 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck23 : ∀ m, NextOK 23 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck24 : ∀ m, NextOK 24 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck25 : ∀ m, NextOK 25 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck26 : ∀ m, NextOK 26 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck27 : ∀ m, NextOK 27 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck28 : ∀ m, NextOK 28 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck29 : ∀ m, NextOK 29 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck30 : ∀ m, NextOK 30 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck31 : ∀ m, NextOK 31 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck32 : ∀ m, NextOK 32 m := by
  unfold NextOK
  decide +kernel

set_option maxRecDepth 8000 in
lemma nextCheck33 : ∀ m, NextOK 33 m := by
  unfold NextOK
  decide +kernel

lemma nextCheck (i : Fin 34) (m) : NextOK i m := by
  fin_cases i <;> first
  | exact nextCheck0 m
  | exact nextCheck1 m
  | exact nextCheck2 m
  | exact nextCheck3 m
  | exact nextCheck4 m
  | exact nextCheck5 m
  | exact nextCheck6 m
  | exact nextCheck7 m
  | exact nextCheck8 m
  | exact nextCheck9 m
  | exact nextCheck10 m
  | exact nextCheck11 m
  | exact nextCheck12 m
  | exact nextCheck13 m
  | exact nextCheck14 m
  | exact nextCheck15 m
  | exact nextCheck16 m
  | exact nextCheck17 m
  | exact nextCheck18 m
  | exact nextCheck19 m
  | exact nextCheck20 m
  | exact nextCheck21 m
  | exact nextCheck22 m
  | exact nextCheck23 m
  | exact nextCheck24 m
  | exact nextCheck25 m
  | exact nextCheck26 m
  | exact nextCheck27 m
  | exact nextCheck28 m
  | exact nextCheck29 m
  | exact nextCheck30 m
  | exact nextCheck31 m
  | exact nextCheck32 m
  | exact nextCheck33 m


lemma canonical {A B : Finset V} (h : Bad A B) : ∃ r : Rep, Bad (decode (leftRep r)) (decode (rightRep r)) := by
  obtain ⟨m,rfl⟩ := decodeSurj A
  let k := firstPerm m
  let i := firstRep m
  have h₁ := bad_rename h (permEquiv k) (permVgood k) false
  simp only [Bool.false_eq_true,↓reduceIte] at h₁
  rw [imageBits _ _ k (firstCheck m)] at h₁
  obtain ⟨b,hb⟩ := decodeSurj (B.image (permEquiv k))
  rw [← hb] at h₁
  have hc := nextCheck i b (bad_frame h₁).2.1
  let t := nextPerm i b
  let w := nextSwap i b
  have hh := bad_rename h₁ (permEquiv t) (permVgood t) w
  refine ⟨nextRep i b, ?_⟩
  cases he : w <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at hh
  · have e : nextSwap i b = false := he
    rw [imageBits _ _ t (fun v => by simpa [e] using (hc v).1),
      imageBits _ _ t (fun v => by simpa [e] using (hc v).2)] at hh
    exact hh
  · have e : nextSwap i b = true := he
    rw [imageBits _ _ t (fun v => by simpa [e] using (hc v).1),
      imageBits _ _ t (fun v => by simpa [e] using (hc v).2)] at hh
    exact hh

def kindRep (i : ℕ) : ℕ := digit 3 i ([0, 0, 35812647670272, 40210710958665, 40210710958665, 40210710958665, 40210710958665, 40210710958665, 40210710958665, 40279430435401, 40210712007435, 40210710958665, 40210710958665, 40210710958665, 40210710958665, 40210710958665, 40210710958665, 40210710958665, 40210710958665, 40210710958665, 40210710958665, 40211382047305, 40210710958665, 40210710958665, 40210710958665, 37449] : List ℕ)

def cliqueWord (i : ℕ) : ℕ := digit 20 i ([0, 0, 844866782293287936115380808947363926390638538165277155409195512353798933564100178035443637420032, 702503081935925289242964010997872012931319299863964635926360801433005865083267670873271647421217, 835967642071198176431543802933055545573600393642938431223571744988739971388376738002304610157344, 986708304320208157527687778133630790489679363788342366947555579879089153074071603149184255214368, 560103946209807821768164206215567778630822873129138470146775643860352711375376175958587042251553, 986186687307739607577063512948647615709287092307327117342529189805452946323763851613080379749424, 702501044899690469883741056289391850198843394916379119141388300073595511190112689895957730701840, 560104336111467495992925092811470016230736799623879622507175471662652263520178989326985517814832, 560104081978921852233591694199187114438152706750914205941331312807226265084709537687884632424448, 844311205628116707440816627259597490728288304212100504488020757845581604746854008289692070789904, 844311205627995290758534278845177641198245635739679185005816832230005816775109118787781988340496, 702468452293115895347761299675537600530833436957892642201611659564334432049725390381415104140048, 702468452293115895471242825099928672356782625966383688150000384874012077000484374184254918373904, 560103946209678312238356978116377034958071321047312062203121913536749908972314737271357466489360, 560103946209678312238356978116377034958071321047312062203121913536749908972314737271357466489360, 560103946209678312238356978116377035158938576579783256300894356841277462385580417651228014817808, 560103946209678312238356978116587659541408537562134328040632401820513288038703513207679651951120, 560103946209807791878878858984629235422075915935376851526134910140583342838988435910189201502736, 560103946209678312238356978116377034958071321047312062203121913536749908972314737271357466489360, 560103946209678312238356978116488928846594189141785143465657896218227452185414227973978116600336, 560103946209799729044121086183309501327247790978977212630562755333577883805165475277124059542032, 560103946209678312238356978116377034958071321047312062203121913536829137134829001608951010439696, 560103946209807317594481342937492780475321320349706284624834523479328299277744718331548734337552, 348553541445314325073200094694879760] : List ℕ)

def cliqueV (k : Rep) (j : Fin 5) : V := ⟨((cliqueWord k.val >>> (4*j.val)) % 16) % 10, by omega⟩

def Classified (k : Rep) : Prop :=
  (kindRep k.val = 0 → ∀ r, ¬ fires (decode (leftRep k)) (decode (rightRep k)) (rows r)) ∧
  (kindRep k.val = 1 → Clique (decode (leftRep k)) (decode (rightRep k)) (cliqueV k)) ∧
  (kindRep k.val ≠ 0 → kindRep k.val ≠ 1 → (leftRep k = 5 ∧ rightRep k = 26) ∨
    (leftRep k = 5 ∧ rightRep k = 50) ∨
    (leftRep k = 5 ∧ rightRep k = 58) ∨
    (leftRep k = 5 ∧ rightRep k = 90) ∨
    (leftRep k = 42 ∧ rightRep k = 261))

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified0 : ∀ t : Fin 16, Classified ⟨0+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified1 : ∀ t : Fin 16, Classified ⟨16+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified2 : ∀ t : Fin 16, Classified ⟨32+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified3 : ∀ t : Fin 16, Classified ⟨48+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified4 : ∀ t : Fin 16, Classified ⟨64+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified5 : ∀ t : Fin 16, Classified ⟨80+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified6 : ∀ t : Fin 16, Classified ⟨96+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified7 : ∀ t : Fin 16, Classified ⟨112+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified8 : ∀ t : Fin 16, Classified ⟨128+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified9 : ∀ t : Fin 16, Classified ⟨144+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified10 : ∀ t : Fin 16, Classified ⟨160+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified11 : ∀ t : Fin 16, Classified ⟨176+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified12 : ∀ t : Fin 16, Classified ⟨192+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified13 : ∀ t : Fin 16, Classified ⟨208+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified14 : ∀ t : Fin 16, Classified ⟨224+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified15 : ∀ t : Fin 16, Classified ⟨240+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified16 : ∀ t : Fin 16, Classified ⟨256+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified17 : ∀ t : Fin 16, Classified ⟨272+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified18 : ∀ t : Fin 16, Classified ⟨288+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified19 : ∀ t : Fin 16, Classified ⟨304+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified20 : ∀ t : Fin 16, Classified ⟨320+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified21 : ∀ t : Fin 16, Classified ⟨336+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified22 : ∀ t : Fin 16, Classified ⟨352+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified23 : ∀ t : Fin 16, Classified ⟨368+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified24 : ∀ t : Fin 16, Classified ⟨384+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified25 : ∀ t : Fin 6, Classified ⟨400+t.val, by omega⟩ := by
  unfold Classified Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma classified (k : Rep) : Classified k := by
  by_cases h0 : k.val < 16
  · exact (show (⟨0+(k.val-0), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified0 ⟨k.val-0, by omega⟩
  by_cases h1 : k.val < 32
  · exact (show (⟨16+(k.val-16), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified1 ⟨k.val-16, by omega⟩
  by_cases h2 : k.val < 48
  · exact (show (⟨32+(k.val-32), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified2 ⟨k.val-32, by omega⟩
  by_cases h3 : k.val < 64
  · exact (show (⟨48+(k.val-48), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified3 ⟨k.val-48, by omega⟩
  by_cases h4 : k.val < 80
  · exact (show (⟨64+(k.val-64), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified4 ⟨k.val-64, by omega⟩
  by_cases h5 : k.val < 96
  · exact (show (⟨80+(k.val-80), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified5 ⟨k.val-80, by omega⟩
  by_cases h6 : k.val < 112
  · exact (show (⟨96+(k.val-96), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified6 ⟨k.val-96, by omega⟩
  by_cases h7 : k.val < 128
  · exact (show (⟨112+(k.val-112), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified7 ⟨k.val-112, by omega⟩
  by_cases h8 : k.val < 144
  · exact (show (⟨128+(k.val-128), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified8 ⟨k.val-128, by omega⟩
  by_cases h9 : k.val < 160
  · exact (show (⟨144+(k.val-144), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified9 ⟨k.val-144, by omega⟩
  by_cases h10 : k.val < 176
  · exact (show (⟨160+(k.val-160), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified10 ⟨k.val-160, by omega⟩
  by_cases h11 : k.val < 192
  · exact (show (⟨176+(k.val-176), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified11 ⟨k.val-176, by omega⟩
  by_cases h12 : k.val < 208
  · exact (show (⟨192+(k.val-192), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified12 ⟨k.val-192, by omega⟩
  by_cases h13 : k.val < 224
  · exact (show (⟨208+(k.val-208), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified13 ⟨k.val-208, by omega⟩
  by_cases h14 : k.val < 240
  · exact (show (⟨224+(k.val-224), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified14 ⟨k.val-224, by omega⟩
  by_cases h15 : k.val < 256
  · exact (show (⟨240+(k.val-240), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified15 ⟨k.val-240, by omega⟩
  by_cases h16 : k.val < 272
  · exact (show (⟨256+(k.val-256), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified16 ⟨k.val-256, by omega⟩
  by_cases h17 : k.val < 288
  · exact (show (⟨272+(k.val-272), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified17 ⟨k.val-272, by omega⟩
  by_cases h18 : k.val < 304
  · exact (show (⟨288+(k.val-288), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified18 ⟨k.val-288, by omega⟩
  by_cases h19 : k.val < 320
  · exact (show (⟨304+(k.val-304), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified19 ⟨k.val-304, by omega⟩
  by_cases h20 : k.val < 336
  · exact (show (⟨320+(k.val-320), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified20 ⟨k.val-320, by omega⟩
  by_cases h21 : k.val < 352
  · exact (show (⟨336+(k.val-336), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified21 ⟨k.val-336, by omega⟩
  by_cases h22 : k.val < 368
  · exact (show (⟨352+(k.val-352), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified22 ⟨k.val-352, by omega⟩
  by_cases h23 : k.val < 384
  · exact (show (⟨368+(k.val-368), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified23 ⟨k.val-368, by omega⟩
  by_cases h24 : k.val < 400
  · exact (show (⟨384+(k.val-384), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified24 ⟨k.val-384, by omega⟩
  by_cases h25 : k.val < 406
  · exact (show (⟨400+(k.val-400), by omega⟩ : Rep) = k by ext; dsimp; omega) ▸ classified25 ⟨k.val-400, by omega⟩
  omega

def eligible (mode : ℕ) (m : Fin 256) : Bool :=
  if mode = 0 then (1461524033014881819847887051302796691466767239031 : ℕ).testBit m.val
  else if mode = 1 then (340282366920938463481821351509772796183 : ℕ).testBit m.val
  else (6277101735386680764176071790128604879584177077448784023839 : ℕ).testBit m.val

set_option maxRecDepth 4000 in
lemma eligBound : ∀ w : Fin 256,
    (Consistent (slots w.val) → (slots w.val).card ≤ 2 → eligible 0 w = true) ∧
    ((slots w.val).card ≤ 1 → eligible 1 w = true) ∧
    (((slots w.val).image Prod.fst).card ≤ 1 → eligible 2 w = true) := by
  unfold Consistent
  decide +kernel

def case0Anchors : Fin 4 → V := ![6, 4, 1, 3]

set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case0Clique : Clique (decode 5) (decode 26) case0Anchors := by
  unfold Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

def case0Extra0Row (i : ℕ) : ℕ := digit 4 i ([4415260066817, 8590066178, 21474969349, 0, 0, 0, 0, 0, 55834707718, 2, 6, 0, 0, 0, 0, 0] : List ℕ)

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case0Extra0Check : ∀ w : Fin 256, eligible 0 w = true → w ∉ ([] : List (Fin 256)) →
    ∀ m : Fin 256, admiss (decode 5) (decode 26) ⟨case0Extra0Row w.val % 15, by omega⟩
      [((some 6), 1), ((some 4), 4), ((some 1), 16), ((some 3), 64), ((some 5), w)] m = false := by decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 8000000 in
lemma case0Impossible (pos : X → Finset Slot) (cv : Cover (decode 5) (decode 26) pos) (cp : Cap (decode 5) (decode 26) pos) : False := by
  obtain ⟨P, hcv, hcp, ha⟩ := normalize_places (by decide) cv cp case0Clique
  have ha0 : P (some 6) = slots 1 := (ha 0).trans (by decide +kernel)
  have ha1 : P (some 4) = slots 4 := (ha 1).trans (by decide +kernel)
  have ha2 : P (some 1) = slots 16 := (ha 2).trans (by decide +kernel)
  have ha3 : P (some 3) = slots 64 := (ha 3).trans (by decide +kernel)
  obtain ⟨w0, hw0⟩ := slotsSurj (P (some 5))
  have el0 := (eligBound w0).1 (hw0.symm ▸ (hcp.1 5).1) (hw0.symm ▸ (hcp.1 5).2)
  have pass0 := pass_marks hcv [((some 6), 1), ((some 4), 4), ((some 1), 16), ((some 3), 64), ((some 5), w0)] (by
    intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> first
    | exact ha0
    | exact ha1
    | exact ha2
    | exact ha3
    | exact hw0.symm)
  obtain ⟨m0,hm0⟩ := pass0 ⟨case0Extra0Row w0.val % 15, by omega⟩
  have mem0 : w0 ∈ ([] : List (Fin 256)) := by
    by_contra hh
    simp [(case0Extra0Check w0 el0 hh m0)] at hm0
  exact List.not_mem_nil mem0

def case1Anchors : Fin 4 → V := ![6, 4, 1, 5]

set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case1Clique : Clique (decode 5) (decode 50) case1Anchors := by
  unfold Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

def case1Extra0Row (i : ℕ) : ℕ := digit 4 i ([4544078544912, 17179869344, 8590133026, 0, 8589934624, 0, 2, 0, 17180263524, 4, 6, 0, 0, 0, 0, 0] : List ℕ)

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case1Extra0Check : ∀ w : Fin 256, eligible 0 w = true → w ∉ ([] : List (Fin 256)) →
    ∀ m : Fin 256, admiss (decode 5) (decode 50) ⟨case1Extra0Row w.val % 15, by omega⟩
      [((some 6), 1), ((some 4), 4), ((some 1), 16), ((some 5), 64), ((some 9), w)] m = false := by decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 8000000 in
lemma case1Impossible (pos : X → Finset Slot) (cv : Cover (decode 5) (decode 50) pos) (cp : Cap (decode 5) (decode 50) pos) : False := by
  obtain ⟨P, hcv, hcp, ha⟩ := normalize_places (by decide) cv cp case1Clique
  have ha0 : P (some 6) = slots 1 := (ha 0).trans (by decide +kernel)
  have ha1 : P (some 4) = slots 4 := (ha 1).trans (by decide +kernel)
  have ha2 : P (some 1) = slots 16 := (ha 2).trans (by decide +kernel)
  have ha3 : P (some 5) = slots 64 := (ha 3).trans (by decide +kernel)
  obtain ⟨w0, hw0⟩ := slotsSurj (P (some 9))
  have el0 := (eligBound w0).1 (hw0.symm ▸ (hcp.1 9).1) (hw0.symm ▸ (hcp.1 9).2)
  have pass0 := pass_marks hcv [((some 6), 1), ((some 4), 4), ((some 1), 16), ((some 5), 64), ((some 9), w0)] (by
    intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> first
    | exact ha0
    | exact ha1
    | exact ha2
    | exact ha3
    | exact hw0.symm)
  obtain ⟨m0,hm0⟩ := pass0 ⟨case1Extra0Row w0.val % 15, by omega⟩
  have mem0 : w0 ∈ ([] : List (Fin 256)) := by
    by_contra hh
    simp [(case1Extra0Check w0 el0 hh m0)] at hm0
  exact List.not_mem_nil mem0

def case2Anchors : Fin 4 → V := ![5, 3, 1, 4]

set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case2Clique : Clique (decode 5) (decode 58) case2Anchors := by
  unfold Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

def case2Extra0Row (i : ℕ) : ℕ := digit 4 i ([6597139104768, 263168, 12885034274, 0, 460288, 0, 3, 0, 47244772386, 4, 2, 0, 0, 0, 0, 0] : List ℕ)

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case2Extra0Check : ∀ w : Fin 256, eligible 0 w = true → w ∉ ([] : List (Fin 256)) →
    ∀ m : Fin 256, admiss (decode 5) (decode 58) ⟨case2Extra0Row w.val % 15, by omega⟩
      [((some 5), 1), ((some 3), 4), ((some 1), 16), ((some 4), 64), ((some 8), w)] m = false := by decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 8000000 in
lemma case2Impossible (pos : X → Finset Slot) (cv : Cover (decode 5) (decode 58) pos) (cp : Cap (decode 5) (decode 58) pos) : False := by
  obtain ⟨P, hcv, hcp, ha⟩ := normalize_places (by decide) cv cp case2Clique
  have ha0 : P (some 5) = slots 1 := (ha 0).trans (by decide +kernel)
  have ha1 : P (some 3) = slots 4 := (ha 1).trans (by decide +kernel)
  have ha2 : P (some 1) = slots 16 := (ha 2).trans (by decide +kernel)
  have ha3 : P (some 4) = slots 64 := (ha 3).trans (by decide +kernel)
  obtain ⟨w0, hw0⟩ := slotsSurj (P (some 8))
  have el0 := (eligBound w0).1 (hw0.symm ▸ (hcp.1 8).1) (hw0.symm ▸ (hcp.1 8).2)
  have pass0 := pass_marks hcv [((some 5), 1), ((some 3), 4), ((some 1), 16), ((some 4), 64), ((some 8), w0)] (by
    intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> first
    | exact ha0
    | exact ha1
    | exact ha2
    | exact ha3
    | exact hw0.symm)
  obtain ⟨m0,hm0⟩ := pass0 ⟨case2Extra0Row w0.val % 15, by omega⟩
  have mem0 : w0 ∈ ([] : List (Fin 256)) := by
    by_contra hh
    simp [(case2Extra0Check w0 el0 hh m0)] at hm0
  exact List.not_mem_nil mem0

def case3Anchors : Fin 4 → V := ![6, 4, 2, 1]

set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case3Clique : Clique (decode 5) (decode 90) case3Anchors := by
  unfold Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

def case3Extra0Row (i : ℕ) : ℕ := digit 4 i ([11068133867536, 4295165201, 42949937738, 0, 21474836544, 5, 5, 0, 4295165713, 1, 10, 0, 0, 0, 0, 0] : List ℕ)

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case3Extra0Check : ∀ w : Fin 256, eligible 0 w = true → w ∉ ([] : List (Fin 256)) →
    ∀ m : Fin 256, admiss (decode 5) (decode 90) ⟨case3Extra0Row w.val % 15, by omega⟩
      [((some 6), 1), ((some 4), 4), ((some 2), 16), ((some 1), 64), ((some 7), w)] m = false := by decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 8000000 in
lemma case3Impossible (pos : X → Finset Slot) (cv : Cover (decode 5) (decode 90) pos) (cp : Cap (decode 5) (decode 90) pos) : False := by
  obtain ⟨P, hcv, hcp, ha⟩ := normalize_places (by decide) cv cp case3Clique
  have ha0 : P (some 6) = slots 1 := (ha 0).trans (by decide +kernel)
  have ha1 : P (some 4) = slots 4 := (ha 1).trans (by decide +kernel)
  have ha2 : P (some 2) = slots 16 := (ha 2).trans (by decide +kernel)
  have ha3 : P (some 1) = slots 64 := (ha 3).trans (by decide +kernel)
  obtain ⟨w0, hw0⟩ := slotsSurj (P (some 7))
  have el0 := (eligBound w0).1 (hw0.symm ▸ (hcp.1 7).1) (hw0.symm ▸ (hcp.1 7).2)
  have pass0 := pass_marks hcv [((some 6), 1), ((some 4), 4), ((some 2), 16), ((some 1), 64), ((some 7), w0)] (by
    intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> first
    | exact ha0
    | exact ha1
    | exact ha2
    | exact ha3
    | exact hw0.symm)
  obtain ⟨m0,hm0⟩ := pass0 ⟨case3Extra0Row w0.val % 15, by omega⟩
  have mem0 : w0 ∈ ([] : List (Fin 256)) := by
    by_contra hh
    simp [(case3Extra0Check w0 el0 hh m0)] at hm0
  exact List.not_mem_nil mem0

def case4Anchors : Fin 3 → V := ![0, 5, 1]

set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case4Clique : Clique (decode 42) (decode 261) case4Anchors := by
  unfold Clique Strong Apart Dir Conflict Stable fires
  decide +kernel

def case4Extra0Row (i : ℕ) : ℕ := digit 4 i ([21474838069, 3, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ)

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case4Extra0Check : ∀ w : Fin 256, eligible 1 w = true → w ∉ ([4, 64, 128] : List (Fin 256)) →
    ∀ m : Fin 256, admiss (decode 42) (decode 261) ⟨case4Extra0Row w.val % 15, by omega⟩
      [((some 0), 1), ((some 5), 4), ((some 1), 16), ((some 2), w)] m = false := by decide +kernel

def case4Extra1Row (i : ℕ) : ℕ := digit 4 i ([25769804544, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ)

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case4Extra1Check : ∀ w : Fin 256, eligible 1 w = true → w ∉ ([1, 64, 128] : List (Fin 256)) →
    ∀ m : Fin 256, admiss (decode 42) (decode 261) ⟨case4Extra1Row w.val % 15, by omega⟩
      [((some 0), 1), ((some 5), 4), ((some 1), 16), ((some 3), w)] m = false := by decide +kernel

def case4Extra2Row (i : ℕ) : ℕ := digit 4 i ([1407374883893296, 3, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List ℕ)

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case4Extra2Check : ∀ w : Fin 256, eligible 2 w = true → w ∉ ([0, 2, 8, 32, 64, 128, 192] : List (Fin 256)) →
    ∀ m : Fin 256, admiss (decode 42) (decode 261) ⟨case4Extra2Row w.val % 15, by omega⟩
      [((some 0), 1), ((some 5), 4), ((some 1), 16), (none, w)] m = false := by decide +kernel

def case4Extra3Row (i : ℕ) : ℕ := digit 4 i ([6957907837712, 17179871648, 21474968402, 0, 655536, 10, 0, 0, 655536, 10, 0, 0, 0, 0, 0, 0] : List ℕ)

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case4Extra3Check : ∀ w : Fin 256, eligible 0 w = true → w ∉ ([64, 66, 72, 96, 128, 130, 136, 160] : List (Fin 256)) →
    ∀ m : Fin 256, admiss (decode 42) (decode 261) ⟨case4Extra3Row w.val % 15, by omega⟩
      [((some 0), 1), ((some 5), 4), ((some 1), 16), ((some 9), w)] m = false := by decide +kernel

def case4FinalRow (i : ℕ) : ℕ := digit 4 i ([0, 2459565877067269188, 3833447290845017395, 892548403, 3688487961612002386, 2459002926541054498, 3688486792471773184, 2617213913242009600, 2459565867940328240, 2459565867332009984, 1224997863947383600, 4919112979967915825, 1224997863929553441, 3833466193284637745, 3688486788462022929, 2459002922532348721, 3674975989580960017, 858792753, 2612707015689123376, 606221872, 2536145822003901232, 3977053404719550720, 2459284401804100676, 1229782865553732915, 892417331, 3688487961612002386, 3688486724661421090, 3688486792471773184, 2535864346724077824, 2459284392945726256, 1229782934256431872, 590426928] : List ℕ)

def case4X : Fin 3 → Fin 256 := ![4, 64, 128]

def case4Y : Fin 3 → Fin 256 := ![1, 64, 128]

def case4Z : Fin 7 → Fin 256 := ![0, 2, 8, 32, 64, 128, 192]

def case4W : Fin 8 → Fin 256 := ![64, 66, 72, 96, 128, 130, 136, 160]

def case4Final (x : Fin 3) (y : Fin 3) (z : Fin 7) (w : Fin 8) :=
  ∀ m : Fin 256, admiss (decode 42) (decode 261) ⟨case4FinalRow (((x.val*3+y.val)*7+z.val)*8+w.val) % 15, by omega⟩
    [((some 0), 1), ((some 5), 4), ((some 1), 16), ((some 2), (case4X x)), ((some 3), (case4Y y)), (none, (case4Z z)), ((some 9), (case4W w))] m = false

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case4Final00 : ∀ z w, case4Final 0 0 z w := by
  unfold case4Final
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case4Final01 : ∀ z w, case4Final 0 1 z w := by
  unfold case4Final
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case4Final02 : ∀ z w, case4Final 0 2 z w := by
  unfold case4Final
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case4Final10 : ∀ z w, case4Final 1 0 z w := by
  unfold case4Final
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case4Final11 : ∀ z w, case4Final 1 1 z w := by
  unfold case4Final
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case4Final12 : ∀ z w, case4Final 1 2 z w := by
  unfold case4Final
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case4Final20 : ∀ z w, case4Final 2 0 z w := by
  unfold case4Final
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case4Final21 : ∀ z w, case4Final 2 1 z w := by
  unfold case4Final
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 4000000 in
lemma case4Final22 : ∀ z w, case4Final 2 2 z w := by
  unfold case4Final
  decide +kernel

set_option maxRecDepth 8000 in
set_option synthInstance.maxSize 10000 in
set_option maxHeartbeats 8000000 in
lemma case4Impossible (pos : X → Finset Slot) (cv : Cover (decode 42) (decode 261) pos) (cp : Cap (decode 42) (decode 261) pos) : False := by
  obtain ⟨P, hcv, hcp, ha⟩ := normalize_places (by decide) cv cp case4Clique
  have ha0 : P (some 0) = slots 1 := (ha 0).trans (by decide +kernel)
  have ha1 : P (some 5) = slots 4 := (ha 1).trans (by decide +kernel)
  have ha2 : P (some 1) = slots 16 := (ha 2).trans (by decide +kernel)
  obtain ⟨w0, hw0⟩ := slotsSurj (P (some 2))
  have strong0 : Strong (decode 42) (decode 261) 2 := by unfold Strong Apart Dir fires; decide +kernel
  have el0 := (eligBound w0).2.1 (hw0.symm ▸ hcp.2.1 2 strong0)
  have pass0 := pass_marks hcv [((some 0), 1), ((some 5), 4), ((some 1), 16), ((some 2), w0)] (by
    intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> first
    | exact ha0
    | exact ha1
    | exact ha2
    | exact hw0.symm)
  obtain ⟨m0,hm0⟩ := pass0 ⟨case4Extra0Row w0.val % 15, by omega⟩
  have mem0 : w0 ∈ ([4, 64, 128] : List (Fin 256)) := by
    by_contra hh
    simp [(case4Extra0Check w0 el0 hh m0)] at hm0
  obtain ⟨w1, hw1⟩ := slotsSurj (P (some 3))
  have strong1 : Strong (decode 42) (decode 261) 3 := by unfold Strong Apart Dir fires; decide +kernel
  have el1 := (eligBound w1).2.1 (hw1.symm ▸ hcp.2.1 3 strong1)
  have pass1 := pass_marks hcv [((some 0), 1), ((some 5), 4), ((some 1), 16), ((some 3), w1)] (by
    intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> first
    | exact ha0
    | exact ha1
    | exact ha2
    | exact hw1.symm)
  obtain ⟨m1,hm1⟩ := pass1 ⟨case4Extra1Row w1.val % 15, by omega⟩
  have mem1 : w1 ∈ ([1, 64, 128] : List (Fin 256)) := by
    by_contra hh
    simp [(case4Extra1Check w1 el1 hh m1)] at hm1
  obtain ⟨w2, hw2⟩ := slotsSurj (P none)
  let gRows : Fin 5 → Fin 15 := ![3, 5, 9, 10, 11]
  have el2 := (eligBound w2).2.2 (hw2.symm ▸ hcp.2.2 gRows (by unfold gRows fires; decide +kernel) (by unfold gRows Apart Dir fires; decide +kernel))
  have pass2 := pass_marks hcv [((some 0), 1), ((some 5), 4), ((some 1), 16), (none, w2)] (by
    intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> first
    | exact ha0
    | exact ha1
    | exact ha2
    | exact hw2.symm)
  obtain ⟨m2,hm2⟩ := pass2 ⟨case4Extra2Row w2.val % 15, by omega⟩
  have mem2 : w2 ∈ ([0, 2, 8, 32, 64, 128, 192] : List (Fin 256)) := by
    by_contra hh
    simp [(case4Extra2Check w2 el2 hh m2)] at hm2
  obtain ⟨w3, hw3⟩ := slotsSurj (P (some 9))
  have el3 := (eligBound w3).1 (hw3.symm ▸ (hcp.1 9).1) (hw3.symm ▸ (hcp.1 9).2)
  have pass3 := pass_marks hcv [((some 0), 1), ((some 5), 4), ((some 1), 16), ((some 9), w3)] (by
    intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> first
    | exact ha0
    | exact ha1
    | exact ha2
    | exact hw3.symm)
  obtain ⟨m3,hm3⟩ := pass3 ⟨case4Extra3Row w3.val % 15, by omega⟩
  have mem3 : w3 ∈ ([64, 66, 72, 96, 128, 130, 136, 160] : List (Fin 256)) := by
    by_contra hh
    simp [(case4Extra3Check w3 el3 hh m3)] at hm3
  have ext0 : ∀ t ∈ ([4, 64, 128] : List (Fin 256)), ∃ i, case4X i = t := by decide +kernel
  obtain ⟨x,hx⟩ := ext0 _ mem0
  have ext1 : ∀ t ∈ ([1, 64, 128] : List (Fin 256)), ∃ i, case4Y i = t := by decide +kernel
  obtain ⟨y,hy⟩ := ext1 _ mem1
  have ext2 : ∀ t ∈ ([0, 2, 8, 32, 64, 128, 192] : List (Fin 256)), ∃ i, case4Z i = t := by decide +kernel
  obtain ⟨z,hz⟩ := ext2 _ mem2
  have ext3 : ∀ t ∈ ([64, 66, 72, 96, 128, 130, 136, 160] : List (Fin 256)), ∃ i, case4W i = t := by decide +kernel
  obtain ⟨w,hw⟩ := ext3 _ mem3
  have passAll := pass_marks hcv [((some 0), 1), ((some 5), 4), ((some 1), 16), ((some 2), (case4X x)), ((some 3), (case4Y y)), (none, (case4Z z)), ((some 9), (case4W w))] (by
    intro t ht
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
    | exact ha0
    | exact ha1
    | exact ha2
    | exact hw0.symm.trans (congrArg (fun t : Fin 256 => slots t.val) hx.symm)
    | exact hw1.symm.trans (congrArg (fun t : Fin 256 => slots t.val) hy.symm)
    | exact hw2.symm.trans (congrArg (fun t : Fin 256 => slots t.val) hz.symm)
    | exact hw3.symm.trans (congrArg (fun t : Fin 256 => slots t.val) hw.symm)
)
  obtain ⟨m,hm⟩ := passAll ⟨case4FinalRow (((x.val*3+y.val)*7+z.val)*8+w.val) % 15, by omega⟩
  have hf : case4Final x y z w := by
    fin_cases x <;> fin_cases y
    · exact case4Final00 z w
    · exact case4Final01 z w
    · exact case4Final02 z w
    · exact case4Final10 z w
    · exact case4Final11 z w
    · exact case4Final12 z w
    · exact case4Final20 z w
    · exact case4Final21 z w
    · exact case4Final22 z w
  simp [hf m] at hm


lemma noBad {A B : Finset V} (bad : Bad A B) : False := by
  obtain ⟨k,h⟩ := canonical bad
  obtain ⟨⟨r,hr⟩,_,⟨pos,cv,cp⟩⟩ := bad_frame h
  obtain ⟨safe,generic,special⟩ := classified k
  by_cases h₀ : kindRep k.val = 0
  · exact safe h₀ r hr
  by_cases h₁ : kindRep k.val = 1
  · exact noFiveClique cv cp (cliqueV k) (generic h₁)
  rcases special h₀ h₁ with ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩ | ⟨ha,hb⟩ <;>
    rw [ha,hb] at cv cp
  · exact case0Impossible pos cv cp
  · exact case1Impossible pos cv cp
  · exact case2Impossible pos cv cp
  · exact case3Impossible pos cv cp
  · exact case4Impossible pos cv cp

lemma lower (C : AndCountCircuit 10) (sep : Separates C) : ¬ C.size ≤ 5 := by
  classical
  intro le
  let D := stripCircuit C
  have hd : Separates D := by
    intro I hI
    simpa only [D, strip_eval_eq] using sep I hI
  have sz : D.size = 5 := le_antisymm le (atLeastFive D hd)
  let U := Finset.univ.filter (fun i : Fin D.size => ∃ r, D.gateVal (rows r) i = true)
  have ne : U.Nonempty := by
    by_contra hn
    have allSafe (i) (r) : D.gateVal (rows r) i = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,r,ht⟩⟩
    have := safe_bound D hd allSafe
    omega
  let p := U.min' ne
  have hp : p ∈ U := U.min'_mem ne
  have er : Early D p := by
    intro j hj r
    apply Bool.eq_false_iff.mpr
    intro ht
    exact (not_le_of_gt hj) (U.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,r,ht⟩))
  exact noBad ⟨D,p,rfl,rfl,sz,hd,er,(Finset.mem_filter.mp hp).2,strip_disjoint C⟩

end AndLower.Source635
open AndLower.Source635 in
lemma AndLower.source635 : ∀ G : SimpleGraph (Fin 10),
    G.edgeSet = {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 0), s(0, 5), s(1, 6), s(2, 7), s(3, 8),
      s(4, 9), s(5, 7), s(6, 8), s(7, 9), s(8, 5), s(9, 6)} →
    (∃ C : PEqualNP.AndCount.AndCountCircuit 10, C.WellFormed ∧
      (∀ I : Finset (Fin 10), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
        C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) ∧ C.size = 6) ∧
    ∀ C : PEqualNP.AndCount.AndCountCircuit 10, C.WellFormed →
      (∀ I : Finset (Fin 10), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
        C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) →
      ¬ C.size ≤ 5 := by
  intro G he
  constructor
  · refine ⟨circuit, ?_, ?_, rfl⟩
    · intro i
      constructor <;> intro j hj <;> exact (Finset.notMem_empty j hj).elim
    · intro I hi hm
      exact upper I ((good_iff G he I).mpr ⟨hi,hm⟩)
  · intro C _ h
    apply lower C
    intro I hi
    obtain ⟨hind,hmax⟩ := (good_iff G he I).mp hi
    exact h I hind hmax

namespace AndLower.Source9051

open PEqualNP.CircuitLowerBounds PEqualNP.AndCount

def isAndOp (op : GateOp) : Bool :=
  GateOp.casesOn op true false false (fun _ => false) false

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih =>
    rw [run_snoc, List.length_append, List.length_singleton, List.length_append, List.length_singleton, ih]
    omega

lemma getD_snoc_lt {α : Type*} (l : List α) (a d : α) (w : ℕ) (h : w < l.length) :
    (l ++ [a]).getD w d = l.getD w d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq {α : Type*} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, Nat.sub_self]
  rfl

lemma getD_snoc_gt {α : Type*} (l : List α) (a d : α) (w : ℕ) (h : l.length < w) :
    (l ++ [a]).getD w d = d := by
  rw [List.getD_eq_default]
  simp
  omega

lemma gateValFuel_stable {n : ℕ} (A : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (d1 d2 : ℕ) (i : Fin A.size), i.val < d1 → i.val < d2 →
      A.gateValFuel U d1 i = A.gateValFuel U d2 i := by
  intro d1
  induction d1 with
  | zero => intro d2 i hi; omega
  | succ d1 ih =>
    intro d2 i h1 h2
    cases d2 with
    | zero => omega
    | succ d2 =>
      simp only [AndCountCircuit.gateValFuel, AndCountCircuit.sideTrue]
      congr 1
      · simp only [decide_eq_decide]
        refine or_congr Iff.rfl (exists_congr fun j => and_congr Iff.rfl ?_)
        constructor
        · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [← ih d2 j (by omega) (by omega)]; exact hv⟩
        · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [ih d2 j (by omega) (by omega)]; exact hv⟩
      · simp only [decide_eq_decide]
        refine or_congr Iff.rfl (exists_congr fun j => and_congr Iff.rfl ?_)
        constructor
        · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [← ih d2 j (by omega) (by omega)]; exact hv⟩
        · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [ih d2 j (by omega) (by omega)]; exact hv⟩

lemma gateVal_eq {n : ℕ} (A : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin A.size) :
    A.gateVal U i =
      (AndCountCircuit.sideTrue U (A.leftVars i) (A.leftGates i) i (A.gateVal U) &&
       AndCountCircuit.sideTrue U (A.rightVars i) (A.rightGates i) i (A.gateVal U)) := by
  unfold AndCountCircuit.gateVal
  have h1 : A.gateValFuel U A.size i = A.gateValFuel U (i.val + 1) i :=
    gateValFuel_stable A U A.size (i.val + 1) i i.isLt (by omega)
  rw [h1]
  simp only [AndCountCircuit.gateValFuel, AndCountCircuit.sideTrue]
  congr 1
  · simp only [decide_eq_decide]
    refine or_congr Iff.rfl (exists_congr fun j => and_congr Iff.rfl ?_)
    constructor
    · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [gateValFuel_stable A U A.size i.val j j.isLt hj]; exact hv⟩
    · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [gateValFuel_stable A U i.val A.size j hj j.isLt]; exact hv⟩
  · simp only [decide_eq_decide]
    refine or_congr Iff.rfl (exists_congr fun j => and_congr Iff.rfl ?_)
    constructor
    · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [gateValFuel_stable A U A.size i.val j j.isLt hj]; exact hv⟩
    · rintro ⟨hj, hv⟩; exact ⟨hj, by rw [gateValFuel_stable A U i.val A.size j hj j.isLt]; exact hv⟩

lemma gateValFuel_withOut {n : ℕ} (A : AndCountCircuit n)
    (Bout : Finset (Fin n)) (Fout : Finset (Fin A.size)) (U : Finset (Fin n)) :
    ∀ (d : ℕ) (i : Fin A.size),
      ({ A with outVars := Bout, outGates := Fout } : AndCountCircuit n).gateValFuel U d i =
        A.gateValFuel U d i := by
  intro d
  induction d with
  | zero => intro i; rfl
  | succ d ih =>
    intro i
    simp only [AndCountCircuit.gateValFuel, AndCountCircuit.sideTrue]
    have hfn : ({ A with outVars := Bout, outGates := Fout } : AndCountCircuit n).gateValFuel U d =
        A.gateValFuel U d := funext ih
    rw [hfn]

def evalRep {n : ℕ} (A : AndCountCircuit n) (U : Finset (Fin n)) :
    Option (Finset (Fin n) × Finset (Fin A.size)) → Bool
  | none => true
  | some (B, F) => decide ((∃ v ∈ B, v ∈ U) ∨ ∃ j ∈ F, A.gateVal U j = true)

def orRep {n k : ℕ} :
    Option (Finset (Fin n) × Finset (Fin k)) →
    Option (Finset (Fin n) × Finset (Fin k)) →
    Option (Finset (Fin n) × Finset (Fin k))
  | none, _ => none
  | _, none => none
  | some (B1, F1), some (B2, F2) => some (B1 ∪ B2, F1 ∪ F2)

lemma evalRep_orRep {n : ℕ} (A : AndCountCircuit n) (U : Finset (Fin n))
    (r1 r2 : Option (Finset (Fin n) × Finset (Fin A.size))) :
    evalRep A U (orRep r1 r2) = (evalRep A U r1 || evalRep A U r2) := by
  cases r1 with
  | none => simp [orRep, evalRep]
  | some p1 =>
    rcases p1 with ⟨B1, F1⟩
    cases r2 with
    | none => simp [orRep, evalRep]
    | some p2 =>
      rcases p2 with ⟨B2, F2⟩
      rw [Bool.eq_iff_iff]
      simp only [orRep, evalRep, decide_eq_true_eq, Bool.or_eq_true]
      constructor
      · rintro (⟨v, hv, hvu⟩ | ⟨j, hj, hju⟩)
        · rcases Finset.mem_union.mp hv with h | h
          · exact Or.inl (Or.inl ⟨v, h, hvu⟩)
          · exact Or.inr (Or.inl ⟨v, h, hvu⟩)
        · rcases Finset.mem_union.mp hj with h | h
          · exact Or.inl (Or.inr ⟨j, h, hju⟩)
          · exact Or.inr (Or.inr ⟨j, h, hju⟩)
      · rintro ((⟨v, hv, hvu⟩ | ⟨j, hj, hju⟩) | (⟨v, hv, hvu⟩ | ⟨j, hj, hju⟩))
        · exact Or.inl ⟨v, Finset.mem_union_left _ hv, hvu⟩
        · exact Or.inr ⟨j, Finset.mem_union_left _ hj, hju⟩
        · exact Or.inl ⟨v, Finset.mem_union_right _ hv, hvu⟩
        · exact Or.inr ⟨j, Finset.mem_union_right _ hj, hju⟩

def liftRep {n k : ℕ} :
    Option (Finset (Fin n) × Finset (Fin k)) →
    Option (Finset (Fin n) × Finset (Fin (k + 1)))
  | none => none
  | some (B, F) => some (B, F.map Fin.castSuccEmb)

abbrev snocCircuit {n : ℕ} (A : AndCountCircuit n)
    (B1 : Finset (Fin n)) (F1 : Finset (Fin A.size))
    (B2 : Finset (Fin n)) (F2 : Finset (Fin A.size)) : AndCountCircuit n where
  size := A.size + 1
  leftVars i := if h : i.val < A.size then A.leftVars ⟨i.val, h⟩ else B1
  leftGates i := if h : i.val < A.size then (A.leftGates ⟨i.val, h⟩).map Fin.castSuccEmb else F1.map Fin.castSuccEmb
  rightVars i := if h : i.val < A.size then A.rightVars ⟨i.val, h⟩ else B2
  rightGates i := if h : i.val < A.size then (A.rightGates ⟨i.val, h⟩).map Fin.castSuccEmb else F2.map Fin.castSuccEmb
  outVars := A.outVars
  outGates := A.outGates.map Fin.castSuccEmb

lemma snocCircuit_wellFormed {n : ℕ} (A : AndCountCircuit n) (hWF : A.WellFormed)
    (B1 : Finset (Fin n)) (F1 : Finset (Fin A.size))
    (B2 : Finset (Fin n)) (F2 : Finset (Fin A.size)) :
    (snocCircuit A B1 F1 B2 F2).WellFormed := by
  intro i
  by_cases hi : i.val < A.size
  · constructor
    · intro j hj
      simp only [snocCircuit, hi, ↓reduceDIte, Finset.mem_map, Fin.castSuccEmb_apply] at hj
      rcases hj with ⟨j0, hj0, rfl⟩
      exact (hWF ⟨i.val, hi⟩).1 j0 hj0
    · intro j hj
      simp only [snocCircuit, hi, ↓reduceDIte, Finset.mem_map, Fin.castSuccEmb_apply] at hj
      rcases hj with ⟨j0, hj0, rfl⟩
      exact (hWF ⟨i.val, hi⟩).2 j0 hj0
  · have hieq : i.val = A.size := by have : i.val < A.size + 1 := i.isLt; omega
    constructor
    · intro j hj
      simp only [snocCircuit, hi, ↓reduceDIte, Finset.mem_map, Fin.castSuccEmb_apply] at hj
      rcases hj with ⟨j0, _, rfl⟩
      change j0.val < i.val
      omega
    · intro j hj
      simp only [snocCircuit, hi, ↓reduceDIte, Finset.mem_map, Fin.castSuccEmb_apply] at hj
      rcases hj with ⟨j0, _, rfl⟩
      change j0.val < i.val
      omega

lemma snocCircuit_gateVal_castSucc {n : ℕ} (A : AndCountCircuit n)
    (B1 : Finset (Fin n)) (F1 : Finset (Fin A.size))
    (B2 : Finset (Fin n)) (F2 : Finset (Fin A.size))
    (U : Finset (Fin n)) :
    ∀ (k : ℕ) (hk : k < A.size),
      (snocCircuit A B1 F1 B2 F2).gateVal U (Fin.castSucc ⟨k, hk⟩) = A.gateVal U ⟨k, hk⟩ := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk
    rw [gateVal_eq (snocCircuit A B1 F1 B2 F2) U (Fin.castSucc ⟨k, hk⟩), gateVal_eq A U ⟨k, hk⟩]
    simp only [snocCircuit, Fin.val_castSucc, hk, ↓reduceDIte, AndCountCircuit.sideTrue]
    congr 1
    · simp only [decide_eq_decide]
      refine or_congr Iff.rfl ?_
      constructor
      · rintro ⟨j, hj, hlt, hval⟩
        rw [Finset.mem_map] at hj
        rcases hj with ⟨j0, hj0, rfl⟩
        have hlt' : j0.val < k := hlt
        refine ⟨j0, hj0, hlt', ?_⟩
        rw [← ih j0.val hlt' j0.isLt]
        exact hval
      · rintro ⟨j0, hj0, hlt, hval⟩
        have hlt' : j0.val < k := hlt
        refine ⟨Fin.castSucc j0, Finset.mem_map.mpr ⟨j0, hj0, rfl⟩, hlt', ?_⟩
        rw [ih j0.val hlt' j0.isLt]
        exact hval
    · simp only [decide_eq_decide]
      refine or_congr Iff.rfl ?_
      constructor
      · rintro ⟨j, hj, hlt, hval⟩
        rw [Finset.mem_map] at hj
        rcases hj with ⟨j0, hj0, rfl⟩
        have hlt' : j0.val < k := hlt
        refine ⟨j0, hj0, hlt', ?_⟩
        rw [← ih j0.val hlt' j0.isLt]
        exact hval
      · rintro ⟨j0, hj0, hlt, hval⟩
        have hlt' : j0.val < k := hlt
        refine ⟨Fin.castSucc j0, Finset.mem_map.mpr ⟨j0, hj0, rfl⟩, hlt', ?_⟩
        rw [ih j0.val hlt' j0.isLt]
        exact hval

lemma snocCircuit_gateVal_last {n : ℕ} (A : AndCountCircuit n)
    (B1 : Finset (Fin n)) (F1 : Finset (Fin A.size))
    (B2 : Finset (Fin n)) (F2 : Finset (Fin A.size))
    (U : Finset (Fin n)) :
    (snocCircuit A B1 F1 B2 F2).gateVal U (Fin.last A.size) =
      (evalRep A U (some (B1, F1)) && evalRep A U (some (B2, F2))) := by
  rw [gateVal_eq]
  simp only [snocCircuit, Fin.val_last, lt_irrefl, ↓reduceDIte, AndCountCircuit.sideTrue, evalRep]
  congr 1
  · simp only [decide_eq_decide]
    refine or_congr Iff.rfl ?_
    constructor
    · rintro ⟨j, hj, _, hval⟩
      rw [Finset.mem_map] at hj
      rcases hj with ⟨j0, hj0, rfl⟩
      exact ⟨j0, hj0, by rw [← snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]; exact hval⟩
    · rintro ⟨j0, hj0, hval⟩
      refine ⟨Fin.castSucc j0, Finset.mem_map.mpr ⟨j0, hj0, rfl⟩, Fin.castSucc_lt_last j0, ?_⟩
      rw [snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]
      exact hval
  · simp only [decide_eq_decide]
    refine or_congr Iff.rfl ?_
    constructor
    · rintro ⟨j, hj, _, hval⟩
      rw [Finset.mem_map] at hj
      rcases hj with ⟨j0, hj0, rfl⟩
      exact ⟨j0, hj0, by rw [← snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]; exact hval⟩
    · rintro ⟨j0, hj0, hval⟩
      refine ⟨Fin.castSucc j0, Finset.mem_map.mpr ⟨j0, hj0, rfl⟩, Fin.castSucc_lt_last j0, ?_⟩
      rw [snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]
      exact hval

lemma evalRep_liftRep {n : ℕ} (A : AndCountCircuit n)
    (B1 : Finset (Fin n)) (F1 : Finset (Fin A.size))
    (B2 : Finset (Fin n)) (F2 : Finset (Fin A.size))
    (U : Finset (Fin n)) (r : Option (Finset (Fin n) × Finset (Fin A.size))) :
    evalRep (snocCircuit A B1 F1 B2 F2) U (liftRep r) = evalRep A U r := by
  cases r with
  | none => rfl
  | some p =>
    rcases p with ⟨B, F⟩
    simp only [liftRep, evalRep, decide_eq_decide]
    refine or_congr Iff.rfl ?_
    constructor
    · rintro ⟨j, hj, hval⟩
      rw [Finset.mem_map] at hj
      rcases hj with ⟨j0, hj0, rfl⟩
      exact ⟨j0, hj0, by rw [← snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]; exact hval⟩
    · rintro ⟨j0, hj0, hval⟩
      refine ⟨Fin.castSucc j0, Finset.mem_map.mpr ⟨j0, hj0, rfl⟩, ?_⟩
      rw [snocCircuit_gateVal_castSucc A B1 F1 B2 F2 U j0.val j0.isLt]
      exact hval

lemma any_map_congr {α : Type*} (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    (l.map f).any id = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.any_cons, id]
    rw [h a List.mem_cons_self, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

lemma step_same_circuit {n : ℕ} (gs : List Gate) (g : Gate) (A : AndCountCircuit n)
    (rep : List (Option (Finset (Fin n) × Finset (Fin A.size))))
    (hlen : rep.length = n + gs.length)
    (hval : ∀ (U : Finset (Fin n)) (w : ℕ),
      (run gs (List.ofFn fun i : Fin n => decide (i ∈ U))).getD w false =
        evalRep A U (rep.getD w (some (∅, ∅))))
    (rnew : Option (Finset (Fin n) × Finset (Fin A.size)))
    (hnew : ∀ U : Finset (Fin n),
      g.op.eval (g.inputs.map fun i => (run gs (List.ofFn fun j : Fin n => decide (j ∈ U))).getD i false) =
        evalRep A U rnew) :
    ∀ (U : Finset (Fin n)) (w : ℕ),
      (run (gs ++ [g]) (List.ofFn fun i : Fin n => decide (i ∈ U))).getD w false =
        evalRep A U ((rep ++ [rnew]).getD w (some (∅, ∅))) := by
  intro U w
  rw [run_snoc]
  have hrl : (run gs (List.ofFn fun i : Fin n => decide (i ∈ U))).length = n + gs.length := by
    rw [run_length, List.length_ofFn]
  rcases Nat.lt_trichotomy w (n + gs.length) with hlt | rfl | hgt
  · rw [getD_snoc_lt _ _ _ w (by omega), getD_snoc_lt _ _ _ w (by omega)]
    exact hval U w
  · rw [← hrl, getD_snoc_eq, hrl, ← hlen, getD_snoc_eq]
    exact hnew U
  · rw [getD_snoc_gt _ _ _ w (by omega), getD_snoc_gt _ _ _ w (by omega)]
    simp [evalRep]

lemma build_aux (n : ℕ) (gs : List Gate)
    (hM : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ (A : AndCountCircuit n) (rep : List (Option (Finset (Fin n) × Finset (Fin A.size)))),
      A.WellFormed ∧
      A.size ≤ gs.countP (fun g => isAndOp g.op) ∧
      rep.length = n + gs.length ∧
      ∀ (U : Finset (Fin n)) (w : ℕ),
        (run gs (List.ofFn fun i : Fin n => decide (i ∈ U))).getD w false =
          evalRep A U (rep.getD w (some (∅, ∅))) := by
  induction gs using List.reverseRecOn with
  | nil =>
    let A0 : AndCountCircuit n :=
      { size := 0
        leftVars := Fin.elim0
        leftGates := Fin.elim0
        rightVars := Fin.elim0
        rightGates := Fin.elim0
        outVars := ∅
        outGates := ∅ }
    let rep0 : List (Option (Finset (Fin n) × Finset (Fin 0))) :=
      List.ofFn fun i : Fin n => some ({i}, ∅)
    refine ⟨A0, rep0, fun i => Fin.elim0 i, by simp [A0], by simp [rep0], ?_⟩
    intro U w
    simp only [run, List.foldl_nil]
    by_cases hw : w < n
    · rw [List.getD_eq_getElem _ _ (by simp [hw]), List.getElem_ofFn]
      rw [List.getD_eq_getElem _ _ (by simp [rep0, hw])]
      simp [rep0, evalRep]
    · rw [List.getD_eq_default _ _ (by simp; omega)]
      rw [List.getD_eq_default _ _ (by simp [rep0]; omega)]
      simp [evalRep]
  | append_singleton gs g ih =>
    have hMgs : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hM g' (List.mem_append_left _ hg')
    obtain ⟨A, rep, hWF, hsz, hlen, hval⟩ := ih hMgs
    obtain ⟨hop, hglen⟩ := hM g (List.mem_append_right _ List.mem_cons_self)
    have hcnt : (gs ++ [g]).countP (fun g' => isAndOp g'.op) =
        gs.countP (fun g' => isAndOp g'.op) + (if isAndOp g.op then 1 else 0) := by
      simp [List.countP_append]
    let getR : ℕ → Option (Finset (Fin n) × Finset (Fin A.size)) :=
      fun u => rep.getD u (some (∅, ∅))
    rcases hop with hand | hor
    · have hisA : isAndOp g.op = true := by simp [isAndOp, hand]
      rcases hins : g.inputs with _ | ⟨u, _ | ⟨v, _ | _⟩⟩
      · refine ⟨A, rep ++ [none], hWF, by rw [hcnt, hisA]; simp; omega, by simp [hlen]; omega, ?_⟩
        exact step_same_circuit gs g A rep hlen hval none fun U => by
          simp [hand, hins, GateOp.eval, evalRep]
      · refine ⟨A, rep ++ [getR u], hWF, by rw [hcnt, hisA]; simp; omega, by simp [hlen]; omega, ?_⟩
        exact step_same_circuit gs g A rep hlen hval (getR u) fun U => by
          simp only [hand, hins, List.map_cons, List.map_nil, GateOp.eval,
            List.all_cons, List.all_nil, Bool.and_true, id]
          exact hval U u
      · cases hru : getR u with
        | none =>
          refine ⟨A, rep ++ [getR v], hWF, by rw [hcnt, hisA]; simp; omega, by simp [hlen]; omega, ?_⟩
          exact step_same_circuit gs g A rep hlen hval (getR v) fun U => by
            simp only [hand, hins, List.map_cons, List.map_nil, GateOp.eval,
              List.all_cons, List.all_nil, Bool.and_true, id]
            rw [hval U u, hval U v]
            change (evalRep A U (getR u) && evalRep A U (getR v)) = evalRep A U (getR v)
            rw [hru]; simp [evalRep]
        | some p1 =>
          cases hrv : getR v with
          | none =>
            refine ⟨A, rep ++ [some p1], hWF, by rw [hcnt, hisA]; simp; omega, by simp [hlen]; omega, ?_⟩
            exact step_same_circuit gs g A rep hlen hval (some p1) fun U => by
              simp only [hand, hins, List.map_cons, List.map_nil, GateOp.eval,
                List.all_cons, List.all_nil, Bool.and_true, id]
              rw [hval U u, hval U v]
              change (evalRep A U (getR u) && evalRep A U (getR v)) = evalRep A U (some p1)
              rw [hru, hrv]; simp [evalRep]
          | some p2 =>
            rcases p1 with ⟨B1, F1⟩
            rcases p2 with ⟨B2, F2⟩
            refine ⟨snocCircuit A B1 F1 B2 F2, rep.map liftRep ++ [some (∅, {Fin.last A.size})],
              snocCircuit_wellFormed A hWF B1 F1 B2 F2,
              by show A.size + 1 ≤ _; rw [hcnt, hisA]; simp; omega,
              by simp [hlen]; omega, ?_⟩
            intro U w
            rw [run_snoc]
            have hrl : (run gs (List.ofFn fun i : Fin n => decide (i ∈ U))).length = n + gs.length := by
              rw [run_length, List.length_ofFn]
            have hmlen : (rep.map liftRep).length = n + gs.length := by rw [List.length_map, hlen]
            rcases Nat.lt_trichotomy w (n + gs.length) with hlt | rfl | hgt
            · rw [getD_snoc_lt _ _ _ w (by omega)]
              rw [getD_snoc_lt _ _ _ w (by omega)]
              rw [hval U w]
              rw [List.getD_eq_getElem _ _ (by omega : w < (rep.map liftRep).length), List.getElem_map, evalRep_liftRep]
              rw [List.getD_eq_getElem _ _ (by omega : w < rep.length)]
            · rw [← hrl, getD_snoc_eq, hrl, ← hmlen, getD_snoc_eq]
              simp only [hand, hins, List.map_cons, List.map_nil, GateOp.eval,
                List.all_cons, List.all_nil, Bool.and_true, id]
              rw [hval U u, hval U v]
              change (evalRep A U (getR u) && evalRep A U (getR v)) =
                evalRep (snocCircuit A B1 F1 B2 F2) U (some (∅, {Fin.last A.size}))
              rw [hru, hrv]
              simp only [evalRep, Finset.notMem_empty, false_and, exists_false, false_or,
                Finset.mem_singleton, exists_eq_left]
              rw [snocCircuit_gateVal_last]
              simp only [evalRep]
              exact Bool.decide_eq_true.symm
            · rw [getD_snoc_gt _ _ _ w (by omega)]
              rw [getD_snoc_gt _ _ _ w (by omega)]
              simp [evalRep]
      · rw [hins] at hglen; simp at hglen
    · let rnew := g.inputs.foldl (fun acc u => orRep acc (getR u)) (some (∅, ∅))
      have hfold : ∀ (U : Finset (Fin n)) (xs : List ℕ)
          (init : Option (Finset (Fin n) × Finset (Fin A.size))),
          evalRep A U (xs.foldl (fun acc u => orRep acc (getR u)) init) =
            (evalRep A U init || xs.any fun u => evalRep A U (getR u)) := by
        intro U xs
        induction xs with
        | nil => intro init; simp
        | cons a t iht =>
          intro init
          simp only [List.foldl_cons, List.any_cons]
          rw [iht (orRep init (getR a)), evalRep_orRep, Bool.or_assoc]
      refine ⟨A, rep ++ [rnew], hWF, by rw [hcnt]; omega, by simp [hlen]; omega, ?_⟩
      exact step_same_circuit gs g A rep hlen hval rnew fun U => by
        simp only [hor, GateOp.eval]
        dsimp only [rnew]
        rw [hfold U g.inputs (some (∅, ∅))]
        have hemp : evalRep A U (some (∅, ∅)) = false := by simp [evalRep]
        rw [hemp, Bool.false_or]
        exact any_map_congr g.inputs _ _ fun u _ => hval U u

end AndLower.Source9051

lemma AndLower.Source9051 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 → (∀ (x5 : Fin x1 → Bool), x3.eval (List.ofFn x5) = Bool.true ↔ ∃ (x6 : Fin x1) (x7 : Fin x1), x2.Adj x6 x7 ∧ x5 x6 = Bool.true ∧ x5 x7 = Bool.true) → ∃ (x6 : PEqualNP.AndCount.AndCountCircuit x1), x6.WellFormed ∧ x6.Computes x2 ∧ x6.size ≤ List.countP (fun (x7 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x7.op Bool.true Bool.false Bool.false (fun (x8 : ℕ) => Bool.false) Bool.false) x3.gates := by
  intro n G C hM heval
  obtain ⟨A, rep, hWF, hsz, _, hval⟩ := PEqualNP.Outside.L_meta_2373.AndLower.Source9051.build_aux n C.gates hM
  cases hrout : rep.getD C.output (some (∅, ∅)) with
  | none =>
    exfalso
    have h0 := hval ∅ C.output
    rw [hrout] at h0
    have h0' : C.eval (List.ofFn fun i : Fin n => decide (i ∈ (∅ : Finset (Fin n)))) = true := h0
    rw [heval] at h0'
    rcases h0' with ⟨a, _, _, ha, _⟩
    simp at ha
  | some p =>
    rcases p with ⟨Bout, Fout⟩
    let A' : PEqualNP.AndCount.AndCountCircuit n := { A with outVars := Bout, outGates := Fout }
    refine ⟨A', hWF, ?_, hsz⟩
    intro U
    have h1 := hval U C.output
    rw [hrout] at h1
    have h2 : A'.eval U = PEqualNP.Outside.L_meta_2373.AndLower.Source9051.evalRep A U (some (Bout, Fout)) := by
      simp only [PEqualNP.AndCount.AndCountCircuit.eval, PEqualNP.Outside.L_meta_2373.AndLower.Source9051.evalRep, A',
        PEqualNP.AndCount.AndCountCircuit.gateVal]
      have hgv : ∀ j : Fin A.size,
          ({ A with outVars := Bout, outGates := Fout } : PEqualNP.AndCount.AndCountCircuit n).gateValFuel U A.size j =
            A.gateValFuel U A.size j :=
        PEqualNP.Outside.L_meta_2373.AndLower.Source9051.gateValFuel_withOut A Bout Fout U A.size
      simp only [hgv]
      rfl
    rw [h2, ← h1]
    have h3 := heval (fun i : Fin n => decide (i ∈ U))
    change C.eval (List.ofFn fun i : Fin n => decide (i ∈ U)) = true ↔ _
    rw [h3]
    constructor
    · rintro ⟨a, b, hab, ha, hb⟩
      exact ⟨a, of_decide_eq_true ha, b, of_decide_eq_true hb, hab⟩
    · rintro ⟨a, ha, b, hb, hab⟩
      exact ⟨a, b, hab, decide_eq_true ha, decide_eq_true hb⟩
namespace AndLower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.AndCount

def petersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def graph : SimpleGraph (Fin 10) :=
  SimpleGraph.fromRel fun a b : Fin 10 =>
    (a.val, b.val) ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
      (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
      (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (ℕ × ℕ))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma graph_related : ∀ u v : Fin 10,
    graph.Adj u v ↔ Source635.related u v = true := by
  unfold graph Source635.related
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma petersen_eq_true : ∀ x : Fin 10 → Bool,
    petersen x = true ↔ ∃ u v : Fin 10, graph.Adj u v ∧ x u = true ∧ x v = true := by
  unfold petersen graph
  decide

lemma monotone_and_lower (C : Circuit) (hm : Monotone2 C)
    (hc : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) :
    6 ≤ C.gates.countP (fun g => match g.op with | .and => true | _ => false) := by
  have computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin 10, graph.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    rw [hc x]
    exact petersen_eq_true x
  obtain ⟨D, hwf, hD, hsize⟩ := Source9051 10 graph C hm computes
  have sep : Source635.Separates D := by
    intro I hI
    obtain ⟨hind, hmax⟩ := hI
    constructor
    · apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨a, ha, b, hb, hab⟩ := (hD I).mp ht
      have hr := (graph_related a b).mp hab
      rw [hind a ha b hb] at hr
      contradiction
    · intro u hu
      obtain ⟨v, hv, huv⟩ := hmax u hu
      apply (hD (insert u I)).mpr
      exact ⟨u, Finset.mem_insert_self .., v, Finset.mem_insert_of_mem hv,
        (graph_related u v).mpr huv⟩
  have hlow : 6 ≤ D.size := by
    have hn := Source635.lower D sep
    omega
  have hp : (fun g : Gate => GateOp.casesOn g.op (true : Bool) false false (fun _ => false) false) =
      (fun g : Gate => match g.op with | .and => true | _ => false) := by
    funext g
    cases g.op <;> rfl
  rw [hp] at hsize
  exact hlow.trans hsize

end AndLower



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

end PEqualNP.Outside.L_meta_2373
