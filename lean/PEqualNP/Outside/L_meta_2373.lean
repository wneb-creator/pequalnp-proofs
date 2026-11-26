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

end PEqualNP.Outside.L_meta_2373
