import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_908_aux

open PEqualNP.AndCount
open PEqualNP.AndCount.AndCountCircuit

abbrev V := Fin 9

abbrev X := Option V

abbrev Slot := Fin 4 × Bool

def edgePairs : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6), (3, 5), (3, 7), (4, 6), (4, 8), (5, 7), (6, 8), (7, 8)]

def related (v w : V) : Bool :=
  decide (v ≠ w ∧ (((v : ℕ), (w : ℕ)) ∈ edgePairs ∨ ((w : ℕ), (v : ℕ)) ∈ edgePairs))

def Good (I : Finset V) : Prop :=
  (∀ v ∈ I, ∀ w ∈ I, related v w = false) ∧
  (∀ u : V, u ∉ I → ∃ v ∈ I, related u v = true)

def rows : Fin 16 → Finset V :=
  ![{0, 3, 4}, {2, 3, 4}, {0, 4, 5}, {0, 3, 6}, {0, 5, 6}, {1, 5, 6}, {1, 2, 7}, {0, 4, 7},
    {2, 4, 7}, {0, 6, 7}, {1, 6, 7}, {1, 2, 8}, {0, 3, 8}, {2, 3, 8}, {0, 5, 8}, {1, 5, 8}]

def rowMasks : Fin 16 → ℕ :=
  ![25, 28, 49, 73, 97, 98, 134, 145, 148, 193, 194, 262, 265, 268, 289, 290]

def through : V → Fin 5 → Fin 16 :=
  ![![0, 2, 3, 4, 7],
    ![5, 6, 10, 11, 15],
    ![1, 6, 8, 11, 13],
    ![0, 1, 3, 12, 13],
    ![0, 1, 2, 7, 8],
    ![2, 4, 5, 14, 15],
    ![3, 4, 5, 9, 10],
    ![6, 7, 8, 9, 10],
    ![11, 12, 13, 14, 15]]

def decode (m : ℕ) : Finset V :=
  Finset.univ.filter (fun v => m.testBit v.val)

def encode (S : Finset V) : ℕ :=
  ∑ v ∈ S, 2 ^ v.val

theorem mem_decode (m : ℕ) (v : V) : v ∈ decode m ↔ m.testBit v.val = true := by
  simp [decode]

theorem decode_rowMasks : ∀ r : Fin 16, decode (rowMasks r) = rows r := by
  decide +kernel

theorem encode_lt (S : Finset V) : encode S < 512 := by
  have hle : encode S ≤ ∑ v : V, 2 ^ v.val :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have htot : (∑ v : V, 2 ^ v.val) = 511 := by decide
  omega

theorem nat_add_eq_or : ∀ a b : ℕ, (a &&& b) = 0 → a + b = a ||| b := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b h
    by_cases ha : a = 0
    · subst ha
      simp
    · have hdiv : a / 2 < a := Nat.bitwise_rec_lemma ha
      have hsub : (a / 2 &&& b / 2) = 0 := by
        apply Nat.eq_of_testBit_eq
        intro k
        rw [Nat.testBit_and, Nat.testBit_div_two, Nat.testBit_div_two, Nat.zero_testBit]
        have hk := congrArg (fun n => n.testBit (k + 1)) h
        simpa [Nat.testBit_and] using hk
      have h0 : a % 2 = 0 ∨ b % 2 = 0 := by
        have hk : (a &&& b).testBit 0 = false := by
          rw [h]
          rfl
        rw [Nat.testBit_and, Nat.testBit_zero, Nat.testBit_zero, Bool.and_eq_false_iff] at hk
        simp only [decide_eq_false_iff_not] at hk
        omega
      have hih := ih (a / 2) hdiv (b / 2) hsub
      have hlor : (a ||| b) = 2 * ((a ||| b) / 2) + (a ||| b) % 2 := (Nat.div_add_mod _ 2).symm
      have hordiv : (a ||| b) / 2 = (a / 2 ||| b / 2) := by
        apply Nat.eq_of_testBit_eq
        intro k
        simp [Nat.testBit_div_two, Nat.testBit_or]
      have hormod : (a ||| b) % 2 = a % 2 + b % 2 := by
        have h2 : (a ||| b).testBit 0 = true ↔ (a.testBit 0 || b.testBit 0) = true := by
          rw [Nat.testBit_or]
        simp only [Nat.testBit_zero, Bool.or_eq_true, decide_eq_true_eq] at h2
        omega
      omega

theorem encode_testBit (S : Finset V) (v : V) :
    (encode S).testBit v.val = decide (v ∈ S) := by
  induction S using Finset.induction_on generalizing v with
  | empty =>
    simp [encode]
  | insert a s ha ih =>
    have hdisj : (2 ^ a.val &&& encode s) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hka : a.val = k
      · subst hka
        have hfa := ih a
        simp [ha] at hfa
        simp [hfa]
      · simp [hka]
    have hsum : encode (insert a s) = 2 ^ a.val + encode s := by
      unfold encode
      exact Finset.sum_insert ha
    rw [hsum, nat_add_eq_or _ _ hdisj, Nat.testBit_or, Nat.testBit_two_pow, ih]
    by_cases hva : a = v
    · subst hva
      simp
    · have hne : a.val ≠ v.val := fun h => hva (Fin.ext h)
      simp [hne, Ne.symm hva]

theorem decode_encode (S : Finset V) : decode (encode S) = S := by
  ext v
  rw [mem_decode, encode_testBit, decide_eq_true_eq]

theorem decodeSurj (S : Finset V) : ∃ m : Fin 512, decode m.val = S :=
  ⟨⟨encode S, encode_lt S⟩, decode_encode S⟩

theorem related_symm : ∀ a b : V, related a b = related b a := by
  decide +kernel

theorem good_iff (G : SimpleGraph V)
    (hG : G = SimpleGraph.fromRel (fun a b : Fin 9 => ((a : ℕ), (b : ℕ)) ∈ edgePairs))
    (I : Finset V) :
    Good I ↔ (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) ∧ (∀ w : V, w ∉ I → ∃ a ∈ I, G.Adj a w) := by
  have hr (a b : V) : related a b = true ↔ G.Adj a b := by
    subst hG
    simp [SimpleGraph.fromRel_adj, related]
  have hn (a b : V) : related a b = false ↔ ¬ G.Adj a b := by
    rw [← hr, Bool.eq_false_iff]
  have hr' (w a : V) : related w a = true ↔ G.Adj a w := by
    rw [related_symm, hr]
  simp only [Good, hn, hr']

theorem rowsGood : ∀ i : Fin 16, Good (rows i) := by
  unfold Good
  decide +kernel

theorem allRowMasks : ∀ m : Fin 512,
    (∀ a b : V, m.val.testBit a.val = true → m.val.testBit b.val = true → related a b = false) →
    (∀ u : V, m.val.testBit u.val = false → ∃ v : V, m.val.testBit v.val = true ∧ related u v = true) →
    ∃ r : Fin 16, m.val = rowMasks r := by
  decide +kernel

theorem allRows : ∀ I : Finset V, Good I → ∃ r : Fin 16, I = rows r := by
  intro I hI
  obtain ⟨m, rfl⟩ := decodeSurj I
  have h1 : ∀ a b : V, m.val.testBit a.val = true → m.val.testBit b.val = true →
      related a b = false := by
    intro a b ha hb
    exact hI.1 a ((mem_decode m.val a).mpr ha) b ((mem_decode m.val b).mpr hb)
  have h2 : ∀ u : V, m.val.testBit u.val = false →
      ∃ v : V, m.val.testBit v.val = true ∧ related u v = true := by
    intro u hu
    have hnu : u ∉ decode m.val := by
      rw [mem_decode]
      simp [hu]
    obtain ⟨v, hv, hr⟩ := hI.2 u hnu
    exact ⟨v, (mem_decode m.val v).mp hv, hr⟩
  obtain ⟨r, hr⟩ := allRowMasks m h1 h2
  exact ⟨r, by rw [hr, decode_rowMasks]⟩

theorem rowContains : ∀ v i, v ∈ rows (through v i) := by
  decide +kernel

theorem rowDiff : ∀ v i j, i ≠ j → ∃ w ∈ rows (through v i), w ∉ rows (through v j) := by
  decide +kernel

theorem orderedPair : ∀ v w : V, v ≠ w → ∃ i, v ∈ rows i ∧ w ∉ rows i := by
  decide +kernel

theorem jointlyPresent : ∀ a b : V, related a b = false → ∃ i, a ∈ rows i ∧ b ∈ rows i := by
  decide +kernel

theorem noSquare : ∀ a b c d : V, related a c = true → related a d = true →
    related b c = true → related b d = true → a = b ∨ c = d := by
  decide +kernel

theorem isolatedEdge : ∀ a b : V, related a b = true → ∃ i, a ∉ rows i ∧
    ∀ x ∈ insert a (rows i), ∀ y ∈ insert a (rows i), related x y = true →
      (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  decide +kernel

def popcnt9 (m : ℕ) : ℕ :=
  (List.finRange 9).countP (fun v : V => m.testBit v.val)

theorem card_decode (m : ℕ) : (decode m).card = popcnt9 m := by
  unfold decode popcnt9
  rw [Finset.card_filter]
  have h : ∀ l : List V, (l.map (fun v => if m.testBit v.val = true then 1 else 0)).sum =
      l.countP (fun v => m.testBit v.val) := by
    intro l
    induction l with
    | nil => rfl
    | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.countP_cons, ih]
      cases m.testBit a.val <;> simp [Nat.add_comm]
  rw [← h (List.finRange 9)]
  rfl

theorem largeMaskHasEdge : ∀ m : Fin 512, 4 ≤ popcnt9 m.val →
    ∃ x y : V, m.val.testBit x.val = true ∧ m.val.testBit y.val = true ∧ related x y = true := by
  decide +kernel

theorem largeHasEdge : ∀ I : Finset V, 4 ≤ I.card →
    ∃ x ∈ I, ∃ y ∈ I, related x y = true := by
  intro I hcard
  obtain ⟨m, rfl⟩ := decodeSurj I
  rw [card_decode] at hcard
  obtain ⟨x, y, hx, hy, hxy⟩ := largeMaskHasEdge m hcard
  exact ⟨x, (mem_decode m.val x).mpr hx, y, (mem_decode m.val y).mpr hy, hxy⟩

theorem sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
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

theorem gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
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

theorem gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
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

theorem sideTrue_mono_U {n k : ℕ} {U Vset : Finset (Fin n)} (hUV : U ⊆ Vset)
    (B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (hv : ∀ j, j < i → v1 j = true → v2 j = true)
    (hs : sideTrue U B F i v1 = true) :
    sideTrue Vset B F i v2 = true := by
  unfold sideTrue at hs ⊢
  rw [decide_eq_true_eq] at hs ⊢
  rcases hs with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
  · exact Or.inl ⟨v, hvB, hUV hvU⟩
  · exact Or.inr ⟨j, hjF, hji, hv j hji hvj⟩

theorem gateValFuel_mono_U {n : ℕ} (C : AndCountCircuit n) {U Vset : Finset (Fin n)}
    (hUV : U ⊆ Vset) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel Vset d i = true := by
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

theorem gateVal_mono_U {n : ℕ} (C : AndCountCircuit n) {U Vset : Finset (Fin n)}
    (hUV : U ⊆ Vset) (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal Vset i = true :=
  gateValFuel_mono_U C hUV C.size i h

def Free (C : AndCountCircuit 9) (v : V) : Finset (Fin C.size) :=
  Finset.univ.filter (fun i => v ∉ C.leftVars i ∧ v ∉ C.rightVars i)

def sideL (C : AndCountCircuit 9) (I : Finset V) (i : Fin C.size) : Bool :=
  sideTrue I (C.leftVars i) (C.leftGates i) i (C.gateVal I)

def sideR (C : AndCountCircuit 9) (I : Finset V) (i : Fin C.size) : Bool :=
  sideTrue I (C.rightVars i) (C.rightGates i) i (C.gateVal I)

def Separates (C : AndCountCircuit 9) : Prop :=
  ∀ I, Good I → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true

theorem unionSide (C : AndCountCircuit 9) (U I J B : Finset V)
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

theorem mergeInput (C : AndCountCircuit 9) (I J U : Finset V) (v : V)
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

theorem free_bound (C : AndCountCircuit 9) (h : Separates C) (v : V) :
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

def MaskLe (C : AndCountCircuit 9) (v w : V) : Prop :=
  ∀ i, (v ∈ C.leftVars i → w ∈ C.leftVars i) ∧ (v ∈ C.rightVars i → w ∈ C.rightVars i)

theorem bare_out_empty (C : AndCountCircuit 9) (h : Separates C) (v : V) : v ∉ C.outVars := by
  intro hv
  have he := (h _ (rowsGood (through v 0))).1
  have ht : C.eval (rows (through v 0)) = true :=
    decide_eq_true (Or.inl ⟨v, hv, rowContains v 0⟩)
  simp [he] at ht

theorem sideMasked (I : Finset V) (v w : V) (hw : w ∈ I) (B : Finset V)
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

theorem notMasked (C : AndCountCircuit 9) (h : Separates C) {v w : V} (hne : v ≠ w) :
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

theorem atLeastFive (C : AndCountCircuit 9) (h : Separates C) : 5 ≤ C.size := by
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

theorem starCenter (L R : Finset V) (h : ∀ a ∈ L, ∀ b ∈ R, related a b = true) :
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

theorem firstTrue (C : AndCountCircuit 9) (h : Separates C) (U : Finset V) (hu : C.eval U = true) :
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

theorem safe_bound (C : AndCountCircuit 9) (h : Separates C)
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
  have hsmall : (Finset.univ \ T).card < 4 := by
    by_contra! hh
    obtain ⟨a, ha, b, hb, hab⟩ := largeHasEdge _ hh
    exact (covers a b hab).elim (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).2
  have htotal := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ T)
  have hbound : T.card ≤ C.size := (Finset.card_image_le).trans_eq (by simp)
  simp [V] at htotal
  omega

def singSet {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) : Finset (Fin n) :=
  Finset.univ.filter (fun v => C.gateVal {v} i = true)

theorem mem_singSet {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ singSet C i ↔ C.gateVal {v} i = true := by
  unfold singSet
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ v)

def stripCircuit {n : ℕ} (C : AndCountCircuit n) : AndCountCircuit n where
  size := C.size
  leftVars i := (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  leftGates := C.leftGates
  rightVars i := (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i
  rightGates := C.rightGates
  outVars := C.outVars ∪ C.outGates.biUnion (singSet C)
  outGates := C.outGates

theorem strip_size {n : ℕ} (C : AndCountCircuit n) : (stripCircuit C).size = C.size := rfl

theorem strip_wf {n : ℕ} (C : AndCountCircuit n) (h : C.WellFormed) : (stripCircuit C).WellFormed := h

theorem mem_strip_leftVars {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).leftVars i ↔
      (v ∈ C.leftVars i ∨ ∃ j ∈ C.leftGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  change v ∈ (C.leftVars i ∪ ((C.leftGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i ↔ _
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    mem_singSet, and_assoc]

theorem mem_strip_rightVars {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) (v : Fin n) :
    v ∈ (stripCircuit C).rightVars i ↔
      (v ∈ C.rightVars i ∨ ∃ j ∈ C.rightGates i, j < i ∧ C.gateVal {v} j = true) ∧
      C.gateVal {v} i ≠ true := by
  change v ∈ (C.rightVars i ∪ ((C.rightGates i).filter (fun j => j < i)).biUnion (singSet C)) \ singSet C i ↔ _
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter,
    mem_singSet, and_assoc]

theorem mem_strip_outVars {n : ℕ} (C : AndCountCircuit n) (v : Fin n) :
    v ∈ (stripCircuit C).outVars ↔
      v ∈ C.outVars ∨ ∃ j ∈ C.outGates, C.gateVal {v} j = true := by
  change v ∈ C.outVars ∪ C.outGates.biUnion (singSet C) ↔ _
  simp only [Finset.mem_union, Finset.mem_biUnion, mem_singSet]

theorem strip_singleton_false {n : ℕ} (C : AndCountCircuit n) (v : Fin n) :
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

theorem strip_disjoint {n : ℕ} (C : AndCountCircuit n) (i : Fin C.size) :
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

theorem strip_gateVal_le {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
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

theorem strip_gateVal_ge {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
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

theorem strip_eval_eq {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
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

def vars (C : AndCountCircuit 9) (i : Fin C.size) (d : Bool) : Finset V :=
  if d then C.rightVars i else C.leftVars i

def refs (C : AndCountCircuit 9) (i : Fin C.size) (d : Bool) : Finset (Fin C.size) :=
  (if d then C.rightGates i else C.leftGates i).filter (· < i)

def fires (A B U : Finset V) : Prop :=
  (∃ v ∈ A, v ∈ U) ∧ (∃ v ∈ B, v ∈ U)

def raw (C : AndCountCircuit 9) (p : Fin C.size) (U : Finset V) : Prop :=
  fires (C.leftVars p) (C.rightVars p) U

def onSide (C : AndCountCircuit 9) (i : Fin C.size) (d : Bool) (U : Finset V) : Prop :=
  (∃ v ∈ vars C i d, v ∈ U) ∨ ∃ j ∈ refs C i d, C.gateVal U j = true

theorem gate_iff (C : AndCountCircuit 9) (i : Fin C.size) (U : Finset V) :
    C.gateVal U i = true ↔ ∀ d, onSide C i d U := by
  rw [gateVal_unfold, Bool.and_eq_true]
  simp [Bool.forall_bool, onSide, sideTrue, refs, vars, and_assoc]

theorem raw_gate (C : AndCountCircuit 9) (p : Fin C.size) (U : Finset V) (hg : raw C p U) :
    C.gateVal U p = true :=
  (gate_iff ..).2 (by
    rintro (_ | _)
    · exact Or.inl hg.1
    · exact Or.inl hg.2)

def Early (C : AndCountCircuit 9) (p : Fin C.size) : Prop :=
  ∀ j < p, ∀ r : Fin 16, C.gateVal (rows r) j = false

theorem earliest_raw (C : AndCountCircuit 9) (p : Fin C.size) (h : Early C p) (r : Fin 16) :
    C.gateVal (rows r) p = true ↔ raw C p (rows r) := by
  refine ⟨fun ht => ?_, raw_gate C p (rows r)⟩
  have hs (d) := (gate_iff ..).1 ht d
  have hv (d) : ∃ v ∈ vars C p d, v ∈ rows r := by
    rcases hs d with hv | ⟨j, hj, ht'⟩
    · exact hv
    · simp [h j (Finset.mem_filter.mp hj).2 r] at ht'
  exact ⟨hv false, hv true⟩

theorem blocked (C : AndCountCircuit 9) (p : Fin C.size) (early : Early C p)
    (sep : Separates C) (nout : p ∉ C.outGates) (T : Finset (Fin 16)) (U : Finset V)
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

def present (A B I : Finset V) : X → Prop
  | none => fires A B I
  | some v => v ∈ I

def wire (C : AndCountCircuit 9) (p i : Fin C.size) (d : Bool) : X → Prop
  | none => p ∈ refs C i d
  | some v => v ∈ vars C i d

theorem wire_on (C : AndCountCircuit 9) (p i : Fin C.size) (d : Bool) (I : Finset V) (z : X)
    (hw : wire C p i d z) (hz : present (C.leftVars p) (C.rightVars p) I z) : onSide C i d I := by
  cases z with
  | none => exact Or.inr ⟨p, hw, raw_gate C p I hz⟩
  | some v => exact Or.inl ⟨v, hw, hz⟩

def Dir (A B : Finset V) (r s : Fin 16) : Prop :=
  ∃ u ∈ rows s, u ∉ rows r ∧
    (fires A B (insert u (rows r)) → fires A B (rows r) ∨ fires A B (rows s))

def Apart (A B : Finset V) (r s : Fin 16) : Prop :=
  Dir A B r s ∨ Dir A B s r

theorem dir_block (C : AndCountCircuit 9) (p : Fin C.size) (early : Early C p)
    (sep : Separates C) (nout : p ∉ C.outGates) (r s : Fin 16)
    (hd : Dir (C.leftVars p) (C.rightVars p) r s)
    (agree : ∀ i, i ≠ p → C.gateVal (rows r) i = false → C.gateVal (rows s) i = false →
      ∃ d, ¬ onSide C i d (rows r) ∧ ¬ onSide C i d (rows s)) : False := by
  obtain ⟨u, hus, hur, hg⟩ := hd
  have hh := blocked C p early sep nout {r, s} (insert u (rows r)) (by
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

noncomputable def idle (C : AndCountCircuit 9) (p : Fin C.size) (z : X) : Finset (Fin C.size) := by
  classical
  exact Finset.univ.filter (fun i => i ≠ p ∧ ¬ wire C p i false z ∧ ¬ wire C p i true z)

noncomputable def pick (C : AndCountCircuit 9) (p i : Fin C.size) (z : X) (r : Fin 16) : Bool := by
  classical
  exact if wire C p i false z then true else if wire C p i true z then false
    else decide (onSide C i false (rows r))

theorem pick_off (C : AndCountCircuit 9) (p i : Fin C.size) (z : X) (r : Fin 16)
    (hr : present (C.leftVars p) (C.rightVars p) (rows r) z) (hi : C.gateVal (rows r) i = false) :
    ¬ onSide C i (pick C p i z r) (rows r) := by
  classical
  have h := Bool.eq_false_iff.mp hi
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

theorem k_idle (C : AndCountCircuit 9) (p : Fin C.size) (early : Early C p)
    (sep : Separates C) (nout : p ∉ C.outGates) (z : X) (k : ℕ)
    (rs : Fin (2 ^ k + 1) → Fin 16)
    (hz : ∀ a, present (C.leftVars p) (C.rightVars p) (rows (rs a)) z)
    (apart : ∀ a b, a ≠ b → Apart (C.leftVars p) (C.rightVars p) (rs a) (rs b)) :
    k + 1 ≤ (idle C p z).card := by
  classical
  let code (a : Fin (2 ^ k + 1)) (j : ↥(idle C p z)) := pick C p j z (rs a)
  have hinj : Function.Injective code := by
    intro a b hab
    by_contra hne
    have ag (i : Fin C.size) (hi : i ≠ p) (ha : C.gateVal (rows (rs a)) i = false)
        (hb : C.gateVal (rows (rs b)) i = false) :
        ∃ d, ¬ onSide C i d (rows (rs a)) ∧ ¬ onSide C i d (rows (rs b)) := by
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
  have hp : 2 ^ (idle C p z).card ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
  omega

def Consistent (M : Finset Slot) : Prop :=
  ∀ q ∈ M, ∀ s ∈ M, q.1 = s.1 → q.2 = s.2

def Cover (A B : Finset V) (pos : X → Finset Slot) : Prop :=
  ∀ r : Fin 16, ∃ M : Finset Slot, Consistent M ∧
    (∀ z, present A B (rows r) z → Disjoint M (pos z)) ∧
    ∀ u : V, u ∉ rows r → (∃ s ∈ M, s ∈ pos (some u)) ∨
      (¬ fires A B (rows r) ∧ fires A B (insert u (rows r)) ∧ ∃ s ∈ M, s ∈ pos none)

def Strong (A B : Finset V) (v : V) : Prop :=
  (v ∈ A ∨ v ∈ B) ∨ ∃ rs : Fin 5 → Fin 16,
    (∀ a, v ∈ rows (rs a)) ∧ (∀ a b, a ≠ b → Apart A B (rs a) (rs b))

def Cap (A B : Finset V) (pos : X → Finset Slot) : Prop :=
  (∀ v, Consistent (pos (some v)) ∧ (pos (some v)).card ≤ 2) ∧
  (∀ v, Strong A B v → (pos (some v)).card ≤ 1) ∧
  (∀ (k : ℕ) (rs : Fin (2 ^ k + 1) → Fin 16), (∀ a, fires A B (rows (rs a))) →
    (∀ a b, a ≠ b → Apart A B (rs a) (rs b)) → ((pos none).image Prod.fst).card + k + 1 ≤ 4)

def otherGate (C : AndCountCircuit 9) (p : Fin C.size) (sz : C.size = 5) : Fin 4 ↪o Fin C.size :=
  (Finset.univ.erase p).orderEmbOfFin (by simp [Finset.card_erase_of_mem, sz])

theorem otherGate_ne (C : AndCountCircuit 9) (p : Fin C.size) (sz : C.size = 5) (j : Fin 4) :
    otherGate C p sz j ≠ p :=
  Finset.ne_of_mem_erase ((Finset.univ.erase p).orderEmbOfFin_mem (by simp [Finset.card_erase_of_mem, sz]) j)

theorem otherGate_onto (C : AndCountCircuit 9) (p : Fin C.size) (sz : C.size = 5)
    (i : Fin C.size) (hi : i ≠ p) : ∃ j : Fin 4, otherGate C p sz j = i := by
  have hh : i ∈ Finset.univ.erase p := by simp [hi]
  change i ∈ Set.range (otherGate C p sz)
  unfold otherGate
  rwa [Finset.range_orderEmbOfFin]

noncomputable def circuitPos (C : AndCountCircuit 9) (p : Fin C.size) (sz : C.size = 5) (z : X) :
    Finset Slot := by
  classical
  exact Finset.univ.filter (fun s => wire C p (otherGate C p sz s.1) s.2 z)

theorem mem_circuitPos (C : AndCountCircuit 9) (p : Fin C.size) (sz : C.size = 5) (z : X) (s : Slot) :
    s ∈ circuitPos C p sz z ↔ wire C p (otherGate C p sz s.1) s.2 z := by
  classical
  simp [circuitPos]

theorem lift_slots_exact (C : AndCountCircuit 9) (p : Fin C.size) (early : Early C p)
    (sep : Separates C) (nout : p ∉ C.outGates) (dis : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (sz : C.size = 5) :
    Cover (C.leftVars p) (C.rightVars p) (circuitPos C p sz) ∧
      Cap (C.leftVars p) (C.rightVars p) (circuitPos C p sz) := by
  classical
  let e := otherGate C p sz
  have de (i) : e i ≠ p := otherGate_ne C p sz i
  have onto (i) (hp : i ≠ p) : ∃ j, e j = i := otherGate_onto C p sz i hp
  let pos := circuitPos C p sz
  have pm {z : X} {s : Slot} : s ∈ pos z ↔ wire C p (e s.1) s.2 z := mem_circuitPos C p sz z s
  refine ⟨?_, ?_⟩
  · intro r
    let d (j : Fin 4) := decide (onSide C (e j) false (rows r))
    let M : Finset Slot := Finset.univ.filter (fun s => C.gateVal (rows r) (e s.1) = false ∧ s.2 = d s.1)
    have off {s : Slot} (hs : s ∈ M) : ¬ onSide C (e s.1) s.2 (rows r) := by
      obtain ⟨hg, hd⟩ := (Finset.mem_filter.mp hs).2
      have hn : ¬ ∀ b, onSide C (e s.1) b (rows r) := fun h => by
        simpa [hg] using (gate_iff ..).2 h
      rw [hd]
      by_cases h₀ : onSide C (e s.1) false (rows r)
      · simpa [d, h₀] using (fun ht => hn (by rintro (_ | _) <;> assumption) :
          ¬ onSide C (e s.1) true (rows r))
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
          have hrow : ¬ fires (C.leftVars p) (C.rightVars p) (rows r) :=
            fun h => hf (Or.inr ⟨_, hp, raw_gate C p _ h⟩)
          exact bad.2 hrow hU s hs (pm.mpr hp))
      simp [(sep _ (rowsGood r)).2 u hu] at hb
  · have cEq (v : V) : Consistent (pos (some v)) := by
      rintro ⟨j, b⟩ hs ⟨k, c⟩ ht rfl
      have h₁ := pm.mp hs
      have h₂ := pm.mp ht
      cases b <;> cases c <;> first | rfl | exact False.elim (Finset.disjoint_left.mp (dis _) h₁ h₂) |
        exact False.elim (Finset.disjoint_left.mp (dis _) h₂ h₁)
    have cardEq (v : V) : (pos (some v)).card = ((pos (some v)).image Prod.fst).card := by
      symm
      exact Finset.card_image_of_injOn (fun a ha b hb hab => Prod.ext hab (cEq v a ha b hb hab))
    have bd (z : X) (k : ℕ) (hz : k + 1 ≤ (idle C p z).card) :
        ((pos z).image Prod.fst).card + k + 1 ≤ 4 := by
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
      simp only [O, Finset.card_map, Finset.card_univ, Fintype.card_fin, sz] at hh
      omega
    have hdisFree (v : V) : Disjoint (((pos (some v)).image Prod.fst).map e.toEmbedding) (Free C v) := by
      refine Finset.disjoint_left.mpr ?_
      simp only [Finset.mem_map, Finset.mem_image]
      rintro _ ⟨j, ⟨s, hs, rfl⟩, rfl⟩
      have hh := pm.mp hs
      intro hfree
      obtain ⟨hl, hr⟩ := (Finset.mem_filter.mp hfree).2
      cases h : s.2
      · exact hl (show wire C p (e s.1) false (some v) from h ▸ hh)
      · exact hr (show wire C p (e s.1) true (some v) from h ▸ hh)
    refine ⟨fun v => ⟨cEq v, ?_⟩, fun v hv => ?_, fun k rs hz ha =>
      bd none k (k_idle C p early sep nout none k rs hz ha)⟩
    · let O := ((pos (some v)).image Prod.fst).map e.toEmbedding
      have hh := Finset.card_le_card (Finset.subset_univ (O ∪ Free C v))
      rw [Finset.card_union_of_disjoint (hdisFree v)] at hh
      simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin, sz] at hh
      have := free_bound C sep v
      rw [cardEq]
      omega
    · rcases hv with hvAB | ⟨rs, hmem, hapart⟩
      · let O := ((pos (some v)).image Prod.fst).map e.toEmbedding
        have hpNotFree : p ∉ Free C v := by
          simp only [Free, Finset.mem_filter, Finset.mem_univ, true_and, not_and_or, not_not]
          exact hvAB
        have hdis : Disjoint O (insert p (Free C v)) := by
          refine Finset.disjoint_insert_right.mpr ⟨?_, hdisFree v⟩
          simp only [O, Finset.mem_map, Finset.mem_image]
          rintro ⟨j, _, hj⟩
          exact de j hj
        have hh := Finset.card_le_card (Finset.subset_univ (O ∪ insert p (Free C v)))
        rw [Finset.card_union_of_disjoint hdis, Finset.card_insert_of_notMem hpNotFree] at hh
        simp only [O, Finset.card_map, Finset.card_univ, Fintype.card_fin, sz] at hh
        have := free_bound C sep v
        rw [cardEq]
        omega
      · have hbd := bd (some v) 2 (k_idle C p early sep nout (some v) 2 rs hmem hapart)
        rw [cardEq]
        omega

theorem lift_slots (C : AndCountCircuit 9) (p : Fin C.size) (early : Early C p)
    (sep : Separates C) (nout : p ∉ C.outGates) (dis : ∀ i, Disjoint (C.leftVars i) (C.rightVars i))
    (sz : C.size = 5) :
    ∃ pos, Cover (C.leftVars p) (C.rightVars p) pos ∧ Cap (C.leftVars p) (C.rightVars p) pos :=
  ⟨circuitPos C p sz, lift_slots_exact C p early sep nout dis sz⟩

def Stable (A B : Finset V) (r : Fin 16) (v : V) : Prop :=
  v ∉ rows r ∧ (fires A B (insert v (rows r)) → fires A B (rows r))

def Conflict (A B : Finset V) (v w : V) : Prop :=
  (∃ r, Stable A B r v ∧ Stable A B r w) ∧
  ((∃ r, Stable A B r v ∧ w ∈ rows r) ∨ (∃ r, Stable A B r w ∧ v ∈ rows r))

def Clique {n : ℕ} (A B : Finset V) (a : Fin n → V) : Prop :=
  (∀ j, Strong A B (a j)) ∧ (∀ j, ∃ r, Stable A B r (a j)) ∧
    ∀ j k, j ≠ k → Conflict A B (a j) (a k)

theorem fromStable {A B : Finset V} {pos : X → Finset Slot} {r : Fin 16}
    {M : Finset Slot} (hit : ∀ u : V, u ∉ rows r → (∃ s ∈ M, s ∈ pos (some u)) ∨
      (¬ fires A B (rows r) ∧ fires A B (insert u (rows r)) ∧ ∃ s ∈ M, s ∈ pos none))
    {v : V} (hh : Stable A B r v) : ∃ s ∈ M, s ∈ pos (some v) :=
  (hit v hh.1).resolve_right fun h => h.1 (hh.2 h.2.1)

theorem clique_places {n : ℕ} {A B : Finset V} {pos : X → Finset Slot} (cv : Cover A B pos)
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
        (¬ fires A B (rows r') ∧ fires A B (insert u (rows r')) ∧ ∃ s ∈ M, s ∈ pos none))
      (hr : Stable A B r' (a i)) : q i ∈ M := by
    simpa [hq] using fromStable hit hr
  obtain ⟨M, con, _, hit⟩ := cv r
  have eqSlot : q j = q k := Prod.ext hgate (con _ (inM hit hrv) _ (inM hit hrw) hgate)
  have contra {j k : Fin n} (eq : q j = q k) (r' : Fin 16)
      (hj : Stable A B r' (a j)) (hk : a k ∈ rows r') : False := by
    obtain ⟨N, _, avo, hh⟩ := cv r'
    have hdis := avo (some (a k)) hk
    exact Finset.disjoint_left.mp hdis (inM hh hj) (by simp [hq, eq])
  rcases hm with ⟨r', hj, hk⟩ | ⟨r', hk, hj⟩
  · exact contra eqSlot r' hj hk
  · exact contra eqSlot.symm r' hk hj

theorem noFiveClique {A B : Finset V} {pos : X → Finset Slot} (cv : Cover A B pos)
    (cap : Cap A B pos) (a : Fin 5 → V) (hc : Clique A B a) : False := by
  obtain ⟨q, _, h⟩ := clique_places cv cap hc
  have ht := Fintype.card_le_of_injective _ h
  simp at ht

def symSlot (σ : Equiv.Perm (Fin 4)) (b : Fin 4 → Bool) (s : Slot) : Slot :=
  (σ s.1, xor s.2 (b s.1))

theorem symSlot_injective (σ : Equiv.Perm (Fin 4)) (b : Fin 4 → Bool) :
    Function.Injective (symSlot σ b) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ eq
  have hij := σ.injective (congrArg Prod.fst eq)
  change i = j at hij
  subst j
  have eq' := congrArg Prod.snd eq
  change xor x (b i) = xor y (b i) at eq'
  cases b i <;> cases x <;> cases y <;> simp_all

theorem symSlot_inv (σ : Equiv.Perm (Fin 4)) (b : Fin 4 → Bool) (s : Slot) :
    symSlot σ.symm (fun j => b (σ.symm j)) (symSlot σ b s) = s := by
  rcases s with ⟨i, x⟩
  simp only [symSlot, Equiv.symm_apply_apply]
  cases b i <;> cases x <;> rfl

theorem symSlot_consistent (σ : Equiv.Perm (Fin 4)) (b : Fin 4 → Bool)
    {S : Finset Slot} (h : Consistent S) : Consistent (S.image (symSlot σ b)) := by
  intro t ht y hy he
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  have hf : x.1 = z.1 := σ.injective he
  exact congrArg (fun s : Slot => (symSlot σ b s).2) (Prod.ext hf (h _ hx _ hz hf))

theorem symSlot_cover (σ : Equiv.Perm (Fin 4)) (b : Fin 4 → Bool)
    {A B : Finset V} {pos : X → Finset Slot} (cv : Cover A B pos) :
    Cover A B (fun z => (pos z).image (symSlot σ b)) := by
  have fi := symSlot_injective σ b
  intro r
  obtain ⟨M, hm, hd, hh⟩ := cv r
  refine ⟨M.image (symSlot σ b), symSlot_consistent σ b hm, ?_, ?_⟩
  · intro z hz
    apply Finset.disjoint_left.mpr
    rintro s hs ht
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp hs
    obtain ⟨y, hy, he'⟩ := Finset.mem_image.mp ht
    exact Finset.disjoint_left.mp (hd z hz) hx (fi (he.trans he'.symm) ▸ hy)
  · intro u hu
    have tr {z} : (∃ s ∈ M, s ∈ pos z) →
        ∃ s ∈ M.image (symSlot σ b), s ∈ (pos z).image (symSlot σ b) := by
      rintro ⟨s, hs, ht⟩
      exact ⟨_, Finset.mem_image_of_mem (symSlot σ b) hs, Finset.mem_image_of_mem (symSlot σ b) ht⟩
    rcases hh u hu with h | ⟨h₁, h₂, h₃⟩
    · exact Or.inl (tr h)
    · exact Or.inr ⟨h₁, h₂, tr h₃⟩

theorem symSlot_cap (σ : Equiv.Perm (Fin 4)) (b : Fin 4 → Bool)
    {A B : Finset V} {pos : X → Finset Slot} (cap : Cap A B pos) :
    Cap A B (fun z => (pos z).image (symSlot σ b)) := by
  have fi := symSlot_injective σ b
  have sz (S : Finset Slot) : (S.image (symSlot σ b)).card = S.card :=
    Finset.card_image_of_injective S fi
  refine ⟨fun v => ⟨symSlot_consistent σ b (cap.1 v).1, (sz _).trans_le (cap.1 v).2⟩,
    fun v h => (sz _).trans_le (cap.2.1 v h), ?_⟩
  intro k rs h₁ h₂
  have eq : ((pos none).image (symSlot σ b)).image Prod.fst = ((pos none).image Prod.fst).image σ := by
    simp [Finset.image_image, symSlot, Function.comp_def]
  rw [eq, Finset.card_image_of_injective _ σ.injective]
  exact cap.2.2 k rs h₁ h₂

theorem normalize_places_sym {n : ℕ} (hn : n ≤ 4) {A B : Finset V} {pos : X → Finset Slot}
    (cv : Cover A B pos) (cap : Cap A B pos) {a : Fin n → V} (hc : Clique A B a) :
    ∃ (σ : Equiv.Perm (Fin 4)) (b : Fin 4 → Bool),
      Cover A B (fun z => (pos z).image (symSlot σ b)) ∧
      Cap A B (fun z => (pos z).image (symSlot σ b)) ∧
      ∀ j, (pos (some (a j))).image (symSlot σ b) = {(Fin.castLE hn j, false)} := by
  classical
  obtain ⟨q, hq, inj⟩ := clique_places cv cap hc
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ (Fin.castLE hn) inj
    (show Function.Injective (Fin.castLE hn) from (Fin.castLEEmb hn).injective)
  let b (k : Fin 4) := decide (∃ j, (q j).1 = k ∧ (q j).2 = true)
  have hbit (j) : b (q j).1 = (q j).2 := by
    cases hh : (q j).2 with
    | true => exact decide_eq_true ⟨j, rfl, hh⟩
    | false =>
      apply decide_eq_false
      rintro ⟨k, hk, ht⟩
      have := inj hk
      subst k
      simp [hh] at ht
  refine ⟨σ, b, symSlot_cover σ b cv, symSlot_cap σ b cap, ?_⟩
  intro j
  simp [hq, symSlot, hσ, hbit]

theorem normalize_places {n : ℕ} (hn : n ≤ 4) {A B : Finset V} {pos : X → Finset Slot}
    (cv : Cover A B pos) (cap : Cap A B pos) {a : Fin n → V} (hc : Clique A B a) :
    ∃ pos' : X → Finset Slot, Cover A B pos' ∧ Cap A B pos' ∧
      ∀ j, pos' (some (a j)) = {(Fin.castLE hn j, false)} := by
  obtain ⟨σ, b, hcv, hcap, hpos⟩ := normalize_places_sym hn cv cap hc
  exact ⟨fun z => (pos z).image (symSlot σ b), hcv, hcap, hpos⟩

def slotId (s : Slot) : ℕ :=
  2 * s.1.val + s.2.toNat

def slots (m : ℕ) : Finset Slot :=
  Finset.univ.filter (fun s => m.testBit (slotId s))

def slotBits (M : Finset Slot) : ℕ :=
  ∑ s ∈ M, 2 ^ slotId s

theorem slotId_inj : Function.Injective slotId := by
  decide +kernel

theorem slotBits_lt (S : Finset Slot) : slotBits S < 256 := by
  have hle : slotBits S ≤ ∑ s : Slot, 2 ^ slotId s :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have htot : (∑ s : Slot, 2 ^ slotId s) = 255 := by decide
  omega

theorem slotBits_testBit (S : Finset Slot) (t : Slot) :
    (slotBits S).testBit (slotId t) = decide (t ∈ S) := by
  induction S using Finset.induction_on generalizing t with
  | empty =>
    simp [slotBits]
  | insert a s ha ih =>
    have hdisj : (2 ^ slotId a &&& slotBits s) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro k
      rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hka : slotId a = k
      · subst hka
        have hfa := ih a
        simp [ha] at hfa
        simp [hfa]
      · simp [hka]
    have hsum : slotBits (insert a s) = 2 ^ slotId a + slotBits s := by
      unfold slotBits
      exact Finset.sum_insert ha
    rw [hsum, nat_add_eq_or _ _ hdisj, Nat.testBit_or, Nat.testBit_two_pow, ih]
    by_cases hat : a = t
    · subst hat
      simp
    · have hne : slotId a ≠ slotId t := fun h => hat (slotId_inj h)
      simp [hne, Ne.symm hat]

theorem slots_slotBits (S : Finset Slot) : slots (slotBits S) = S := by
  ext t
  simp [slots, slotBits_testBit]

theorem slotsSurj (S : Finset Slot) : ∃ m : Fin 256, slots m.val = S :=
  ⟨⟨slotBits S, slotBits_lt S⟩, slots_slotBits S⟩

def fitsMask (m : ℕ) : Bool :=
  (m &&& (m >>> 1) &&& 85) == 0

theorem fitsSpec : ∀ m : Fin 256, Consistent (slots m.val) → fitsMask m.val = true := by
  unfold Consistent
  decide +kernel

def meets (m n : ℕ) : Bool :=
  (m &&& n) != 0

theorem meetSpec (m n : Fin 256) :
    meets m.val n.val = true ↔ ∃ s ∈ slots m.val, s ∈ slots n.val := by
  unfold meets
  simp only [bne_iff_ne, ne_eq]
  constructor
  · intro h
    have ex : ∃ j, (m.val &&& n.val).testBit j = true := by
      by_contra! hn
      apply h
      apply Nat.eq_of_testBit_eq
      simpa using hn
    obtain ⟨j, hj⟩ := ex
    rw [Nat.testBit_and, Bool.and_eq_true] at hj
    have lt : j < 8 := by
      by_contra! he
      have b : m.val < 2 ^ j := lt_of_lt_of_le m.isLt
        (by exact Nat.pow_le_pow_right (by decide) he : 2 ^ 8 ≤ 2 ^ j)
      simp [Nat.testBit_lt_two_pow b] at hj
    have rep : ∀ a : Fin 8, ∃ s : Slot, slotId s = a.val := by decide +kernel
    obtain ⟨s, hs⟩ := rep ⟨j, lt⟩
    exact ⟨s, by simpa [slots, hs] using hj.1, by simpa [slots, hs] using hj.2⟩
  · rintro ⟨s, hs, ht⟩ h
    have h₁ := (Finset.mem_filter.mp hs).2
    have h₂ := (Finset.mem_filter.mp ht).2
    have hx : (m.val &&& n.val).testBit (slotId s) = true := by simp [h₁, h₂]
    simp [h] at hx

abbrev Marks := List (X × Fin 256)

def hot (A B I : Finset V) : Bool :=
  decide (∃ v ∈ A, v ∈ I) && decide (∃ v ∈ B, v ∈ I)

theorem hotSpec {A B I : Finset V} : hot A B I = true ↔ fires A B I := by
  simp [hot, fires]

def admiss (A B : Finset V) (r : Fin 16) (L : Marks) (m : Fin 256) : Bool :=
  fitsMask m.val &&
  let gOK := L.all fun t => t.1.isSome || meets m.val t.2.val
  L.all fun t =>
    let hit := meets m.val t.2.val
    match t.1 with
    | none => !(hot A B (rows r)) || !hit
    | some u => if u ∈ rows r then !hit else
        hit || (!(hot A B (rows r)) && hot A B (insert u (rows r)) && gOK)

def Pass (A B : Finset V) (L : Marks) : Prop :=
  ∀ r : Fin 16, ∃ m : Fin 256, admiss A B r L m = true

theorem pass_marks {A B : Finset V} {pos : X → Finset Slot} (cv : Cover A B pos)
    (L : Marks) (assigned : ∀ t ∈ L, pos t.1 = slots t.2.val) : Pass A B L := by
  intro r
  obtain ⟨M, hm, ha, hp⟩ := cv r
  obtain ⟨m, rfl⟩ := slotsSurj M
  have hh {z : X} {w : Fin 256} (ht : (z, w) ∈ L) :
      meets m.val w.val = true ↔ ∃ s ∈ slots m.val, s ∈ pos z := by
    rw [meetSpec, assigned _ ht]
  refine ⟨m, ?_⟩
  simp only [admiss, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fitsSpec m hm, ?_⟩
  rintro ⟨(_ | u), w⟩ ht
  · simp only [Bool.or_eq_true, Bool.not_eq_true']
    by_cases h : fires A B (rows r)
    · right
      apply Bool.eq_false_iff.mpr
      rintro he
      obtain ⟨s, hs, h'⟩ := (hh ht).mp he
      exact Finset.disjoint_left.mp (ha none h) hs h'
    · exact Or.inl (Bool.eq_false_iff.mpr (fun hv => h (hotSpec.mp hv)))
  · by_cases hu : u ∈ rows r
    · simp only [hu, ↓reduceIte, Bool.not_eq_true']
      apply Bool.eq_false_iff.mpr
      rintro he
      obtain ⟨s, hs, h'⟩ := (hh ht).mp he
      exact Finset.disjoint_left.mp (ha (some u) hu) hs h'
    · simp only [hu, ↓reduceIte, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true]
      rcases hp u hu with he | ⟨h₀, h₁, he⟩
      · exact Or.inl ((hh ht).mpr he)
      · refine Or.inr ⟨⟨Bool.eq_false_iff.mpr (fun ht => h₀ (hotSpec.mp ht)), hotSpec.mpr h₁⟩, ?_⟩
        rintro ⟨(_ | z), w'⟩ hw
        · simpa using (hh hw).mpr he
        · simp

def Autom (f : V → V) : Prop :=
  ∀ v w, related (f v) (f w) = related v w

def automFn : Fin 4 → V → V :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8],
    ![0, 1, 2, 4, 3, 6, 5, 8, 7],
    ![0, 2, 1, 5, 6, 3, 4, 7, 8],
    ![0, 2, 1, 6, 5, 4, 3, 8, 7]]

theorem automFn_inv : ∀ (k : Fin 4) (v : V), automFn k (automFn k v) = v := by
  decide +kernel

def automEquiv (k : Fin 4) : Equiv.Perm V where
  toFun := automFn k
  invFun := automFn k
  left_inv := automFn_inv k
  right_inv := automFn_inv k

theorem automFn_good : ∀ k : Fin 4, Autom (automFn k) := by
  unfold Autom
  decide +kernel

theorem good_image (f : Equiv.Perm V) (ha : Autom f) (I : Finset V) :
    Good (I.image f) ↔ Good I := by
  constructor
  · rintro ⟨hi, hm⟩
    refine ⟨fun v hv w hw => ?_, fun u hu => ?_⟩
    · rw [← ha v w]
      exact hi _ (Finset.mem_image_of_mem f hv) _ (Finset.mem_image_of_mem f hw)
    · obtain ⟨v, hv, hh⟩ := hm (f u) (by simpa using hu)
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      exact ⟨x, hx, (ha u x).symm ▸ hh⟩
  · rintro ⟨hi, hm⟩
    constructor
    · intro v hv w hw
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
      exact (ha x y).trans (hi x hx y hy)
    · intro u hu
      obtain ⟨z, rfl⟩ := f.surjective u
      obtain ⟨x, hx, hr⟩ := hm z (by simpa using hu)
      exact ⟨f x, Finset.mem_image_of_mem f hx, (ha z x).trans hr⟩

def rename (C : AndCountCircuit 9) (f : Equiv.Perm V) (sw : Bool) : AndCountCircuit 9 where
  size := C.size
  leftVars i := (vars C i sw).image f
  rightVars i := (vars C i (!sw)).image f
  leftGates i := if sw then C.rightGates i else C.leftGates i
  rightGates i := if sw then C.leftGates i else C.rightGates i
  outVars := C.outVars.image f
  outGates := C.outGates

theorem renameGate (C : AndCountCircuit 9) (f : Equiv.Perm V) (sw : Bool) (I : Finset V)
    (i : Fin C.size) : (rename C f sw).gateVal (I.image f) i = C.gateVal I i := by
  have hs (B : Finset V) (F : Finset (Fin C.size)) (j : Fin C.size) (v : Fin C.size → Bool) :
      sideTrue (I.image f) (B.image f) F j v = sideTrue I B F j v := by
    simp [sideTrue]
  have hf (d : ℕ) (j : Fin C.size) :
      (rename C f sw).gateValFuel (I.image f) d j = C.gateValFuel I d j := by
    induction d generalizing j with
    | zero => rfl
    | succ d ih =>
      have he : (rename C f sw).gateValFuel (I.image f) d = C.gateValFuel I d := funext ih
      simp only [gateValFuel, he]
      cases sw <;> simp only [rename, vars, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, ↓reduceIte, hs, Bool.and_comm]
  exact hf _ i

theorem renameEval (C : AndCountCircuit 9) (f : Equiv.Perm V) (sw : Bool) (I : Finset V) :
    (rename C f sw).eval (I.image f) = C.eval I := by
  unfold eval
  apply decide_eq_decide.mpr
  change ((∃ v ∈ C.outVars.image f, v ∈ I.image f) ∨
    ∃ i ∈ C.outGates, (rename C f sw).gateVal (I.image f) i = true) ↔ _
  simp [renameGate]

def Bad (A B : Finset V) : Prop :=
  ∃ (C : AndCountCircuit 9) (p : Fin C.size),
    C.leftVars p = A ∧ C.rightVars p = B ∧ C.size = 5 ∧ Separates C ∧ Early C p ∧
    (∃ r : Fin 16, C.gateVal (rows r) p = true) ∧ ∀ i, Disjoint (C.leftVars i) (C.rightVars i)

theorem bad_rename {A B : Finset V} (h : Bad A B) (f : Equiv.Perm V) (hf : Autom f) (sw : Bool) :
    Bad ((if sw then B else A).image f) ((if sw then A else B).image f) := by
  obtain ⟨C, p, hA, hB, sz, sp, er, ⟨r, hr⟩, dis⟩ := h
  have pre (I : Finset V) : (I.image f.symm).image f = I := by simp [Finset.image_image]
  have gp (I : Finset V) (hi : Good I) : Good (I.image f.symm) := by
    apply (good_image f hf _).mp
    rwa [pre]
  refine ⟨rename C f sw, p, ?_, ?_, sz, ?_, ?_, ?_, ?_⟩
  · cases sw <;> simp [rename, vars, hA, hB]
  · cases sw <;> simp [rename, vars, hA, hB]
  · intro I hi
    have hh := sp _ (gp I hi)
    constructor
    · simpa [pre] using (renameEval C f sw (I.image f.symm)).trans hh.1
    · intro u hu
      have hm : f.symm u ∉ I.image f.symm := by simpa using hu
      simpa [pre] using (renameEval C f sw (insert (f.symm u) (I.image f.symm))).trans (hh.2 _ hm)
  · intro j hj k
    obtain ⟨t, ht⟩ := allRows _ (gp _ (rowsGood k))
    have eq := renameGate C f sw (rows t) j
    rw [← ht, pre] at eq
    exact eq.trans (ht ▸ er j hj t)
  · obtain ⟨t, ht⟩ := allRows _ ((good_image f hf _).mpr (rowsGood r))
    refine ⟨t, ?_⟩
    rw [← ht, renameGate]
    exact hr
  · intro i
    have tr {L R : Finset V} (h : Disjoint L R) : Disjoint (L.image f) (R.image f) := by
      apply Finset.disjoint_left.mpr
      intro z hz hzr
      rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
      exact Finset.disjoint_left.mp h hx (by simpa using hzr)
    cases sw
    · exact tr (dis i)
    · exact tr (dis i).symm

theorem bad_nout (C : AndCountCircuit 9) (p : Fin C.size) (sp : Separates C)
    (hr : ∃ r : Fin 16, C.gateVal (rows r) p = true) : p ∉ C.outGates := by
  obtain ⟨r, hr⟩ := hr
  intro hp
  have ht : C.eval (rows r) = true := decide_eq_true (Or.inr ⟨p, hp, hr⟩)
  simp [(sp _ (rowsGood r)).1] at ht

theorem bad_frame {A B : Finset V} (h : Bad A B) :
    (∃ r : Fin 16, fires A B (rows r)) ∧ Disjoint A B ∧ ∃ pos, Cover A B pos ∧ Cap A B pos := by
  obtain ⟨C, p, rfl, rfl, sz, sp, er, ⟨r, hr⟩, dis⟩ := h
  have no := bad_nout C p sp ⟨r, hr⟩
  exact ⟨⟨r, (earliest_raw C p er r).mp hr⟩, dis p, lift_slots C p er sp no dis sz⟩

theorem lower_of_noBad (hno : ∀ A B : Finset V, ¬ Bad A B) (C : AndCountCircuit 9)
    (sep : Separates C) : 6 ≤ C.size := by
  classical
  by_contra! hlt
  let D := stripCircuit C
  have hd : Separates D := by
    intro I hI
    simpa only [D, strip_eval_eq] using sep I hI
  have hsz : D.size = C.size := rfl
  have sz : D.size = 5 := le_antisymm (by omega) (atLeastFive D hd)
  let U := Finset.univ.filter (fun i : Fin D.size => ∃ r : Fin 16, D.gateVal (rows r) i = true)
  have ne : U.Nonempty := by
    by_contra hn
    have allSafe (i) (r) : D.gateVal (rows r) i = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, ht⟩⟩
    have := safe_bound D hd allSafe
    omega
  let p := U.min' ne
  have hp : p ∈ U := U.min'_mem ne
  have er : Early D p := by
    intro j hj r
    apply Bool.eq_false_iff.mpr
    intro ht
    exact (not_le_of_gt hj) (U.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, r, ht⟩))
  exact hno _ _ ⟨D, p, rfl, rfl, sz, hd, er, (Finset.mem_filter.mp hp).2, strip_disjoint C⟩


def pow2 (k : ℕ) : ℕ :=
  match k with
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 16
  | 5 => 32
  | 6 => 64
  | 7 => 128
  | 8 => 256
  | 9 => 512
  | 10 => 1024
  | 11 => 2048
  | 12 => 4096
  | 13 => 8192
  | 14 => 16384
  | _ => 32768

theorem pow2_eq (k : ℕ) (hk : k < 16) : pow2 k = 2 ^ k := by
  interval_cases k <;> rfl

def bitOn (m k : ℕ) : Bool :=
  (m / pow2 k) % 2 == 1

theorem bitOn_eq_testBit (m k : ℕ) (hk : k < 16) : bitOn m k = m.testBit k := by
  unfold bitOn
  rw [pow2_eq k hk, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
  cases h : (m / 2 ^ k) % 2 with
  | zero => rfl
  | succ n =>
    have hlt : (m / 2 ^ k) % 2 < 2 := Nat.mod_lt _ (by decide)
    have hn : n = 0 := by omega
    subst hn
    rfl

theorem shiftAnd1_ne_zero (m k : ℕ) : (((m >>> k) &&& 1) != 0) = m.testBit k := by
  rw [Nat.testBit, Nat.and_comm]

theorem shiftAnd1_eq_zero (m k : ℕ) : (((m >>> k) &&& 1) == 0) = !m.testBit k := by
  rw [← shiftAnd1_ne_zero m k]
  simp [bne]

def rowAt (r : ℕ) : ℕ :=
  match r with
  | 0 => 25
  | 1 => 28
  | 2 => 49
  | 3 => 73
  | 4 => 97
  | 5 => 98
  | 6 => 134
  | 7 => 145
  | 8 => 148
  | 9 => 193
  | 10 => 194
  | 11 => 262
  | 12 => 265
  | 13 => 268
  | 14 => 289
  | _ => 290

theorem rowAt_eq_rowMasks : ∀ r : Fin 16, rowAt r.val = rowMasks r := by
  decide +kernel

theorem decode_rowAt : ∀ r : Fin 16, decode (rowAt r.val) = rows r := by
  intro r
  rw [rowAt_eq_rowMasks r, decode_rowMasks r]

theorem rowAt_lt : ∀ r : Fin 16, rowAt r.val < 512 := by
  decide +kernel

def firesB (a b u : ℕ) : Bool :=
  (a &&& u) != 0 && (b &&& u) != 0

theorem and_ne_zero_iff (x y : ℕ) (hx : x < 512) :
    ((x &&& y) != 0) = true ↔ ∃ v ∈ decode x, v ∈ decode y := by
  simp only [bne_iff_ne, ne_eq]
  constructor
  · intro h
    have ex : ∃ j, (x &&& y).testBit j = true := by
      by_contra! hn
      apply h
      apply Nat.eq_of_testBit_eq
      simpa using hn
    obtain ⟨j, hj⟩ := ex
    rw [Nat.testBit_and, Bool.and_eq_true] at hj
    have hlt : j < 9 := by
      by_contra! hge
      have hb : x < 2 ^ j := lt_of_lt_of_le hx
        (by exact Nat.pow_le_pow_right (by decide) hge : 2 ^ 9 ≤ 2 ^ j)
      simp [Nat.testBit_lt_two_pow hb] at hj
    exact ⟨⟨j, hlt⟩, (mem_decode x ⟨j, hlt⟩).mpr hj.1, (mem_decode y ⟨j, hlt⟩).mpr hj.2⟩
  · rintro ⟨v, hvx, hvy⟩ h0
    have h1 := (mem_decode x v).mp hvx
    have h2 := (mem_decode y v).mp hvy
    have hx' : (x &&& y).testBit v.val = true := by simp [h1, h2]
    simp [h0] at hx'

theorem firesB_iff (a b u : ℕ) (ha : a < 512) (hb : b < 512) :
    firesB a b u = true ↔ fires (decode a) (decode b) (decode u) := by
  unfold firesB fires
  rw [Bool.and_eq_true, and_ne_zero_iff a u ha, and_ne_zero_iff b u hb]

theorem decode_or_bit (m : ℕ) (v : V) :
    decode (m ||| (1 <<< v.val)) = insert v (decode m) := by
  ext x
  rw [mem_decode, Finset.mem_insert, mem_decode, Nat.testBit_or, Bool.or_eq_true]
  have h1 : (1 <<< v.val).testBit x.val = true ↔ x = v := by
    rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow, decide_eq_true_eq]
    exact ⟨fun h => Fin.ext h.symm, fun h => by subst h; rfl⟩
  rw [h1, or_comm]

def hotMask (a b : ℕ) : ℕ :=
  let rec go (r acc : ℕ) : ℕ :=
    match r with
    | 0 => acc
    | r' + 1 => go r' (if firesB a b (rowAt r') then acc ||| (1 <<< r') else acc)
  go 16 0

theorem hotMask_go_testBit (a b : ℕ) :
    ∀ (r acc k : ℕ),
      (hotMask.go a b r acc).testBit k =
        (acc.testBit k || (decide (k < r) && firesB a b (rowAt k))) := by
  intro r
  induction r with
  | zero =>
    intro acc k
    simp [hotMask.go]
  | succ r' ih =>
    intro acc k
    unfold hotMask.go
    rw [ih]
    by_cases hkr : k = r'
    · subst hkr
      have h1 : ¬ (k < k) := Nat.lt_irrefl k
      have h2 : k < k + 1 := Nat.lt_succ_self k
      simp only [h1, h2, decide_false, decide_true, Bool.false_and, Bool.or_false, Bool.true_and]
      cases hf : firesB a b (rowAt k) with
      | false => simp
      | true =>
        simp [Nat.testBit_or, Nat.shiftLeft_eq]
    · have hlt : decide (k < r') = decide (k < r' + 1) := by
        apply decide_eq_decide.mpr
        omega
      rw [hlt]
      cases hf : firesB a b (rowAt r') with
      | false => simp
      | true =>
        simp [Nat.testBit_or, Nat.shiftLeft_eq, Ne.symm hkr]

theorem testBit_hotMask (a b : ℕ) (r : Fin 16) :
    (hotMask a b).testBit r.val = firesB a b (rowAt r.val) := by
  unfold hotMask
  rw [hotMask_go_testBit]
  simp [r.isLt]

theorem bitOn_hotMask (a b : ℕ) (r : Fin 16) :
    bitOn (hotMask a b) r.val = firesB a b (rowAt r.val) := by
  rw [bitOn_eq_testBit _ _ r.isLt, testBit_hotMask]

theorem hotMask_testBit_ge (a b k : ℕ) (hk : 16 ≤ k) :
    (hotMask a b).testBit k = false := by
  unfold hotMask
  rw [hotMask_go_testBit]
  have hlt : ¬ (k < 16) := by omega
  simp [hlt]

theorem hotMask_ne_zero_iff (a b : ℕ) :
    hotMask a b ≠ 0 ↔ ∃ r : Fin 16, firesB a b (rowAt r.val) = true := by
  constructor
  · intro hne
    have ex : ∃ k, (hotMask a b).testBit k = true := by
      by_contra! hn
      apply hne
      apply Nat.eq_of_testBit_eq
      simpa using hn
    obtain ⟨k, hk⟩ := ex
    have hlt : k < 16 := by
      by_contra! hge
      rw [hotMask_testBit_ge a b k hge] at hk
      exact Bool.false_ne_true hk
    exact ⟨⟨k, hlt⟩, by rwa [← testBit_hotMask a b ⟨k, hlt⟩]⟩
  · rintro ⟨r, hr⟩ h0
    have ht := testBit_hotMask a b r
    rw [h0, Nat.zero_testBit] at ht
    rw [hr] at ht
    exact Bool.false_ne_true ht

def perm1 (m : ℕ) : ℕ :=
  (m &&& 7) |||
  (((m >>> 3) &&& 1) <<< 4) ||| (((m >>> 4) &&& 1) <<< 3) |||
  (((m >>> 5) &&& 1) <<< 6) ||| (((m >>> 6) &&& 1) <<< 5) |||
  (((m >>> 7) &&& 1) <<< 8) ||| (((m >>> 8) &&& 1) <<< 7)

def perm2 (m : ℕ) : ℕ :=
  (m &&& 1) |||
  (((m >>> 1) &&& 1) <<< 2) ||| (((m >>> 2) &&& 1) <<< 1) |||
  (((m >>> 3) &&& 1) <<< 5) ||| (((m >>> 5) &&& 1) <<< 3) |||
  (((m >>> 4) &&& 1) <<< 6) ||| (((m >>> 6) &&& 1) <<< 4) |||
  (m &&& 384)

def perm3 (m : ℕ) : ℕ :=
  perm1 (perm2 m)

def permAt (k : Fin 4) (m : ℕ) : ℕ :=
  match k.val with
  | 0 => m
  | 1 => perm1 m
  | 2 => perm2 m
  | _ => perm3 m

theorem perm1_lt : ∀ m : Fin 512, perm1 m.val < 512 := by
  decide +kernel

theorem perm2_lt : ∀ m : Fin 512, perm2 m.val < 512 := by
  decide +kernel

theorem perm3_lt : ∀ m : Fin 512, perm3 m.val < 512 := by
  decide +kernel

theorem permAt_lt (k : Fin 4) (m : Fin 512) : permAt k m.val < 512 := by
  fin_cases k
  · exact m.isLt
  · exact perm1_lt m
  · exact perm2_lt m
  · exact perm3_lt m

theorem perm1_testBit : ∀ (m : Fin 512) (v : V),
    (perm1 m.val).testBit (automFn 1 v).val = m.val.testBit v.val := by
  decide +kernel

theorem perm2_testBit : ∀ (m : Fin 512) (v : V),
    (perm2 m.val).testBit (automFn 2 v).val = m.val.testBit v.val := by
  decide +kernel

theorem perm3_testBit : ∀ (m : Fin 512) (v : V),
    (perm3 m.val).testBit (automFn 3 v).val = m.val.testBit v.val := by
  decide +kernel

theorem perm0_testBit : ∀ (m : Fin 512) (v : V),
    m.val.testBit (automFn 0 v).val = m.val.testBit v.val := by
  decide +kernel

theorem decode_permAt (k : Fin 4) (m : Fin 512) :
    decode (permAt k m.val) = (decode m.val).image (automEquiv k) := by
  ext w
  obtain ⟨v, rfl⟩ := (automEquiv k).surjective w
  rw [mem_decode, Finset.mem_image]
  constructor
  · intro h
    refine ⟨v, (mem_decode m.val v).mpr ?_, rfl⟩
    fin_cases k
    · exact (perm0_testBit m v).symm.trans h
    · exact (perm1_testBit m v).symm.trans h
    · exact (perm2_testBit m v).symm.trans h
    · exact (perm3_testBit m v).symm.trans h
  · rintro ⟨x, hx, hxv⟩
    have hEq : x = v := (automEquiv k).injective hxv
    subst hEq
    have hmem := (mem_decode m.val x).mp hx
    fin_cases k
    · exact (perm0_testBit m x).trans hmem
    · exact (perm1_testBit m x).trans hmem
    · exact (perm2_testBit m x).trans hmem
    · exact (perm3_testBit m x).trans hmem

def isCanonB (a b : ℕ) : Bool :=
  let key := (a <<< 9) ||| b
  let ok (x y : ℕ) := key <= ((x <<< 9) ||| y) && key <= ((y <<< 9) ||| x)
  ok a b && ok (perm1 a) (perm1 b) && ok (perm2 a) (perm2 b) && ok (perm3 a) (perm3 b)

theorem shift9_or_eq_mul_add (a b : ℕ) (hb : b < 512) :
    ((a <<< 9) ||| b) = a * 512 + b := by
  have hdisj : ((a <<< 9) &&& b) = 0 := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.zero_testBit]
    by_cases hk : k < 9
    · simp [Nat.testBit_shiftLeft, hk]
    · have hb' : b < 2 ^ k := lt_of_lt_of_le hb
        (by exact Nat.pow_le_pow_right (by decide) (by omega) : 2 ^ 9 ≤ 2 ^ k)
      simp [Nat.testBit_lt_two_pow hb']
  have hsh : a <<< 9 = a * 512 := Nat.shiftLeft_eq a 9
  rw [← nat_add_eq_or _ _ hdisj, hsh]

theorem canonical {A B : Finset V} (h : Bad A B) :
    ∃ a b : Fin 512,
      Bad (decode a.val) (decode b.val) ∧
      a.val ≠ 0 ∧ b.val ≠ 0 ∧
      (a.val &&& b.val) = 0 ∧
      hotMask a.val b.val ≠ 0 ∧
      isCanonB a.val b.val = true := by
  classical
  have hex : ∃ n : ℕ, ∃ a b : Fin 512, ((a.val <<< 9) ||| b.val) = n ∧
      Bad (decode a.val) (decode b.val) := by
    obtain ⟨a0, ha0⟩ := decodeSurj A
    obtain ⟨b0, hb0⟩ := decodeSurj B
    exact ⟨(a0.val <<< 9) ||| b0.val, a0, b0, rfl, by rwa [ha0, hb0]⟩
  let n0 := Nat.find hex
  obtain ⟨a, b, hkey, hBad⟩ := Nat.find_spec hex
  obtain ⟨⟨r, hfir⟩, hdisj, _⟩ := bad_frame hBad
  have ha0 : a.val ≠ 0 := by
    intro h0
    obtain ⟨v, hv, _⟩ := hfir.1
    rw [h0, mem_decode, Nat.zero_testBit] at hv
    exact Bool.false_ne_true hv
  have hb0 : b.val ≠ 0 := by
    intro h0
    obtain ⟨v, hv, _⟩ := hfir.2
    rw [h0, mem_decode, Nat.zero_testBit] at hv
    exact Bool.false_ne_true hv
  have hab0 : (a.val &&& b.val) = 0 := by
    by_contra hne'
    have ht : ((a.val &&& b.val) != 0) = true := bne_iff_ne.mpr hne'
    obtain ⟨v, hva, hvb⟩ := (and_ne_zero_iff a.val b.val a.isLt).mp ht
    exact Finset.disjoint_left.mp hdisj hva hvb
  have hhot : hotMask a.val b.val ≠ 0 := by
    apply (hotMask_ne_zero_iff a.val b.val).mpr
    refine ⟨r, (firesB_iff a.val b.val (rowAt r.val) a.isLt b.isLt).mpr ?_⟩
    rwa [decode_rowAt r]
  have hle (k : Fin 4) (sw : Bool) :
      ((a.val <<< 9) ||| b.val) ≤
        (((if sw then permAt k b.val else permAt k a.val) <<< 9) |||
          (if sw then permAt k a.val else permAt k b.val)) := by
    rw [hkey]
    apply Nat.find_min' hex
    have hren := bad_rename hBad (automEquiv k) (automFn_good k) sw
    cases sw
    · refine ⟨⟨permAt k a.val, permAt_lt k a⟩, ⟨permAt k b.val, permAt_lt k b⟩, rfl, ?_⟩
      simpa [decode_permAt] using hren
    · refine ⟨⟨permAt k b.val, permAt_lt k b⟩, ⟨permAt k a.val, permAt_lt k a⟩, rfl, ?_⟩
      simpa [decode_permAt] using hren
  have hcanon : isCanonB a.val b.val = true := by
    unfold isCanonB
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨hle 0 false, hle 0 true⟩, ⟨hle 1 false, hle 1 true⟩⟩,
      ⟨hle 2 false, hle 2 true⟩⟩, ⟨hle 3 false, hle 3 true⟩⟩
  exact ⟨a, b, hBad, ha0, hb0, hab0, hhot, hcanon⟩

def decodeTritA (t : ℕ) : ℕ :=
  let rec go (k cur acc bit : ℕ) : ℕ :=
    match k with
    | 0 => acc
    | k' + 1 => go k' (cur / 3) (if cur % 3 == 1 then acc ||| bit else acc) (bit <<< 1)
  go 9 t 0 1

def decodeTritB (t : ℕ) : ℕ :=
  let rec go (k cur acc bit : ℕ) : ℕ :=
    match k with
    | 0 => acc
    | k' + 1 => go k' (cur / 3) (if cur % 3 == 2 then acc ||| bit else acc) (bit <<< 1)
  go 9 t 0 1

def tritSum : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, a, b =>
    (if a % 2 == 1 then 1 else if b % 2 == 1 then 2 else 0) + 3 * tritSum k (a / 2) (b / 2)

def tritCodeB (a b : ℕ) : ℕ :=
  let rec go (k aCur bCur acc p3 : ℕ) : ℕ :=
    match k with
    | 0 => acc
    | k' + 1 =>
      let d := if aCur % 2 == 1 then 1 else if bCur % 2 == 1 then 2 else 0
      go k' (aCur / 2) (bCur / 2) (acc + d * p3) (p3 * 3)
  go 9 a b 0 1

theorem tritCodeB_go_eq : ∀ (k a b acc p3 : ℕ),
    tritCodeB.go k a b acc p3 = acc + p3 * tritSum k a b := by
  intro k
  induction k with
  | zero =>
    intro a b acc p3
    simp [tritCodeB.go, tritSum]
  | succ k ih =>
    intro a b acc p3
    unfold tritCodeB.go tritSum
    rw [ih]
    ring

theorem tritSum_lt : ∀ (k a b : ℕ), tritSum k a b < 3 ^ k := by
  intro k
  induction k with
  | zero =>
    intro a b
    simp [tritSum]
  | succ k ih =>
    intro a b
    unfold tritSum
    have hlt := ih (a / 2) (b / 2)
    have hd : (if a % 2 == 1 then 1 else if b % 2 == 1 then 2 else 0) ≤ 2 := by
      split
      · omega
      · split <;> omega
    have hpow : 3 ^ (k + 1) = 3 * 3 ^ k := by ring
    omega

theorem decodeTritA_go_lt : ∀ (k cur acc s : ℕ),
    acc < 2 ^ s → decodeTritA.go k cur acc (2 ^ s) < 2 ^ (s + k) := by
  intro k
  induction k with
  | zero =>
    intro cur acc s hacc
    simpa [decodeTritA.go] using hacc
  | succ k ih =>
    intro cur acc s hacc
    unfold decodeTritA.go
    have hsh : (2 ^ s) <<< 1 = 2 ^ (s + 1) := by
      rw [Nat.shiftLeft_eq]
      ring
    have hacc' : (if cur % 3 == 1 then acc ||| 2 ^ s else acc) < 2 ^ (s + 1) := by
      have hpow : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by ring
      split
      · have hdisj : (acc &&& 2 ^ s) = 0 := by
          apply Nat.eq_of_testBit_eq
          intro j
          rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
          by_cases hjs : s = j
          · subst hjs
            simp [Nat.testBit_lt_two_pow hacc]
          · simp [hjs]
        rw [← nat_add_eq_or _ _ hdisj]
        omega
      · omega
    rw [hsh]
    have hres := ih (cur / 3) (if cur % 3 == 1 then acc ||| 2 ^ s else acc) (s + 1) hacc'
    have hexp : s + 1 + k = s + (k + 1) := by omega
    rwa [hexp] at hres

theorem decodeTritB_go_lt : ∀ (k cur acc s : ℕ),
    acc < 2 ^ s → decodeTritB.go k cur acc (2 ^ s) < 2 ^ (s + k) := by
  intro k
  induction k with
  | zero =>
    intro cur acc s hacc
    simpa [decodeTritB.go] using hacc
  | succ k ih =>
    intro cur acc s hacc
    unfold decodeTritB.go
    have hsh : (2 ^ s) <<< 1 = 2 ^ (s + 1) := by
      rw [Nat.shiftLeft_eq]
      ring
    have hacc' : (if cur % 3 == 2 then acc ||| 2 ^ s else acc) < 2 ^ (s + 1) := by
      have hpow : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by ring
      split
      · have hdisj : (acc &&& 2 ^ s) = 0 := by
          apply Nat.eq_of_testBit_eq
          intro j
          rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
          by_cases hjs : s = j
          · subst hjs
            simp [Nat.testBit_lt_two_pow hacc]
          · simp [hjs]
        rw [← nat_add_eq_or _ _ hdisj]
        omega
      · omega
    rw [hsh]
    have hres := ih (cur / 3) (if cur % 3 == 2 then acc ||| 2 ^ s else acc) (s + 1) hacc'
    have hexp : s + 1 + k = s + (k + 1) := by omega
    rwa [hexp] at hres

theorem decodeTritA_lt (t : ℕ) : decodeTritA t < 512 := by
  have h := decodeTritA_go_lt 9 t 0 0 (by decide)
  simpa [decodeTritA] using h

theorem decodeTritB_lt (t : ℕ) : decodeTritB t < 512 := by
  have h := decodeTritB_go_lt 9 t 0 0 (by decide)
  simpa [decodeTritB] using h

theorem and_div_two_eq_zero {a b : ℕ} (h : (a &&& b) = 0) : (a / 2 &&& b / 2) = 0 := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_and, Nat.testBit_div_two, Nat.testBit_div_two, Nat.zero_testBit]
  have hk := congrArg (fun n => n.testBit (k + 1)) h
  simpa [Nat.testBit_and] using hk

theorem and_eq_zero_mod_two {a b : ℕ} (h : (a &&& b) = 0) : a % 2 = 0 ∨ b % 2 = 0 := by
  have hk : (a &&& b).testBit 0 = false := by
    rw [h]
    rfl
  rw [Nat.testBit_and, Nat.testBit_zero, Nat.testBit_zero, Bool.and_eq_false_iff] at hk
  simp only [decide_eq_false_iff_not] at hk
  omega

theorem or_shiftLeft_step (acc a s : ℕ) (hacc : acc < 2 ^ s) :
    (if a % 2 == 1 then acc ||| 2 ^ s else acc) ||| ((a / 2) <<< (s + 1)) = acc ||| (a <<< s) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft]
  by_cases hlt : j < s
  · have h1 : ¬ (s ≤ j) := by omega
    have h2 : ¬ (s + 1 ≤ j) := by omega
    have hne : s ≠ j := by omega
    split <;> simp [h1, h2, Nat.testBit_or, hne]
  · by_cases heq : j = s
    · subst heq
      have h1 : ¬ (j + 1 ≤ j) := by omega
      have haccj : acc.testBit j = false := Nat.testBit_lt_two_pow hacc
      have ha0 : a.testBit 0 = (a % 2 == 1) := by
        rw [Nat.testBit_zero]
        cases h : a % 2 with
        | zero => rfl
        | succ n =>
          have hmod : a % 2 < 2 := Nat.mod_lt _ (by decide)
          have hn : n = 0 := by omega
          subst hn
          rfl
      simp only [h1, decide_false, Bool.false_and, Bool.or_false, Nat.le_refl, decide_true,
        Nat.sub_self, Bool.true_and, haccj, Bool.false_or, ha0]
      cases hmod : (a % 2 == 1) <;> simp [Nat.testBit_or, haccj]
    · have hge : s + 1 ≤ j := by omega
      have hge' : s ≤ j := by omega
      have haccj : acc.testBit j = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hacc (Nat.pow_le_pow_right (by decide) hge'))
      have hsub : j - s = (j - (s + 1)) + 1 := by omega
      have hne : s ≠ j := by omega
      have hdiv : (a / 2).testBit (j - (s + 1)) = a.testBit (j - s) := by
        rw [hsub, Nat.testBit_div_two]
      simp only [hge, hge', decide_true, Bool.true_and, haccj, Bool.false_or, hdiv]
      split <;> simp [Nat.testBit_or, haccj, hne]

theorem decodeTritA_go_tritSum : ∀ (k a b acc s : ℕ),
    (a &&& b) = 0 → a < 2 ^ k → b < 2 ^ k → acc < 2 ^ s →
    decodeTritA.go k (tritSum k a b) acc (2 ^ s) = acc ||| (a <<< s) := by
  intro k
  induction k with
  | zero =>
    intro a b acc s _ ha _ _
    have ha0 : a = 0 := by omega
    subst ha0
    simp [decodeTritA.go]
  | succ k ih =>
    intro a b acc s hab ha hb hacc
    unfold decodeTritA.go tritSum
    set d := if a % 2 == 1 then 1 else if b % 2 == 1 then 2 else 0
    have hdlt : d < 3 := by
      dsimp only [d]
      split
      · omega
      · split <;> omega
    have hmod3 : (d + 3 * tritSum k (a / 2) (b / 2)) % 3 = d := by omega
    have hdiv3 : (d + 3 * tritSum k (a / 2) (b / 2)) / 3 = tritSum k (a / 2) (b / 2) := by omega
    rw [hmod3, hdiv3]
    have hdisj0 := and_eq_zero_mod_two hab
    have hd1 : (d == 1) = (a % 2 == 1) := by
      dsimp only [d]
      cases h1 : (a % 2 == 1) with
      | true => rfl
      | false =>
        cases h2 : (b % 2 == 1) <;> rfl
    rw [hd1]
    have hsh : (2 ^ s) <<< 1 = 2 ^ (s + 1) := by
      rw [Nat.shiftLeft_eq]
      ring
    rw [hsh]
    have hacc' : (if a % 2 == 1 then acc ||| 2 ^ s else acc) < 2 ^ (s + 1) := by
      have hpow : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by ring
      split
      · have hdisj : (acc &&& 2 ^ s) = 0 := by
          apply Nat.eq_of_testBit_eq
          intro j
          rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
          by_cases hjs : s = j
          · subst hjs
            simp [Nat.testBit_lt_two_pow hacc]
          · simp [hjs]
        rw [← nat_add_eq_or _ _ hdisj]
        omega
      · omega
    have ha' : a / 2 < 2 ^ k := by
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
    have hb' : b / 2 < 2 ^ k := by
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
    rw [ih (a / 2) (b / 2) _ (s + 1) (and_div_two_eq_zero hab) ha' hb' hacc']
    exact or_shiftLeft_step acc a s hacc

theorem decodeTritB_go_tritSum : ∀ (k a b acc s : ℕ),
    (a &&& b) = 0 → a < 2 ^ k → b < 2 ^ k → acc < 2 ^ s →
    decodeTritB.go k (tritSum k a b) acc (2 ^ s) = acc ||| (b <<< s) := by
  intro k
  induction k with
  | zero =>
    intro a b acc s _ _ hb _
    have hb0 : b = 0 := by omega
    subst hb0
    simp [decodeTritB.go]
  | succ k ih =>
    intro a b acc s hab ha hb hacc
    unfold decodeTritB.go tritSum
    set d := if a % 2 == 1 then 1 else if b % 2 == 1 then 2 else 0
    have hdlt : d < 3 := by
      dsimp only [d]
      split
      · omega
      · split <;> omega
    have hmod3 : (d + 3 * tritSum k (a / 2) (b / 2)) % 3 = d := by omega
    have hdiv3 : (d + 3 * tritSum k (a / 2) (b / 2)) / 3 = tritSum k (a / 2) (b / 2) := by omega
    rw [hmod3, hdiv3]
    have hdisj0 := and_eq_zero_mod_two hab
    have hd2 : (d == 2) = (b % 2 == 1) := by
      dsimp only [d]
      rcases hdisj0 with h0 | h0
      · have ha0 : (a % 2 == 1) = false := by simp [h0]
        rw [ha0]
        cases h2 : (b % 2 == 1) <;> rfl
      · have hb0 : (b % 2 == 1) = false := by simp [h0]
        rw [hb0]
        cases h1 : (a % 2 == 1) <;> rfl
    rw [hd2]
    have hsh : (2 ^ s) <<< 1 = 2 ^ (s + 1) := by
      rw [Nat.shiftLeft_eq]
      ring
    rw [hsh]
    have hacc' : (if b % 2 == 1 then acc ||| 2 ^ s else acc) < 2 ^ (s + 1) := by
      have hpow : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by ring
      split
      · have hdisj : (acc &&& 2 ^ s) = 0 := by
          apply Nat.eq_of_testBit_eq
          intro j
          rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
          by_cases hjs : s = j
          · subst hjs
            simp [Nat.testBit_lt_two_pow hacc]
          · simp [hjs]
        rw [← nat_add_eq_or _ _ hdisj]
        omega
      · omega
    have ha' : a / 2 < 2 ^ k := by
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
    have hb' : b / 2 < 2 ^ k := by
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
    rw [ih (a / 2) (b / 2) _ (s + 1) (and_div_two_eq_zero hab) ha' hb' hacc']
    exact or_shiftLeft_step acc b s hacc

theorem tritCode_spec : ∀ a b : Fin 512, (a.val &&& b.val) = 0 →
    tritCodeB a.val b.val < 19683 ∧
    decodeTritA (tritCodeB a.val b.val) = a.val ∧
    decodeTritB (tritCodeB a.val b.val) = b.val := by
  intro a b hab
  have hcode : tritCodeB a.val b.val = tritSum 9 a.val b.val := by
    unfold tritCodeB
    rw [tritCodeB_go_eq]
    ring
  rw [hcode]
  refine ⟨?_, ?_, ?_⟩
  · have h := tritSum_lt 9 a.val b.val
    omega
  · have h := decodeTritA_go_tritSum 9 a.val b.val 0 0 hab a.isLt b.isLt (by decide)
    simpa [decodeTritA] using h
  · have h := decodeTritB_go_tritSum 9 a.val b.val 0 0 hab a.isLt b.isLt (by decide)
    simpa [decodeTritB] using h

def thrRow (v k : ℕ) : ℕ :=
  match v with
  | 1 => match k with | 0 => 5 | 1 => 6 | 2 => 10 | 3 => 11 | _ => 15
  | 2 => match k with | 0 => 1 | 1 => 6 | 2 => 8 | 3 => 11 | _ => 13
  | 3 => match k with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 12 | _ => 13
  | 4 => match k with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 7 | _ => 8
  | 5 => match k with | 0 => 2 | 1 => 4 | 2 => 5 | 3 => 14 | _ => 15
  | 6 => match k with | 0 => 3 | 1 => 4 | 2 => 5 | 3 => 9 | _ => 10
  | 7 => match k with | 0 => 6 | 1 => 7 | 2 => 8 | 3 => 9 | _ => 10
  | 8 => match k with | 0 => 11 | 1 => 12 | 2 => 13 | 3 => 14 | _ => 15
  | _ => 0

def sub0Pack (i : ℕ) : ℕ :=
  match i with
  | 0 => 475936
  | 1 => 607008
  | 2 => 803616
  | 3 => 934688
  | 4 => 619296
  | 5 => 815904
  | 6 => 946976
  | 7 => 824096
  | 8 => 955168
  | 9 => 967456
  | 10 => 619552
  | 11 => 816160
  | 12 => 947232
  | 13 => 824352
  | 14 => 955424
  | 15 => 967712
  | 16 => 825120
  | 17 => 956192
  | 18 => 968480
  | 19 => 968992
  | 20 => 619568
  | 21 => 816176
  | 22 => 947248
  | 23 => 824368
  | 24 => 955440
  | 25 => 967728
  | 26 => 825136
  | 27 => 956208
  | 28 => 968496
  | 29 => 969008
  | 30 => 825152
  | 31 => 956224
  | 32 => 968512
  | 33 => 969024
  | 34 => 969072
  | 35 => 619570
  | 36 => 816178
  | 37 => 947250
  | 38 => 824370
  | 39 => 955442
  | 40 => 967730
  | 41 => 825138
  | 42 => 956210
  | 43 => 968498
  | 44 => 969010
  | 45 => 825154
  | 46 => 956226
  | 47 => 968514
  | 48 => 969026
  | 49 => 969074
  | 50 => 825155
  | 51 => 956227
  | 52 => 968515
  | 53 => 969027
  | 54 => 969075
  | _ => 969076

def dirB (a b hm r s : ℕ) : Bool :=
  if ((hm >>> r) &&& 1) != 0 || ((hm >>> s) &&& 1) != 0 then true
  else
    let rr := rowAt r
    let diff := rowAt s &&& (511 ^^^ rr)
    let rec go (u : ℕ) : Bool :=
      match u with
      | 0 => false
      | u' + 1 =>
        if ((diff >>> u') &&& 1) != 0 && !(firesB a b (rr ||| (1 <<< u'))) then true
        else go u'
    go 9

def apartB (a b hm r s : ℕ) : Bool :=
  dirB a b hm r s || dirB a b hm s r

def stableB (a b hm r v : ℕ) : Bool :=
  let rr := rowAt r
  if ((rr >>> v) &&& 1) != 0 then false
  else if ((hm >>> r) &&& 1) != 0 then true
  else !(firesB a b (rr ||| (1 <<< v)))

def row5 (v sub0 k : ℕ) : ℕ :=
  if v == 0 then (sub0Pack sub0 >>> (4 * k)) &&& 15 else thrRow v k

def strongB (a b hm sub0 v : ℕ) : Bool :=
  if (((a ||| b) >>> v) &&& 1) != 0 then true
  else
    let r0 := row5 v sub0 0
    let r1 := row5 v sub0 1
    let r2 := row5 v sub0 2
    let r3 := row5 v sub0 3
    let r4 := row5 v sub0 4
    apartB a b hm r0 r1 && apartB a b hm r0 r2 && apartB a b hm r0 r3 && apartB a b hm r0 r4 &&
    apartB a b hm r1 r2 && apartB a b hm r1 r3 && apartB a b hm r1 r4 &&
    apartB a b hm r2 r3 && apartB a b hm r2 r4 && apartB a b hm r3 r4

def hasStableB (a b hm v : ℕ) : Bool :=
  let rec go (r : ℕ) : Bool :=
    match r with
    | 0 => false
    | r' + 1 => if stableB a b hm r' v then true else go r'
  go 16

def conflictB (a b hm v w : ℕ) : Bool :=
  let rec go1 (r : ℕ) : Bool :=
    match r with
    | 0 => false
    | r' + 1 => if stableB a b hm r' v && stableB a b hm r' w then true else go1 r'
  let rec go2 (r : ℕ) : Bool :=
    match r with
    | 0 => false
    | r' + 1 =>
      let rr := rowAt r'
      if (stableB a b hm r' v && ((rr >>> w) &&& 1) != 0) ||
         (stableB a b hm r' w && ((rr >>> v) &&& 1) != 0) then true
      else go2 r'
  go1 16 && go2 16

def checkClique5 (a b hm wit : ℕ) : Bool :=
  let w0 := wit &&& 15
  let w1 := (wit >>> 4) &&& 15
  let w2 := (wit >>> 8) &&& 15
  let w3 := (wit >>> 12) &&& 15
  let w4 := (wit >>> 16) &&& 15
  let sub0 := wit >>> 20
  w0 < w1 && w1 < w2 && w2 < w3 && w3 < w4 && w4 < 9 && sub0 < 56 &&
  strongB a b hm sub0 w0 && strongB a b hm sub0 w1 && strongB a b hm sub0 w2 &&
  strongB a b hm sub0 w3 && strongB a b hm sub0 w4 &&
  hasStableB a b hm w0 && hasStableB a b hm w1 && hasStableB a b hm w2 &&
  hasStableB a b hm w3 && hasStableB a b hm w4 &&
  conflictB a b hm w0 w1 && conflictB a b hm w0 w2 && conflictB a b hm w0 w3 && conflictB a b hm w0 w4 &&
  conflictB a b hm w1 w2 && conflictB a b hm w1 w3 && conflictB a b hm w1 w4 &&
  conflictB a b hm w2 w3 && conflictB a b hm w2 w4 && conflictB a b hm w3 w4

theorem rows_diff_exists : ∀ r s : Fin 16, r ≠ s → ∃ u : V, u ∈ rows s ∧ u ∉ rows r := by
  decide +kernel

theorem testBit_511 : ∀ v : V, (511 : ℕ).testBit v.val = true := by
  decide +kernel

theorem dirB_go_sound (a b rr diff : ℕ) :
    ∀ k : ℕ, k ≤ 9 → dirB.go a b rr diff k = true →
      ∃ u : V, u.val < k ∧ diff.testBit u.val = true ∧ firesB a b (rr ||| (1 <<< u.val)) = false := by
  intro k
  induction k with
  | zero =>
    intro _ h
    simp [dirB.go] at h
  | succ k ih =>
    intro hk h
    unfold dirB.go at h
    by_cases hcur : (((diff >>> k) &&& 1) != 0 && !(firesB a b (rr ||| (1 <<< k)))) = true
    · rw [Bool.and_eq_true, shiftAnd1_ne_zero, Bool.not_eq_true'] at hcur
      exact ⟨⟨k, by omega⟩, Nat.lt_succ_self k, hcur.1, hcur.2⟩
    · have hcurf : (((diff >>> k) &&& 1) != 0 && !(firesB a b (rr ||| (1 <<< k)))) = false :=
        Bool.eq_false_iff.mpr hcur
      rw [hcurf] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨u, hu, hd, hf⟩ := ih (by omega) h
      exact ⟨u, by omega, hd, hf⟩

theorem dirB_sound (a b : ℕ) (ha : a < 512) (hb : b < 512) (r s : Fin 16) (hrs : r ≠ s)
    (h : dirB a b (hotMask a b) r.val s.val = true) :
    Dir (decode a) (decode b) r s := by
  unfold dirB at h
  by_cases hhot : ((((hotMask a b >>> r.val) &&& 1) != 0) || (((hotMask a b >>> s.val) &&& 1) != 0)) = true
  · obtain ⟨u, hus, hur⟩ := rows_diff_exists r s hrs
    refine ⟨u, hus, hur, fun _ => ?_⟩
    rw [Bool.or_eq_true, shiftAnd1_ne_zero, shiftAnd1_ne_zero, testBit_hotMask, testBit_hotMask] at hhot
    rcases hhot with hr | hs
    · exact Or.inl (by rw [← decode_rowAt r]; exact (firesB_iff a b _ ha hb).mp hr)
    · exact Or.inr (by rw [← decode_rowAt s]; exact (firesB_iff a b _ ha hb).mp hs)
  · have hhotf : ((((hotMask a b >>> r.val) &&& 1) != 0) || (((hotMask a b >>> s.val) &&& 1) != 0)) = false :=
      Bool.eq_false_iff.mpr hhot
    rw [hhotf] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨u, _, hdiff, hnf⟩ := dirB_go_sound a b (rowAt r.val) (rowAt s.val &&& (511 ^^^ rowAt r.val)) 9 (le_refl _) h
    rw [Nat.testBit_and, Nat.testBit_xor, testBit_511 u, Bool.true_xor, Bool.and_eq_true, Bool.not_eq_true'] at hdiff
    have hus : u ∈ rows s := by
      rw [← decode_rowAt s, mem_decode]
      exact hdiff.1
    have hur : u ∉ rows r := by
      rw [← decode_rowAt r, mem_decode]
      simp [hdiff.2]
    refine ⟨u, hus, hur, fun hf => ?_⟩
    exfalso
    have hfb : firesB a b (rowAt r.val ||| (1 <<< u.val)) = true := by
      rw [firesB_iff a b _ ha hb, decode_or_bit, decode_rowAt r]
      exact hf
    rw [hnf] at hfb
    exact Bool.false_ne_true hfb

theorem apartB_sound (a b : ℕ) (ha : a < 512) (hb : b < 512) (r s : Fin 16) (hrs : r ≠ s)
    (h : apartB a b (hotMask a b) r.val s.val = true) :
    Apart (decode a) (decode b) r s := by
  unfold apartB at h
  rw [Bool.or_eq_true] at h
  rcases h with h1 | h2
  · exact Or.inl (dirB_sound a b ha hb r s hrs h1)
  · exact Or.inr (dirB_sound a b ha hb s r hrs.symm h2)

theorem stableB_iff (a b : ℕ) (ha : a < 512) (hb : b < 512) (r : Fin 16) (v : V) :
    stableB a b (hotMask a b) r.val v.val = true ↔ Stable (decode a) (decode b) r v := by
  unfold stableB Stable
  dsimp only
  rw [shiftAnd1_ne_zero, shiftAnd1_ne_zero, testBit_hotMask]
  have hmem : (rowAt r.val).testBit v.val = true ↔ v ∈ rows r := by
    rw [← decode_rowAt r, mem_decode]
  have hfir : firesB a b (rowAt r.val) = true ↔ fires (decode a) (decode b) (rows r) := by
    rw [firesB_iff a b _ ha hb, decode_rowAt r]
  have hfirIns : firesB a b (rowAt r.val ||| (1 <<< v.val)) = true ↔
      fires (decode a) (decode b) (insert v (rows r)) := by
    rw [firesB_iff a b _ ha hb, decode_or_bit, decode_rowAt r]
  cases hv : (rowAt r.val).testBit v.val with
  | true =>
    simp only [↓reduceIte, Bool.false_eq_true, false_iff, not_and]
    intro hnot
    exact (hnot (hmem.mp hv)).elim
  | false =>
    have hnot : v ∉ rows r := by
      intro hm
      rw [hmem.mpr hm] at hv
      exact Bool.noConfusion hv
    simp only [Bool.false_eq_true, ↓reduceIte, hnot, not_false_eq_true, true_and]
    cases hf : firesB a b (rowAt r.val) with
    | true =>
      simp only [↓reduceIte, true_iff]
      intro _
      exact hfir.mp hf
    | false =>
      have hnf : ¬ fires (decode a) (decode b) (rows r) := by
        intro ht
        rw [hfir.mpr ht] at hf
        exact Bool.noConfusion hf
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_eq_true']
      constructor
      · intro hfi htr
        rw [hfirIns.mpr htr] at hfi
        exact Bool.noConfusion hfi
      · intro himp
        apply Bool.eq_false_iff.mpr
        intro ht
        exact hnf (himp (hfirIns.mp ht))

theorem row5_lt : ∀ (v : V) (sub0 : Fin 56) (k : Fin 5), row5 v.val sub0.val k.val < 16 := by
  decide +kernel

theorem row5_mem : ∀ (v : V) (sub0 : Fin 56) (k : Fin 5),
    v ∈ rows ⟨row5 v.val sub0.val k.val, row5_lt v sub0 k⟩ := by
  decide +kernel

theorem row5_inj : ∀ (v : V) (sub0 : Fin 56) (j k : Fin 5),
    j ≠ k → row5 v.val sub0.val j.val ≠ row5 v.val sub0.val k.val := by
  decide +kernel

theorem strongB_sound (a b sub0 : ℕ) (ha : a < 512) (hb : b < 512) (hs : sub0 < 56) (v : V)
    (h : strongB a b (hotMask a b) sub0 v.val = true) :
    Strong (decode a) (decode b) v := by
  unfold strongB at h
  rw [shiftAnd1_ne_zero, Nat.testBit_or] at h
  by_cases hab : (a.testBit v.val || b.testBit v.val) = true
  · left
    rw [Bool.or_eq_true] at hab
    rcases hab with hva | hvb
    · exact Or.inl ((mem_decode a v).mpr hva)
    · exact Or.inr ((mem_decode b v).mpr hvb)
  · have habf : (a.testBit v.val || b.testBit v.val) = false := Bool.eq_false_iff.mpr hab
    rw [habf] at h
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at h
    right
    let rs : Fin 5 → Fin 16 := fun k => ⟨row5 v.val sub0 k.val, row5_lt v ⟨sub0, hs⟩ k⟩
    refine ⟨rs, fun k => row5_mem v ⟨sub0, hs⟩ k, ?_⟩
    have hne (j k : Fin 5) (hjk : j ≠ k) : rs j ≠ rs k := fun heq =>
      row5_inj v ⟨sub0, hs⟩ j k hjk (congrArg Fin.val heq)
    intro j k hjk
    fin_cases j <;> fin_cases k
    · exact (hjk rfl).elim
    · exact apartB_sound a b ha hb (rs 0) (rs 1) (hne 0 1 hjk) h.1.1.1.1.1.1.1.1.1
    · exact apartB_sound a b ha hb (rs 0) (rs 2) (hne 0 2 hjk) h.1.1.1.1.1.1.1.1.2
    · exact apartB_sound a b ha hb (rs 0) (rs 3) (hne 0 3 hjk) h.1.1.1.1.1.1.1.2
    · exact apartB_sound a b ha hb (rs 0) (rs 4) (hne 0 4 hjk) h.1.1.1.1.1.1.2
    · exact (apartB_sound a b ha hb (rs 0) (rs 1) (hne 0 1 hjk.symm) h.1.1.1.1.1.1.1.1.1).symm
    · exact (hjk rfl).elim
    · exact apartB_sound a b ha hb (rs 1) (rs 2) (hne 1 2 hjk) h.1.1.1.1.1.2
    · exact apartB_sound a b ha hb (rs 1) (rs 3) (hne 1 3 hjk) h.1.1.1.1.2
    · exact apartB_sound a b ha hb (rs 1) (rs 4) (hne 1 4 hjk) h.1.1.1.2
    · exact (apartB_sound a b ha hb (rs 0) (rs 2) (hne 0 2 hjk.symm) h.1.1.1.1.1.1.1.1.2).symm
    · exact (apartB_sound a b ha hb (rs 1) (rs 2) (hne 1 2 hjk.symm) h.1.1.1.1.1.2).symm
    · exact (hjk rfl).elim
    · exact apartB_sound a b ha hb (rs 2) (rs 3) (hne 2 3 hjk) h.1.1.2
    · exact apartB_sound a b ha hb (rs 2) (rs 4) (hne 2 4 hjk) h.1.2
    · exact (apartB_sound a b ha hb (rs 0) (rs 3) (hne 0 3 hjk.symm) h.1.1.1.1.1.1.1.2).symm
    · exact (apartB_sound a b ha hb (rs 1) (rs 3) (hne 1 3 hjk.symm) h.1.1.1.1.2).symm
    · exact (apartB_sound a b ha hb (rs 2) (rs 3) (hne 2 3 hjk.symm) h.1.1.2).symm
    · exact (hjk rfl).elim
    · exact apartB_sound a b ha hb (rs 3) (rs 4) (hne 3 4 hjk) h.2
    · exact (apartB_sound a b ha hb (rs 0) (rs 4) (hne 0 4 hjk.symm) h.1.1.1.1.1.1.2).symm
    · exact (apartB_sound a b ha hb (rs 1) (rs 4) (hne 1 4 hjk.symm) h.1.1.1.2).symm
    · exact (apartB_sound a b ha hb (rs 2) (rs 4) (hne 2 4 hjk.symm) h.1.2).symm
    · exact (apartB_sound a b ha hb (rs 3) (rs 4) (hne 3 4 hjk.symm) h.2).symm
    · exact (hjk rfl).elim

theorem hasStableB_go_sound (a b hm v : ℕ) :
    ∀ n : ℕ, n ≤ 16 → hasStableB.go a b hm v n = true →
      ∃ r : Fin 16, r.val < n ∧ stableB a b hm r.val v = true := by
  intro n
  induction n with
  | zero =>
    intro _ h
    simp [hasStableB.go] at h
  | succ n ih =>
    intro hn h
    unfold hasStableB.go at h
    by_cases hs : stableB a b hm n v = true
    · exact ⟨⟨n, by omega⟩, Nat.lt_succ_self n, hs⟩
    · have hsf : stableB a b hm n v = false := Bool.eq_false_iff.mpr hs
      rw [hsf] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨r, hr, hst⟩ := ih (by omega) h
      exact ⟨r, by omega, hst⟩

theorem hasStableB_sound (a b : ℕ) (ha : a < 512) (hb : b < 512) (v : V)
    (h : hasStableB a b (hotMask a b) v.val = true) :
    ∃ r : Fin 16, Stable (decode a) (decode b) r v := by
  obtain ⟨r, _, hst⟩ := hasStableB_go_sound a b (hotMask a b) v.val 16 (le_refl _) h
  exact ⟨r, (stableB_iff a b ha hb r v).mp hst⟩

theorem conflictB_go1_sound (a b hm v w : ℕ) :
    ∀ n : ℕ, n ≤ 16 → conflictB.go1 a b hm v w n = true →
      ∃ r : Fin 16, r.val < n ∧ stableB a b hm r.val v = true ∧ stableB a b hm r.val w = true := by
  intro n
  induction n with
  | zero =>
    intro _ h
    simp [conflictB.go1] at h
  | succ n ih =>
    intro hn h
    unfold conflictB.go1 at h
    by_cases hs : (stableB a b hm n v && stableB a b hm n w) = true
    · rw [Bool.and_eq_true] at hs
      exact ⟨⟨n, by omega⟩, Nat.lt_succ_self n, hs.1, hs.2⟩
    · have hsf : (stableB a b hm n v && stableB a b hm n w) = false := Bool.eq_false_iff.mpr hs
      rw [hsf] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨r, hr, h1, h2⟩ := ih (by omega) h
      exact ⟨r, by omega, h1, h2⟩

theorem conflictB_go2_sound (a b hm v w : ℕ) :
    ∀ n : ℕ, n ≤ 16 → conflictB.go2 a b hm v w n = true →
      ∃ r : Fin 16, r.val < n ∧
        ((stableB a b hm r.val v = true ∧ (rowAt r.val).testBit w = true) ∨
         (stableB a b hm r.val w = true ∧ (rowAt r.val).testBit v = true)) := by
  intro n
  induction n with
  | zero =>
    intro _ h
    simp [conflictB.go2] at h
  | succ n ih =>
    intro hn h
    unfold conflictB.go2 at h
    dsimp only at h
    by_cases hs : ((stableB a b hm n v && ((rowAt n >>> w) &&& 1) != 0) ||
        (stableB a b hm n w && ((rowAt n >>> v) &&& 1) != 0)) = true
    · rw [Bool.or_eq_true, Bool.and_eq_true, Bool.and_eq_true,
        shiftAnd1_ne_zero, shiftAnd1_ne_zero] at hs
      exact ⟨⟨n, by omega⟩, Nat.lt_succ_self n, hs⟩
    · have hsf : ((stableB a b hm n v && ((rowAt n >>> w) &&& 1) != 0) ||
          (stableB a b hm n w && ((rowAt n >>> v) &&& 1) != 0)) = false := Bool.eq_false_iff.mpr hs
      rw [hsf] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨r, hr, hst⟩ := ih (by omega) h
      exact ⟨r, by omega, hst⟩

theorem conflictB_sound (a b : ℕ) (ha : a < 512) (hb : b < 512) (v w : V)
    (h : conflictB a b (hotMask a b) v.val w.val = true) :
    Conflict (decode a) (decode b) v w := by
  unfold conflictB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨r1, _, hs1, hs2⟩ := conflictB_go1_sound a b (hotMask a b) v.val w.val 16 (le_refl _) h.1
  obtain ⟨r2, _, h2⟩ := conflictB_go2_sound a b (hotMask a b) v.val w.val 16 (le_refl _) h.2
  refine ⟨⟨r1, (stableB_iff a b ha hb r1 v).mp hs1, (stableB_iff a b ha hb r1 w).mp hs2⟩, ?_⟩
  rcases h2 with ⟨hsv, hmw⟩ | ⟨hsw, hmv⟩
  · exact Or.inl ⟨r2, (stableB_iff a b ha hb r2 v).mp hsv, by rw [← decode_rowAt r2, mem_decode]; exact hmw⟩
  · exact Or.inr ⟨r2, (stableB_iff a b ha hb r2 w).mp hsw, by rw [← decode_rowAt r2, mem_decode]; exact hmv⟩

theorem conflict_symm {A B : Finset V} {v w : V} (h : Conflict A B v w) : Conflict A B w v := by
  obtain ⟨⟨r, h1, h2⟩, h3⟩ := h
  exact ⟨⟨r, h2, h1⟩, h3.symm⟩

theorem checkClique5_sound (a b wit : ℕ) (ha : a < 512) (hb : b < 512)
    (h : checkClique5 a b (hotMask a b) wit = true) :
    ∃ f : Fin 5 → V, Clique (decode a) (decode b) f := by
  unfold checkClique5 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h01, h12⟩, h23⟩, h34⟩, h49⟩, hsub⟩,
    hs0⟩, hs1⟩, hs2⟩, hs3⟩, hs4⟩,
    ht0⟩, ht1⟩, ht2⟩, ht3⟩, ht4⟩,
    hc01⟩, hc02⟩, hc03⟩, hc04⟩,
    hc12⟩, hc13⟩, hc14⟩, hc23⟩, hc24⟩, hc34⟩ := h
  let v0 : V := ⟨wit &&& 15, by omega⟩
  let v1 : V := ⟨(wit >>> 4) &&& 15, by omega⟩
  let v2 : V := ⟨(wit >>> 8) &&& 15, by omega⟩
  let v3 : V := ⟨(wit >>> 12) &&& 15, by omega⟩
  let v4 : V := ⟨(wit >>> 16) &&& 15, by omega⟩
  let f : Fin 5 → V := ![v0, v1, v2, v3, v4]
  refine ⟨f, ?_, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact strongB_sound a b (wit >>> 20) ha hb hsub v0 hs0
    · exact strongB_sound a b (wit >>> 20) ha hb hsub v1 hs1
    · exact strongB_sound a b (wit >>> 20) ha hb hsub v2 hs2
    · exact strongB_sound a b (wit >>> 20) ha hb hsub v3 hs3
    · exact strongB_sound a b (wit >>> 20) ha hb hsub v4 hs4
  · intro j
    fin_cases j
    · exact hasStableB_sound a b ha hb v0 ht0
    · exact hasStableB_sound a b ha hb v1 ht1
    · exact hasStableB_sound a b ha hb v2 ht2
    · exact hasStableB_sound a b ha hb v3 ht3
    · exact hasStableB_sound a b ha hb v4 ht4
  · intro j k hjk
    fin_cases j <;> fin_cases k
    · exact (hjk rfl).elim
    · exact conflictB_sound a b ha hb v0 v1 hc01
    · exact conflictB_sound a b ha hb v0 v2 hc02
    · exact conflictB_sound a b ha hb v0 v3 hc03
    · exact conflictB_sound a b ha hb v0 v4 hc04
    · exact conflict_symm (conflictB_sound a b ha hb v0 v1 hc01)
    · exact (hjk rfl).elim
    · exact conflictB_sound a b ha hb v1 v2 hc12
    · exact conflictB_sound a b ha hb v1 v3 hc13
    · exact conflictB_sound a b ha hb v1 v4 hc14
    · exact conflict_symm (conflictB_sound a b ha hb v0 v2 hc02)
    · exact conflict_symm (conflictB_sound a b ha hb v1 v2 hc12)
    · exact (hjk rfl).elim
    · exact conflictB_sound a b ha hb v2 v3 hc23
    · exact conflictB_sound a b ha hb v2 v4 hc24
    · exact conflict_symm (conflictB_sound a b ha hb v0 v3 hc03)
    · exact conflict_symm (conflictB_sound a b ha hb v1 v3 hc13)
    · exact conflict_symm (conflictB_sound a b ha hb v2 v3 hc23)
    · exact (hjk rfl).elim
    · exact conflictB_sound a b ha hb v3 v4 hc34
    · exact conflict_symm (conflictB_sound a b ha hb v0 v4 hc04)
    · exact conflict_symm (conflictB_sound a b ha hb v1 v4 hc14)
    · exact conflict_symm (conflictB_sound a b ha hb v2 v4 hc24)
    · exact conflict_symm (conflictB_sound a b ha hb v3 v4 hc34)
    · exact (hjk rfl).elim

def checkChunk (start len : ℕ) (wits : List ℕ) (specs : List ℕ) : Bool :=
  let rec go (rem t : ℕ) (ws sp : List ℕ) : Bool :=
    match rem with
    | 0 => ws.isEmpty && sp.isEmpty
    | rem' + 1 =>
      let a := decodeTritA t
      let b := decodeTritB t
      if a != 0 && b != 0 && isCanonB a b then
        let hm := hotMask a b
        if hm != 0 then
          match ws with
          | [] => false
          | wit :: ws' =>
            if wit == 0 then
              match sp with
              | [] => false
              | code :: sp' => if code == ((a <<< 9) ||| b) then go rem' (t + 1) ws' sp' else false
            else
              if checkClique5 a b hm wit then go rem' (t + 1) ws' sp else false
        else go rem' (t + 1) ws sp
      else go rem' (t + 1) ws sp
  go len start wits specs

theorem checkChunk_go_sound : ∀ (rem start : ℕ) (ws sp : List ℕ),
    checkChunk.go rem start ws sp = true →
    ∀ t : ℕ, start ≤ t → t < start + rem →
      decodeTritA t ≠ 0 → decodeTritB t ≠ 0 →
      isCanonB (decodeTritA t) (decodeTritB t) = true →
      hotMask (decodeTritA t) (decodeTritB t) ≠ 0 →
      (decodeTritA t * 512 + decodeTritB t) ∈ sp ∨
        ∃ f : Fin 5 → V, Clique (decode (decodeTritA t)) (decode (decodeTritB t)) f := by
  intro rem
  induction rem with
  | zero =>
    intro start ws sp _ t ht1 ht2
    omega
  | succ rem' ih =>
    intro start ws sp hok t ht1 ht2 ha hb hc hh
    unfold checkChunk.go at hok
    dsimp only at hok
    by_cases hts : t = start
    · subst hts
      have hcond1 : (decodeTritA t != 0 && decodeTritB t != 0 && isCanonB (decodeTritA t) (decodeTritB t)) = true := by
        simp [ha, hb, hc]
      have hcond2 : (hotMask (decodeTritA t) (decodeTritB t) != 0) = true := by
        simp [hh]
      simp only [hcond1, ↓reduceIte, hcond2] at hok
      cases ws with
      | nil => exact absurd hok Bool.false_ne_true
      | cons wit ws' =>
        simp only at hok
        by_cases hw0 : wit = 0
        · subst hw0
          simp only [beq_self_eq_true, ↓reduceIte] at hok
          cases sp with
          | nil => exact absurd hok Bool.false_ne_true
          | cons code sp' =>
            simp only at hok
            by_cases hcode : (code == ((decodeTritA t <<< 9) ||| decodeTritB t)) = true
            · left
              have heq : code = decodeTritA t * 512 + decodeTritB t := by
                rw [beq_iff_eq.mp hcode]
                exact shift9_or_eq_mul_add _ _ (decodeTritB_lt t)
              rw [heq]
              exact List.mem_cons_self
            · have hcf : (code == ((decodeTritA t <<< 9) ||| decodeTritB t)) = false :=
                Bool.eq_false_iff.mpr hcode
              rw [hcf] at hok
              simp at hok
        · have hwf : (wit == 0) = false := beq_false_of_ne hw0
          rw [hwf] at hok
          simp only [Bool.false_eq_true, ↓reduceIte] at hok
          by_cases hclq : checkClique5 (decodeTritA t) (decodeTritB t) (hotMask (decodeTritA t) (decodeTritB t)) wit = true
          · exact Or.inr (checkClique5_sound _ _ wit (decodeTritA_lt t) (decodeTritB_lt t) hclq)
          · have hcf : checkClique5 (decodeTritA t) (decodeTritB t) (hotMask (decodeTritA t) (decodeTritB t)) wit = false :=
              Bool.eq_false_iff.mpr hclq
            rw [hcf] at hok
            simp at hok
    · have ht1' : start + 1 ≤ t := by omega
      have ht2' : t < (start + 1) + rem' := by omega
      by_cases hcond1 : (decodeTritA start != 0 && decodeTritB start != 0 && isCanonB (decodeTritA start) (decodeTritB start)) = true
      · simp only [hcond1, ↓reduceIte] at hok
        by_cases hcond2 : (hotMask (decodeTritA start) (decodeTritB start) != 0) = true
        · simp only [hcond2, ↓reduceIte] at hok
          cases ws with
          | nil => exact absurd hok Bool.false_ne_true
          | cons wit ws' =>
            simp only at hok
            by_cases hw0 : wit = 0
            · subst hw0
              simp only [beq_self_eq_true, ↓reduceIte] at hok
              cases sp with
              | nil => exact absurd hok Bool.false_ne_true
              | cons code sp' =>
                simp only at hok
                by_cases hcode : (code == ((decodeTritA start <<< 9) ||| decodeTritB start)) = true
                · simp only [hcode, ↓reduceIte] at hok
                  rcases ih (start + 1) ws' sp' hok t ht1' ht2' ha hb hc hh with hmem | hclq
                  · exact Or.inl (List.mem_cons_of_mem code hmem)
                  · exact Or.inr hclq
                · have hcf : (code == ((decodeTritA start <<< 9) ||| decodeTritB start)) = false :=
                    Bool.eq_false_iff.mpr hcode
                  rw [hcf] at hok
                  simp at hok
            · have hwf : (wit == 0) = false := beq_false_of_ne hw0
              rw [hwf] at hok
              simp only [Bool.false_eq_true, ↓reduceIte] at hok
              by_cases hclq : checkClique5 (decodeTritA start) (decodeTritB start) (hotMask (decodeTritA start) (decodeTritB start)) wit = true
              · simp only [hclq, ↓reduceIte] at hok
                exact ih (start + 1) ws' sp hok t ht1' ht2' ha hb hc hh
              · have hcf : checkClique5 (decodeTritA start) (decodeTritB start) (hotMask (decodeTritA start) (decodeTritB start)) wit = false :=
                  Bool.eq_false_iff.mpr hclq
                rw [hcf] at hok
                simp at hok
        · have hcf2 : (hotMask (decodeTritA start) (decodeTritB start) != 0) = false :=
            Bool.eq_false_iff.mpr hcond2
          rw [hcf2] at hok
          simp only [Bool.false_eq_true, ↓reduceIte] at hok
          exact ih (start + 1) ws sp hok t ht1' ht2' ha hb hc hh
      · have hcf1 : (decodeTritA start != 0 && decodeTritB start != 0 && isCanonB (decodeTritA start) (decodeTritB start)) = false :=
          Bool.eq_false_iff.mpr hcond1
        rw [hcf1] at hok
        simp only [Bool.false_eq_true, ↓reduceIte] at hok
        exact ih (start + 1) ws sp hok t ht1' ht2' ha hb hc hh

theorem checkChunk_sound (start len : ℕ) (wits specs : List ℕ)
    (hok : checkChunk start len wits specs = true)
    (t : ℕ) (ht1 : start ≤ t) (ht2 : t < start + len)
    (ha : decodeTritA t ≠ 0) (hb : decodeTritB t ≠ 0)
    (hc : isCanonB (decodeTritA t) (decodeTritB t) = true)
    (hh : hotMask (decodeTritA t) (decodeTritB t) ≠ 0) :
    (decodeTritA t * 512 + decodeTritB t) ∈ specs ∨
      ∃ f : Fin 5 → V, Clique (decode (decodeTritA t)) (decode (decodeTritB t)) f :=
  checkChunk_go_sound len start wits specs hok t ht1 ht2 ha hb hc hh

theorem checkChunk_of_pair (start len : ℕ) (wits specs : List ℕ)
    (hok : checkChunk start len wits specs = true)
    (a b : Fin 512) (hab : (a.val &&& b.val) = 0)
    (ht1 : start ≤ tritCodeB a.val b.val) (ht2 : tritCodeB a.val b.val < start + len)
    (ha : a.val ≠ 0) (hb : b.val ≠ 0)
    (hc : isCanonB a.val b.val = true)
    (hh : hotMask a.val b.val ≠ 0) :
    (a.val * 512 + b.val) ∈ specs ∨
      ∃ f : Fin 5 → V, Clique (decode a.val) (decode b.val) f := by
  obtain ⟨_, hda, hdb⟩ := tritCode_spec a b hab
  have h := checkChunk_sound start len wits specs hok (tritCodeB a.val b.val) ht1 ht2
    (hda.symm ▸ ha) (hdb.symm ▸ hb) (hda.symm ▸ hdb.symm ▸ hc) (hda.symm ▸ hdb.symm ▸ hh)
  rwa [hda, hdb] at h


def SeparatesRows (C : AndCountCircuit 9) : Prop :=
  ∀ r : Fin 16, C.eval (rows r) = false ∧ ∀ u : V, u ∉ rows r → C.eval (insert u (rows r)) = true

theorem separatesRows_of_separates {C : AndCountCircuit 9} (h : Separates C) : SeparatesRows C :=
  fun r => h (rows r) (rowsGood r)

theorem bool_ne_eq_not {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

theorem gate_true_of_both_sides (C : AndCountCircuit 9) (i : Fin C.size) (d : Bool) (U : Finset V)
    (h1 : onSide C i d U) (h2 : onSide C i (!d) U) : C.gateVal U i = true :=
  (gate_iff C i U).mpr fun b => by
    by_cases hbd : b = d
    · exact hbd ▸ h1
    · exact (bool_ne_eq_not hbd) ▸ h2

theorem gate_false_of_not_onSide (C : AndCountCircuit 9) (i : Fin C.size) (d : Bool) (U : Finset V)
    (h : ¬ onSide C i d U) : C.gateVal U i = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  exact h ((gate_iff C i U).mp ht d)

theorem raw_side_true (C : AndCountCircuit 9) (i : Fin C.size) (d : Bool) (U : Finset V)
    (h1 : ∃ v ∈ vars C i d, v ∈ U) (h2 : ∃ w ∈ vars C i (!d), w ∈ U) :
    C.gateVal U i = true :=
  gate_true_of_both_sides C i d U (Or.inl h1) (Or.inl h2)

theorem not_onSide_other (C : AndCountCircuit 9) (i : Fin C.size) (d : Bool) (U : Finset V)
    (hf : C.gateVal U i = false) (hs : onSide C i d U) : ¬ onSide C i (!d) U := by
  intro hs2
  have ht := gate_true_of_both_sides C i d U hs hs2
  simp [hf] at ht

theorem ref_false_of_other_on (C : AndCountCircuit 9) (i : Fin C.size) (d : Bool) (U : Finset V)
    (hf : C.gateVal U i = false) (hs : onSide C i d U) {k : Fin C.size} (hk : k ∈ refs C i (!d)) :
    C.gateVal U k = false := by
  apply Bool.eq_false_iff.mpr
  intro ht
  exact not_onSide_other C i d U hf hs (Or.inr ⟨k, hk, ht⟩)

theorem bare_out_empty_rows (C : AndCountCircuit 9) (sep : SeparatesRows C) (v : V) : v ∉ C.outVars := by
  intro hv
  have hrow : ∃ r : Fin 16, v ∈ rows r := by
    fin_cases v <;> first
      | exact ⟨0, by decide⟩ | exact ⟨5, by decide⟩ | exact ⟨1, by decide⟩
      | exact ⟨6, by decide⟩ | exact ⟨11, by decide⟩
  obtain ⟨r, hr⟩ := hrow
  have he := (sep r).1
  have ht : C.eval (rows r) = true := decide_eq_true (Or.inl ⟨v, hv, hr⟩)
  simp [he] at ht

theorem not_out_of_row_true (C : AndCountCircuit 9) (sep : SeparatesRows C)
    (i : Fin C.size) (r : Fin 16) (ht : C.gateVal (rows r) i = true) : i ∉ C.outGates := by
  intro hi
  have he := (sep r).1
  have hv : C.eval (rows r) = true := decide_eq_true (Or.inr ⟨i, hi, ht⟩)
  simp [he] at hv

theorem eval_true_exists_out (C : AndCountCircuit 9) (sep : SeparatesRows C)
    (U : Finset V) (ht : C.eval U = true) : ∃ i ∈ C.outGates, C.gateVal U i = true := by
  rw [eval, decide_eq_true_eq] at ht
  rcases ht with ⟨v, hv, _⟩ | ⟨i, hi, hg⟩
  · exact (bare_out_empty_rows C sep v hv).elim
  · exact ⟨i, hi, hg⟩

theorem five_exhaust (C : AndCountCircuit 9) (sz : C.size = 5) (p : Fin C.size)
    (e : Fin 4 → Fin C.size) (he_ne : ∀ j, e j ≠ p) (he_inj : Function.Injective e)
    (x : Fin C.size) : x = p ∨ x = e 0 ∨ x = e 1 ∨ x = e 2 ∨ x = e 3 := by
  classical
  let S : Finset (Fin C.size) := {p, e 0, e 1, e 2, e 3}
  have hcard : S.card = 5 := by
    have h0 : p ∉ ({e 0, e 1, e 2, e 3} : Finset (Fin C.size)) := by
      simp [Ne.symm (he_ne 0), Ne.symm (he_ne 1), Ne.symm (he_ne 2), Ne.symm (he_ne 3)]
    have h1 : e 0 ∉ ({e 1, e 2, e 3} : Finset (Fin C.size)) := by
      simp [he_inj.ne (by decide : (0 : Fin 4) ≠ 1), he_inj.ne (by decide : (0 : Fin 4) ≠ 2), he_inj.ne (by decide : (0 : Fin 4) ≠ 3)]
    have h2 : e 1 ∉ ({e 2, e 3} : Finset (Fin C.size)) := by
      simp [he_inj.ne (by decide : (1 : Fin 4) ≠ 2), he_inj.ne (by decide : (1 : Fin 4) ≠ 3)]
    have h3 : e 2 ∉ ({e 3} : Finset (Fin C.size)) := by
      simp [he_inj.ne (by decide : (2 : Fin 4) ≠ 3)]
    simp only [S, Finset.card_insert_of_notMem h0, Finset.card_insert_of_notMem h1,
      Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h3, Finset.card_singleton]
  have huniv : S = Finset.univ := Finset.eq_univ_of_card S (by simp [hcard, sz])
  have hx : x ∈ S := huniv ▸ Finset.mem_univ x
  simpa [S] using hx

theorem set1B_impossible (C : AndCountCircuit 9) (sz : C.size = 5) (sep : SeparatesRows C)
    (p : Fin C.size) (e : Fin 4 → Fin C.size) (d : Fin 4 → Bool)
    (he_ne : ∀ j, e j ≠ p) (he_inj : Function.Injective e)
    (hpL : C.leftVars p = {1, 2}) (hpR : C.rightVars p = {0, 3})
    (h0L : vars C (e 0) (d 0) = {0}) (h0R : vars C (e 0) (!(d 0)) = {5})
    (h1L : vars C (e 1) (d 1) = {1, 5}) (h1R : vars C (e 1) (!(d 1)) = {2, 3})
    (h2L : vars C (e 2) (d 2) = {4, 7}) (h2R : vars C (e 2) (!(d 2)) = {6, 8})
    (h3L : vars C (e 3) (d 3) = {4, 8}) (h3R : vars C (e 3) (!(d 3)) = {6, 7}) : False := by
  have hp : p ∉ C.outGates := not_out_of_row_true C sep p 1 (raw_side_true C p false (rows 1)
    ⟨2, by simp [vars, hpL], by decide⟩ ⟨3, by simp [vars, hpR], by decide⟩)
  have h0 : e 0 ∉ C.outGates := not_out_of_row_true C sep (e 0) 2 (raw_side_true C (e 0) (d 0) (rows 2)
    ⟨0, by simp [h0L], by decide⟩ ⟨5, by simp [h0R], by decide⟩)
  have h1 : e 1 ∉ C.outGates := not_out_of_row_true C sep (e 1) 6 (raw_side_true C (e 1) (d 1) (rows 6)
    ⟨1, by simp [h1L], by decide⟩ ⟨2, by simp [h1R], by decide⟩)
  have h2 : e 2 ∉ C.outGates := not_out_of_row_true C sep (e 2) 9 (raw_side_true C (e 2) (d 2) (rows 9)
    ⟨7, by simp [h2L], by decide⟩ ⟨6, by simp [h2R], by decide⟩)
  have h3 : e 3 ∉ C.outGates := not_out_of_row_true C sep (e 3) 7 (raw_side_true C (e 3) (d 3) (rows 7)
    ⟨4, by simp [h3L], by decide⟩ ⟨7, by simp [h3R], by decide⟩)
  obtain ⟨j, hj, _⟩ := eval_true_exists_out C sep _ ((sep 0).2 1 (by decide))
  rcases five_exhaust C sz p e he_ne he_inj j with hj' | hj' | hj' | hj' | hj' <;> rw [hj'] at hj
  · exact hp hj
  · exact h0 hj
  · exact h1 hj
  · exact h2 hj
  · exact h3 hj

theorem set1A_impossible (C : AndCountCircuit 9) (sz : C.size = 5) (sep : SeparatesRows C)
    (p : Fin C.size) (early : Early C p) (e : Fin 4 → Fin C.size) (d : Fin 4 → Bool)
    (he_ne : ∀ j, e j ≠ p) (he_inj : Function.Injective e)
    (hpL : C.leftVars p = {1, 2}) (hpR : C.rightVars p = {0, 3})
    (h0L : vars C (e 0) (d 0) = {0, 1, 5}) (h0R : vars C (e 0) (!(d 0)) = {2, 3})
    (h1L : vars C (e 1) (d 1) = {4, 8}) (h1R : vars C (e 1) (!(d 1)) = {6, 7})
    (h2L : vars C (e 2) (d 2) = {4, 7}) (h2R : vars C (e 2) (!(d 2)) = {6, 8})
    (h3L : vars C (e 3) (d 3) = {5}) (h3R : vars C (e 3) (!(d 3)) = ∅) : False := by
  have hp_f : C.gateVal (rows 1) p = true := raw_side_true C p false (rows 1)
    ⟨2, by simp [vars, hpL], by decide⟩ ⟨3, by simp [vars, hpR], by decide⟩
  have h0_f : C.gateVal (rows 0) (e 0) = true := raw_side_true C (e 0) (d 0) (rows 0)
    ⟨0, by simp [h0L], by decide⟩ ⟨3, by simp [h0R], by decide⟩
  have h1_f : C.gateVal (rows 7) (e 1) = true := raw_side_true C (e 1) (d 1) (rows 7)
    ⟨4, by simp [h1L], by decide⟩ ⟨7, by simp [h1R], by decide⟩
  have h2_f : C.gateVal (rows 9) (e 2) = true := raw_side_true C (e 2) (d 2) (rows 9)
    ⟨7, by simp [h2L], by decide⟩ ⟨6, by simp [h2R], by decide⟩
  have only_safe (j : Fin C.size) (hj : ∀ r, C.gateVal (rows r) j = false) : j = e 3 := by
    rcases five_exhaust C sz p e he_ne he_inj j with hj' | hj' | hj' | hj' | hj'
    · have := hj 1; rw [hj'] at this; simp [hp_f] at this
    · have := hj 0; rw [hj'] at this; simp [h0_f] at this
    · have := hj 7; rw [hj'] at this; simp [h1_f] at this
    · have := hj 9; rw [hj'] at this; simp [h2_f] at this
    · exact hj'
  have out_eq (j : Fin C.size) (hj : j ∈ C.outGates) : j = e 3 :=
    only_safe j (fun r => Bool.eq_false_iff.mpr fun ht => not_out_of_row_true C sep j r ht hj)
  have h3_one (r : Fin 16) (u : V) (hu : u ∉ rows r) : C.gateVal (insert u (rows r)) (e 3) = true := by
    obtain ⟨j, hj, hg⟩ := eval_true_exists_out C sep _ ((sep r).2 u hu)
    rwa [out_eq j hj] at hg
  have h3_out : e 3 ∈ C.outGates := by
    obtain ⟨j, hj, _⟩ := eval_true_exists_out C sep _ ((sep 0).2 1 (by decide))
    rwa [out_eq j hj] at hj
  have h3_row (r : Fin 16) : C.gateVal (rows r) (e 3) = false :=
    Bool.eq_false_iff.mpr fun ht => not_out_of_row_true C sep (e 3) r ht h3_out
  have hp_min : ∀ j : Fin C.size, ¬ j < p := by
    intro j hjp
    have hj3 : j = e 3 := only_safe j (early j hjp)
    subst hj3
    have hno : ∀ k : Fin C.size, ¬ k < e 3 := by
      intro k hk
      have hk3 : k = e 3 := only_safe k (early k (lt_trans hk hjp))
      exact lt_irrefl _ (hk3 ▸ hk)
    have ht := h3_one 0 1 (by decide)
    have hs := (gate_iff C (e 3) _).mp ht (!(d 3))
    rcases hs with ⟨v, hv, _⟩ | ⟨k, hk, _⟩
    · simp [h3R] at hv
    · exact hno k (Finset.mem_filter.mp hk).2
  have ins5_eq (r : Fin 16) (h0r : (0 : V) ∈ rows r) :
      ∀ j : Fin C.size, j < e 3 → C.gateVal (insert 5 (rows r)) j = C.gateVal (rows r) j := by
    intro j
    induction j using ((wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction) with
    | h j ih =>
      intro hj3
      rw [Bool.eq_iff_iff, gate_iff, gate_iff]
      have side_eq (b : Bool) : onSide C j b (insert 5 (rows r)) ↔ onSide C j b (rows r) := by
        have ref_eq : (∃ k ∈ refs C j b, C.gateVal (insert 5 (rows r)) k = true) ↔
            (∃ k ∈ refs C j b, C.gateVal (rows r) k = true) := by
          constructor
          · rintro ⟨k, hk, hkt⟩
            have hkj : k < j := (Finset.mem_filter.mp hk).2
            exact ⟨k, hk, (ih k hkj (lt_trans hkj hj3)).symm.trans hkt⟩
          · rintro ⟨k, hk, hkt⟩
            have hkj : k < j := (Finset.mem_filter.mp hk).2
            exact ⟨k, hk, (ih k hkj (lt_trans hkj hj3)).trans hkt⟩
        have var_eq : (∃ v ∈ vars C j b, v ∈ insert 5 (rows r)) ↔ (∃ v ∈ vars C j b, v ∈ rows r) := by
          constructor
          · rintro ⟨v, hv, hvi⟩
            rcases Finset.mem_insert.mp hvi with rfl | hvr
            · have hne3 : j ≠ e 3 := ne_of_lt hj3
              rcases five_exhaust C sz p e he_ne he_inj j with hj' | hj' | hj' | hj' | hj'
              · rw [hj'] at hv
                cases b
                · simp only [vars, Bool.false_eq_true, ↓reduceIte, hpL] at hv; exfalso; revert hv; decide
                · simp only [vars, ↓reduceIte, hpR] at hv; exfalso; revert hv; decide
              · rw [hj'] at hv ⊢
                by_cases hbd : b = d 0
                · rw [hbd]; exact ⟨0, by simp [h0L], h0r⟩
                · rw [bool_ne_eq_not hbd, h0R] at hv; exfalso; revert hv; decide
              · rw [hj'] at hv
                by_cases hbd : b = d 1
                · rw [hbd, h1L] at hv; exfalso; revert hv; decide
                · rw [bool_ne_eq_not hbd, h1R] at hv; exfalso; revert hv; decide
              · rw [hj'] at hv
                by_cases hbd : b = d 2
                · rw [hbd, h2L] at hv; exfalso; revert hv; decide
                · rw [bool_ne_eq_not hbd, h2R] at hv; exfalso; revert hv; decide
              · exact (hne3 hj').elim
            · exact ⟨v, hv, hvr⟩
          · rintro ⟨v, hv, hvr⟩; exact ⟨v, hv, Finset.mem_insert_of_mem hvr⟩
        exact or_congr var_eq ref_eq
      exact forall_congr' side_eq
  have h3_sideL_off (r : Fin 16) (h0r : (0 : V) ∈ rows r) (h5r : (5 : V) ∉ rows r) :
      ¬ onSide C (e 3) (d 3) (rows r) := by
    have ht := h3_one r 5 h5r
    have hs := (gate_iff C (e 3) _).mp ht (!(d 3))
    have hs_row : onSide C (e 3) (!(d 3)) (rows r) := by
      rcases hs with ⟨v, hv, _⟩ | ⟨k, hk, hkt⟩
      · simp [h3R] at hv
      · exact Or.inr ⟨k, hk, (ins5_eq r h0r k (Finset.mem_filter.mp hk).2).symm.trans hkt⟩
    have hnot := not_onSide_other C (e 3) (!(d 3)) (rows r) (h3_row r) hs_row
    simpa using hnot
  have h3_off0 := h3_sideL_off 0 (by decide) (by decide)
  have h3_off7 := h3_sideL_off 7 (by decide) (by decide)
  let U : Finset V := insert 4 (rows 6)
  have hp_U : C.gateVal U p = false := gate_false_of_not_onSide C p true U (by
    rintro (⟨v, hv, hvu⟩ | ⟨k, hk, _⟩)
    · simp only [vars, ↓reduceIte, hpR] at hv
      revert v hv hvu; decide
    · exact hp_min k (Finset.mem_filter.mp hk).2)
  have h3_U := h3_one 6 4 (by decide)
  have hs3_U := (gate_iff C (e 3) U).mp h3_U (d 3)
  rcases hs3_U with ⟨v, hv, hvu⟩ | ⟨k, hk, hkt⟩
  · rw [h3L] at hv; revert v hv hvu; decide
  · have hk3 : k < e 3 := (Finset.mem_filter.mp hk).2
    have hk_r0 : C.gateVal (rows 0) k = false :=
      Bool.eq_false_iff.mpr fun ht => h3_off0 (Or.inr ⟨k, hk, ht⟩)
    have hk_r7 : C.gateVal (rows 7) k = false :=
      Bool.eq_false_iff.mpr fun ht => h3_off7 (Or.inr ⟨k, hk, ht⟩)
    rcases five_exhaust C sz p e he_ne he_inj k with hk' | hk' | hk' | hk' | hk'
    · rw [hk'] at hkt; simp [hp_U] at hkt
    · rw [hk'] at hk_r0; simp [h0_f] at hk_r0
    · rw [hk'] at hk_r7; simp [h1_f] at hk_r7
    · rw [hk'] at hk3 hk_r0 hk_r7 hkt
      have h2_on0 : onSide C (e 2) (d 2) (rows 0) := Or.inl ⟨4, by simp [h2L], by decide⟩
      have h2_on7 : onSide C (e 2) (d 2) (rows 7) := Or.inl ⟨4, by simp [h2L], by decide⟩
      have hs2_U := (gate_iff C (e 2) U).mp hkt (!(d 2))
      rcases hs2_U with ⟨v, hv, hvu⟩ | ⟨m, hm, hmt⟩
      · rw [h2R] at hv; revert v hv hvu; decide
      · have hm2 : m < e 2 := (Finset.mem_filter.mp hm).2
        have hm_r0 := ref_false_of_other_on C (e 2) (d 2) (rows 0) hk_r0 h2_on0 hm
        have hm_r7 := ref_false_of_other_on C (e 2) (d 2) (rows 7) hk_r7 h2_on7 hm
        rcases five_exhaust C sz p e he_ne he_inj m with hm' | hm' | hm' | hm' | hm'
        · rw [hm'] at hmt; simp [hp_U] at hmt
        · rw [hm'] at hm_r0; simp [h0_f] at hm_r0
        · rw [hm'] at hm_r7; simp [h1_f] at hm_r7
        · rw [hm'] at hm2; exact lt_irrefl _ hm2
        · rw [hm'] at hm2; exact lt_irrefl _ (lt_trans hm2 hk3)
    · rw [hk'] at hk3; exact lt_irrefl _ hk3

theorem case2_impossible (C : AndCountCircuit 9) (sz : C.size = 5) (sep : SeparatesRows C)
    (p : Fin C.size) (early : Early C p) (e : Fin 4 → Fin C.size) (d : Fin 4 → Bool)
    (he_ne : ∀ j, e j ≠ p) (he_inj : Function.Injective e)
    (hpL : C.leftVars p = {4, 7}) (hpR : C.rightVars p = {5, 8})
    (h0L : vars C (e 0) (d 0) = {0}) (h0R : vars C (e 0) (!(d 0)) = {1, 2})
    (h1L : vars C (e 1) (d 1) = {4}) (h1R : vars C (e 1) (!(d 1)) = {1, 6})
    (h2L : vars C (e 2) (d 2) = {7, 8}) (h2R : vars C (e 2) (!(d 2)) = {3, 6})
    (h3L : vars C (e 3) (d 3) = {5}) (h3R : vars C (e 3) (!(d 3)) = {2, 3}) : False := by
  have hp_r2 : C.gateVal (rows 2) p = true := raw_side_true C p false (rows 2)
    ⟨4, by simp [vars, hpL], by decide⟩ ⟨5, by simp [vars, hpR], by decide⟩
  have h2_r9 : C.gateVal (rows 9) (e 2) = true := raw_side_true C (e 2) (d 2) (rows 9)
    ⟨7, by simp [h2L], by decide⟩ ⟨6, by simp [h2R], by decide⟩
  have h2_r12 : C.gateVal (rows 12) (e 2) = true := raw_side_true C (e 2) (d 2) (rows 12)
    ⟨8, by simp [h2L], by decide⟩ ⟨3, by simp [h2R], by decide⟩
  have hp_not_out : p ∉ C.outGates := not_out_of_row_true C sep p 2 hp_r2
  have h2_not_out : e 2 ∉ C.outGates := not_out_of_row_true C sep (e 2) 9 h2_r9
  have h0_on2 : onSide C (e 0) (d 0) (rows 2) := Or.inl ⟨0, by simp [h0L], by decide⟩
  have h0_on9 : onSide C (e 0) (d 0) (rows 9) := Or.inl ⟨0, by simp [h0L], by decide⟩
  have h0_on12 : onSide C (e 0) (d 0) (rows 12) := Or.inl ⟨0, by simp [h0L], by decide⟩
  have h1_on2 : onSide C (e 1) (d 1) (rows 2) := Or.inl ⟨4, by simp [h1L], by decide⟩
  have h1_on9 : onSide C (e 1) (!(d 1)) (rows 9) := Or.inl ⟨6, by simp [h1R], by decide⟩
  have h3_on2 : onSide C (e 3) (d 3) (rows 2) := Or.inl ⟨5, by simp [h3L], by decide⟩
  have h3_on12 : onSide C (e 3) (!(d 3)) (rows 12) := Or.inl ⟨3, by simp [h3R], by decide⟩
  have out_13 (U : Finset V) (hU : C.eval U = true) (h1U : (1 : V) ∉ U) (h2U : (2 : V) ∉ U) :
      (C.gateVal (rows 2) (e 1) = false ∧ C.gateVal (rows 9) (e 1) = false ∧
        C.gateVal (rows 12) (e 1) = false ∧ C.gateVal U (e 1) = true) ∨
      (C.gateVal (rows 2) (e 3) = false ∧ C.gateVal (rows 9) (e 3) = false ∧
        C.gateVal (rows 12) (e 3) = false ∧ C.gateVal U (e 3) = true) := by
    obtain ⟨j, hj, hjt⟩ := eval_true_exists_out C sep U hU
    have hjr (r : Fin 16) : C.gateVal (rows r) j = false :=
      Bool.eq_false_iff.mpr fun ht => not_out_of_row_true C sep j r ht hj
    rcases five_exhaust C sz p e he_ne he_inj j with hj' | hj' | hj' | hj' | hj'
    · rw [hj'] at hj; exact (hp_not_out hj).elim
    · rw [hj'] at hjt
      rcases (gate_iff C (e 0) U).mp hjt (!(d 0)) with ⟨v, hv, hvu⟩ | ⟨k, hk, hkt⟩
      · rw [h0R] at hv; simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;> contradiction
      · have hk2 := ref_false_of_other_on C (e 0) (d 0) (rows 2) (hj' ▸ hjr 2) h0_on2 hk
        have hk9 := ref_false_of_other_on C (e 0) (d 0) (rows 9) (hj' ▸ hjr 9) h0_on9 hk
        have hk12 := ref_false_of_other_on C (e 0) (d 0) (rows 12) (hj' ▸ hjr 12) h0_on12 hk
        have hklt : k < e 0 := (Finset.mem_filter.mp hk).2
        rcases five_exhaust C sz p e he_ne he_inj k with hk' | hk' | hk' | hk' | hk'
        · rw [hk'] at hk2; simp [hp_r2] at hk2
        · rw [hk'] at hklt; exact (lt_irrefl _ hklt).elim
        · rw [hk'] at hk2 hk9 hk12 hkt; exact Or.inl ⟨hk2, hk9, hk12, hkt⟩
        · rw [hk'] at hk9; simp [h2_r9] at hk9
        · rw [hk'] at hk2 hk9 hk12 hkt; exact Or.inr ⟨hk2, hk9, hk12, hkt⟩
    · exact Or.inl ⟨hj' ▸ hjr 2, hj' ▸ hjr 9, hj' ▸ hjr 12, hj' ▸ hjt⟩
    · rw [hj'] at hj; exact (h2_not_out hj).elim
    · exact Or.inr ⟨hj' ▸ hjr 2, hj' ▸ hjr 9, hj' ▸ hjr 12, hj' ▸ hjt⟩
  let U1 : Finset V := insert 3 (rows 9)
  let U2 : Finset V := insert 8 (rows 7)
  let U3 : Finset V := insert 7 (rows 14)
  have hU1 : C.eval U1 = true := (sep 9).2 3 (by decide)
  have hU2 : C.eval U2 = true := (sep 7).2 8 (by decide)
  have hU3 : C.eval U3 = true := (sep 14).2 7 (by decide)
  have hp_r9 : C.gateVal (rows 9) p = false := gate_false_of_not_onSide C p true (rows 9) (by
    rintro (⟨v, hv, hvr⟩ | ⟨k, hk, hkt⟩)
    · simp only [vars, ↓reduceIte, hpR] at hv; revert v hv hvr; decide
    · simp [early k (Finset.mem_filter.mp hk).2 9] at hkt)
  by_cases h1_9 : C.gateVal (rows 9) (e 1) = false
  · by_cases h3_12 : C.gateVal (rows 12) (e 3) = false
    · have h3_9 : C.gateVal (rows 9) (e 3) = false := by
        by_contra h3t
        have h3t' : C.gateVal (rows 9) (e 3) = true := by cases h : C.gateVal (rows 9) (e 3) <;> simp_all
        have h0_9_12 : C.gateVal (rows 9) (e 0) = true → C.gateVal (rows 12) (e 0) = true := by
          intro h0t
          rcases (gate_iff C (e 0) (rows 9)).mp h0t (!(d 0)) with ⟨v, hv, hvr⟩ | ⟨k, hk, hkt⟩
          · rw [h0R] at hv; exfalso; revert v hv hvr; decide
          · have hklt : k < e 0 := (Finset.mem_filter.mp hk).2
            rcases five_exhaust C sz p e he_ne he_inj k with hk' | hk' | hk' | hk' | hk'
            · rw [hk'] at hkt; simp [hp_r9] at hkt
            · rw [hk'] at hklt; exact (lt_irrefl _ hklt).elim
            · rw [hk'] at hkt; simp [h1_9] at hkt
            · rw [hk'] at hk
              exact gate_true_of_both_sides C (e 0) (d 0) (rows 12) h0_on12 (Or.inr ⟨e 2, hk, h2_r12⟩)
            · rw [hk'] at hklt
              exfalso
              rcases (gate_iff C (e 3) (rows 9)).mp h3t' (d 3) with ⟨v, hv, hvr⟩ | ⟨m, hm, hmt⟩
              · rw [h3L] at hv; revert v hv hvr; decide
              · have hmlt : m < e 3 := (Finset.mem_filter.mp hm).2
                have hm12 := ref_false_of_other_on C (e 3) (!(d 3)) (rows 12) h3_12 h3_on12 (by simpa using hm)
                rcases five_exhaust C sz p e he_ne he_inj m with hm' | hm' | hm' | hm' | hm'
                · rw [hm'] at hmt; simp [hp_r9] at hmt
                · rw [hm'] at hmlt; exact lt_irrefl _ (lt_trans hklt hmlt)
                · rw [hm'] at hmt; simp [h1_9] at hmt
                · rw [hm'] at hm12; simp [h2_r12] at hm12
                · rw [hm'] at hmlt; exact lt_irrefl _ hmlt
        rcases (gate_iff C (e 3) (rows 9)).mp h3t' (d 3) with ⟨v, hv, hvr⟩ | ⟨m, hm, hmt⟩
        · rw [h3L] at hv; revert v hv hvr; decide
        · have hmlt : m < e 3 := (Finset.mem_filter.mp hm).2
          have hm12 := ref_false_of_other_on C (e 3) (!(d 3)) (rows 12) h3_12 h3_on12 (by simpa using hm)
          rcases five_exhaust C sz p e he_ne he_inj m with hm' | hm' | hm' | hm' | hm'
          · rw [hm'] at hmt; simp [hp_r9] at hmt
          · rw [hm'] at hmt hm12; simp [h0_9_12 hmt] at hm12
          · rw [hm'] at hmt; simp [h1_9] at hmt
          · rw [hm'] at hm12; simp [h2_r12] at hm12
          · rw [hm'] at hmlt; exact lt_irrefl _ hmlt
      have h0_9_12 : C.gateVal (rows 12) (e 0) = false → C.gateVal (rows 9) (e 0) = false := by
        intro h012
        apply Bool.eq_false_iff.mpr
        intro h09
        rcases (gate_iff C (e 0) (rows 9)).mp h09 (!(d 0)) with ⟨v, hv, hvr⟩ | ⟨k, hk, hkt⟩
        · rw [h0R] at hv; revert v hv hvr; decide
        · have hk12 := ref_false_of_other_on C (e 0) (d 0) (rows 12) h012 h0_on12 hk
          have hklt : k < e 0 := (Finset.mem_filter.mp hk).2
          rcases five_exhaust C sz p e he_ne he_inj k with hk' | hk' | hk' | hk' | hk'
          · rw [hk'] at hkt; simp [hp_r9] at hkt
          · rw [hk'] at hklt; exact lt_irrefl _ hklt
          · rw [hk'] at hkt; simp [h1_9] at hkt
          · rw [hk'] at hk12; simp [h2_r12] at hk12
          · rw [hk'] at hkt; simp [h3_9] at hkt
      have killU1 (j : Fin C.size) :
          j ≠ e 2 → (j = e 0 → C.gateVal (rows 9) (e 0) = false) → C.gateVal U1 j = false := by
        induction j using ((wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction) with
        | h j ih =>
          intro hne2 h0f
          rcases five_exhaust C sz p e he_ne he_inj j with hj' | hj' | hj' | hj' | hj'
          · rw [hj'] at ih ⊢
            exact gate_false_of_not_onSide C p true U1 (by
              rintro (⟨v, hv, hvu⟩ | ⟨k, hk, hkt⟩)
              · simp only [vars, ↓reduceIte, hpR] at hv; revert v hv hvu; decide
              · have hklt : k < p := (Finset.mem_filter.mp hk).2
                have hk9 := early k hklt 9
                have hne : k ≠ e 2 := fun h => by simp [h, h2_r9] at hk9
                have hkf := ih k hklt hne (fun h => h ▸ hk9)
                simp [hkf] at hkt)
          · rw [hj'] at ih h0f ⊢
            exact gate_false_of_not_onSide C (e 0) (!(d 0)) U1 (by
              rintro (⟨v, hv, hvu⟩ | ⟨k, hk, hkt⟩)
              · rw [h0R] at hv; revert v hv hvu; decide
              · have hklt : k < e 0 := (Finset.mem_filter.mp hk).2
                have hk9 := ref_false_of_other_on C (e 0) (d 0) (rows 9) (h0f rfl) h0_on9 hk
                have hne : k ≠ e 2 := fun h => by simp [h, h2_r9] at hk9
                have hkf := ih k hklt hne (fun h => h ▸ hk9)
                simp [hkf] at hkt)
          · rw [hj'] at ih ⊢
            exact gate_false_of_not_onSide C (e 1) (d 1) U1 (by
              rintro (⟨v, hv, hvu⟩ | ⟨k, hk, hkt⟩)
              · rw [h1L] at hv; revert v hv hvu; decide
              · have hklt : k < e 1 := (Finset.mem_filter.mp hk).2
                have hk9 := ref_false_of_other_on C (e 1) (!(d 1)) (rows 9) h1_9 h1_on9 (by simpa using hk)
                have hne : k ≠ e 2 := fun h => by simp [h, h2_r9] at hk9
                have hkf := ih k hklt hne (fun h => h ▸ hk9)
                simp [hkf] at hkt)
          · exact (hne2 hj').elim
          · rw [hj'] at ih ⊢
            exact gate_false_of_not_onSide C (e 3) (d 3) U1 (by
              rintro (⟨v, hv, hvu⟩ | ⟨k, hk, hkt⟩)
              · rw [h3L] at hv; revert v hv hvu; decide
              · have hklt : k < e 3 := (Finset.mem_filter.mp hk).2
                have hk12 := ref_false_of_other_on C (e 3) (!(d 3)) (rows 12) h3_12 h3_on12 (by simpa using hk)
                have hne : k ≠ e 2 := fun h => by simp [h, h2_r12] at hk12
                have hkf := ih k hklt hne (fun h => h0_9_12 (h ▸ hk12))
                simp [hkf] at hkt)
      rcases out_13 U1 hU1 (by decide) (by decide) with ⟨_, _, _, h1t⟩ | ⟨_, _, _, h3t⟩
      · have := killU1 (e 1) (he_inj.ne (by decide)) (fun h => (he_inj.ne (by decide : (1 : Fin 4) ≠ 0) h).elim)
        simp [this] at h1t
      · have := killU1 (e 3) (he_inj.ne (by decide)) (fun h => (he_inj.ne (by decide : (3 : Fin 4) ≠ 0) h).elim)
        simp [this] at h3t
    · have h3_12t : C.gateVal (rows 12) (e 3) = true := by cases h : C.gateVal (rows 12) (e 3) <;> simp_all
      have get1 (U : Finset V) (hU : C.eval U = true) (h1U : (1 : V) ∉ U) (h2U : (2 : V) ∉ U) :
          C.gateVal (rows 2) (e 1) = false ∧ C.gateVal (rows 9) (e 1) = false ∧
          C.gateVal (rows 12) (e 1) = false ∧ C.gateVal U (e 1) = true := by
        rcases out_13 U hU h1U h2U with h | ⟨_, _, h3f, _⟩
        · exact h
        · simp [h3_12t] at h3f
      obtain ⟨h1_2, h1_9', h1_12, h1_U1⟩ := get1 U1 hU1 (by decide) (by decide)
      obtain ⟨_, _, _, h1_U3⟩ := get1 U3 hU3 (by decide) (by decide)
      have hp_U1 : C.gateVal U1 p = false := by
        have hlt_false (k : Fin C.size) : k < p → C.gateVal U1 k = false := by
          induction k using ((wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction) with
          | h k ih =>
            intro hkp
            have hk9 := early k hkp 9
            have hk12 := early k hkp 12
            rcases five_exhaust C sz p e he_ne he_inj k with hk' | hk' | hk' | hk' | hk'
            · rw [hk'] at hkp; exact (lt_irrefl _ hkp).elim
            · rw [hk'] at ih hkp ⊢
              exact gate_false_of_not_onSide C (e 0) (!(d 0)) U1 (by
                rintro (⟨v, hv, hvu⟩ | ⟨m, hm, hmt⟩)
                · rw [h0R] at hv; revert v hv hvu; decide
                · have hmlt : m < e 0 := (Finset.mem_filter.mp hm).2
                  simp [ih m hmlt (lt_trans hmlt hkp)] at hmt)
            · rw [hk'] at ih hkp ⊢
              exact gate_false_of_not_onSide C (e 1) (d 1) U1 (by
                rintro (⟨v, hv, hvu⟩ | ⟨m, hm, hmt⟩)
                · rw [h1L] at hv; revert v hv hvu; decide
                · have hmlt : m < e 1 := (Finset.mem_filter.mp hm).2
                  simp [ih m hmlt (lt_trans hmlt hkp)] at hmt)
            · rw [hk'] at hk9; simp [h2_r9] at hk9
            · rw [hk'] at hk12; simp [h3_12t] at hk12
        exact gate_false_of_not_onSide C p true U1 (by
          rintro (⟨v, hv, hvu⟩ | ⟨k, hk, hkt⟩)
          · simp only [vars, ↓reduceIte, hpR] at hv; revert v hv hvu; decide
          · simp [hlt_false k (Finset.mem_filter.mp hk).2] at hkt)
      have h1_on12 : onSide C (e 1) (d 1) (rows 12) := by
        rcases (gate_iff C (e 1) U1).mp h1_U1 (d 1) with ⟨v, hv, hvu⟩ | ⟨a, ha, hat⟩
        · rw [h1L] at hv; exfalso; revert v hv hvu; decide
        · have halt : a < e 1 := (Finset.mem_filter.mp ha).2
          have ha9 := ref_false_of_other_on C (e 1) (!(d 1)) (rows 9) h1_9' h1_on9 (by simpa using ha)
          rcases five_exhaust C sz p e he_ne he_inj a with ha' | ha' | ha' | ha' | ha'
          · rw [ha'] at hat; simp [hp_U1] at hat
          · rw [ha'] at ha halt ha9 hat
            have h0_12 : C.gateVal (rows 12) (e 0) = true := by
              rcases (gate_iff C (e 0) U1).mp hat (!(d 0)) with ⟨v, hv, hvu⟩ | ⟨c, hc, hct⟩
              · rw [h0R] at hv; exfalso; revert v hv hvu; decide
              · have hclt : c < e 0 := (Finset.mem_filter.mp hc).2
                have hc9 := ref_false_of_other_on C (e 0) (d 0) (rows 9) ha9 h0_on9 hc
                rcases five_exhaust C sz p e he_ne he_inj c with hc' | hc' | hc' | hc' | hc'
                · rw [hc'] at hct; simp [hp_U1] at hct
                · rw [hc'] at hclt; exact (lt_irrefl _ hclt).elim
                · rw [hc'] at hclt; exact (lt_irrefl _ (lt_trans hclt halt)).elim
                · rw [hc'] at hc9; simp [h2_r9] at hc9
                · rw [hc'] at hc
                  exact gate_true_of_both_sides C (e 0) (d 0) (rows 12) h0_on12 (Or.inr ⟨e 3, hc, h3_12t⟩)
            exact Or.inr ⟨e 0, ha, h0_12⟩
          · rw [ha'] at halt; exact (lt_irrefl _ halt).elim
          · rw [ha'] at ha9; simp [h2_r9] at ha9
          · rw [ha'] at ha; exact Or.inr ⟨e 3, ha, h3_12t⟩
      rcases (gate_iff C (e 1) U3).mp h1_U3 (!(d 1)) with ⟨v, hv, hvu⟩ | ⟨b, hb, hbt⟩
      · rw [h1R] at hv; revert v hv hvu; decide
      · have hblt : b < e 1 := (Finset.mem_filter.mp hb).2
        have hb2 := ref_false_of_other_on C (e 1) (d 1) (rows 2) h1_2 h1_on2 hb
        have hb12 := ref_false_of_other_on C (e 1) (d 1) (rows 12) h1_12 h1_on12 hb
        rcases five_exhaust C sz p e he_ne he_inj b with hb' | hb' | hb' | hb' | hb'
        · rw [hb'] at hb2; simp [hp_r2] at hb2
        · rw [hb'] at hblt hb2 hb12 hbt
          rcases (gate_iff C (e 0) U3).mp hbt (!(d 0)) with ⟨v, hv, hvu⟩ | ⟨c, hc, _⟩
          · rw [h0R] at hv; revert v hv hvu; decide
          · have hclt : c < e 0 := (Finset.mem_filter.mp hc).2
            have hc2 := ref_false_of_other_on C (e 0) (d 0) (rows 2) hb2 h0_on2 hc
            have hc12 := ref_false_of_other_on C (e 0) (d 0) (rows 12) hb12 h0_on12 hc
            rcases five_exhaust C sz p e he_ne he_inj c with hc' | hc' | hc' | hc' | hc'
            · rw [hc'] at hc2; simp [hp_r2] at hc2
            · rw [hc'] at hclt; exact lt_irrefl _ hclt
            · rw [hc'] at hclt; exact lt_irrefl _ (lt_trans hclt hblt)
            · rw [hc'] at hc12; simp [h2_r12] at hc12
            · rw [hc'] at hc12; simp [h3_12t] at hc12
        · rw [hb'] at hblt; exact lt_irrefl _ hblt
        · rw [hb'] at hb12; simp [h2_r12] at hb12
        · rw [hb'] at hb12; simp [h3_12t] at hb12
  · have h1_9t : C.gateVal (rows 9) (e 1) = true := by cases h : C.gateVal (rows 9) (e 1) <;> simp_all
    have get3 (U : Finset V) (hU : C.eval U = true) (h1U : (1 : V) ∉ U) (h2U : (2 : V) ∉ U) :
        C.gateVal (rows 2) (e 3) = false ∧ C.gateVal (rows 9) (e 3) = false ∧
        C.gateVal (rows 12) (e 3) = false ∧ C.gateVal U (e 3) = true := by
      rcases out_13 U hU h1U h2U with ⟨_, h1f, _, _⟩ | h
      · simp [h1_9t] at h1f
      · exact h
    obtain ⟨h3_2, h3_9, h3_12', h3_U1⟩ := get3 U1 hU1 (by decide) (by decide)
    obtain ⟨_, _, _, h3_U2⟩ := get3 U2 hU2 (by decide) (by decide)
    have hp_U1 : C.gateVal U1 p = false := by
      have hlt_false (k : Fin C.size) : k < p → C.gateVal U1 k = false := by
        induction k using ((wellFounded_lt : WellFounded ((· < ·) : Fin C.size → Fin C.size → Prop)).induction) with
        | h k ih =>
          intro hkp
          have hk9 := early k hkp 9
          rcases five_exhaust C sz p e he_ne he_inj k with hk' | hk' | hk' | hk' | hk'
          · rw [hk'] at hkp; exact (lt_irrefl _ hkp).elim
          · rw [hk'] at ih hkp ⊢
            exact gate_false_of_not_onSide C (e 0) (!(d 0)) U1 (by
              rintro (⟨v, hv, hvu⟩ | ⟨m, hm, hmt⟩)
              · rw [h0R] at hv; revert v hv hvu; decide
              · have hmlt : m < e 0 := (Finset.mem_filter.mp hm).2
                simp [ih m hmlt (lt_trans hmlt hkp)] at hmt)
          · rw [hk'] at hk9; simp [h1_9t] at hk9
          · rw [hk'] at hk9; simp [h2_r9] at hk9
          · rw [hk'] at ih hkp ⊢
            exact gate_false_of_not_onSide C (e 3) (d 3) U1 (by
              rintro (⟨v, hv, hvu⟩ | ⟨m, hm, hmt⟩)
              · rw [h3L] at hv; revert v hv hvu; decide
              · have hmlt : m < e 3 := (Finset.mem_filter.mp hm).2
                simp [ih m hmlt (lt_trans hmlt hkp)] at hmt)
      exact gate_false_of_not_onSide C p true U1 (by
        rintro (⟨v, hv, hvu⟩ | ⟨k, hk, hkt⟩)
        · simp only [vars, ↓reduceIte, hpR] at hv; revert v hv hvu; decide
        · simp [hlt_false k (Finset.mem_filter.mp hk).2] at hkt)
    have h3_on9 : onSide C (e 3) (d 3) (rows 9) := by
      rcases (gate_iff C (e 3) U1).mp h3_U1 (d 3) with ⟨v, hv, hvu⟩ | ⟨a, ha, hat⟩
      · rw [h3L] at hv; exfalso; revert v hv hvu; decide
      · have halt : a < e 3 := (Finset.mem_filter.mp ha).2
        have ha12 := ref_false_of_other_on C (e 3) (!(d 3)) (rows 12) h3_12' h3_on12 (by simpa using ha)
        rcases five_exhaust C sz p e he_ne he_inj a with ha' | ha' | ha' | ha' | ha'
        · rw [ha'] at hat; simp [hp_U1] at hat
        · rw [ha'] at ha halt ha12 hat
          have h0_9 : C.gateVal (rows 9) (e 0) = true := by
            rcases (gate_iff C (e 0) U1).mp hat (!(d 0)) with ⟨v, hv, hvu⟩ | ⟨c, hc, hct⟩
            · rw [h0R] at hv; exfalso; revert v hv hvu; decide
            · have hclt : c < e 0 := (Finset.mem_filter.mp hc).2
              have hc12 := ref_false_of_other_on C (e 0) (d 0) (rows 12) ha12 h0_on12 hc
              rcases five_exhaust C sz p e he_ne he_inj c with hc' | hc' | hc' | hc' | hc'
              · rw [hc'] at hct; simp [hp_U1] at hct
              · rw [hc'] at hclt; exact (lt_irrefl _ hclt).elim
              · rw [hc'] at hc
                exact gate_true_of_both_sides C (e 0) (d 0) (rows 9) h0_on9 (Or.inr ⟨e 1, hc, h1_9t⟩)
              · rw [hc'] at hc12; simp [h2_r12] at hc12
              · rw [hc'] at hclt; exact (lt_irrefl _ (lt_trans hclt halt)).elim
          exact Or.inr ⟨e 0, ha, h0_9⟩
        · rw [ha'] at ha; exact Or.inr ⟨e 1, ha, h1_9t⟩
        · rw [ha'] at ha12; simp [h2_r12] at ha12
        · rw [ha'] at halt; exact (lt_irrefl _ halt).elim
    rcases (gate_iff C (e 3) U2).mp h3_U2 (!(d 3)) with ⟨v, hv, hvu⟩ | ⟨b, hb, hbt⟩
    · rw [h3R] at hv; revert v hv hvu; decide
    · have hblt : b < e 3 := (Finset.mem_filter.mp hb).2
      have hb2 := ref_false_of_other_on C (e 3) (d 3) (rows 2) h3_2 h3_on2 hb
      have hb9 := ref_false_of_other_on C (e 3) (d 3) (rows 9) h3_9 h3_on9 hb
      rcases five_exhaust C sz p e he_ne he_inj b with hb' | hb' | hb' | hb' | hb'
      · rw [hb'] at hb2; simp [hp_r2] at hb2
      · rw [hb'] at hblt hb2 hb9 hbt
        rcases (gate_iff C (e 0) U2).mp hbt (!(d 0)) with ⟨v, hv, hvu⟩ | ⟨c, hc, _⟩
        · rw [h0R] at hv; revert v hv hvu; decide
        · have hclt : c < e 0 := (Finset.mem_filter.mp hc).2
          have hc2 := ref_false_of_other_on C (e 0) (d 0) (rows 2) hb2 h0_on2 hc
          have hc9 := ref_false_of_other_on C (e 0) (d 0) (rows 9) hb9 h0_on9 hc
          rcases five_exhaust C sz p e he_ne he_inj c with hc' | hc' | hc' | hc' | hc'
          · rw [hc'] at hc2; simp [hp_r2] at hc2
          · rw [hc'] at hclt; exact lt_irrefl _ hclt
          · rw [hc'] at hc9; simp [h1_9t] at hc9
          · rw [hc'] at hc9; simp [h2_r9] at hc9
          · rw [hc'] at hclt; exact lt_irrefl _ (lt_trans hclt hblt)
      · rw [hb'] at hb9; simp [h1_9t] at hb9
      · rw [hb'] at hb9; simp [h2_r9] at hb9
      · rw [hb'] at hblt; exact lt_irrefl _ hblt

theorem decode_6 : decode 6 = {1, 2} := by decide +kernel

theorem decode_9 : decode 9 = {0, 3} := by decide +kernel

theorem decode_144 : decode 144 = {4, 7} := by decide +kernel

theorem decode_288 : decode 288 = {5, 8} := by decide +kernel

def sat0Allowed : List (List ℕ) :=
  [[1, 1, 2, 2, 24, 65, 36, 40, 20],
   [1, 1, 2, 2, 36, 65, 24, 40, 20],
   [1, 8, 4, 4, 80, 10, 160, 96, 144],
   [1, 8, 4, 4, 80, 10, 160, 144, 96]]

def sat1Allowed : List (List ℕ) :=
  [[1, 10, 130, 160, 4, 64, 40, 16, 16]]

theorem sat0Allowed_ok : ∀ lf ∈ sat0Allowed, lf.length = 9 ∧ ∀ w ∈ lf, w < 256 := by
  decide +kernel

theorem sat1Allowed_ok : ∀ lf ∈ sat1Allowed, lf.length = 9 ∧ ∀ w ∈ lf, w < 256 := by
  decide +kernel

theorem circuitVars_of_symSlot (C : AndCountCircuit 9) (p : Fin C.size) (sz : C.size = 5)
    (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Bool) (lf : List ℕ)
    (hpos : ∀ v : V, (circuitPos C p sz (some v)).image (symSlot σ f) = slots (lf.getD v.val 256)) :
    let e : Fin 4 → Fin C.size := fun j => otherGate C p sz (σ.symm j)
    let d : Fin 4 → Bool := fun j => f (σ.symm j)
    (∀ j, e j ≠ p) ∧ Function.Injective e ∧
    (∀ (j : Fin 4) (v : V), v ∈ vars C (e j) (d j) ↔ (lf.getD v.val 256).testBit (2 * j.val) = true) ∧
    (∀ (j : Fin 4) (v : V), v ∈ vars C (e j) (!(d j)) ↔ (lf.getD v.val 256).testBit (2 * j.val + 1) = true) := by
  refine ⟨fun j => otherGate_ne C p sz (σ.symm j),
    (otherGate C p sz).injective.comp σ.symm.injective, ?_, ?_⟩
  · intro j v
    have hmem : (j, false) ∈ slots (lf.getD v.val 256) ↔ (lf.getD v.val 256).testBit (2 * j.val) = true := by
      simp [slots, slotId]
    rw [← hmem, ← hpos v]
    have hinv : symSlot σ f (σ.symm j, f (σ.symm j)) = (j, false) := by
      simp only [symSlot, Equiv.apply_symm_apply]
      cases f (σ.symm j) <;> rfl
    constructor
    · intro hv
      have hcp : (σ.symm j, f (σ.symm j)) ∈ circuitPos C p sz (some v) := (mem_circuitPos ..).mpr hv
      exact Finset.mem_image.mpr ⟨_, hcp, hinv⟩
    · intro hi
      rcases Finset.mem_image.mp hi with ⟨s, hs, hseq⟩
      have hse : s = (σ.symm j, f (σ.symm j)) := symSlot_injective σ f (hseq.trans hinv.symm)
      subst hse
      exact (mem_circuitPos ..).mp hs
  · intro j v
    have hmem : (j, true) ∈ slots (lf.getD v.val 256) ↔ (lf.getD v.val 256).testBit (2 * j.val + 1) = true := by
      simp [slots, slotId]
    rw [← hmem, ← hpos v]
    have hinv : symSlot σ f (σ.symm j, !(f (σ.symm j))) = (j, true) := by
      simp only [symSlot, Equiv.apply_symm_apply]
      cases f (σ.symm j) <;> rfl
    constructor
    · intro hv
      have hcp : (σ.symm j, !(f (σ.symm j))) ∈ circuitPos C p sz (some v) := (mem_circuitPos ..).mpr hv
      exact Finset.mem_image.mpr ⟨_, hcp, hinv⟩
    · intro hi
      rcases Finset.mem_image.mp hi with ⟨s, hs, hseq⟩
      have hse : s = (σ.symm j, !(f (σ.symm j))) := symSlot_injective σ f (hseq.trans hinv.symm)
      subst hse
      exact (mem_circuitPos ..).mp hs

theorem vars_eq_of_bitmask {C : AndCountCircuit 9} {i : Fin C.size} {b : Bool}
    (lf : List ℕ) (bit : ℕ)
    (h : ∀ v : V, v ∈ vars C i b ↔ (lf.getD v.val 256).testBit bit = true)
    (S : Finset V) (hS : ∀ v : V, decide (v ∈ S) = (lf.getD v.val 256).testBit bit) :
    vars C i b = S := by
  ext v
  rw [h v, ← hS v, decide_eq_true_eq]

theorem sat0_leaf_impossible {C : AndCountCircuit 9} {p : Fin C.size} (sz : C.size = 5)
    (sep : Separates C) (early : Early C p)
    (hpL : C.leftVars p = decode 6) (hpR : C.rightVars p = decode 9)
    (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Bool) (lf : List ℕ)
    (hmem : lf ∈ sat0Allowed)
    (hpos : ∀ v : V, (circuitPos C p sz (some v)).image (symSlot σ f) = slots (lf.getD v.val 256)) :
    False := by
  have hpL' : C.leftVars p = {1, 2} := hpL.trans decode_6
  have hpR' : C.rightVars p = {0, 3} := hpR.trans decode_9
  have hsepR : SeparatesRows C := separatesRows_of_separates sep
  obtain ⟨he_ne, he_inj, hl, hr⟩ := circuitVars_of_symSlot C p sz σ f lf hpos
  let e : Fin 4 → Fin C.size := fun j => otherGate C p sz (σ.symm j)
  let d : Fin 4 → Bool := fun j => f (σ.symm j)
  simp only [sat0Allowed, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · let p0213 : Fin 4 → Fin 4 := ![0, 2, 1, 3]
    let d0 : Fin 4 → Bool := ![d 0, d 2, !(d 1), d 3]
    have hp0213 : Function.Injective p0213 := by decide
    exact set1A_impossible C sz hsepR p early (fun j => e (p0213 j)) d0
      (fun j => he_ne (p0213 j)) (he_inj.comp hp0213) hpL' hpR'
      (vars_eq_of_bitmask [1, 1, 2, 2, 24, 65, 36, 40, 20] 0 (hl 0) {0, 1, 5} (by decide))
      (vars_eq_of_bitmask [1, 1, 2, 2, 24, 65, 36, 40, 20] 1 (hr 0) {2, 3} (by decide))
      (vars_eq_of_bitmask [1, 1, 2, 2, 24, 65, 36, 40, 20] 4 (hl 2) {4, 8} (by decide))
      (vars_eq_of_bitmask [1, 1, 2, 2, 24, 65, 36, 40, 20] 5 (hr 2) {6, 7} (by decide))
      (vars_eq_of_bitmask [1, 1, 2, 2, 24, 65, 36, 40, 20] 3 (hr 1) {4, 7} (by decide))
      (by simpa [d0, p0213, Bool.not_not] using vars_eq_of_bitmask [1, 1, 2, 2, 24, 65, 36, 40, 20] 2 (hl 1) {6, 8} (by decide))
      (vars_eq_of_bitmask [1, 1, 2, 2, 24, 65, 36, 40, 20] 6 (hl 3) {5} (by decide))
      (vars_eq_of_bitmask [1, 1, 2, 2, 24, 65, 36, 40, 20] 7 (hr 3) ∅ (by decide))
  · let d1 : Fin 4 → Bool := ![d 0, d 1, !(d 2), d 3]
    exact set1A_impossible C sz hsepR p early e d1 he_ne he_inj hpL' hpR'
      (vars_eq_of_bitmask [1, 1, 2, 2, 36, 65, 24, 40, 20] 0 (hl 0) {0, 1, 5} (by decide))
      (vars_eq_of_bitmask [1, 1, 2, 2, 36, 65, 24, 40, 20] 1 (hr 0) {2, 3} (by decide))
      (vars_eq_of_bitmask [1, 1, 2, 2, 36, 65, 24, 40, 20] 2 (hl 1) {4, 8} (by decide))
      (vars_eq_of_bitmask [1, 1, 2, 2, 36, 65, 24, 40, 20] 3 (hr 1) {6, 7} (by decide))
      (vars_eq_of_bitmask [1, 1, 2, 2, 36, 65, 24, 40, 20] 5 (hr 2) {4, 7} (by decide))
      (by simpa [d1, Bool.not_not] using vars_eq_of_bitmask [1, 1, 2, 2, 36, 65, 24, 40, 20] 4 (hl 2) {6, 8} (by decide))
      (vars_eq_of_bitmask [1, 1, 2, 2, 36, 65, 24, 40, 20] 6 (hl 3) {5} (by decide))
      (vars_eq_of_bitmask [1, 1, 2, 2, 36, 65, 24, 40, 20] 7 (hr 3) ∅ (by decide))
  · let p0132 : Fin 4 → Fin 4 := ![0, 1, 3, 2]
    let d2 : Fin 4 → Bool := ![d 0, !(d 1), d 3, d 2]
    have hp0132 : Function.Injective p0132 := by decide
    exact set1B_impossible C sz hsepR p (fun j => e (p0132 j)) d2
      (fun j => he_ne (p0132 j)) (he_inj.comp hp0132) hpL' hpR'
      (vars_eq_of_bitmask [1, 8, 4, 4, 80, 10, 160, 96, 144] 0 (hl 0) {0} (by decide))
      (vars_eq_of_bitmask [1, 8, 4, 4, 80, 10, 160, 96, 144] 1 (hr 0) {5} (by decide))
      (vars_eq_of_bitmask [1, 8, 4, 4, 80, 10, 160, 96, 144] 3 (hr 1) {1, 5} (by decide))
      (by simpa [d2, p0132, Bool.not_not] using vars_eq_of_bitmask [1, 8, 4, 4, 80, 10, 160, 96, 144] 2 (hl 1) {2, 3} (by decide))
      (vars_eq_of_bitmask [1, 8, 4, 4, 80, 10, 160, 96, 144] 6 (hl 3) {4, 7} (by decide))
      (vars_eq_of_bitmask [1, 8, 4, 4, 80, 10, 160, 96, 144] 7 (hr 3) {6, 8} (by decide))
      (vars_eq_of_bitmask [1, 8, 4, 4, 80, 10, 160, 96, 144] 4 (hl 2) {4, 8} (by decide))
      (vars_eq_of_bitmask [1, 8, 4, 4, 80, 10, 160, 96, 144] 5 (hr 2) {6, 7} (by decide))
  · let d3 : Fin 4 → Bool := ![d 0, !(d 1), d 2, d 3]
    exact set1B_impossible C sz hsepR p e d3 he_ne he_inj hpL' hpR'
      (vars_eq_of_bitmask [1, 8, 4, 4, 80, 10, 160, 144, 96] 0 (hl 0) {0} (by decide))
      (vars_eq_of_bitmask [1, 8, 4, 4, 80, 10, 160, 144, 96] 1 (hr 0) {5} (by decide))
      (vars_eq_of_bitmask [1, 8, 4, 4, 80, 10, 160, 144, 96] 3 (hr 1) {1, 5} (by decide))
      (by simpa [d3, Bool.not_not] using vars_eq_of_bitmask [1, 8, 4, 4, 80, 10, 160, 144, 96] 2 (hl 1) {2, 3} (by decide))
      (vars_eq_of_bitmask [1, 8, 4, 4, 80, 10, 160, 144, 96] 4 (hl 2) {4, 7} (by decide))
      (vars_eq_of_bitmask [1, 8, 4, 4, 80, 10, 160, 144, 96] 5 (hr 2) {6, 8} (by decide))
      (vars_eq_of_bitmask [1, 8, 4, 4, 80, 10, 160, 144, 96] 6 (hl 3) {4, 8} (by decide))
      (vars_eq_of_bitmask [1, 8, 4, 4, 80, 10, 160, 144, 96] 7 (hr 3) {6, 7} (by decide))

theorem sat1_leaf_impossible {C : AndCountCircuit 9} {p : Fin C.size} (sz : C.size = 5)
    (sep : Separates C) (early : Early C p)
    (hpL : C.leftVars p = decode 144) (hpR : C.rightVars p = decode 288)
    (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Bool) (lf : List ℕ)
    (hmem : lf ∈ sat1Allowed)
    (hpos : ∀ v : V, (circuitPos C p sz (some v)).image (symSlot σ f) = slots (lf.getD v.val 256)) :
    False := by
  have hpL' : C.leftVars p = {4, 7} := hpL.trans decode_144
  have hpR' : C.rightVars p = {5, 8} := hpR.trans decode_288
  have hsepR : SeparatesRows C := separatesRows_of_separates sep
  obtain ⟨he_ne, he_inj, hl, hr⟩ := circuitVars_of_symSlot C p sz σ f lf hpos
  let e : Fin 4 → Fin C.size := fun j => otherGate C p sz (σ.symm j)
  let d : Fin 4 → Bool := fun j => f (σ.symm j)
  simp only [sat1Allowed, List.mem_cons, List.not_mem_nil, or_false] at hmem
  subst hmem
  exact case2_impossible C sz hsepR p early e d he_ne he_inj hpL' hpR'
    (vars_eq_of_bitmask [1, 10, 130, 160, 4, 64, 40, 16, 16] 0 (hl 0) {0} (by decide))
    (vars_eq_of_bitmask [1, 10, 130, 160, 4, 64, 40, 16, 16] 1 (hr 0) {1, 2} (by decide))
    (vars_eq_of_bitmask [1, 10, 130, 160, 4, 64, 40, 16, 16] 2 (hl 1) {4} (by decide))
    (vars_eq_of_bitmask [1, 10, 130, 160, 4, 64, 40, 16, 16] 3 (hr 1) {1, 6} (by decide))
    (vars_eq_of_bitmask [1, 10, 130, 160, 4, 64, 40, 16, 16] 4 (hl 2) {7, 8} (by decide))
    (vars_eq_of_bitmask [1, 10, 130, 160, 4, 64, 40, 16, 16] 5 (hr 2) {3, 6} (by decide))
    (vars_eq_of_bitmask [1, 10, 130, 160, 4, 64, 40, 16, 16] 6 (hl 3) {5} (by decide))
    (vars_eq_of_bitmask [1, 10, 130, 160, 4, 64, 40, 16, 16] 7 (hr 3) {2, 3} (by decide))

theorem not_bad_of_sat0_pos
    (hspec : ∀ pos : X → Finset Slot,
      Cover (decode 6) (decode 9) pos → Cap (decode 6) (decode 9) pos →
      ∃ (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Bool),
        ∃ lf ∈ sat0Allowed, ∀ v : V, (pos (some v)).image (symSlot σ f) = slots (lf.getD v.val 256)) :
    ¬ Bad (decode 6) (decode 9) := by
  intro ⟨C, p, hpL, hpR, sz, sep, early, hr, dis⟩
  have hno := bad_nout C p sep hr
  obtain ⟨hcov, hcap⟩ := lift_slots_exact C p early sep hno dis sz
  rw [hpL, hpR] at hcov hcap
  obtain ⟨σ, f, lf, hmem, hpos⟩ := hspec (circuitPos C p sz) hcov hcap
  exact sat0_leaf_impossible sz sep early hpL hpR σ f lf hmem hpos

theorem not_bad_of_sat1_pos
    (hspec : ∀ pos : X → Finset Slot,
      Cover (decode 144) (decode 288) pos → Cap (decode 144) (decode 288) pos →
      ∃ (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Bool),
        ∃ lf ∈ sat1Allowed, ∀ v : V, (pos (some v)).image (symSlot σ f) = slots (lf.getD v.val 256)) :
    ¬ Bad (decode 144) (decode 288) := by
  intro ⟨C, p, hpL, hpR, sz, sep, early, hr, dis⟩
  have hno := bad_nout C p sep hr
  obtain ⟨hcov, hcap⟩ := lift_slots_exact C p early sep hno dis sz
  rw [hpL, hpR] at hcov hcap
  obtain ⟨σ, f, lf, hmem, hpos⟩ := hspec (circuitPos C p sz) hcov hcap
  exact sat1_leaf_impossible sz sep early hpL hpR σ f lf hmem hpos

theorem not_bad_of_empty_allowed {a b : ℕ}
    (hspec : ∀ pos : X → Finset Slot,
      Cover (decode a) (decode b) pos → Cap (decode a) (decode b) pos →
      ∃ (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Bool),
        ∃ lf ∈ ([] : List (List ℕ)), ∀ v : V, (pos (some v)).image (symSlot σ f) = slots (lf.getD v.val 256)) :
    ¬ Bad (decode a) (decode b) := by
  intro hBad
  obtain ⟨_, _, pos, hcov, hcap⟩ := bad_frame hBad
  obtain ⟨_, _, _, hmem, _⟩ := hspec pos hcov hcap
  simp at hmem

theorem main_of_noBad (hno : ∀ A B : Finset V, ¬ Bad A B) :
    ∀ G : SimpleGraph (Fin 9), G = SimpleGraph.fromRel (fun a b : Fin 9 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6), (3, 5), (3, 7), (4, 6), (4, 8), (5, 7), (6, 8), (7, 8)] : List (ℕ × ℕ))) →
      ∀ C : PEqualNP.AndCount.AndCountCircuit 9, C.WellFormed →
        (∀ I : Finset (Fin 9), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 9, w ∉ I → ∃ a ∈ I, G.Adj a w) →
          C.eval I = false ∧ ∀ w : Fin 9, w ∉ I → C.eval (insert w I) = true) →
        6 ≤ C.size := by
  intro G hG C _ hC
  apply lower_of_noBad hno C
  intro I hI
  obtain ⟨h1, h2⟩ := (good_iff G hG I).mp hI
  exact hC I h1 h2


def inMask (v : ℕ) : ℕ :=
  match v with
  | 0 => 21149 | 1 => 35936 | 2 => 10562 | 3 => 12299 | 4 => 391 | 5 => 49204 | 6 => 1592 | 7 => 1984 | _ => 63488

theorem bitOn_inMask : ∀ (v : V) (r : Fin 16), bitOn (inMask v.val) r.val = decide (v ∈ rows r) := by
  decide +kernel

def stMaskGo (a b hm v : ℕ) : ℕ → ℕ → ℕ
  | 0, acc => acc
  | r + 1, acc => stMaskGo a b hm v r (if stableB a b hm r v then acc ||| (1 <<< r) else acc)

def stMask (a b hm v : ℕ) : ℕ := stMaskGo a b hm v 16 0

theorem stMaskGo_testBit (a b hm v : ℕ) :
    ∀ (k acc : ℕ) (r : Fin 16),
      (stMaskGo a b hm v k acc).testBit r.val =
        ((decide (r.val < k) && stableB a b hm r.val v) || acc.testBit r.val) := by
  intro k
  induction k with
  | zero => intro acc r; simp [stMaskGo]
  | succ k ih =>
    intro acc r
    simp only [stMaskGo, ih]
    by_cases hlt : r.val < k
    · have hlt1 : r.val < k + 1 := by omega
      have hne : ¬ k ≤ r.val := by omega
      cases stableB a b hm k v <;> simp [hlt, hlt1, hne, Nat.testBit_or, Nat.testBit_shiftLeft]
    · by_cases heq : r.val = k
      · rw [heq]
        cases stableB a b hm k v <;> simp [Nat.testBit_or, Nat.testBit_shiftLeft]
      · have hnot1 : ¬ r.val < k + 1 := by omega
        have htb1 : Nat.testBit 1 (r.val - k) = false := by
          cases hm' : r.val - k with
          | zero => omega
          | succ m => simp [Nat.testBit_succ]
        simp only [hlt, hnot1, decide_false, Bool.false_and, Bool.false_or]
        cases stableB a b hm k v
        · rfl
        · simp [Nat.testBit_or, Nat.testBit_shiftLeft, htb1]

theorem bitOn_stMask (a b : ℕ) (v : V) (r : Fin 16) :
    bitOn (stMask a b (hotMask a b) v.val) r.val = stableB a b (hotMask a b) r.val v.val := by
  rw [bitOn_eq_testBit _ _ r.isLt, stMask, stMaskGo_testBit]
  simp [r.isLt]

def all81 : ℕ := (1 <<< 81) - 1

def consMask (i : ℕ) : ℕ := (i % 3) + 4 * ((i / 3) % 3) + 16 * ((i / 9) % 3) + 64 * (i / 27)

def disj81_0 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 2417851639229258349412351
  | 1 => 1727036885163755963865965
  | 2 => 1036222131098253578319579
  | 3 => 345407377032751192773193
  | 4 => 2152881596573997160435655
  | 5 => 1537772568981426543168325
  | 6 => 922663541388855925900995
  | 7 => 307554513796285308633665
  | 8 => 298091297987168837598783
  | 9 => 212922355705120598284845
  | 10 => 127753413423072358970907
  | 11 => 42584471141024119656969
  | 12 => 33121255331907648622087
  | 13 => 23658039522791177587205
  | 14 => 14194823713674706552323
  | _ => 4731607904558235517441
def disj81_1 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 2413138496083309906100735
  | 1 => 1723670354345221361500525
  | 2 => 1034202212607132816900315
  | 3 => 344734070869044272300105
  | 4 => 2148684962265960875295175
  | 5 => 1534774973047114910925125
  | 6 => 920864983828268946555075
  | 7 => 306954994609422982185025
  | 8 => 297510225544517659656255
  | 9 => 212507303960369756897325
  | 10 => 127504382376221854138395
  | 11 => 42501460792073951379465
  | 12 => 33056691727168628850695
  | 13 => 23611922662263306321925
  | 14 => 14167153597357983793155
  | _ => 4722384532452661264385
def disj81_2 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 4722348503655373864959
  | 1 => 3373106074039552760685
  | 2 => 2023863644423731656411
  | 3 => 674621214807910552137
  | 4 => 4204830859419168509895
  | 5 => 3003450613870834649925
  | 6 => 1802070368322500789955
  | 7 => 600690122774166929985
  | 8 => 582207349765731024447
  | 9 => 415862392689807874605
  | 10 => 249517435613884724763
  | 11 => 83172478537961574921
  | 12 => 64689705529525669383
  | 13 => 46206932521089763845
  | 14 => 27724159512653858307
  | _ => 9241386504217952769
def disj81_3 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 9205357706930553343
  | 1 => 6575255504950395245
  | 2 => 3945153302970237147
  | 3 => 1315051100990079049
  | 4 => 8196551382883369415
  | 5 => 5854679559202406725
  | 6 => 3512807735521444035
  | 7 => 1170935911840481345
  | 8 => 1134907114553081919
  | 9 => 810647938966487085
  | 10 => 486388763379892251
  | 11 => 162129587793297417
  | 12 => 126100790505897991
  | 13 => 90071993218498565
  | 14 => 54043195931099139
  | _ => 18014398643699713
def disj81_4 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 2417851621214859974148095
  | 1 => 1727036872296328552962925
  | 2 => 1036222123377797131777755
  | 3 => 345407374459265710592585
  | 4 => 2152881580533779429035975
  | 5 => 1537772557524128163597125
  | 6 => 922663534514476898158275
  | 7 => 307554511504825632719425
  | 8 => 298091295766215613251135
  | 9 => 212922354118725438036525
  | 10 => 127753412471235262821915
  | 11 => 42584470823745087607305
  | 12 => 33121255085135068139015
  | 13 => 23658039346525048670725
  | 14 => 14194823607915029202435
  | _ => 4731607869305009734145
def disj81_5 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 2413138478104027183448575
  | 1 => 1723670341502876559606125
  | 2 => 1034202204901725935763675
  | 3 => 344734068300575311921225
  | 4 => 2148684946257010505810375
  | 5 => 1534774961612150361293125
  | 6 => 920864976967290216775875
  | 7 => 306954992322430072258625
  | 8 => 297510223327893762342975
  | 9 => 212507302377066973102125
  | 10 => 127504381426240183861275
  | 11 => 42501460475413394620425
  | 12 => 33056691480877084704775
  | 13 => 23611922486340774789125
  | 14 => 14167153491804464873475
  | _ => 4722384497268154957825
def disj81_6 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 4722348468471135993855
  | 1 => 3373106048907954281325
  | 2 => 2023863629344772568795
  | 3 => 674621209781590856265
  | 4 => 4204830828090737528775
  | 5 => 3003450591493383949125
  | 6 => 1802070354896030369475
  | 7 => 600690118298676789825
  | 8 => 582207345427948273215
  | 9 => 415862389591391623725
  | 10 => 249517433754834974235
  | 11 => 83172477918278324745
  | 12 => 64689705047549808135
  | 13 => 46206932176821291525
  | 14 => 27724159306092774915
  | _ => 9241386435364258305
def disj81_7 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 9205357638345294335
  | 1 => 6575255455960924525
  | 2 => 3945153273576554715
  | 3 => 1315051091192184905
  | 4 => 8196551321814303175
  | 5 => 5854679515581645125
  | 6 => 3512807709348987075
  | 7 => 1170935903116329025
  | 8 => 1134907106097365055
  | 9 => 810647932926689325
  | 10 => 486388759756013595
  | 11 => 162129586585337865
  | 12 => 126100789566373895
  | 13 => 90071992547409925
  | 14 => 54043195528445955
  | _ => 18014398509481985
def disj81_8 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 18014398509481983
  | 1 => 12867427506772845
  | 2 => 7720456504063707
  | 3 => 2573485501354569
  | 4 => 16040217850908615
  | 5 => 11457298464934725
  | 6 => 6874379078960835
  | 7 => 2291459692986945
  | 8 => 2220953240895039
  | 9 => 1586395172067885
  | 10 => 951837103240731
  | 11 => 317279034413577
  | 12 => 246772582321671
  | 13 => 176266130229765
  | 14 => 105759678137859
  | _ => 35253226045953
def disj81_9 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 17979282856608255
  | 1 => 12842344897577325
  | 2 => 7705406938546395
  | 3 => 2568468979515465
  | 4 => 16008950488760775
  | 5 => 11434964634829125
  | 6 => 6860978780897475
  | 7 => 2286992926965825
  | 8 => 2216623913828415
  | 9 => 1583302795591725
  | 10 => 949981677355035
  | 11 => 316660559118345
  | 12 => 246291545980935
  | 13 => 175922532843525
  | 14 => 105553519706115
  | _ => 35184506568705
def disj81_10 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 35184238133247
  | 1 => 25131598666605
  | 2 => 15078959199963
  | 3 => 5026319733321
  | 4 => 31328431214535
  | 5 => 22377450867525
  | 6 => 13426470520515
  | 7 => 4475490173505
  | 8 => 4337782783551
  | 9 => 3098416273965
  | 10 => 1859049764379
  | 11 => 619683254793
  | 12 => 481975864839
  | 13 => 344268474885
  | 14 => 206561084931
  | _ => 68853694977
def disj81_11 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 68585259519
  | 1 => 48989471085
  | 2 => 29393682651
  | 3 => 9797894217
  | 4 => 61069066695
  | 5 => 43620761925
  | 6 => 26172457155
  | 7 => 8724152385
  | 8 => 8455716927
  | 9 => 6039797805
  | 10 => 3623878683
  | 11 => 1207959561
  | 12 => 939524103
  | 13 => 671088645
  | 14 => 402653187
  | _ => 134217729
def disj81_12 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 134217727
  | 1 => 95869805
  | 2 => 57521883
  | 3 => 19173961
  | 4 => 119508935
  | 5 => 85363525
  | 6 => 51218115
  | 7 => 17072705
  | 8 => 16547391
  | 9 => 11819565
  | 10 => 7091739
  | 11 => 2363913
  | 12 => 1838599
  | 13 => 1313285
  | 14 => 787971
  | _ => 262657
def disj81_13 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 133956095
  | 1 => 95682925
  | 2 => 57409755
  | 3 => 19136585
  | 4 => 119275975
  | 5 => 85197125
  | 6 => 51118275
  | 7 => 17039425
  | 8 => 16515135
  | 9 => 11796525
  | 10 => 7077915
  | 11 => 2359305
  | 12 => 1835015
  | 13 => 1310725
  | 14 => 786435
  | _ => 262145
def disj81_14 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 262143
  | 1 => 187245
  | 2 => 112347
  | 3 => 37449
  | 4 => 233415
  | 5 => 166725
  | 6 => 100035
  | 7 => 33345
  | 8 => 32319
  | 9 => 23085
  | 10 => 13851
  | 11 => 4617
  | 12 => 3591
  | 13 => 2565
  | 14 => 1539
  | _ => 513
def disj81_15 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 511
  | 1 => 365
  | 2 => 219
  | 3 => 73
  | 4 => 455
  | 5 => 325
  | 6 => 195
  | 7 => 65
  | 8 => 63
  | 9 => 45
  | 10 => 27
  | 11 => 9
  | 12 => 7
  | 13 => 5
  | 14 => 3
  | _ => 1
def disj81 (w : ℕ) : ℕ :=
  match w / 16 with
  | 0 => disj81_0 (w % 16)
  | 1 => disj81_1 (w % 16)
  | 2 => disj81_2 (w % 16)
  | 3 => disj81_3 (w % 16)
  | 4 => disj81_4 (w % 16)
  | 5 => disj81_5 (w % 16)
  | 6 => disj81_6 (w % 16)
  | 7 => disj81_7 (w % 16)
  | 8 => disj81_8 (w % 16)
  | 9 => disj81_9 (w % 16)
  | 10 => disj81_10 (w % 16)
  | 11 => disj81_11 (w % 16)
  | 12 => disj81_12 (w % 16)
  | 13 => disj81_13 (w % 16)
  | 14 => disj81_14 (w % 16)
  | _ => disj81_15 (w % 16)

def meet81_0 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 0
  | 1 => 690814754065502385546386
  | 2 => 1381629508131004771092772
  | 3 => 2072444262196507156639158
  | 4 => 264970042655261188976696
  | 5 => 880079070247831806244026
  | 6 => 1495188097840402423511356
  | 7 => 2110297125432973040778686
  | 8 => 2119760341242089511813568
  | 9 => 2204929283524137751127506
  | 10 => 2290098225806185990441444
  | 11 => 2375267168088234229755382
  | 12 => 2384730383897350700790264
  | 13 => 2394193599706467171825146
  | 14 => 2403656815515583642860028
  | _ => 2413120031324700113894910
def meet81_1 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 4713143145948443311616
  | 1 => 694181284884036987911826
  | 2 => 1383649426622125532512036
  | 3 => 2073117568360214077112246
  | 4 => 269166676963297474117176
  | 5 => 883076666182143438487226
  | 6 => 1496986655400989402857276
  | 7 => 2110896644619835367227326
  | 8 => 2120341413684740689756096
  | 9 => 2205344335268888592515026
  | 10 => 2290347256853036495273956
  | 11 => 2375350178437184398032886
  | 12 => 2384794947502089720561656
  | 13 => 2394239716566995043090426
  | 14 => 2403684485631900365619196
  | _ => 2413129254696805688147966
def meet81_2 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 2413129290725602975547392
  | 1 => 2414478533155218796651666
  | 2 => 2415827775584834617755940
  | 3 => 2417177018014450438860214
  | 4 => 2413646808369839180902456
  | 5 => 2414848188615387514762426
  | 6 => 2416049568860935848622396
  | 7 => 2417250949106484182482366
  | 8 => 2417269431879492618387904
  | 9 => 2417435776836568541537746
  | 10 => 2417602121793644464687588
  | 11 => 2417768466750720387837430
  | 12 => 2417786949523728823742968
  | 13 => 2417805432296737259648506
  | 14 => 2417823915069745695554044
  | _ => 2417842397842754131459582
def meet81_3 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 2417842433871551418859008
  | 1 => 2417845063973753399017106
  | 2 => 2417847694075955379175204
  | 3 => 2417850324178157359333302
  | 4 => 2417843442677875466042936
  | 5 => 2417845784549699147005626
  | 6 => 2417848126421522827968316
  | 7 => 2417850468293346508931006
  | 8 => 2417850504322143796330432
  | 9 => 2417850828581319382925266
  | 10 => 2417851152840494969520100
  | 11 => 2417851477099670556114934
  | 12 => 2417851513128467843514360
  | 13 => 2417851549157265130913786
  | 14 => 2417851585186062418313212
  | _ => 2417851621214859705712638
def meet81_4 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 18014398375264256
  | 1 => 690814766932929796449426
  | 2 => 1381629515851461217634596
  | 3 => 2072444264769992638819766
  | 4 => 264970058695478920376376
  | 5 => 880079081705130185815226
  | 6 => 1495188104714781451254076
  | 7 => 2110297127724432716692926
  | 8 => 2119760343463042736161216
  | 9 => 2204929285110532911375826
  | 10 => 2290098226758023086590436
  | 11 => 2375267168405513261805046
  | 12 => 2384730384144123281273336
  | 13 => 2394193599882733300741626
  | 14 => 2403656815621343320209916
  | _ => 2413120031359953339678206
def meet81_5 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 4713161125231165963776
  | 1 => 694181297726381789806226
  | 2 => 1383649434327532413648676
  | 3 => 2073117570928683037491126
  | 4 => 269166692972247843601976
  | 5 => 883076677617107988119226
  | 6 => 1496986662261968132636476
  | 7 => 2110896646906828277153726
  | 8 => 2120341415901364587069376
  | 9 => 2205344336852191376310226
  | 10 => 2290347257803018165551076
  | 11 => 2375350178753844954791926
  | 12 => 2384794947748381264707576
  | 13 => 2394239716742917574623226
  | 14 => 2403684485737453884538876
  | _ => 2413129254731990194454526
def meet81_6 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 2413129290760787213418496
  | 1 => 2414478533180350395131026
  | 2 => 2415827775599913576843556
  | 3 => 2417177018019476758556086
  | 4 => 2413646808401167611883576
  | 5 => 2414848188637764965463226
  | 6 => 2416049568874362319042876
  | 7 => 2417250949110959672622526
  | 8 => 2417269431883830401139136
  | 9 => 2417435776839666957788626
  | 10 => 2417602121795503514438116
  | 11 => 2417768466751340071087606
  | 12 => 2417786949524210799604216
  | 13 => 2417805432297081528120826
  | 14 => 2417823915069952256637436
  | _ => 2417842397842822985154046
def meet81_7 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 2417842433871620004118016
  | 1 => 2417845063973802388487826
  | 2 => 2417847694075984772857636
  | 3 => 2417850324178167157227446
  | 4 => 2417843442677936535109176
  | 5 => 2417845784549742767767226
  | 6 => 2417848126421549000425276
  | 7 => 2417850468293355233083326
  | 8 => 2417850504322152252047296
  | 9 => 2417850828581325422723026
  | 10 => 2417851152840498593398756
  | 11 => 2417851477099671764074486
  | 12 => 2417851513128468783038456
  | 13 => 2417851549157265802002426
  | 14 => 2417851585186062820966396
  | _ => 2417851621214859839930366
def meet81_8 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 2417851621214859839930368
  | 1 => 2417851626361830842639506
  | 2 => 2417851631508801845348644
  | 3 => 2417851636655772848057782
  | 4 => 2417851623189040498503736
  | 5 => 2417851627771959884477626
  | 6 => 2417851632354879270451516
  | 7 => 2417851636937798656425406
  | 8 => 2417851637008305108517312
  | 9 => 2417851637642863177344466
  | 10 => 2417851638277421246171620
  | 11 => 2417851638911979314998774
  | 12 => 2417851638982485767090680
  | 13 => 2417851639052992219182586
  | 14 => 2417851639123498671274492
  | _ => 2417851639194005123366398
def meet81_9 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 2417851621249975492804096
  | 1 => 2417851626386913451835026
  | 2 => 2417851631523851410865956
  | 3 => 2417851636660789369896886
  | 4 => 2417851623220307860651576
  | 5 => 2417851627794293714583226
  | 6 => 2417851632368279568514876
  | 7 => 2417851636942265422446526
  | 8 => 2417851637012634435583936
  | 9 => 2417851637645955553820626
  | 10 => 2417851638279276672057316
  | 11 => 2417851638912597790294006
  | 12 => 2417851638982966803431416
  | 13 => 2417851639053335816568826
  | 14 => 2417851639123704829706236
  | _ => 2417851639194073842843646
def meet81_10 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 2417851639194074111279104
  | 1 => 2417851639204126750745746
  | 2 => 2417851639214179390212388
  | 3 => 2417851639224232029679030
  | 4 => 2417851639197929918197816
  | 5 => 2417851639206880898544826
  | 6 => 2417851639215831878891836
  | 7 => 2417851639224782859238846
  | 8 => 2417851639224920566628800
  | 9 => 2417851639226159933138386
  | 10 => 2417851639227399299647972
  | 11 => 2417851639228638666157558
  | 12 => 2417851639228776373547512
  | 13 => 2417851639228914080937466
  | 14 => 2417851639229051788327420
  | _ => 2417851639229189495717374
def meet81_11 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 2417851639229189764152832
  | 1 => 2417851639229209359941266
  | 2 => 2417851639229228955729700
  | 3 => 2417851639229248551518134
  | 4 => 2417851639229197280345656
  | 5 => 2417851639229214728650426
  | 6 => 2417851639229232176955196
  | 7 => 2417851639229249625259966
  | 8 => 2417851639229249893695424
  | 9 => 2417851639229252309614546
  | 10 => 2417851639229254725533668
  | 11 => 2417851639229257141452790
  | 12 => 2417851639229257409888248
  | 13 => 2417851639229257678323706
  | 14 => 2417851639229257946759164
  | _ => 2417851639229258215194622
def meet81_12 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 2417851639229258215194624
  | 1 => 2417851639229258253542546
  | 2 => 2417851639229258291890468
  | 3 => 2417851639229258330238390
  | 4 => 2417851639229258229903416
  | 5 => 2417851639229258264048826
  | 6 => 2417851639229258298194236
  | 7 => 2417851639229258332339646
  | 8 => 2417851639229258332864960
  | 9 => 2417851639229258337592786
  | 10 => 2417851639229258342320612
  | 11 => 2417851639229258347048438
  | 12 => 2417851639229258347573752
  | 13 => 2417851639229258348099066
  | 14 => 2417851639229258348624380
  | _ => 2417851639229258349149694
def meet81_13 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 2417851639229258215456256
  | 1 => 2417851639229258253729426
  | 2 => 2417851639229258292002596
  | 3 => 2417851639229258330275766
  | 4 => 2417851639229258230136376
  | 5 => 2417851639229258264215226
  | 6 => 2417851639229258298294076
  | 7 => 2417851639229258332372926
  | 8 => 2417851639229258332897216
  | 9 => 2417851639229258337615826
  | 10 => 2417851639229258342334436
  | 11 => 2417851639229258347053046
  | 12 => 2417851639229258347577336
  | 13 => 2417851639229258348101626
  | 14 => 2417851639229258348625916
  | _ => 2417851639229258349150206
def meet81_14 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 2417851639229258349150208
  | 1 => 2417851639229258349225106
  | 2 => 2417851639229258349300004
  | 3 => 2417851639229258349374902
  | 4 => 2417851639229258349178936
  | 5 => 2417851639229258349245626
  | 6 => 2417851639229258349312316
  | 7 => 2417851639229258349379006
  | 8 => 2417851639229258349380032
  | 9 => 2417851639229258349389266
  | 10 => 2417851639229258349398500
  | 11 => 2417851639229258349407734
  | 12 => 2417851639229258349408760
  | 13 => 2417851639229258349409786
  | 14 => 2417851639229258349410812
  | _ => 2417851639229258349411838
def meet81_15 (lo : ℕ) : ℕ :=
  match lo with
  | 0 => 2417851639229258349411840
  | 1 => 2417851639229258349411986
  | 2 => 2417851639229258349412132
  | 3 => 2417851639229258349412278
  | 4 => 2417851639229258349411896
  | 5 => 2417851639229258349412026
  | 6 => 2417851639229258349412156
  | 7 => 2417851639229258349412286
  | 8 => 2417851639229258349412288
  | 9 => 2417851639229258349412306
  | 10 => 2417851639229258349412324
  | 11 => 2417851639229258349412342
  | 12 => 2417851639229258349412344
  | 13 => 2417851639229258349412346
  | 14 => 2417851639229258349412348
  | _ => 2417851639229258349412350
def meet81 (w : ℕ) : ℕ :=
  match w / 16 with
  | 0 => meet81_0 (w % 16)
  | 1 => meet81_1 (w % 16)
  | 2 => meet81_2 (w % 16)
  | 3 => meet81_3 (w % 16)
  | 4 => meet81_4 (w % 16)
  | 5 => meet81_5 (w % 16)
  | 6 => meet81_6 (w % 16)
  | 7 => meet81_7 (w % 16)
  | 8 => meet81_8 (w % 16)
  | 9 => meet81_9 (w % 16)
  | 10 => meet81_10 (w % 16)
  | 11 => meet81_11 (w % 16)
  | 12 => meet81_12 (w % 16)
  | 13 => meet81_13 (w % 16)
  | 14 => meet81_14 (w % 16)
  | _ => meet81_15 (w % 16)

def canonDomV (isCap1 : Bool) (used : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  match isCap1, used with
  | true, 0 => [(0, 0, 2417851639229258349412351, 0), (1, 1, 1727036885163755963865965, 690814754065502385546386)]
  | true, 1 => [(0, 1, 2417851639229258349412351, 0), (1, 1, 1727036885163755963865965, 690814754065502385546386), (2, 1, 1036222131098253578319579, 1381629508131004771092772), (4, 2, 2152881596573997160435655, 264970042655261188976696)]
  | true, 2 => [(0, 2, 2417851639229258349412351, 0), (1, 2, 1727036885163755963865965, 690814754065502385546386), (2, 2, 1036222131098253578319579, 1381629508131004771092772), (4, 2, 2152881596573997160435655, 264970042655261188976696), (8, 2, 298091297987168837598783, 2119760341242089511813568), (16, 3, 2413138496083309906100735, 4713143145948443311616)]
  | true, 3 => [(0, 3, 2417851639229258349412351, 0), (1, 3, 1727036885163755963865965, 690814754065502385546386), (2, 3, 1036222131098253578319579, 1381629508131004771092772), (4, 3, 2152881596573997160435655, 264970042655261188976696), (8, 3, 298091297987168837598783, 2119760341242089511813568), (16, 3, 2413138496083309906100735, 4713143145948443311616), (32, 3, 4722348503655373864959, 2413129290725602975547392), (64, 4, 2417851621214859974148095, 18014398375264256)]
  | true, 4 => [(0, 4, 2417851639229258349412351, 0), (1, 4, 1727036885163755963865965, 690814754065502385546386), (2, 4, 1036222131098253578319579, 1381629508131004771092772), (4, 4, 2152881596573997160435655, 264970042655261188976696), (8, 4, 298091297987168837598783, 2119760341242089511813568), (16, 4, 2413138496083309906100735, 4713143145948443311616), (32, 4, 4722348503655373864959, 2413129290725602975547392), (64, 4, 2417851621214859974148095, 18014398375264256), (128, 4, 18014398509481983, 2417851621214859839930368)]
  | false, 0 => [(0, 0, 2417851639229258349412351, 0), (1, 1, 1727036885163755963865965, 690814754065502385546386), (5, 2, 1537772568981426543168325, 880079070247831806244026)]
  | false, 1 => [(0, 1, 2417851639229258349412351, 0), (1, 1, 1727036885163755963865965, 690814754065502385546386), (2, 1, 1036222131098253578319579, 1381629508131004771092772), (4, 2, 2152881596573997160435655, 264970042655261188976696), (5, 2, 1537772568981426543168325, 880079070247831806244026), (6, 2, 922663541388855925900995, 1495188097840402423511356), (20, 3, 2148684962265960875295175, 269166676963297474117176)]
  | false, 2 => [(0, 2, 2417851639229258349412351, 0), (1, 2, 1727036885163755963865965, 690814754065502385546386), (2, 2, 1036222131098253578319579, 1381629508131004771092772), (4, 2, 2152881596573997160435655, 264970042655261188976696), (5, 2, 1537772568981426543168325, 880079070247831806244026), (6, 2, 922663541388855925900995, 1495188097840402423511356), (8, 2, 298091297987168837598783, 2119760341242089511813568), (9, 2, 212922355705120598284845, 2204929283524137751127506), (10, 2, 127753413423072358970907, 2290098225806185990441444), (16, 3, 2413138496083309906100735, 4713143145948443311616), (17, 3, 1723670354345221361500525, 694181284884036987911826), (18, 3, 1034202212607132816900315, 1383649426622125532512036), (20, 3, 2148684962265960875295175, 269166676963297474117176), (24, 3, 297510225544517659656255, 2120341413684740689756096), (80, 4, 2413138478104027183448575, 4713161125231165963776)]
  | false, 3 => [(0, 3, 2417851639229258349412351, 0), (1, 3, 1727036885163755963865965, 690814754065502385546386), (2, 3, 1036222131098253578319579, 1381629508131004771092772), (4, 3, 2152881596573997160435655, 264970042655261188976696), (5, 3, 1537772568981426543168325, 880079070247831806244026), (6, 3, 922663541388855925900995, 1495188097840402423511356), (8, 3, 298091297987168837598783, 2119760341242089511813568), (9, 3, 212922355705120598284845, 2204929283524137751127506), (10, 3, 127753413423072358970907, 2290098225806185990441444), (16, 3, 2413138496083309906100735, 4713143145948443311616), (17, 3, 1723670354345221361500525, 694181284884036987911826), (18, 3, 1034202212607132816900315, 1383649426622125532512036), (20, 3, 2148684962265960875295175, 269166676963297474117176), (24, 3, 297510225544517659656255, 2120341413684740689756096), (32, 3, 4722348503655373864959, 2413129290725602975547392), (33, 3, 3373106074039552760685, 2414478533155218796651666), (34, 3, 2023863644423731656411, 2415827775584834617755940), (36, 3, 4204830859419168509895, 2413646808369839180902456), (40, 3, 582207349765731024447, 2417269431879492618387904), (64, 4, 2417851621214859974148095, 18014398375264256), (65, 4, 1727036872296328552962925, 690814766932929796449426), (66, 4, 1036222123377797131777755, 1381629515851461217634596), (68, 4, 2152881580533779429035975, 264970058695478920376376), (72, 4, 298091295766215613251135, 2119760343463042736161216), (80, 4, 2413138478104027183448575, 4713161125231165963776), (96, 4, 4722348468471135993855, 2413129290760787213418496)]
  | false, 4 => [(0, 4, 2417851639229258349412351, 0), (1, 4, 1727036885163755963865965, 690814754065502385546386), (2, 4, 1036222131098253578319579, 1381629508131004771092772), (4, 4, 2152881596573997160435655, 264970042655261188976696), (5, 4, 1537772568981426543168325, 880079070247831806244026), (6, 4, 922663541388855925900995, 1495188097840402423511356), (8, 4, 298091297987168837598783, 2119760341242089511813568), (9, 4, 212922355705120598284845, 2204929283524137751127506), (10, 4, 127753413423072358970907, 2290098225806185990441444), (16, 4, 2413138496083309906100735, 4713143145948443311616), (17, 4, 1723670354345221361500525, 694181284884036987911826), (18, 4, 1034202212607132816900315, 1383649426622125532512036), (20, 4, 2148684962265960875295175, 269166676963297474117176), (24, 4, 297510225544517659656255, 2120341413684740689756096), (32, 4, 4722348503655373864959, 2413129290725602975547392), (33, 4, 3373106074039552760685, 2414478533155218796651666), (34, 4, 2023863644423731656411, 2415827775584834617755940), (36, 4, 4204830859419168509895, 2413646808369839180902456), (40, 4, 582207349765731024447, 2417269431879492618387904), (64, 4, 2417851621214859974148095, 18014398375264256), (65, 4, 1727036872296328552962925, 690814766932929796449426), (66, 4, 1036222123377797131777755, 1381629515851461217634596), (68, 4, 2152881580533779429035975, 264970058695478920376376), (72, 4, 298091295766215613251135, 2119760343463042736161216), (80, 4, 2413138478104027183448575, 4713161125231165963776), (96, 4, 4722348468471135993855, 2413129290760787213418496), (128, 4, 18014398509481983, 2417851621214859839930368), (129, 4, 12867427506772845, 2417851626361830842639506), (130, 4, 7720456504063707, 2417851631508801845348644), (132, 4, 16040217850908615, 2417851623189040498503736), (136, 4, 2220953240895039, 2417851637008305108517312), (144, 4, 17979282856608255, 2417851621249975492804096), (160, 4, 35184238133247, 2417851639194074111279104)]
  | _, _ => []

def canonDomN (gcap used : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  match gcap, used with
  | 1, 0 => [(0, 0, 2417851639229258349412351, 0), (1, 1, 1727036885163755963865965, 690814754065502385546386), (3, 1, 345407377032751192773193, 2072444262196507156639158)]
  | 1, 1 => [(0, 1, 2417851639229258349412351, 0), (1, 1, 1727036885163755963865965, 690814754065502385546386), (2, 1, 1036222131098253578319579, 1381629508131004771092772), (3, 1, 345407377032751192773193, 2072444262196507156639158), (4, 2, 2152881596573997160435655, 264970042655261188976696), (12, 2, 33121255331907648622087, 2384730383897350700790264)]
  | 1, 2 => [(0, 2, 2417851639229258349412351, 0), (1, 2, 1727036885163755963865965, 690814754065502385546386), (2, 2, 1036222131098253578319579, 1381629508131004771092772), (3, 2, 345407377032751192773193, 2072444262196507156639158), (4, 2, 2152881596573997160435655, 264970042655261188976696), (8, 2, 298091297987168837598783, 2119760341242089511813568), (12, 2, 33121255331907648622087, 2384730383897350700790264), (16, 3, 2413138496083309906100735, 4713143145948443311616), (48, 3, 9205357706930553343, 2417842433871551418859008)]
  | 1, 3 => [(0, 3, 2417851639229258349412351, 0), (1, 3, 1727036885163755963865965, 690814754065502385546386), (2, 3, 1036222131098253578319579, 1381629508131004771092772), (3, 3, 345407377032751192773193, 2072444262196507156639158), (4, 3, 2152881596573997160435655, 264970042655261188976696), (8, 3, 298091297987168837598783, 2119760341242089511813568), (12, 3, 33121255331907648622087, 2384730383897350700790264), (16, 3, 2413138496083309906100735, 4713143145948443311616), (32, 3, 4722348503655373864959, 2413129290725602975547392), (48, 3, 9205357706930553343, 2417842433871551418859008), (64, 4, 2417851621214859974148095, 18014398375264256), (192, 4, 134217727, 2417851639229258215194624)]
  | 1, 4 => [(0, 4, 2417851639229258349412351, 0), (1, 4, 1727036885163755963865965, 690814754065502385546386), (2, 4, 1036222131098253578319579, 1381629508131004771092772), (3, 4, 345407377032751192773193, 2072444262196507156639158), (4, 4, 2152881596573997160435655, 264970042655261188976696), (8, 4, 298091297987168837598783, 2119760341242089511813568), (12, 4, 33121255331907648622087, 2384730383897350700790264), (16, 4, 2413138496083309906100735, 4713143145948443311616), (32, 4, 4722348503655373864959, 2413129290725602975547392), (48, 4, 9205357706930553343, 2417842433871551418859008), (64, 4, 2417851621214859974148095, 18014398375264256), (128, 4, 18014398509481983, 2417851621214859839930368), (192, 4, 134217727, 2417851639229258215194624)]
  | 2, 0 => [(0, 0, 2417851639229258349412351, 0), (1, 1, 1727036885163755963865965, 690814754065502385546386), (3, 1, 345407377032751192773193, 2072444262196507156639158), (5, 2, 1537772568981426543168325, 880079070247831806244026), (7, 2, 307554513796285308633665, 2110297125432973040778686), (15, 2, 4731607904558235517441, 2413120031324700113894910)]
  | 2, 1 => [(0, 1, 2417851639229258349412351, 0), (1, 1, 1727036885163755963865965, 690814754065502385546386), (2, 1, 1036222131098253578319579, 1381629508131004771092772), (3, 1, 345407377032751192773193, 2072444262196507156639158), (4, 2, 2152881596573997160435655, 264970042655261188976696), (5, 2, 1537772568981426543168325, 880079070247831806244026), (6, 2, 922663541388855925900995, 1495188097840402423511356), (7, 2, 307554513796285308633665, 2110297125432973040778686), (12, 2, 33121255331907648622087, 2384730383897350700790264), (13, 2, 23658039522791177587205, 2394193599706467171825146), (14, 2, 14194823713674706552323, 2403656815515583642860028), (15, 2, 4731607904558235517441, 2413120031324700113894910), (20, 3, 2148684962265960875295175, 269166676963297474117176), (28, 3, 33056691727168628850695, 2384794947502089720561656), (60, 3, 126100790505897991, 2417851513128467843514360)]
  | 2, 2 => [(0, 2, 2417851639229258349412351, 0), (1, 2, 1727036885163755963865965, 690814754065502385546386), (2, 2, 1036222131098253578319579, 1381629508131004771092772), (3, 2, 345407377032751192773193, 2072444262196507156639158), (4, 2, 2152881596573997160435655, 264970042655261188976696), (5, 2, 1537772568981426543168325, 880079070247831806244026), (6, 2, 922663541388855925900995, 1495188097840402423511356), (7, 2, 307554513796285308633665, 2110297125432973040778686), (8, 2, 298091297987168837598783, 2119760341242089511813568), (9, 2, 212922355705120598284845, 2204929283524137751127506), (10, 2, 127753413423072358970907, 2290098225806185990441444), (11, 2, 42584471141024119656969, 2375267168088234229755382), (12, 2, 33121255331907648622087, 2384730383897350700790264), (13, 2, 23658039522791177587205, 2394193599706467171825146), (14, 2, 14194823713674706552323, 2403656815515583642860028), (15, 2, 4731607904558235517441, 2413120031324700113894910), (16, 3, 2413138496083309906100735, 4713143145948443311616), (17, 3, 1723670354345221361500525, 694181284884036987911826), (18, 3, 1034202212607132816900315, 1383649426622125532512036), (19, 3, 344734070869044272300105, 2073117568360214077112246), (20, 3, 2148684962265960875295175, 269166676963297474117176), (24, 3, 297510225544517659656255, 2120341413684740689756096), (28, 3, 33056691727168628850695, 2384794947502089720561656), (48, 3, 9205357706930553343, 2417842433871551418859008), (49, 3, 6575255504950395245, 2417845063973753399017106), (50, 3, 3945153302970237147, 2417847694075955379175204), (51, 3, 1315051100990079049, 2417850324178157359333302), (52, 3, 8196551382883369415, 2417843442677875466042936), (56, 3, 1134907114553081919, 2417850504322143796330432), (60, 3, 126100790505897991, 2417851513128467843514360), (80, 4, 2413138478104027183448575, 4713161125231165963776), (112, 4, 9205357638345294335, 2417842433871620004118016), (240, 4, 511, 2417851639229258349411840)]
  | 2, 3 => [(0, 3, 2417851639229258349412351, 0), (1, 3, 1727036885163755963865965, 690814754065502385546386), (2, 3, 1036222131098253578319579, 1381629508131004771092772), (3, 3, 345407377032751192773193, 2072444262196507156639158), (4, 3, 2152881596573997160435655, 264970042655261188976696), (5, 3, 1537772568981426543168325, 880079070247831806244026), (6, 3, 922663541388855925900995, 1495188097840402423511356), (7, 3, 307554513796285308633665, 2110297125432973040778686), (8, 3, 298091297987168837598783, 2119760341242089511813568), (9, 3, 212922355705120598284845, 2204929283524137751127506), (10, 3, 127753413423072358970907, 2290098225806185990441444), (11, 3, 42584471141024119656969, 2375267168088234229755382), (12, 3, 33121255331907648622087, 2384730383897350700790264), (13, 3, 23658039522791177587205, 2394193599706467171825146), (14, 3, 14194823713674706552323, 2403656815515583642860028), (15, 3, 4731607904558235517441, 2413120031324700113894910), (16, 3, 2413138496083309906100735, 4713143145948443311616), (17, 3, 1723670354345221361500525, 694181284884036987911826), (18, 3, 1034202212607132816900315, 1383649426622125532512036), (19, 3, 344734070869044272300105, 2073117568360214077112246), (20, 3, 2148684962265960875295175, 269166676963297474117176), (24, 3, 297510225544517659656255, 2120341413684740689756096), (28, 3, 33056691727168628850695, 2384794947502089720561656), (32, 3, 4722348503655373864959, 2413129290725602975547392), (33, 3, 3373106074039552760685, 2414478533155218796651666), (34, 3, 2023863644423731656411, 2415827775584834617755940), (35, 3, 674621214807910552137, 2417177018014450438860214), (36, 3, 4204830859419168509895, 2413646808369839180902456), (40, 3, 582207349765731024447, 2417269431879492618387904), (44, 3, 64689705529525669383, 2417786949523728823742968), (48, 3, 9205357706930553343, 2417842433871551418859008), (49, 3, 6575255504950395245, 2417845063973753399017106), (50, 3, 3945153302970237147, 2417847694075955379175204), (51, 3, 1315051100990079049, 2417850324178157359333302), (52, 3, 8196551382883369415, 2417843442677875466042936), (56, 3, 1134907114553081919, 2417850504322143796330432), (60, 3, 126100790505897991, 2417851513128467843514360), (64, 4, 2417851621214859974148095, 18014398375264256), (65, 4, 1727036872296328552962925, 690814766932929796449426), (66, 4, 1036222123377797131777755, 1381629515851461217634596), (67, 4, 345407374459265710592585, 2072444264769992638819766), (68, 4, 2152881580533779429035975, 264970058695478920376376), (72, 4, 298091295766215613251135, 2119760343463042736161216), (76, 4, 33121255085135068139015, 2384730384144123281273336), (80, 4, 2413138478104027183448575, 4713161125231165963776), (96, 4, 4722348468471135993855, 2413129290760787213418496), (112, 4, 9205357638345294335, 2417842433871620004118016), (192, 4, 134217727, 2417851639229258215194624), (193, 4, 95869805, 2417851639229258253542546), (194, 4, 57521883, 2417851639229258291890468), (195, 4, 19173961, 2417851639229258330238390), (196, 4, 119508935, 2417851639229258229903416), (200, 4, 16547391, 2417851639229258332864960), (204, 4, 1838599, 2417851639229258347573752), (208, 4, 133956095, 2417851639229258215456256), (224, 4, 262143, 2417851639229258349150208), (240, 4, 511, 2417851639229258349411840)]
  | 2, 4 => [(0, 4, 2417851639229258349412351, 0), (1, 4, 1727036885163755963865965, 690814754065502385546386), (2, 4, 1036222131098253578319579, 1381629508131004771092772), (3, 4, 345407377032751192773193, 2072444262196507156639158), (4, 4, 2152881596573997160435655, 264970042655261188976696), (5, 4, 1537772568981426543168325, 880079070247831806244026), (6, 4, 922663541388855925900995, 1495188097840402423511356), (7, 4, 307554513796285308633665, 2110297125432973040778686), (8, 4, 298091297987168837598783, 2119760341242089511813568), (9, 4, 212922355705120598284845, 2204929283524137751127506), (10, 4, 127753413423072358970907, 2290098225806185990441444), (11, 4, 42584471141024119656969, 2375267168088234229755382), (12, 4, 33121255331907648622087, 2384730383897350700790264), (13, 4, 23658039522791177587205, 2394193599706467171825146), (14, 4, 14194823713674706552323, 2403656815515583642860028), (15, 4, 4731607904558235517441, 2413120031324700113894910), (16, 4, 2413138496083309906100735, 4713143145948443311616), (17, 4, 1723670354345221361500525, 694181284884036987911826), (18, 4, 1034202212607132816900315, 1383649426622125532512036), (19, 4, 344734070869044272300105, 2073117568360214077112246), (20, 4, 2148684962265960875295175, 269166676963297474117176), (24, 4, 297510225544517659656255, 2120341413684740689756096), (28, 4, 33056691727168628850695, 2384794947502089720561656), (32, 4, 4722348503655373864959, 2413129290725602975547392), (33, 4, 3373106074039552760685, 2414478533155218796651666), (34, 4, 2023863644423731656411, 2415827775584834617755940), (35, 4, 674621214807910552137, 2417177018014450438860214), (36, 4, 4204830859419168509895, 2413646808369839180902456), (40, 4, 582207349765731024447, 2417269431879492618387904), (44, 4, 64689705529525669383, 2417786949523728823742968), (48, 4, 9205357706930553343, 2417842433871551418859008), (49, 4, 6575255504950395245, 2417845063973753399017106), (50, 4, 3945153302970237147, 2417847694075955379175204), (51, 4, 1315051100990079049, 2417850324178157359333302), (52, 4, 8196551382883369415, 2417843442677875466042936), (56, 4, 1134907114553081919, 2417850504322143796330432), (60, 4, 126100790505897991, 2417851513128467843514360), (64, 4, 2417851621214859974148095, 18014398375264256), (65, 4, 1727036872296328552962925, 690814766932929796449426), (66, 4, 1036222123377797131777755, 1381629515851461217634596), (67, 4, 345407374459265710592585, 2072444264769992638819766), (68, 4, 2152881580533779429035975, 264970058695478920376376), (72, 4, 298091295766215613251135, 2119760343463042736161216), (76, 4, 33121255085135068139015, 2384730384144123281273336), (80, 4, 2413138478104027183448575, 4713161125231165963776), (96, 4, 4722348468471135993855, 2413129290760787213418496), (112, 4, 9205357638345294335, 2417842433871620004118016), (128, 4, 18014398509481983, 2417851621214859839930368), (129, 4, 12867427506772845, 2417851626361830842639506), (130, 4, 7720456504063707, 2417851631508801845348644), (131, 4, 2573485501354569, 2417851636655772848057782), (132, 4, 16040217850908615, 2417851623189040498503736), (136, 4, 2220953240895039, 2417851637008305108517312), (140, 4, 246772582321671, 2417851638982485767090680), (144, 4, 17979282856608255, 2417851621249975492804096), (160, 4, 35184238133247, 2417851639194074111279104), (176, 4, 68585259519, 2417851639229189764152832), (192, 4, 134217727, 2417851639229258215194624), (193, 4, 95869805, 2417851639229258253542546), (194, 4, 57521883, 2417851639229258291890468), (195, 4, 19173961, 2417851639229258330238390), (196, 4, 119508935, 2417851639229258229903416), (200, 4, 16547391, 2417851639229258332864960), (204, 4, 1838599, 2417851639229258347573752), (208, 4, 133956095, 2417851639229258215456256), (224, 4, 262143, 2417851639229258349150208), (240, 4, 511, 2417851639229258349411840)]
  | 3, 0 => [(0, 0, 2417851639229258349412351, 0), (1, 1, 1727036885163755963865965, 690814754065502385546386), (3, 1, 345407377032751192773193, 2072444262196507156639158), (5, 2, 1537772568981426543168325, 880079070247831806244026), (7, 2, 307554513796285308633665, 2110297125432973040778686), (15, 2, 4731607904558235517441, 2413120031324700113894910), (21, 3, 1534774973047114910925125, 883076666182143438487226), (23, 3, 306954994609422982185025, 2110896644619835367227326), (31, 3, 4722384532452661264385, 2413129254696805688147966), (63, 3, 18014398643699713, 2417851621214859705712638)]
  | 3, 1 => [(0, 1, 2417851639229258349412351, 0), (1, 1, 1727036885163755963865965, 690814754065502385546386), (2, 1, 1036222131098253578319579, 1381629508131004771092772), (3, 1, 345407377032751192773193, 2072444262196507156639158), (4, 2, 2152881596573997160435655, 264970042655261188976696), (5, 2, 1537772568981426543168325, 880079070247831806244026), (6, 2, 922663541388855925900995, 1495188097840402423511356), (7, 2, 307554513796285308633665, 2110297125432973040778686), (12, 2, 33121255331907648622087, 2384730383897350700790264), (13, 2, 23658039522791177587205, 2394193599706467171825146), (14, 2, 14194823713674706552323, 2403656815515583642860028), (15, 2, 4731607904558235517441, 2413120031324700113894910), (20, 3, 2148684962265960875295175, 269166676963297474117176), (21, 3, 1534774973047114910925125, 883076666182143438487226), (22, 3, 920864983828268946555075, 1496986655400989402857276), (23, 3, 306954994609422982185025, 2110896644619835367227326), (28, 3, 33056691727168628850695, 2384794947502089720561656), (29, 3, 23611922662263306321925, 2394239716566995043090426), (30, 3, 14167153597357983793155, 2403684485631900365619196), (31, 3, 4722384532452661264385, 2413129254696805688147966), (60, 3, 126100790505897991, 2417851513128467843514360), (61, 3, 90071993218498565, 2417851549157265130913786), (62, 3, 54043195931099139, 2417851585186062418313212), (63, 3, 18014398643699713, 2417851621214859705712638), (84, 4, 2148684946257010505810375, 269166692972247843601976), (92, 4, 33056691480877084704775, 2384794947748381264707576), (124, 4, 126100789566373895, 2417851513128468783038456), (252, 4, 7, 2417851639229258349412344)]
  | 3, 2 => [(0, 2, 2417851639229258349412351, 0), (1, 2, 1727036885163755963865965, 690814754065502385546386), (2, 2, 1036222131098253578319579, 1381629508131004771092772), (3, 2, 345407377032751192773193, 2072444262196507156639158), (4, 2, 2152881596573997160435655, 264970042655261188976696), (5, 2, 1537772568981426543168325, 880079070247831806244026), (6, 2, 922663541388855925900995, 1495188097840402423511356), (7, 2, 307554513796285308633665, 2110297125432973040778686), (8, 2, 298091297987168837598783, 2119760341242089511813568), (9, 2, 212922355705120598284845, 2204929283524137751127506), (10, 2, 127753413423072358970907, 2290098225806185990441444), (11, 2, 42584471141024119656969, 2375267168088234229755382), (12, 2, 33121255331907648622087, 2384730383897350700790264), (13, 2, 23658039522791177587205, 2394193599706467171825146), (14, 2, 14194823713674706552323, 2403656815515583642860028), (15, 2, 4731607904558235517441, 2413120031324700113894910), (16, 3, 2413138496083309906100735, 4713143145948443311616), (17, 3, 1723670354345221361500525, 694181284884036987911826), (18, 3, 1034202212607132816900315, 1383649426622125532512036), (19, 3, 344734070869044272300105, 2073117568360214077112246), (20, 3, 2148684962265960875295175, 269166676963297474117176), (21, 3, 1534774973047114910925125, 883076666182143438487226), (22, 3, 920864983828268946555075, 1496986655400989402857276), (23, 3, 306954994609422982185025, 2110896644619835367227326), (24, 3, 297510225544517659656255, 2120341413684740689756096), (25, 3, 212507303960369756897325, 2205344335268888592515026), (26, 3, 127504382376221854138395, 2290347256853036495273956), (27, 3, 42501460792073951379465, 2375350178437184398032886), (28, 3, 33056691727168628850695, 2384794947502089720561656), (29, 3, 23611922662263306321925, 2394239716566995043090426), (30, 3, 14167153597357983793155, 2403684485631900365619196), (31, 3, 4722384532452661264385, 2413129254696805688147966), (48, 3, 9205357706930553343, 2417842433871551418859008), (49, 3, 6575255504950395245, 2417845063973753399017106), (50, 3, 3945153302970237147, 2417847694075955379175204), (51, 3, 1315051100990079049, 2417850324178157359333302), (52, 3, 8196551382883369415, 2417843442677875466042936), (53, 3, 5854679559202406725, 2417845784549699147005626), (54, 3, 3512807735521444035, 2417848126421522827968316), (55, 3, 1170935911840481345, 2417850468293346508931006), (56, 3, 1134907114553081919, 2417850504322143796330432), (57, 3, 810647938966487085, 2417850828581319382925266), (58, 3, 486388763379892251, 2417851152840494969520100), (59, 3, 162129587793297417, 2417851477099670556114934), (60, 3, 126100790505897991, 2417851513128467843514360), (61, 3, 90071993218498565, 2417851549157265130913786), (62, 3, 54043195931099139, 2417851585186062418313212), (63, 3, 18014398643699713, 2417851621214859705712638), (80, 4, 2413138478104027183448575, 4713161125231165963776), (81, 4, 1723670341502876559606125, 694181297726381789806226), (82, 4, 1034202204901725935763675, 1383649434327532413648676), (83, 4, 344734068300575311921225, 2073117570928683037491126), (84, 4, 2148684946257010505810375, 269166692972247843601976), (88, 4, 297510223327893762342975, 2120341415901364587069376), (92, 4, 33056691480877084704775, 2384794947748381264707576), (112, 4, 9205357638345294335, 2417842433871620004118016), (113, 4, 6575255455960924525, 2417845063973802388487826), (114, 4, 3945153273576554715, 2417847694075984772857636), (115, 4, 1315051091192184905, 2417850324178167157227446), (116, 4, 8196551321814303175, 2417843442677936535109176), (120, 4, 1134907106097365055, 2417850504322152252047296), (124, 4, 126100789566373895, 2417851513128468783038456), (240, 4, 511, 2417851639229258349411840), (241, 4, 365, 2417851639229258349411986), (242, 4, 219, 2417851639229258349412132), (243, 4, 73, 2417851639229258349412278), (244, 4, 455, 2417851639229258349411896), (248, 4, 63, 2417851639229258349412288), (252, 4, 7, 2417851639229258349412344)]
  | 3, 3 => [(0, 3, 2417851639229258349412351, 0), (1, 3, 1727036885163755963865965, 690814754065502385546386), (2, 3, 1036222131098253578319579, 1381629508131004771092772), (3, 3, 345407377032751192773193, 2072444262196507156639158), (4, 3, 2152881596573997160435655, 264970042655261188976696), (5, 3, 1537772568981426543168325, 880079070247831806244026), (6, 3, 922663541388855925900995, 1495188097840402423511356), (7, 3, 307554513796285308633665, 2110297125432973040778686), (8, 3, 298091297987168837598783, 2119760341242089511813568), (9, 3, 212922355705120598284845, 2204929283524137751127506), (10, 3, 127753413423072358970907, 2290098225806185990441444), (11, 3, 42584471141024119656969, 2375267168088234229755382), (12, 3, 33121255331907648622087, 2384730383897350700790264), (13, 3, 23658039522791177587205, 2394193599706467171825146), (14, 3, 14194823713674706552323, 2403656815515583642860028), (15, 3, 4731607904558235517441, 2413120031324700113894910), (16, 3, 2413138496083309906100735, 4713143145948443311616), (17, 3, 1723670354345221361500525, 694181284884036987911826), (18, 3, 1034202212607132816900315, 1383649426622125532512036), (19, 3, 344734070869044272300105, 2073117568360214077112246), (20, 3, 2148684962265960875295175, 269166676963297474117176), (21, 3, 1534774973047114910925125, 883076666182143438487226), (22, 3, 920864983828268946555075, 1496986655400989402857276), (23, 3, 306954994609422982185025, 2110896644619835367227326), (24, 3, 297510225544517659656255, 2120341413684740689756096), (25, 3, 212507303960369756897325, 2205344335268888592515026), (26, 3, 127504382376221854138395, 2290347256853036495273956), (27, 3, 42501460792073951379465, 2375350178437184398032886), (28, 3, 33056691727168628850695, 2384794947502089720561656), (29, 3, 23611922662263306321925, 2394239716566995043090426), (30, 3, 14167153597357983793155, 2403684485631900365619196), (31, 3, 4722384532452661264385, 2413129254696805688147966), (32, 3, 4722348503655373864959, 2413129290725602975547392), (33, 3, 3373106074039552760685, 2414478533155218796651666), (34, 3, 2023863644423731656411, 2415827775584834617755940), (35, 3, 674621214807910552137, 2417177018014450438860214), (36, 3, 4204830859419168509895, 2413646808369839180902456), (37, 3, 3003450613870834649925, 2414848188615387514762426), (38, 3, 1802070368322500789955, 2416049568860935848622396), (39, 3, 600690122774166929985, 2417250949106484182482366), (40, 3, 582207349765731024447, 2417269431879492618387904), (41, 3, 415862392689807874605, 2417435776836568541537746), (42, 3, 249517435613884724763, 2417602121793644464687588), (43, 3, 83172478537961574921, 2417768466750720387837430), (44, 3, 64689705529525669383, 2417786949523728823742968), (45, 3, 46206932521089763845, 2417805432296737259648506), (46, 3, 27724159512653858307, 2417823915069745695554044), (47, 3, 9241386504217952769, 2417842397842754131459582), (48, 3, 9205357706930553343, 2417842433871551418859008), (49, 3, 6575255504950395245, 2417845063973753399017106), (50, 3, 3945153302970237147, 2417847694075955379175204), (51, 3, 1315051100990079049, 2417850324178157359333302), (52, 3, 8196551382883369415, 2417843442677875466042936), (53, 3, 5854679559202406725, 2417845784549699147005626), (54, 3, 3512807735521444035, 2417848126421522827968316), (55, 3, 1170935911840481345, 2417850468293346508931006), (56, 3, 1134907114553081919, 2417850504322143796330432), (57, 3, 810647938966487085, 2417850828581319382925266), (58, 3, 486388763379892251, 2417851152840494969520100), (59, 3, 162129587793297417, 2417851477099670556114934), (60, 3, 126100790505897991, 2417851513128467843514360), (61, 3, 90071993218498565, 2417851549157265130913786), (62, 3, 54043195931099139, 2417851585186062418313212), (63, 3, 18014398643699713, 2417851621214859705712638), (64, 4, 2417851621214859974148095, 18014398375264256), (65, 4, 1727036872296328552962925, 690814766932929796449426), (66, 4, 1036222123377797131777755, 1381629515851461217634596), (67, 4, 345407374459265710592585, 2072444264769992638819766), (68, 4, 2152881580533779429035975, 264970058695478920376376), (69, 4, 1537772557524128163597125, 880079081705130185815226), (70, 4, 922663534514476898158275, 1495188104714781451254076), (71, 4, 307554511504825632719425, 2110297127724432716692926), (72, 4, 298091295766215613251135, 2119760343463042736161216), (73, 4, 212922354118725438036525, 2204929285110532911375826), (74, 4, 127753412471235262821915, 2290098226758023086590436), (75, 4, 42584470823745087607305, 2375267168405513261805046), (76, 4, 33121255085135068139015, 2384730384144123281273336), (77, 4, 23658039346525048670725, 2394193599882733300741626), (78, 4, 14194823607915029202435, 2403656815621343320209916), (79, 4, 4731607869305009734145, 2413120031359953339678206), (80, 4, 2413138478104027183448575, 4713161125231165963776), (81, 4, 1723670341502876559606125, 694181297726381789806226), (82, 4, 1034202204901725935763675, 1383649434327532413648676), (83, 4, 344734068300575311921225, 2073117570928683037491126), (84, 4, 2148684946257010505810375, 269166692972247843601976), (88, 4, 297510223327893762342975, 2120341415901364587069376), (92, 4, 33056691480877084704775, 2384794947748381264707576), (96, 4, 4722348468471135993855, 2413129290760787213418496), (97, 4, 3373106048907954281325, 2414478533180350395131026), (98, 4, 2023863629344772568795, 2415827775599913576843556), (99, 4, 674621209781590856265, 2417177018019476758556086), (100, 4, 4204830828090737528775, 2413646808401167611883576), (104, 4, 582207345427948273215, 2417269431883830401139136), (108, 4, 64689705047549808135, 2417786949524210799604216), (112, 4, 9205357638345294335, 2417842433871620004118016), (113, 4, 6575255455960924525, 2417845063973802388487826), (114, 4, 3945153273576554715, 2417847694075984772857636), (115, 4, 1315051091192184905, 2417850324178167157227446), (116, 4, 8196551321814303175, 2417843442677936535109176), (120, 4, 1134907106097365055, 2417850504322152252047296), (124, 4, 126100789566373895, 2417851513128468783038456), (192, 4, 134217727, 2417851639229258215194624), (193, 4, 95869805, 2417851639229258253542546), (194, 4, 57521883, 2417851639229258291890468), (195, 4, 19173961, 2417851639229258330238390), (196, 4, 119508935, 2417851639229258229903416), (197, 4, 85363525, 2417851639229258264048826), (198, 4, 51218115, 2417851639229258298194236), (199, 4, 17072705, 2417851639229258332339646), (200, 4, 16547391, 2417851639229258332864960), (201, 4, 11819565, 2417851639229258337592786), (202, 4, 7091739, 2417851639229258342320612), (203, 4, 2363913, 2417851639229258347048438), (204, 4, 1838599, 2417851639229258347573752), (205, 4, 1313285, 2417851639229258348099066), (206, 4, 787971, 2417851639229258348624380), (207, 4, 262657, 2417851639229258349149694), (208, 4, 133956095, 2417851639229258215456256), (209, 4, 95682925, 2417851639229258253729426), (210, 4, 57409755, 2417851639229258292002596), (211, 4, 19136585, 2417851639229258330275766), (212, 4, 119275975, 2417851639229258230136376), (216, 4, 16515135, 2417851639229258332897216), (220, 4, 1835015, 2417851639229258347577336), (224, 4, 262143, 2417851639229258349150208), (225, 4, 187245, 2417851639229258349225106), (226, 4, 112347, 2417851639229258349300004), (227, 4, 37449, 2417851639229258349374902), (228, 4, 233415, 2417851639229258349178936), (232, 4, 32319, 2417851639229258349380032), (236, 4, 3591, 2417851639229258349408760), (240, 4, 511, 2417851639229258349411840), (241, 4, 365, 2417851639229258349411986), (242, 4, 219, 2417851639229258349412132), (243, 4, 73, 2417851639229258349412278), (244, 4, 455, 2417851639229258349411896), (248, 4, 63, 2417851639229258349412288), (252, 4, 7, 2417851639229258349412344)]
  | 3, 4 => [(0, 4, 2417851639229258349412351, 0), (1, 4, 1727036885163755963865965, 690814754065502385546386), (2, 4, 1036222131098253578319579, 1381629508131004771092772), (3, 4, 345407377032751192773193, 2072444262196507156639158), (4, 4, 2152881596573997160435655, 264970042655261188976696), (5, 4, 1537772568981426543168325, 880079070247831806244026), (6, 4, 922663541388855925900995, 1495188097840402423511356), (7, 4, 307554513796285308633665, 2110297125432973040778686), (8, 4, 298091297987168837598783, 2119760341242089511813568), (9, 4, 212922355705120598284845, 2204929283524137751127506), (10, 4, 127753413423072358970907, 2290098225806185990441444), (11, 4, 42584471141024119656969, 2375267168088234229755382), (12, 4, 33121255331907648622087, 2384730383897350700790264), (13, 4, 23658039522791177587205, 2394193599706467171825146), (14, 4, 14194823713674706552323, 2403656815515583642860028), (15, 4, 4731607904558235517441, 2413120031324700113894910), (16, 4, 2413138496083309906100735, 4713143145948443311616), (17, 4, 1723670354345221361500525, 694181284884036987911826), (18, 4, 1034202212607132816900315, 1383649426622125532512036), (19, 4, 344734070869044272300105, 2073117568360214077112246), (20, 4, 2148684962265960875295175, 269166676963297474117176), (21, 4, 1534774973047114910925125, 883076666182143438487226), (22, 4, 920864983828268946555075, 1496986655400989402857276), (23, 4, 306954994609422982185025, 2110896644619835367227326), (24, 4, 297510225544517659656255, 2120341413684740689756096), (25, 4, 212507303960369756897325, 2205344335268888592515026), (26, 4, 127504382376221854138395, 2290347256853036495273956), (27, 4, 42501460792073951379465, 2375350178437184398032886), (28, 4, 33056691727168628850695, 2384794947502089720561656), (29, 4, 23611922662263306321925, 2394239716566995043090426), (30, 4, 14167153597357983793155, 2403684485631900365619196), (31, 4, 4722384532452661264385, 2413129254696805688147966), (32, 4, 4722348503655373864959, 2413129290725602975547392), (33, 4, 3373106074039552760685, 2414478533155218796651666), (34, 4, 2023863644423731656411, 2415827775584834617755940), (35, 4, 674621214807910552137, 2417177018014450438860214), (36, 4, 4204830859419168509895, 2413646808369839180902456), (37, 4, 3003450613870834649925, 2414848188615387514762426), (38, 4, 1802070368322500789955, 2416049568860935848622396), (39, 4, 600690122774166929985, 2417250949106484182482366), (40, 4, 582207349765731024447, 2417269431879492618387904), (41, 4, 415862392689807874605, 2417435776836568541537746), (42, 4, 249517435613884724763, 2417602121793644464687588), (43, 4, 83172478537961574921, 2417768466750720387837430), (44, 4, 64689705529525669383, 2417786949523728823742968), (45, 4, 46206932521089763845, 2417805432296737259648506), (46, 4, 27724159512653858307, 2417823915069745695554044), (47, 4, 9241386504217952769, 2417842397842754131459582), (48, 4, 9205357706930553343, 2417842433871551418859008), (49, 4, 6575255504950395245, 2417845063973753399017106), (50, 4, 3945153302970237147, 2417847694075955379175204), (51, 4, 1315051100990079049, 2417850324178157359333302), (52, 4, 8196551382883369415, 2417843442677875466042936), (53, 4, 5854679559202406725, 2417845784549699147005626), (54, 4, 3512807735521444035, 2417848126421522827968316), (55, 4, 1170935911840481345, 2417850468293346508931006), (56, 4, 1134907114553081919, 2417850504322143796330432), (57, 4, 810647938966487085, 2417850828581319382925266), (58, 4, 486388763379892251, 2417851152840494969520100), (59, 4, 162129587793297417, 2417851477099670556114934), (60, 4, 126100790505897991, 2417851513128467843514360), (61, 4, 90071993218498565, 2417851549157265130913786), (62, 4, 54043195931099139, 2417851585186062418313212), (63, 4, 18014398643699713, 2417851621214859705712638), (64, 4, 2417851621214859974148095, 18014398375264256), (65, 4, 1727036872296328552962925, 690814766932929796449426), (66, 4, 1036222123377797131777755, 1381629515851461217634596), (67, 4, 345407374459265710592585, 2072444264769992638819766), (68, 4, 2152881580533779429035975, 264970058695478920376376), (69, 4, 1537772557524128163597125, 880079081705130185815226), (70, 4, 922663534514476898158275, 1495188104714781451254076), (71, 4, 307554511504825632719425, 2110297127724432716692926), (72, 4, 298091295766215613251135, 2119760343463042736161216), (73, 4, 212922354118725438036525, 2204929285110532911375826), (74, 4, 127753412471235262821915, 2290098226758023086590436), (75, 4, 42584470823745087607305, 2375267168405513261805046), (76, 4, 33121255085135068139015, 2384730384144123281273336), (77, 4, 23658039346525048670725, 2394193599882733300741626), (78, 4, 14194823607915029202435, 2403656815621343320209916), (79, 4, 4731607869305009734145, 2413120031359953339678206), (80, 4, 2413138478104027183448575, 4713161125231165963776), (81, 4, 1723670341502876559606125, 694181297726381789806226), (82, 4, 1034202204901725935763675, 1383649434327532413648676), (83, 4, 344734068300575311921225, 2073117570928683037491126), (84, 4, 2148684946257010505810375, 269166692972247843601976), (88, 4, 297510223327893762342975, 2120341415901364587069376), (92, 4, 33056691480877084704775, 2384794947748381264707576), (96, 4, 4722348468471135993855, 2413129290760787213418496), (97, 4, 3373106048907954281325, 2414478533180350395131026), (98, 4, 2023863629344772568795, 2415827775599913576843556), (99, 4, 674621209781590856265, 2417177018019476758556086), (100, 4, 4204830828090737528775, 2413646808401167611883576), (104, 4, 582207345427948273215, 2417269431883830401139136), (108, 4, 64689705047549808135, 2417786949524210799604216), (112, 4, 9205357638345294335, 2417842433871620004118016), (113, 4, 6575255455960924525, 2417845063973802388487826), (114, 4, 3945153273576554715, 2417847694075984772857636), (115, 4, 1315051091192184905, 2417850324178167157227446), (116, 4, 8196551321814303175, 2417843442677936535109176), (120, 4, 1134907106097365055, 2417850504322152252047296), (124, 4, 126100789566373895, 2417851513128468783038456), (128, 4, 18014398509481983, 2417851621214859839930368), (129, 4, 12867427506772845, 2417851626361830842639506), (130, 4, 7720456504063707, 2417851631508801845348644), (131, 4, 2573485501354569, 2417851636655772848057782), (132, 4, 16040217850908615, 2417851623189040498503736), (133, 4, 11457298464934725, 2417851627771959884477626), (134, 4, 6874379078960835, 2417851632354879270451516), (135, 4, 2291459692986945, 2417851636937798656425406), (136, 4, 2220953240895039, 2417851637008305108517312), (137, 4, 1586395172067885, 2417851637642863177344466), (138, 4, 951837103240731, 2417851638277421246171620), (139, 4, 317279034413577, 2417851638911979314998774), (140, 4, 246772582321671, 2417851638982485767090680), (141, 4, 176266130229765, 2417851639052992219182586), (142, 4, 105759678137859, 2417851639123498671274492), (143, 4, 35253226045953, 2417851639194005123366398), (144, 4, 17979282856608255, 2417851621249975492804096), (145, 4, 12842344897577325, 2417851626386913451835026), (146, 4, 7705406938546395, 2417851631523851410865956), (147, 4, 2568468979515465, 2417851636660789369896886), (148, 4, 16008950488760775, 2417851623220307860651576), (152, 4, 2216623913828415, 2417851637012634435583936), (156, 4, 246291545980935, 2417851638982966803431416), (160, 4, 35184238133247, 2417851639194074111279104), (161, 4, 25131598666605, 2417851639204126750745746), (162, 4, 15078959199963, 2417851639214179390212388), (163, 4, 5026319733321, 2417851639224232029679030), (164, 4, 31328431214535, 2417851639197929918197816), (168, 4, 4337782783551, 2417851639224920566628800), (172, 4, 481975864839, 2417851639228776373547512), (176, 4, 68585259519, 2417851639229189764152832), (177, 4, 48989471085, 2417851639229209359941266), (178, 4, 29393682651, 2417851639229228955729700), (179, 4, 9797894217, 2417851639229248551518134), (180, 4, 61069066695, 2417851639229197280345656), (184, 4, 8455716927, 2417851639229249893695424), (188, 4, 939524103, 2417851639229257409888248), (192, 4, 134217727, 2417851639229258215194624), (193, 4, 95869805, 2417851639229258253542546), (194, 4, 57521883, 2417851639229258291890468), (195, 4, 19173961, 2417851639229258330238390), (196, 4, 119508935, 2417851639229258229903416), (197, 4, 85363525, 2417851639229258264048826), (198, 4, 51218115, 2417851639229258298194236), (199, 4, 17072705, 2417851639229258332339646), (200, 4, 16547391, 2417851639229258332864960), (201, 4, 11819565, 2417851639229258337592786), (202, 4, 7091739, 2417851639229258342320612), (203, 4, 2363913, 2417851639229258347048438), (204, 4, 1838599, 2417851639229258347573752), (205, 4, 1313285, 2417851639229258348099066), (206, 4, 787971, 2417851639229258348624380), (207, 4, 262657, 2417851639229258349149694), (208, 4, 133956095, 2417851639229258215456256), (209, 4, 95682925, 2417851639229258253729426), (210, 4, 57409755, 2417851639229258292002596), (211, 4, 19136585, 2417851639229258330275766), (212, 4, 119275975, 2417851639229258230136376), (216, 4, 16515135, 2417851639229258332897216), (220, 4, 1835015, 2417851639229258347577336), (224, 4, 262143, 2417851639229258349150208), (225, 4, 187245, 2417851639229258349225106), (226, 4, 112347, 2417851639229258349300004), (227, 4, 37449, 2417851639229258349374902), (228, 4, 233415, 2417851639229258349178936), (232, 4, 32319, 2417851639229258349380032), (236, 4, 3591, 2417851639229258349408760), (240, 4, 511, 2417851639229258349411840), (241, 4, 365, 2417851639229258349411986), (242, 4, 219, 2417851639229258349412132), (243, 4, 73, 2417851639229258349412278), (244, 4, 455, 2417851639229258349411896), (248, 4, 63, 2417851639229258349412288), (252, 4, 7, 2417851639229258349412344)]
  | 4, 0 => [(0, 0, 2417851639229258349412351, 0), (1, 1, 1727036885163755963865965, 690814754065502385546386), (3, 1, 345407377032751192773193, 2072444262196507156639158), (5, 2, 1537772568981426543168325, 880079070247831806244026), (7, 2, 307554513796285308633665, 2110297125432973040778686), (15, 2, 4731607904558235517441, 2413120031324700113894910), (21, 3, 1534774973047114910925125, 883076666182143438487226), (23, 3, 306954994609422982185025, 2110896644619835367227326), (31, 3, 4722384532452661264385, 2413129254696805688147966), (63, 3, 18014398643699713, 2417851621214859705712638), (85, 4, 1534774961612150361293125, 883076677617107988119226), (87, 4, 306954992322430072258625, 2110896646906828277153726), (95, 4, 4722384497268154957825, 2413129254731990194454526), (127, 4, 18014398509481985, 2417851621214859839930366), (255, 4, 1, 2417851639229258349412350)]
  | 4, 1 => [(0, 1, 2417851639229258349412351, 0), (1, 1, 1727036885163755963865965, 690814754065502385546386), (2, 1, 1036222131098253578319579, 1381629508131004771092772), (3, 1, 345407377032751192773193, 2072444262196507156639158), (4, 2, 2152881596573997160435655, 264970042655261188976696), (5, 2, 1537772568981426543168325, 880079070247831806244026), (6, 2, 922663541388855925900995, 1495188097840402423511356), (7, 2, 307554513796285308633665, 2110297125432973040778686), (12, 2, 33121255331907648622087, 2384730383897350700790264), (13, 2, 23658039522791177587205, 2394193599706467171825146), (14, 2, 14194823713674706552323, 2403656815515583642860028), (15, 2, 4731607904558235517441, 2413120031324700113894910), (20, 3, 2148684962265960875295175, 269166676963297474117176), (21, 3, 1534774973047114910925125, 883076666182143438487226), (22, 3, 920864983828268946555075, 1496986655400989402857276), (23, 3, 306954994609422982185025, 2110896644619835367227326), (28, 3, 33056691727168628850695, 2384794947502089720561656), (29, 3, 23611922662263306321925, 2394239716566995043090426), (30, 3, 14167153597357983793155, 2403684485631900365619196), (31, 3, 4722384532452661264385, 2413129254696805688147966), (60, 3, 126100790505897991, 2417851513128467843514360), (61, 3, 90071993218498565, 2417851549157265130913786), (62, 3, 54043195931099139, 2417851585186062418313212), (63, 3, 18014398643699713, 2417851621214859705712638), (84, 4, 2148684946257010505810375, 269166692972247843601976), (85, 4, 1534774961612150361293125, 883076677617107988119226), (86, 4, 920864976967290216775875, 1496986662261968132636476), (87, 4, 306954992322430072258625, 2110896646906828277153726), (92, 4, 33056691480877084704775, 2384794947748381264707576), (93, 4, 23611922486340774789125, 2394239716742917574623226), (94, 4, 14167153491804464873475, 2403684485737453884538876), (95, 4, 4722384497268154957825, 2413129254731990194454526), (124, 4, 126100789566373895, 2417851513128468783038456), (125, 4, 90071992547409925, 2417851549157265802002426), (126, 4, 54043195528445955, 2417851585186062820966396), (127, 4, 18014398509481985, 2417851621214859839930366), (252, 4, 7, 2417851639229258349412344), (253, 4, 5, 2417851639229258349412346), (254, 4, 3, 2417851639229258349412348), (255, 4, 1, 2417851639229258349412350)]
  | 4, 2 => [(0, 2, 2417851639229258349412351, 0), (1, 2, 1727036885163755963865965, 690814754065502385546386), (2, 2, 1036222131098253578319579, 1381629508131004771092772), (3, 2, 345407377032751192773193, 2072444262196507156639158), (4, 2, 2152881596573997160435655, 264970042655261188976696), (5, 2, 1537772568981426543168325, 880079070247831806244026), (6, 2, 922663541388855925900995, 1495188097840402423511356), (7, 2, 307554513796285308633665, 2110297125432973040778686), (8, 2, 298091297987168837598783, 2119760341242089511813568), (9, 2, 212922355705120598284845, 2204929283524137751127506), (10, 2, 127753413423072358970907, 2290098225806185990441444), (11, 2, 42584471141024119656969, 2375267168088234229755382), (12, 2, 33121255331907648622087, 2384730383897350700790264), (13, 2, 23658039522791177587205, 2394193599706467171825146), (14, 2, 14194823713674706552323, 2403656815515583642860028), (15, 2, 4731607904558235517441, 2413120031324700113894910), (16, 3, 2413138496083309906100735, 4713143145948443311616), (17, 3, 1723670354345221361500525, 694181284884036987911826), (18, 3, 1034202212607132816900315, 1383649426622125532512036), (19, 3, 344734070869044272300105, 2073117568360214077112246), (20, 3, 2148684962265960875295175, 269166676963297474117176), (21, 3, 1534774973047114910925125, 883076666182143438487226), (22, 3, 920864983828268946555075, 1496986655400989402857276), (23, 3, 306954994609422982185025, 2110896644619835367227326), (24, 3, 297510225544517659656255, 2120341413684740689756096), (25, 3, 212507303960369756897325, 2205344335268888592515026), (26, 3, 127504382376221854138395, 2290347256853036495273956), (27, 3, 42501460792073951379465, 2375350178437184398032886), (28, 3, 33056691727168628850695, 2384794947502089720561656), (29, 3, 23611922662263306321925, 2394239716566995043090426), (30, 3, 14167153597357983793155, 2403684485631900365619196), (31, 3, 4722384532452661264385, 2413129254696805688147966), (48, 3, 9205357706930553343, 2417842433871551418859008), (49, 3, 6575255504950395245, 2417845063973753399017106), (50, 3, 3945153302970237147, 2417847694075955379175204), (51, 3, 1315051100990079049, 2417850324178157359333302), (52, 3, 8196551382883369415, 2417843442677875466042936), (53, 3, 5854679559202406725, 2417845784549699147005626), (54, 3, 3512807735521444035, 2417848126421522827968316), (55, 3, 1170935911840481345, 2417850468293346508931006), (56, 3, 1134907114553081919, 2417850504322143796330432), (57, 3, 810647938966487085, 2417850828581319382925266), (58, 3, 486388763379892251, 2417851152840494969520100), (59, 3, 162129587793297417, 2417851477099670556114934), (60, 3, 126100790505897991, 2417851513128467843514360), (61, 3, 90071993218498565, 2417851549157265130913786), (62, 3, 54043195931099139, 2417851585186062418313212), (63, 3, 18014398643699713, 2417851621214859705712638), (80, 4, 2413138478104027183448575, 4713161125231165963776), (81, 4, 1723670341502876559606125, 694181297726381789806226), (82, 4, 1034202204901725935763675, 1383649434327532413648676), (83, 4, 344734068300575311921225, 2073117570928683037491126), (84, 4, 2148684946257010505810375, 269166692972247843601976), (85, 4, 1534774961612150361293125, 883076677617107988119226), (86, 4, 920864976967290216775875, 1496986662261968132636476), (87, 4, 306954992322430072258625, 2110896646906828277153726), (88, 4, 297510223327893762342975, 2120341415901364587069376), (89, 4, 212507302377066973102125, 2205344336852191376310226), (90, 4, 127504381426240183861275, 2290347257803018165551076), (91, 4, 42501460475413394620425, 2375350178753844954791926), (92, 4, 33056691480877084704775, 2384794947748381264707576), (93, 4, 23611922486340774789125, 2394239716742917574623226), (94, 4, 14167153491804464873475, 2403684485737453884538876), (95, 4, 4722384497268154957825, 2413129254731990194454526), (112, 4, 9205357638345294335, 2417842433871620004118016), (113, 4, 6575255455960924525, 2417845063973802388487826), (114, 4, 3945153273576554715, 2417847694075984772857636), (115, 4, 1315051091192184905, 2417850324178167157227446), (116, 4, 8196551321814303175, 2417843442677936535109176), (117, 4, 5854679515581645125, 2417845784549742767767226), (118, 4, 3512807709348987075, 2417848126421549000425276), (119, 4, 1170935903116329025, 2417850468293355233083326), (120, 4, 1134907106097365055, 2417850504322152252047296), (121, 4, 810647932926689325, 2417850828581325422723026), (122, 4, 486388759756013595, 2417851152840498593398756), (123, 4, 162129586585337865, 2417851477099671764074486), (124, 4, 126100789566373895, 2417851513128468783038456), (125, 4, 90071992547409925, 2417851549157265802002426), (126, 4, 54043195528445955, 2417851585186062820966396), (127, 4, 18014398509481985, 2417851621214859839930366), (240, 4, 511, 2417851639229258349411840), (241, 4, 365, 2417851639229258349411986), (242, 4, 219, 2417851639229258349412132), (243, 4, 73, 2417851639229258349412278), (244, 4, 455, 2417851639229258349411896), (245, 4, 325, 2417851639229258349412026), (246, 4, 195, 2417851639229258349412156), (247, 4, 65, 2417851639229258349412286), (248, 4, 63, 2417851639229258349412288), (249, 4, 45, 2417851639229258349412306), (250, 4, 27, 2417851639229258349412324), (251, 4, 9, 2417851639229258349412342), (252, 4, 7, 2417851639229258349412344), (253, 4, 5, 2417851639229258349412346), (254, 4, 3, 2417851639229258349412348), (255, 4, 1, 2417851639229258349412350)]
  | 4, 3 => [(0, 3, 2417851639229258349412351, 0), (1, 3, 1727036885163755963865965, 690814754065502385546386), (2, 3, 1036222131098253578319579, 1381629508131004771092772), (3, 3, 345407377032751192773193, 2072444262196507156639158), (4, 3, 2152881596573997160435655, 264970042655261188976696), (5, 3, 1537772568981426543168325, 880079070247831806244026), (6, 3, 922663541388855925900995, 1495188097840402423511356), (7, 3, 307554513796285308633665, 2110297125432973040778686), (8, 3, 298091297987168837598783, 2119760341242089511813568), (9, 3, 212922355705120598284845, 2204929283524137751127506), (10, 3, 127753413423072358970907, 2290098225806185990441444), (11, 3, 42584471141024119656969, 2375267168088234229755382), (12, 3, 33121255331907648622087, 2384730383897350700790264), (13, 3, 23658039522791177587205, 2394193599706467171825146), (14, 3, 14194823713674706552323, 2403656815515583642860028), (15, 3, 4731607904558235517441, 2413120031324700113894910), (16, 3, 2413138496083309906100735, 4713143145948443311616), (17, 3, 1723670354345221361500525, 694181284884036987911826), (18, 3, 1034202212607132816900315, 1383649426622125532512036), (19, 3, 344734070869044272300105, 2073117568360214077112246), (20, 3, 2148684962265960875295175, 269166676963297474117176), (21, 3, 1534774973047114910925125, 883076666182143438487226), (22, 3, 920864983828268946555075, 1496986655400989402857276), (23, 3, 306954994609422982185025, 2110896644619835367227326), (24, 3, 297510225544517659656255, 2120341413684740689756096), (25, 3, 212507303960369756897325, 2205344335268888592515026), (26, 3, 127504382376221854138395, 2290347256853036495273956), (27, 3, 42501460792073951379465, 2375350178437184398032886), (28, 3, 33056691727168628850695, 2384794947502089720561656), (29, 3, 23611922662263306321925, 2394239716566995043090426), (30, 3, 14167153597357983793155, 2403684485631900365619196), (31, 3, 4722384532452661264385, 2413129254696805688147966), (32, 3, 4722348503655373864959, 2413129290725602975547392), (33, 3, 3373106074039552760685, 2414478533155218796651666), (34, 3, 2023863644423731656411, 2415827775584834617755940), (35, 3, 674621214807910552137, 2417177018014450438860214), (36, 3, 4204830859419168509895, 2413646808369839180902456), (37, 3, 3003450613870834649925, 2414848188615387514762426), (38, 3, 1802070368322500789955, 2416049568860935848622396), (39, 3, 600690122774166929985, 2417250949106484182482366), (40, 3, 582207349765731024447, 2417269431879492618387904), (41, 3, 415862392689807874605, 2417435776836568541537746), (42, 3, 249517435613884724763, 2417602121793644464687588), (43, 3, 83172478537961574921, 2417768466750720387837430), (44, 3, 64689705529525669383, 2417786949523728823742968), (45, 3, 46206932521089763845, 2417805432296737259648506), (46, 3, 27724159512653858307, 2417823915069745695554044), (47, 3, 9241386504217952769, 2417842397842754131459582), (48, 3, 9205357706930553343, 2417842433871551418859008), (49, 3, 6575255504950395245, 2417845063973753399017106), (50, 3, 3945153302970237147, 2417847694075955379175204), (51, 3, 1315051100990079049, 2417850324178157359333302), (52, 3, 8196551382883369415, 2417843442677875466042936), (53, 3, 5854679559202406725, 2417845784549699147005626), (54, 3, 3512807735521444035, 2417848126421522827968316), (55, 3, 1170935911840481345, 2417850468293346508931006), (56, 3, 1134907114553081919, 2417850504322143796330432), (57, 3, 810647938966487085, 2417850828581319382925266), (58, 3, 486388763379892251, 2417851152840494969520100), (59, 3, 162129587793297417, 2417851477099670556114934), (60, 3, 126100790505897991, 2417851513128467843514360), (61, 3, 90071993218498565, 2417851549157265130913786), (62, 3, 54043195931099139, 2417851585186062418313212), (63, 3, 18014398643699713, 2417851621214859705712638), (64, 4, 2417851621214859974148095, 18014398375264256), (65, 4, 1727036872296328552962925, 690814766932929796449426), (66, 4, 1036222123377797131777755, 1381629515851461217634596), (67, 4, 345407374459265710592585, 2072444264769992638819766), (68, 4, 2152881580533779429035975, 264970058695478920376376), (69, 4, 1537772557524128163597125, 880079081705130185815226), (70, 4, 922663534514476898158275, 1495188104714781451254076), (71, 4, 307554511504825632719425, 2110297127724432716692926), (72, 4, 298091295766215613251135, 2119760343463042736161216), (73, 4, 212922354118725438036525, 2204929285110532911375826), (74, 4, 127753412471235262821915, 2290098226758023086590436), (75, 4, 42584470823745087607305, 2375267168405513261805046), (76, 4, 33121255085135068139015, 2384730384144123281273336), (77, 4, 23658039346525048670725, 2394193599882733300741626), (78, 4, 14194823607915029202435, 2403656815621343320209916), (79, 4, 4731607869305009734145, 2413120031359953339678206), (80, 4, 2413138478104027183448575, 4713161125231165963776), (81, 4, 1723670341502876559606125, 694181297726381789806226), (82, 4, 1034202204901725935763675, 1383649434327532413648676), (83, 4, 344734068300575311921225, 2073117570928683037491126), (84, 4, 2148684946257010505810375, 269166692972247843601976), (85, 4, 1534774961612150361293125, 883076677617107988119226), (86, 4, 920864976967290216775875, 1496986662261968132636476), (87, 4, 306954992322430072258625, 2110896646906828277153726), (88, 4, 297510223327893762342975, 2120341415901364587069376), (89, 4, 212507302377066973102125, 2205344336852191376310226), (90, 4, 127504381426240183861275, 2290347257803018165551076), (91, 4, 42501460475413394620425, 2375350178753844954791926), (92, 4, 33056691480877084704775, 2384794947748381264707576), (93, 4, 23611922486340774789125, 2394239716742917574623226), (94, 4, 14167153491804464873475, 2403684485737453884538876), (95, 4, 4722384497268154957825, 2413129254731990194454526), (96, 4, 4722348468471135993855, 2413129290760787213418496), (97, 4, 3373106048907954281325, 2414478533180350395131026), (98, 4, 2023863629344772568795, 2415827775599913576843556), (99, 4, 674621209781590856265, 2417177018019476758556086), (100, 4, 4204830828090737528775, 2413646808401167611883576), (101, 4, 3003450591493383949125, 2414848188637764965463226), (102, 4, 1802070354896030369475, 2416049568874362319042876), (103, 4, 600690118298676789825, 2417250949110959672622526), (104, 4, 582207345427948273215, 2417269431883830401139136), (105, 4, 415862389591391623725, 2417435776839666957788626), (106, 4, 249517433754834974235, 2417602121795503514438116), (107, 4, 83172477918278324745, 2417768466751340071087606), (108, 4, 64689705047549808135, 2417786949524210799604216), (109, 4, 46206932176821291525, 2417805432297081528120826), (110, 4, 27724159306092774915, 2417823915069952256637436), (111, 4, 9241386435364258305, 2417842397842822985154046), (112, 4, 9205357638345294335, 2417842433871620004118016), (113, 4, 6575255455960924525, 2417845063973802388487826), (114, 4, 3945153273576554715, 2417847694075984772857636), (115, 4, 1315051091192184905, 2417850324178167157227446), (116, 4, 8196551321814303175, 2417843442677936535109176), (117, 4, 5854679515581645125, 2417845784549742767767226), (118, 4, 3512807709348987075, 2417848126421549000425276), (119, 4, 1170935903116329025, 2417850468293355233083326), (120, 4, 1134907106097365055, 2417850504322152252047296), (121, 4, 810647932926689325, 2417850828581325422723026), (122, 4, 486388759756013595, 2417851152840498593398756), (123, 4, 162129586585337865, 2417851477099671764074486), (124, 4, 126100789566373895, 2417851513128468783038456), (125, 4, 90071992547409925, 2417851549157265802002426), (126, 4, 54043195528445955, 2417851585186062820966396), (127, 4, 18014398509481985, 2417851621214859839930366), (192, 4, 134217727, 2417851639229258215194624), (193, 4, 95869805, 2417851639229258253542546), (194, 4, 57521883, 2417851639229258291890468), (195, 4, 19173961, 2417851639229258330238390), (196, 4, 119508935, 2417851639229258229903416), (197, 4, 85363525, 2417851639229258264048826), (198, 4, 51218115, 2417851639229258298194236), (199, 4, 17072705, 2417851639229258332339646), (200, 4, 16547391, 2417851639229258332864960), (201, 4, 11819565, 2417851639229258337592786), (202, 4, 7091739, 2417851639229258342320612), (203, 4, 2363913, 2417851639229258347048438), (204, 4, 1838599, 2417851639229258347573752), (205, 4, 1313285, 2417851639229258348099066), (206, 4, 787971, 2417851639229258348624380), (207, 4, 262657, 2417851639229258349149694), (208, 4, 133956095, 2417851639229258215456256), (209, 4, 95682925, 2417851639229258253729426), (210, 4, 57409755, 2417851639229258292002596), (211, 4, 19136585, 2417851639229258330275766), (212, 4, 119275975, 2417851639229258230136376), (213, 4, 85197125, 2417851639229258264215226), (214, 4, 51118275, 2417851639229258298294076), (215, 4, 17039425, 2417851639229258332372926), (216, 4, 16515135, 2417851639229258332897216), (217, 4, 11796525, 2417851639229258337615826), (218, 4, 7077915, 2417851639229258342334436), (219, 4, 2359305, 2417851639229258347053046), (220, 4, 1835015, 2417851639229258347577336), (221, 4, 1310725, 2417851639229258348101626), (222, 4, 786435, 2417851639229258348625916), (223, 4, 262145, 2417851639229258349150206), (224, 4, 262143, 2417851639229258349150208), (225, 4, 187245, 2417851639229258349225106), (226, 4, 112347, 2417851639229258349300004), (227, 4, 37449, 2417851639229258349374902), (228, 4, 233415, 2417851639229258349178936), (229, 4, 166725, 2417851639229258349245626), (230, 4, 100035, 2417851639229258349312316), (231, 4, 33345, 2417851639229258349379006), (232, 4, 32319, 2417851639229258349380032), (233, 4, 23085, 2417851639229258349389266), (234, 4, 13851, 2417851639229258349398500), (235, 4, 4617, 2417851639229258349407734), (236, 4, 3591, 2417851639229258349408760), (237, 4, 2565, 2417851639229258349409786), (238, 4, 1539, 2417851639229258349410812), (239, 4, 513, 2417851639229258349411838), (240, 4, 511, 2417851639229258349411840), (241, 4, 365, 2417851639229258349411986), (242, 4, 219, 2417851639229258349412132), (243, 4, 73, 2417851639229258349412278), (244, 4, 455, 2417851639229258349411896), (245, 4, 325, 2417851639229258349412026), (246, 4, 195, 2417851639229258349412156), (247, 4, 65, 2417851639229258349412286), (248, 4, 63, 2417851639229258349412288), (249, 4, 45, 2417851639229258349412306), (250, 4, 27, 2417851639229258349412324), (251, 4, 9, 2417851639229258349412342), (252, 4, 7, 2417851639229258349412344), (253, 4, 5, 2417851639229258349412346), (254, 4, 3, 2417851639229258349412348), (255, 4, 1, 2417851639229258349412350)]
  | 4, 4 => [(0, 4, 2417851639229258349412351, 0), (1, 4, 1727036885163755963865965, 690814754065502385546386), (2, 4, 1036222131098253578319579, 1381629508131004771092772), (3, 4, 345407377032751192773193, 2072444262196507156639158), (4, 4, 2152881596573997160435655, 264970042655261188976696), (5, 4, 1537772568981426543168325, 880079070247831806244026), (6, 4, 922663541388855925900995, 1495188097840402423511356), (7, 4, 307554513796285308633665, 2110297125432973040778686), (8, 4, 298091297987168837598783, 2119760341242089511813568), (9, 4, 212922355705120598284845, 2204929283524137751127506), (10, 4, 127753413423072358970907, 2290098225806185990441444), (11, 4, 42584471141024119656969, 2375267168088234229755382), (12, 4, 33121255331907648622087, 2384730383897350700790264), (13, 4, 23658039522791177587205, 2394193599706467171825146), (14, 4, 14194823713674706552323, 2403656815515583642860028), (15, 4, 4731607904558235517441, 2413120031324700113894910), (16, 4, 2413138496083309906100735, 4713143145948443311616), (17, 4, 1723670354345221361500525, 694181284884036987911826), (18, 4, 1034202212607132816900315, 1383649426622125532512036), (19, 4, 344734070869044272300105, 2073117568360214077112246), (20, 4, 2148684962265960875295175, 269166676963297474117176), (21, 4, 1534774973047114910925125, 883076666182143438487226), (22, 4, 920864983828268946555075, 1496986655400989402857276), (23, 4, 306954994609422982185025, 2110896644619835367227326), (24, 4, 297510225544517659656255, 2120341413684740689756096), (25, 4, 212507303960369756897325, 2205344335268888592515026), (26, 4, 127504382376221854138395, 2290347256853036495273956), (27, 4, 42501460792073951379465, 2375350178437184398032886), (28, 4, 33056691727168628850695, 2384794947502089720561656), (29, 4, 23611922662263306321925, 2394239716566995043090426), (30, 4, 14167153597357983793155, 2403684485631900365619196), (31, 4, 4722384532452661264385, 2413129254696805688147966), (32, 4, 4722348503655373864959, 2413129290725602975547392), (33, 4, 3373106074039552760685, 2414478533155218796651666), (34, 4, 2023863644423731656411, 2415827775584834617755940), (35, 4, 674621214807910552137, 2417177018014450438860214), (36, 4, 4204830859419168509895, 2413646808369839180902456), (37, 4, 3003450613870834649925, 2414848188615387514762426), (38, 4, 1802070368322500789955, 2416049568860935848622396), (39, 4, 600690122774166929985, 2417250949106484182482366), (40, 4, 582207349765731024447, 2417269431879492618387904), (41, 4, 415862392689807874605, 2417435776836568541537746), (42, 4, 249517435613884724763, 2417602121793644464687588), (43, 4, 83172478537961574921, 2417768466750720387837430), (44, 4, 64689705529525669383, 2417786949523728823742968), (45, 4, 46206932521089763845, 2417805432296737259648506), (46, 4, 27724159512653858307, 2417823915069745695554044), (47, 4, 9241386504217952769, 2417842397842754131459582), (48, 4, 9205357706930553343, 2417842433871551418859008), (49, 4, 6575255504950395245, 2417845063973753399017106), (50, 4, 3945153302970237147, 2417847694075955379175204), (51, 4, 1315051100990079049, 2417850324178157359333302), (52, 4, 8196551382883369415, 2417843442677875466042936), (53, 4, 5854679559202406725, 2417845784549699147005626), (54, 4, 3512807735521444035, 2417848126421522827968316), (55, 4, 1170935911840481345, 2417850468293346508931006), (56, 4, 1134907114553081919, 2417850504322143796330432), (57, 4, 810647938966487085, 2417850828581319382925266), (58, 4, 486388763379892251, 2417851152840494969520100), (59, 4, 162129587793297417, 2417851477099670556114934), (60, 4, 126100790505897991, 2417851513128467843514360), (61, 4, 90071993218498565, 2417851549157265130913786), (62, 4, 54043195931099139, 2417851585186062418313212), (63, 4, 18014398643699713, 2417851621214859705712638), (64, 4, 2417851621214859974148095, 18014398375264256), (65, 4, 1727036872296328552962925, 690814766932929796449426), (66, 4, 1036222123377797131777755, 1381629515851461217634596), (67, 4, 345407374459265710592585, 2072444264769992638819766), (68, 4, 2152881580533779429035975, 264970058695478920376376), (69, 4, 1537772557524128163597125, 880079081705130185815226), (70, 4, 922663534514476898158275, 1495188104714781451254076), (71, 4, 307554511504825632719425, 2110297127724432716692926), (72, 4, 298091295766215613251135, 2119760343463042736161216), (73, 4, 212922354118725438036525, 2204929285110532911375826), (74, 4, 127753412471235262821915, 2290098226758023086590436), (75, 4, 42584470823745087607305, 2375267168405513261805046), (76, 4, 33121255085135068139015, 2384730384144123281273336), (77, 4, 23658039346525048670725, 2394193599882733300741626), (78, 4, 14194823607915029202435, 2403656815621343320209916), (79, 4, 4731607869305009734145, 2413120031359953339678206), (80, 4, 2413138478104027183448575, 4713161125231165963776), (81, 4, 1723670341502876559606125, 694181297726381789806226), (82, 4, 1034202204901725935763675, 1383649434327532413648676), (83, 4, 344734068300575311921225, 2073117570928683037491126), (84, 4, 2148684946257010505810375, 269166692972247843601976), (85, 4, 1534774961612150361293125, 883076677617107988119226), (86, 4, 920864976967290216775875, 1496986662261968132636476), (87, 4, 306954992322430072258625, 2110896646906828277153726), (88, 4, 297510223327893762342975, 2120341415901364587069376), (89, 4, 212507302377066973102125, 2205344336852191376310226), (90, 4, 127504381426240183861275, 2290347257803018165551076), (91, 4, 42501460475413394620425, 2375350178753844954791926), (92, 4, 33056691480877084704775, 2384794947748381264707576), (93, 4, 23611922486340774789125, 2394239716742917574623226), (94, 4, 14167153491804464873475, 2403684485737453884538876), (95, 4, 4722384497268154957825, 2413129254731990194454526), (96, 4, 4722348468471135993855, 2413129290760787213418496), (97, 4, 3373106048907954281325, 2414478533180350395131026), (98, 4, 2023863629344772568795, 2415827775599913576843556), (99, 4, 674621209781590856265, 2417177018019476758556086), (100, 4, 4204830828090737528775, 2413646808401167611883576), (101, 4, 3003450591493383949125, 2414848188637764965463226), (102, 4, 1802070354896030369475, 2416049568874362319042876), (103, 4, 600690118298676789825, 2417250949110959672622526), (104, 4, 582207345427948273215, 2417269431883830401139136), (105, 4, 415862389591391623725, 2417435776839666957788626), (106, 4, 249517433754834974235, 2417602121795503514438116), (107, 4, 83172477918278324745, 2417768466751340071087606), (108, 4, 64689705047549808135, 2417786949524210799604216), (109, 4, 46206932176821291525, 2417805432297081528120826), (110, 4, 27724159306092774915, 2417823915069952256637436), (111, 4, 9241386435364258305, 2417842397842822985154046), (112, 4, 9205357638345294335, 2417842433871620004118016), (113, 4, 6575255455960924525, 2417845063973802388487826), (114, 4, 3945153273576554715, 2417847694075984772857636), (115, 4, 1315051091192184905, 2417850324178167157227446), (116, 4, 8196551321814303175, 2417843442677936535109176), (117, 4, 5854679515581645125, 2417845784549742767767226), (118, 4, 3512807709348987075, 2417848126421549000425276), (119, 4, 1170935903116329025, 2417850468293355233083326), (120, 4, 1134907106097365055, 2417850504322152252047296), (121, 4, 810647932926689325, 2417850828581325422723026), (122, 4, 486388759756013595, 2417851152840498593398756), (123, 4, 162129586585337865, 2417851477099671764074486), (124, 4, 126100789566373895, 2417851513128468783038456), (125, 4, 90071992547409925, 2417851549157265802002426), (126, 4, 54043195528445955, 2417851585186062820966396), (127, 4, 18014398509481985, 2417851621214859839930366), (128, 4, 18014398509481983, 2417851621214859839930368), (129, 4, 12867427506772845, 2417851626361830842639506), (130, 4, 7720456504063707, 2417851631508801845348644), (131, 4, 2573485501354569, 2417851636655772848057782), (132, 4, 16040217850908615, 2417851623189040498503736), (133, 4, 11457298464934725, 2417851627771959884477626), (134, 4, 6874379078960835, 2417851632354879270451516), (135, 4, 2291459692986945, 2417851636937798656425406), (136, 4, 2220953240895039, 2417851637008305108517312), (137, 4, 1586395172067885, 2417851637642863177344466), (138, 4, 951837103240731, 2417851638277421246171620), (139, 4, 317279034413577, 2417851638911979314998774), (140, 4, 246772582321671, 2417851638982485767090680), (141, 4, 176266130229765, 2417851639052992219182586), (142, 4, 105759678137859, 2417851639123498671274492), (143, 4, 35253226045953, 2417851639194005123366398), (144, 4, 17979282856608255, 2417851621249975492804096), (145, 4, 12842344897577325, 2417851626386913451835026), (146, 4, 7705406938546395, 2417851631523851410865956), (147, 4, 2568468979515465, 2417851636660789369896886), (148, 4, 16008950488760775, 2417851623220307860651576), (149, 4, 11434964634829125, 2417851627794293714583226), (150, 4, 6860978780897475, 2417851632368279568514876), (151, 4, 2286992926965825, 2417851636942265422446526), (152, 4, 2216623913828415, 2417851637012634435583936), (153, 4, 1583302795591725, 2417851637645955553820626), (154, 4, 949981677355035, 2417851638279276672057316), (155, 4, 316660559118345, 2417851638912597790294006), (156, 4, 246291545980935, 2417851638982966803431416), (157, 4, 175922532843525, 2417851639053335816568826), (158, 4, 105553519706115, 2417851639123704829706236), (159, 4, 35184506568705, 2417851639194073842843646), (160, 4, 35184238133247, 2417851639194074111279104), (161, 4, 25131598666605, 2417851639204126750745746), (162, 4, 15078959199963, 2417851639214179390212388), (163, 4, 5026319733321, 2417851639224232029679030), (164, 4, 31328431214535, 2417851639197929918197816), (165, 4, 22377450867525, 2417851639206880898544826), (166, 4, 13426470520515, 2417851639215831878891836), (167, 4, 4475490173505, 2417851639224782859238846), (168, 4, 4337782783551, 2417851639224920566628800), (169, 4, 3098416273965, 2417851639226159933138386), (170, 4, 1859049764379, 2417851639227399299647972), (171, 4, 619683254793, 2417851639228638666157558), (172, 4, 481975864839, 2417851639228776373547512), (173, 4, 344268474885, 2417851639228914080937466), (174, 4, 206561084931, 2417851639229051788327420), (175, 4, 68853694977, 2417851639229189495717374), (176, 4, 68585259519, 2417851639229189764152832), (177, 4, 48989471085, 2417851639229209359941266), (178, 4, 29393682651, 2417851639229228955729700), (179, 4, 9797894217, 2417851639229248551518134), (180, 4, 61069066695, 2417851639229197280345656), (181, 4, 43620761925, 2417851639229214728650426), (182, 4, 26172457155, 2417851639229232176955196), (183, 4, 8724152385, 2417851639229249625259966), (184, 4, 8455716927, 2417851639229249893695424), (185, 4, 6039797805, 2417851639229252309614546), (186, 4, 3623878683, 2417851639229254725533668), (187, 4, 1207959561, 2417851639229257141452790), (188, 4, 939524103, 2417851639229257409888248), (189, 4, 671088645, 2417851639229257678323706), (190, 4, 402653187, 2417851639229257946759164), (191, 4, 134217729, 2417851639229258215194622), (192, 4, 134217727, 2417851639229258215194624), (193, 4, 95869805, 2417851639229258253542546), (194, 4, 57521883, 2417851639229258291890468), (195, 4, 19173961, 2417851639229258330238390), (196, 4, 119508935, 2417851639229258229903416), (197, 4, 85363525, 2417851639229258264048826), (198, 4, 51218115, 2417851639229258298194236), (199, 4, 17072705, 2417851639229258332339646), (200, 4, 16547391, 2417851639229258332864960), (201, 4, 11819565, 2417851639229258337592786), (202, 4, 7091739, 2417851639229258342320612), (203, 4, 2363913, 2417851639229258347048438), (204, 4, 1838599, 2417851639229258347573752), (205, 4, 1313285, 2417851639229258348099066), (206, 4, 787971, 2417851639229258348624380), (207, 4, 262657, 2417851639229258349149694), (208, 4, 133956095, 2417851639229258215456256), (209, 4, 95682925, 2417851639229258253729426), (210, 4, 57409755, 2417851639229258292002596), (211, 4, 19136585, 2417851639229258330275766), (212, 4, 119275975, 2417851639229258230136376), (213, 4, 85197125, 2417851639229258264215226), (214, 4, 51118275, 2417851639229258298294076), (215, 4, 17039425, 2417851639229258332372926), (216, 4, 16515135, 2417851639229258332897216), (217, 4, 11796525, 2417851639229258337615826), (218, 4, 7077915, 2417851639229258342334436), (219, 4, 2359305, 2417851639229258347053046), (220, 4, 1835015, 2417851639229258347577336), (221, 4, 1310725, 2417851639229258348101626), (222, 4, 786435, 2417851639229258348625916), (223, 4, 262145, 2417851639229258349150206), (224, 4, 262143, 2417851639229258349150208), (225, 4, 187245, 2417851639229258349225106), (226, 4, 112347, 2417851639229258349300004), (227, 4, 37449, 2417851639229258349374902), (228, 4, 233415, 2417851639229258349178936), (229, 4, 166725, 2417851639229258349245626), (230, 4, 100035, 2417851639229258349312316), (231, 4, 33345, 2417851639229258349379006), (232, 4, 32319, 2417851639229258349380032), (233, 4, 23085, 2417851639229258349389266), (234, 4, 13851, 2417851639229258349398500), (235, 4, 4617, 2417851639229258349407734), (236, 4, 3591, 2417851639229258349408760), (237, 4, 2565, 2417851639229258349409786), (238, 4, 1539, 2417851639229258349410812), (239, 4, 513, 2417851639229258349411838), (240, 4, 511, 2417851639229258349411840), (241, 4, 365, 2417851639229258349411986), (242, 4, 219, 2417851639229258349412132), (243, 4, 73, 2417851639229258349412278), (244, 4, 455, 2417851639229258349411896), (245, 4, 325, 2417851639229258349412026), (246, 4, 195, 2417851639229258349412156), (247, 4, 65, 2417851639229258349412286), (248, 4, 63, 2417851639229258349412288), (249, 4, 45, 2417851639229258349412306), (250, 4, 27, 2417851639229258349412324), (251, 4, 9, 2417851639229258349412342), (252, 4, 7, 2417851639229258349412344), (253, 4, 5, 2417851639229258349412346), (254, 4, 3, 2417851639229258349412348), (255, 4, 1, 2417851639229258349412350)]
  | _, _ => []

def perm4 (p : Fin 24) : Fin 4 → Fin 4 :=
  match p.val with
  | 0 => ![0, 1, 2, 3] | 1 => ![0, 1, 3, 2] | 2 => ![0, 2, 1, 3] | 3 => ![0, 2, 3, 1]
  | 4 => ![0, 3, 1, 2] | 5 => ![0, 3, 2, 1] | 6 => ![1, 0, 2, 3] | 7 => ![1, 0, 3, 2]
  | 8 => ![1, 2, 0, 3] | 9 => ![1, 2, 3, 0] | 10 => ![1, 3, 0, 2] | 11 => ![1, 3, 2, 0]
  | 12 => ![2, 0, 1, 3] | 13 => ![2, 0, 3, 1] | 14 => ![2, 1, 0, 3] | 15 => ![2, 1, 3, 0]
  | 16 => ![2, 3, 0, 1] | 17 => ![2, 3, 1, 0] | 18 => ![3, 0, 1, 2] | 19 => ![3, 0, 2, 1]
  | 20 => ![3, 1, 0, 2] | 21 => ![3, 1, 2, 0] | 22 => ![3, 2, 0, 1] | _ => ![3, 2, 1, 0]

theorem perm4_bij : ∀ p : Fin 24, Function.Bijective (perm4 p) := by
  decide +kernel

noncomputable def perm4Equiv (p : Fin 24) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (perm4 p) (perm4_bij p)

theorem perm4Equiv_apply (p : Fin 24) (g : Fin 4) : perm4Equiv p g = perm4 p g := rfl

def flip4 (f : Fin 16) (g : Fin 4) : Bool := f.val.testBit g.val

def fixes4 (used : ℕ) (p : Fin 24) (f : Fin 16) : Bool :=
  (List.finRange 4).all fun g => if g.val < used then (perm4 p g == g) && !(flip4 f g) else true

theorem fixes4_spec (used : ℕ) (p : Fin 24) (f : Fin 16) (h : fixes4 used p f = true)
    (g : Fin 4) (hg : g.val < used) : perm4Equiv p g = g ∧ flip4 f g = false := by
  unfold fixes4 at h
  rw [List.all_eq_true] at h
  have hg' := h g (List.mem_finRange g)
  simp only [hg, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hg'
  exact hg'

def symSlotB (p : Fin 24) (f : Fin 16) (s : Slot) : Slot :=
  (perm4 p s.1, xor s.2 (flip4 f s.1))

def applySym4 (p : Fin 24) (f : Fin 16) (w : ℕ) : ℕ :=
  let bit (g : Fin 4) (d : Bool) : ℕ :=
    if w.testBit (2 * g.val + d.toNat) then 2 ^ slotId (symSlotB p f (g, d)) else 0
  bit 0 false + bit 0 true + bit 1 false + bit 1 true +
  bit 2 false + bit 2 true + bit 3 false + bit 3 true

theorem applySym4_eq_slotBits (p : Fin 24) (f : Fin 16) (w : Fin 256) :
    applySym4 p f w.val = slotBits ((slots w.val).image (symSlot (perm4Equiv p) (flip4 f))) := by
  have hinj := symSlot_injective (perm4Equiv p) (flip4 f)
  unfold slotBits
  rw [Finset.sum_image (fun a _ b _ h => hinj h)]
  unfold slots
  rw [Finset.sum_filter]
  have hsum : ∑ s : Slot, (if w.val.testBit (slotId s) = true then 2 ^ slotId (symSlot (perm4Equiv p) (flip4 f) s) else 0) =
      applySym4 p f w.val := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_four, Fintype.sum_bool, applySym4, symSlot, symSlotB, perm4Equiv_apply, slotId,
      Bool.toNat_false, Bool.toNat_true]
    ac_rfl
  exact hsum.symm

theorem applySym4_slots (p : Fin 24) (f : Fin 16) (w : Fin 256) :
    slots (applySym4 p f w.val) = (slots w.val).image (symSlot (perm4Equiv p) (flip4 f)) := by
  rw [applySym4_eq_slotBits, slots_slotBits]

theorem applySym4_lt (p : Fin 24) (f : Fin 16) (w : Fin 256) : applySym4 p f w.val < 256 := by
  rw [applySym4_eq_slotBits]
  exact slotBits_lt _

def isCap1Mask (w : ℕ) : Bool :=
  fitsMask w && (List.range 8).countP (fun k => w.testBit k) ≤ 1

def isCap2Mask (w : ℕ) : Bool :=
  fitsMask w && (List.range 8).countP (fun k => w.testBit k) ≤ 2

def gateCountB (w : ℕ) : ℕ :=
  (if w % 4 != 0 then 1 else 0) + (if (w / 4) % 4 != 0 then 1 else 0) +
  (if (w / 16) % 4 != 0 then 1 else 0) + (if (w / 64) % 4 != 0 then 1 else 0)

theorem isCap1Mask_of_cap : ∀ w : Fin 256,
    Consistent (slots w.val) → (slots w.val).card ≤ 1 → isCap1Mask w.val = true := by
  unfold Consistent
  decide +kernel

theorem isCap2Mask_of_cap : ∀ w : Fin 256,
    Consistent (slots w.val) → (slots w.val).card ≤ 2 → isCap2Mask w.val = true := by
  unfold Consistent
  decide +kernel

theorem gateCountB_eq : ∀ w : Fin 256,
    ((slots w.val).image Prod.fst).card = gateCountB w.val := by
  decide +kernel

theorem sym4_comp (σ1 σ2 : Equiv.Perm (Fin 4)) (f1 f2 : Fin 4 → Bool) (s : Slot) :
    symSlot σ2 f2 (symSlot σ1 f1 s) = symSlot (σ1.trans σ2) (fun g => xor (f1 g) (f2 (σ1 g))) s := by
  rcases s with ⟨g, d⟩
  simp only [symSlot, Equiv.trans_apply]
  cases d <;> cases f1 g <;> cases f2 (σ1 g) <;> rfl

theorem image_symSlot_comp (σ1 σ2 : Equiv.Perm (Fin 4)) (f1 f2 : Fin 4 → Bool) (S : Finset Slot) :
    (S.image (symSlot σ1 f1)).image (symSlot σ2 f2) =
      S.image (symSlot (σ1.trans σ2) (fun g => xor (f1 g) (f2 (σ1 g)))) := by
  rw [Finset.image_image]
  congr 1
  funext s
  exact sym4_comp σ1 σ2 f1 f2 s

theorem slots_image_fixed (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Bool) (used : ℕ)
    (hfix : ∀ g : Fin 4, g.val < used → σ g = g ∧ f g = false)
    (w : ℕ) (hw : w < 2 ^ (2 * used)) :
    (slots w).image (symSlot σ f) = slots w := by
  ext s
  constructor
  · intro hs
    rcases Finset.mem_image.mp hs with ⟨t, ht, rfl⟩
    have htb : w.testBit (slotId t) = true := (Finset.mem_filter.mp ht).2
    have hlt : slotId t < 2 * used := by
      by_contra hge
      have hpow : 2 ^ (2 * used) ≤ 2 ^ slotId t := Nat.pow_le_pow_right (by decide) (by omega)
      have hwf : w.testBit (slotId t) = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hw hpow)
      simp [hwf] at htb
    have hgt : t.1.val < used := by unfold slotId at hlt; omega
    obtain ⟨hσ, hf⟩ := hfix t.1 hgt
    have heq : symSlot σ f t = t := by
      rcases t with ⟨g, d⟩; simp [symSlot, hσ, hf]
    rwa [heq]
  · intro hs
    have htb : w.testBit (slotId s) = true := (Finset.mem_filter.mp hs).2
    have hlt : slotId s < 2 * used := by
      by_contra hge
      have hpow : 2 ^ (2 * used) ≤ 2 ^ slotId s := Nat.pow_le_pow_right (by decide) (by omega)
      have hwf : w.testBit (slotId s) = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hw hpow)
      simp [hwf] at htb
    have hgs : s.1.val < used := by unfold slotId at hlt; omega
    obtain ⟨hσ, hf⟩ := hfix s.1 hgs
    have heq : symSlot σ f s = s := by
      rcases s with ⟨g, d⟩; simp [symSlot, hσ, hf]
    exact Finset.mem_image.mpr ⟨s, hs, heq⟩

def MaskInv (used vm : ℕ) : Prop :=
  ∀ i j : Fin 81, consMask i.val % (2 ^ (2 * used)) = consMask j.val % (2 ^ (2 * used)) →
    vm.testBit i.val = vm.testBit j.val

theorem consMask_lt : ∀ idx : Fin 81, consMask idx.val < 256 := by decide +kernel

theorem consMask_consistent : ∀ idx : Fin 81, Consistent (slots (consMask idx.val)) := by
  unfold Consistent
  decide +kernel

theorem consMask_surj_mask : ∀ m : Fin 256, fitsMask m.val = true → ∃ idx : Fin 81, consMask idx.val = m.val := by
  decide +kernel

theorem consMask_surj (M : Finset Slot) (hM : Consistent M) : ∃ idx : Fin 81, slots (consMask idx.val) = M := by
  obtain ⟨m, rfl⟩ := slotsSurj M
  obtain ⟨idx, hidx⟩ := consMask_surj_mask m (fitsSpec m hM)
  exact ⟨idx, by rw [hidx]⟩

theorem all81_testBit : ∀ idx : Fin 81, all81.testBit idx.val = true := by decide +kernel

theorem maskInv_all81 (used : ℕ) : MaskInv used all81 := by
  intro i j _
  rw [all81_testBit i, all81_testBit j]

theorem maskInv_land {used vm1 vm2 : ℕ} (h1 : MaskInv used vm1) (h2 : MaskInv used vm2) :
    MaskInv used (vm1 &&& vm2) := by
  intro i j hij
  rw [Nat.testBit_and, Nat.testBit_and, h1 i j hij, h2 i j hij]

theorem maskInv_lor {used vm1 vm2 : ℕ} (h1 : MaskInv used vm1) (h2 : MaskInv used vm2) :
    MaskInv used (vm1 ||| vm2) := by
  intro i j hij
  rw [Nat.testBit_or, Nat.testBit_or, h1 i j hij, h2 i j hij]

theorem maskInv_mono {u1 u2 vm : ℕ} (hle : u1 ≤ u2) (h : MaskInv u1 vm) : MaskInv u2 vm := by
  intro i j hij
  apply h i j
  have hdvd : 2 ^ (2 * u1) ∣ 2 ^ (2 * u2) := Nat.pow_dvd_pow 2 (by omega)
  rw [← Nat.mod_mod_of_dvd (consMask i.val) hdvd, ← Nat.mod_mod_of_dvd (consMask j.val) hdvd, hij]

theorem and_mod_eq {x y w k : ℕ} (hw : w < 2 ^ k) (hxy : x % 2 ^ k = y % 2 ^ k) :
    (x &&& w) = (y &&& w) := by
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_and, Nat.testBit_and]
  by_cases hb : b < k
  · have hxb : x.testBit b = (x % 2 ^ k).testBit b := by rw [Nat.testBit_mod_two_pow]; simp [hb]
    have hyb : y.testBit b = (y % 2 ^ k).testBit b := by rw [Nat.testBit_mod_two_pow]; simp [hb]
    rw [hxb, hyb, hxy]
  · have hpow : 2 ^ k ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hw hpow)]
    simp

theorem disj81_spec : ∀ (w : Fin 256) (idx : Fin 81),
    (disj81 w.val).testBit idx.val = decide ((consMask idx.val &&& w.val) == 0) := by
  decide +kernel

theorem meet81_spec : ∀ (w : Fin 256) (idx : Fin 81),
    (meet81 w.val).testBit idx.val = decide ((consMask idx.val &&& w.val) != 0) := by
  decide +kernel

theorem maskInv_disj81 {used w : ℕ} (hused : used ≤ 4) (hw : w < 2 ^ (2 * used)) :
    MaskInv used (disj81 w) := by
  have hw256 : w < 256 := lt_of_lt_of_le hw (show 2 ^ (2 * used) ≤ 2 ^ 8 from Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  intro i j hij
  rw [disj81_spec ⟨w, hw256⟩ i, disj81_spec ⟨w, hw256⟩ j, and_mod_eq hw hij]

theorem maskInv_meet81 {used w : ℕ} (hused : used ≤ 4) (hw : w < 2 ^ (2 * used)) :
    MaskInv used (meet81 w) := by
  have hw256 : w < 256 := lt_of_lt_of_le hw (show 2 ^ (2 * used) ≤ 2 ^ 8 from Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  intro i j hij
  rw [meet81_spec ⟨w, hw256⟩ i, meet81_spec ⟨w, hw256⟩ j, and_mod_eq hw hij]

theorem disj81_of_disjoint {w : ℕ} (hw : w < 256) (idx : Fin 81)
    (h : Disjoint (slots (consMask idx.val)) (slots w)) : (disj81 w).testBit idx.val = true := by
  rw [disj81_spec ⟨w, hw⟩ idx, decide_eq_true_eq, beq_iff_eq]
  by_contra hne
  have hm : meets (consMask idx.val) w = true := by simp [meets, hne]
  obtain ⟨s, hs1, hs2⟩ := (meetSpec ⟨consMask idx.val, consMask_lt idx⟩ ⟨w, hw⟩).mp hm
  exact Finset.disjoint_left.mp h hs1 hs2

theorem meet81_of_exists {w : ℕ} (hw : w < 256) (idx : Fin 81)
    (h : ∃ s ∈ slots (consMask idx.val), s ∈ slots w) : (meet81 w).testBit idx.val = true := by
  rw [meet81_spec ⟨w, hw⟩ idx, decide_eq_true_eq]
  exact (meetSpec ⟨consMask idx.val, consMask_lt idx⟩ ⟨w, hw⟩).mpr h

def ValidMInv (a b : ℕ) (pos : X → Finset Slot) (vms : List ℕ) : Prop :=
  vms.length = 16 ∧
  ∀ r : Fin 16, ∃ idx : Fin 81,
    (vms.getD r.val 0).testBit idx.val = true ∧
    (∀ z : X, present (decode a) (decode b) (rows r) z → Disjoint (slots (consMask idx.val)) (pos z)) ∧
    (∀ u : V, u ∉ rows r →
      (∃ s ∈ slots (consMask idx.val), s ∈ pos (some u)) ∨
      (¬ fires (decode a) (decode b) (rows r) ∧ fires (decode a) (decode b) (insert u (rows r)) ∧
        ∃ s ∈ slots (consMask idx.val), s ∈ pos none))

theorem validMInv_init {a b : ℕ} {pos : X → Finset Slot} (hcov : Cover (decode a) (decode b) pos) :
    ValidMInv a b pos [all81, all81, all81, all81, all81, all81, all81, all81,
      all81, all81, all81, all81, all81, all81, all81, all81] := by
  refine ⟨rfl, fun r => ?_⟩
  obtain ⟨M, hcons, hdisj, hhit⟩ := hcov r
  obtain ⟨idx, rfl⟩ := consMask_surj M hcons
  refine ⟨idx, ?_, hdisj, hhit⟩
  have hget : ([all81, all81, all81, all81, all81, all81, all81, all81,
      all81, all81, all81, all81, all81, all81, all81, all81] : List ℕ).getD r.val 0 = all81 := by
    fin_cases r <;> rfl
  rw [hget]
  exact all81_testBit idx

theorem validMInv_sym4 {a b used : ℕ} {pos : X → Finset Slot} {vms : List ℕ}
    (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Bool)
    (hfix : ∀ g : Fin 4, g.val < used → σ g = g ∧ f g = false)
    (hmi : ∀ r : Fin 16, MaskInv used (vms.getD r.val 0))
    (hvm : ValidMInv a b pos vms) :
    ValidMInv a b (fun z => (pos z).image (symSlot σ f)) vms := by
  refine ⟨hvm.1, fun r => ?_⟩
  obtain ⟨idx, hbit, hdisj, hhit⟩ := hvm.2 r
  have hcons' : Consistent ((slots (consMask idx.val)).image (symSlot σ f)) :=
    symSlot_consistent σ f (consMask_consistent idx)
  obtain ⟨idx', hidx'⟩ := consMask_surj _ hcons'
  have hinj := symSlot_injective σ f
  have hmod : consMask idx'.val % 2 ^ (2 * used) = consMask idx.val % 2 ^ (2 * used) := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hk : k < 2 * used
    · simp only [hk, decide_true, Bool.true_and]
      by_cases hk8 : k < 8
      · let s : Slot := (⟨k / 2, by omega⟩, decide (k % 2 = 1))
        have hsid : slotId s = k := by unfold slotId s; cases h : decide (k % 2 = 1) <;> simp_all <;> omega
        have hgs : s.1.val < used := by dsimp [s]; omega
        obtain ⟨hσ, hf⟩ := hfix s.1 hgs
        have hfixs : symSlot σ f s = s := by simp [symSlot, hσ, hf]
        rw [← hsid]
        have h1 : (consMask idx'.val).testBit (slotId s) = true ↔ s ∈ slots (consMask idx'.val) := by
          simp [slots]
        have h2 : (consMask idx.val).testBit (slotId s) = true ↔ s ∈ slots (consMask idx.val) := by
          simp [slots]
        rw [Bool.eq_iff_iff, h1, h2, hidx']
        constructor
        · intro hs
          rcases Finset.mem_image.mp hs with ⟨t, ht, hts⟩
          have hteq : t = s := hinj (hts.trans hfixs.symm)
          rwa [← hteq]
        · intro hs
          exact Finset.mem_image.mpr ⟨s, hs, hfixs⟩
      · have hpow1 : consMask idx'.val < 2 ^ k :=
          lt_of_lt_of_le (consMask_lt idx') (show 2 ^ 8 ≤ 2 ^ k from Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
        have hpow2 : consMask idx.val < 2 ^ k :=
          lt_of_lt_of_le (consMask_lt idx) (show 2 ^ 8 ≤ 2 ^ k from Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
        rw [Nat.testBit_lt_two_pow hpow1, Nat.testBit_lt_two_pow hpow2]
    · simp [hk]
  refine ⟨idx', ?_, ?_, ?_⟩
  · rw [hmi r idx' idx hmod]; exact hbit
  · intro z hz
    rw [hidx']
    apply Finset.disjoint_left.mpr
    intro s hs1 hs2
    rcases Finset.mem_image.mp hs1 with ⟨t1, ht1, rfl⟩
    rcases Finset.mem_image.mp hs2 with ⟨t2, ht2, heq⟩
    have := hinj heq
    subst this
    exact Finset.disjoint_left.mp (hdisj z hz) ht1 ht2
  · intro u hu
    rw [hidx']
    have tr {z : X} (h : ∃ s ∈ slots (consMask idx.val), s ∈ pos z) :
        ∃ s ∈ (slots (consMask idx.val)).image (symSlot σ f), s ∈ (pos z).image (symSlot σ f) := by
      rcases h with ⟨s, hs1, hs2⟩
      exact ⟨symSlot σ f s, Finset.mem_image_of_mem _ hs1, Finset.mem_image_of_mem _ hs2⟩
    rcases hhit u hu with h | ⟨h1, h2, h3⟩
    · exact Or.inl (tr h)
    · exact Or.inr ⟨h1, h2, tr h3⟩

def MatchesL (pos : X → Finset Slot) (L : List (ℕ × ℕ)) : Prop :=
  ∀ t ∈ L, t.2 < 256 ∧ ((∃ h : t.1 < 9, pos (some ⟨t.1, h⟩) = slots t.2) ∨ (t.1 = 9 ∧ pos none = slots t.2))

def BoundsL (used : ℕ) (L : List (ℕ × ℕ)) : Prop :=
  ∀ t ∈ L, t.2 < 2 ^ (2 * used)

theorem boundsL_mono {u1 u2 : ℕ} {L : List (ℕ × ℕ)} (hle : u1 ≤ u2) (h : BoundsL u1 L) : BoundsL u2 L :=
  fun t ht => lt_of_lt_of_le (h t ht) (Nat.pow_le_pow_right (by decide) (by omega))

theorem matchesL_sym4 {pos : X → Finset Slot} {L : List (ℕ × ℕ)} {used : ℕ}
    (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Bool)
    (hfix : ∀ g : Fin 4, g.val < used → σ g = g ∧ f g = false)
    (hL : MatchesL pos L) (hB : BoundsL used L) :
    MatchesL (fun z => (pos z).image (symSlot σ f)) L := by
  intro t ht
  obtain ⟨hlt, hcase⟩ := hL t ht
  have hbt := hB t ht
  refine ⟨hlt, ?_⟩
  rcases hcase with ⟨hk, hp⟩ | ⟨hk, hp⟩
  · left; refine ⟨hk, ?_⟩; dsimp only; rw [hp, slots_image_fixed σ f used hfix t.2 hbt]
  · right; refine ⟨hk, ?_⟩; dsimp only; rw [hp, slots_image_fixed σ f used hfix t.2 hbt]


def findNoneM9 : List (ℕ × ℕ) → Option ℕ
  | [] => none
  | (k, w) :: rest => if k == 9 then some (meet81 w) else findNoneM9 rest

theorem findNoneM9_sound {pos : X → Finset Slot} {L : List (ℕ × ℕ)} {used : ℕ}
    (hL : MatchesL pos L) (hB : BoundsL used L) {m9 : ℕ} (hf : findNoneM9 L = some m9) :
    ∃ w9, w9 < 256 ∧ w9 < 2 ^ (2 * used) ∧ pos none = slots w9 ∧ m9 = meet81 w9 := by
  induction L with
  | nil => simp [findNoneM9] at hf
  | cons hd tl ih =>
    rcases hd with ⟨k, w⟩
    have hhd := hL (k, w) (by simp)
    have hbhd := hB (k, w) (by simp)
    have htl : MatchesL pos tl := fun t ht => hL t (by simp [ht])
    have hbtl : BoundsL used tl := fun t ht => hB t (by simp [ht])
    simp only [findNoneM9] at hf
    by_cases hk : k = 9
    · subst hk
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hf
      rcases hhd.2 with ⟨hlt, _⟩ | ⟨_, hp⟩
      · omega
      · exact ⟨w, hhd.1, hbhd, hp, hf.symm⟩
    · have hne : (k == 9) = false := by simp [hk]
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hf
      exact ih htl hbtl hf

def stAt (st0 st1 st2 st3 st4 st5 st6 st7 st8 v : ℕ) : ℕ :=
  match v with | 0 => st0 | 1 => st1 | 2 => st2 | 3 => st3 | 4 => st4 | 5 => st5 | 6 => st6 | 7 => st7 | _ => st8

theorem stAt_stMask (a b : ℕ) (v : V) :
    stAt (stMask a b (hotMask a b) 0) (stMask a b (hotMask a b) 1)
      (stMask a b (hotMask a b) 2) (stMask a b (hotMask a b) 3) (stMask a b (hotMask a b) 4)
      (stMask a b (hotMask a b) 5) (stMask a b (hotMask a b) 6) (stMask a b (hotMask a b) 7)
      (stMask a b (hotMask a b) 8) v.val = stMask a b (hotMask a b) v.val := by
  fin_cases v <;> rfl

theorem shiftRight_one_add (m k : ℕ) : (m >>> k) >>> 1 = m >>> (k + 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp [Nat.testBit_shiftRight, Nat.add_assoc, Nat.add_comm 1 j]

theorem land1_ne_zero_eq_testBit (m k : ℕ) : (((m >>> k) &&& 1) != 0) = m.testBit k :=
  shiftAnd1_ne_zero m k

def applyVGoNo9 (im sm dw mw : ℕ) : List ℕ → Option (List ℕ)
  | [] => some []
  | vm :: rest =>
    let vm' := if (im &&& 1) != 0 then vm &&& dw else if (sm &&& 1) != 0 then vm &&& mw else vm
    if vm' == 0 then none
    else match applyVGoNo9 (im >>> 1) (sm >>> 1) dw mw rest with
      | none => none
      | some tl => some (vm' :: tl)

def applyVGoWith9 (im sm dw mw mwm9 : ℕ) : List ℕ → Option (List ℕ)
  | [] => some []
  | vm :: rest =>
    let vm' := if (im &&& 1) != 0 then vm &&& dw else if (sm &&& 1) != 0 then vm &&& mw else vm &&& mwm9
    if vm' == 0 then none
    else match applyVGoWith9 (im >>> 1) (sm >>> 1) dw mw mwm9 rest with
      | none => none
      | some tl => some (vm' :: tl)

def prepNList (st0 st1 st2 st3 st4 st5 st6 st7 st8 : ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (v, wv) :: rest =>
    if v < 9 then (inMask v ||| stAt st0 st1 st2 st3 st4 st5 st6 st7 st8 v, meet81 wv) ::
      prepNList st0 st1 st2 st3 st4 st5 st6 st7 st8 rest
    else prepNList st0 st1 st2 st3 st4 st5 st6 st7 st8 rest

def preNReqRow (r : ℕ) : List (ℕ × ℕ) → ℕ → ℕ
  | [], acc => acc
  | (sk, mwv) :: rest, acc =>
    if ((sk >>> r) &&& 1) == 0 then preNReqRow r rest (acc &&& mwv)
    else preNReqRow r rest acc

def preNReqsGo (pL : List (ℕ × ℕ)) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | r, n + 1 => preNReqRow r pL all81 :: preNReqsGo pL (r + 1) n

def preNReqs (pL : List (ℕ × ℕ)) : List ℕ := preNReqsGo pL 0 16

def applyNGo (hm dw mw : ℕ) : List ℕ → List ℕ → Option (List ℕ)
  | [], _ => some []
  | _, [] => some []
  | req :: reqs, vm :: rest =>
    let vm' := if (hm &&& 1) != 0 then vm &&& dw else vm &&& (req ||| mw)
    if vm' == 0 then none
    else match applyNGo (hm >>> 1) dw mw reqs rest with
      | none => none
      | some tl => some (vm' :: tl)

theorem applyVGoNo9_sound {a b used : ℕ} (ha : a < 512) (hb : b < 512) (hused : used ≤ 4)
    {pos : X → Finset Slot} (v : V) {w : ℕ} (hw : w < 2 ^ (2 * used)) (hposv : pos (some v) = slots w)
    (vms : List ℕ) (hmi : ∀ r : Fin 16, MaskInv used (vms.getD r.val 0))
    (hvm : ValidMInv a b pos vms) :
    ∃ vms', applyVGoNo9 (inMask v.val) (stMask a b (hotMask a b) v.val) (disj81 w) (meet81 w) vms = some vms' ∧
      (∀ r : Fin 16, MaskInv used (vms'.getD r.val 0)) ∧ ValidMInv a b pos vms' := by
  have hw256 : w < 256 := lt_of_lt_of_le hw (show 2 ^ (2 * used) ≤ 2 ^ 8 from Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  have go : ∀ (k : ℕ) (xs : List ℕ) (hklen : k + xs.length = 16),
      (∀ (j : ℕ) (hj : j < xs.length), MaskInv used (xs.getD j 0)) →
      (∀ (j : ℕ) (hj : j < xs.length),
        let r : Fin 16 := ⟨k + j, by omega⟩
        ∃ idx : Fin 81,
          (xs.getD j 0).testBit idx.val = true ∧
          (∀ z : X, present (decode a) (decode b) (rows r) z → Disjoint (slots (consMask idx.val)) (pos z)) ∧
          (∀ u : V, u ∉ rows r →
            (∃ s ∈ slots (consMask idx.val), s ∈ pos (some u)) ∨
            (¬ fires (decode a) (decode b) (rows r) ∧ fires (decode a) (decode b) (insert u (rows r)) ∧
              ∃ s ∈ slots (consMask idx.val), s ∈ pos none))) →
      ∃ ys, applyVGoNo9 (inMask v.val >>> k) (stMask a b (hotMask a b) v.val >>> k) (disj81 w) (meet81 w) xs = some ys ∧
        ∃ hylen : ys.length = xs.length,
        (∀ (j : ℕ) (hj : j < ys.length), MaskInv used (ys.getD j 0)) ∧
        (∀ (j : ℕ) (hj : j < ys.length),
          let r : Fin 16 := ⟨k + j, by omega⟩
          ∃ idx : Fin 81,
            (ys.getD j 0).testBit idx.val = true ∧
            (∀ z : X, present (decode a) (decode b) (rows r) z → Disjoint (slots (consMask idx.val)) (pos z)) ∧
            (∀ u : V, u ∉ rows r →
              (∃ s ∈ slots (consMask idx.val), s ∈ pos (some u)) ∨
              (¬ fires (decode a) (decode b) (rows r) ∧ fires (decode a) (decode b) (insert u (rows r)) ∧
                ∃ s ∈ slots (consMask idx.val), s ∈ pos none))) := by
    intro k xs
    induction xs generalizing k with
    | nil => intro _ _ _; exact ⟨[], rfl, rfl, fun _ hj => by simp at hj, fun _ hj => by simp at hj⟩
    | cons vm rest ih =>
      intro hlen hmi_xs hvm_xs
      have hkr : k < 16 := by simp at hlen; omega
      have hmi0 : MaskInv used vm := by simpa using hmi_xs 0 (by simp)
      obtain ⟨idx0, hbit0, hdisj0, hhit0⟩ := hvm_xs 0 (by simp)
      simp only [List.getD_cons_zero] at hbit0
      let r0 : Fin 16 := ⟨k, hkr⟩
      have hdisj0' : ∀ z : X, present (decode a) (decode b) (rows r0) z → Disjoint (slots (consMask idx0.val)) (pos z) := by
        simpa only [Nat.add_zero] using hdisj0
      have hhit0' : ∀ u : V, u ∉ rows r0 →
          (∃ s ∈ slots (consMask idx0.val), s ∈ pos (some u)) ∨
          (¬ fires (decode a) (decode b) (rows r0) ∧ fires (decode a) (decode b) (insert u (rows r0)) ∧
            ∃ s ∈ slots (consMask idx0.val), s ∈ pos none) := by
        simpa only [Nat.add_zero] using hhit0
      set vm' := if ((inMask v.val >>> k) &&& 1) != 0 then vm &&& disj81 w
        else if ((stMask a b (hotMask a b) v.val >>> k) &&& 1) != 0 then vm &&& meet81 w else vm
      have hstep : MaskInv used vm' ∧ vm'.testBit idx0.val = true := by
        dsimp [vm']
        split_ifs with hin hst
        · refine ⟨maskInv_land hmi0 (maskInv_disj81 hused hw), ?_⟩
          rw [Nat.testBit_and, hbit0, Bool.true_and]
          rw [land1_ne_zero_eq_testBit, ← bitOn_eq_testBit _ _ hkr] at hin
          have hvr : v ∈ rows r0 := of_decide_eq_true ((bitOn_inMask v r0).symm.trans hin)
          exact disj81_of_disjoint hw256 idx0 (hposv ▸ hdisj0' (some v) hvr)
        · refine ⟨maskInv_land hmi0 (maskInv_meet81 hused hw), ?_⟩
          rw [Nat.testBit_and, hbit0, Bool.true_and]
          have hinf : bitOn (inMask v.val) k = false := by
            rw [bitOn_eq_testBit _ _ hkr, ← land1_ne_zero_eq_testBit]
            exact Bool.eq_false_iff.mpr hin
          have hvr : v ∉ rows r0 := of_decide_eq_false ((bitOn_inMask v r0).symm.trans hinf)
          rw [land1_ne_zero_eq_testBit, ← bitOn_eq_testBit _ _ hkr] at hst
          have hst' : Stable (decode a) (decode b) r0 v := by
            rw [← stableB_iff a b ha hb r0 v, ← bitOn_stMask a b v r0]; exact hst
          rcases hhit0' v hvr with hm | ⟨hnf, hfi, _⟩
          · exact meet81_of_exists hw256 idx0 (hposv ▸ hm)
          · exact (hnf (hst'.2 hfi)).elim
        · exact ⟨hmi0, hbit0⟩
      have hne0 : vm' ≠ 0 := fun h0 => by
        have := hstep.2; rw [h0, Nat.zero_testBit] at this; simp at this
      have hne0b : (vm' == 0) = false := by simp [hne0]
      obtain ⟨tail, htail_eq, htail_len, htail_mi, htail_vm⟩ := ih (k + 1) (by simp at hlen; omega)
        (fun j hj => by simpa using hmi_xs (j + 1) (by simp; omega))
        (fun j hj => by
          have := hvm_xs (j + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 j] using this)
      refine ⟨vm' :: tail, ?_, by simp [htail_len], ?_, ?_⟩
      · unfold applyVGoNo9
        dsimp only
        rw [shiftRight_one_add, shiftRight_one_add]
        change (if (vm' == 0) = true then none else match applyVGoNo9 _ _ _ _ _ with | none => none | some t => some (vm' :: t)) = some (vm' :: tail)
        rw [hne0b, htail_eq]; rfl
      · intro j hj
        cases j with
        | zero => exact hstep.1
        | succ j' => exact htail_mi j' (by simp at hj; omega)
      · intro j hj
        cases j with
        | zero => exact ⟨idx0, hstep.2, by simpa using hdisj0, by simpa using hhit0⟩
        | succ j' =>
          have := htail_vm j' (by simp at hj; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 j'] using this
  have hvlen : vms.length = 16 := hvm.1
  obtain ⟨ys, hys, hlen, hmi', hvm'⟩ := go 0 vms (by omega)
    (fun j hj => hmi ⟨j, by omega⟩) (fun j hj => by simpa using hvm.2 ⟨j, by omega⟩)
  refine ⟨ys, by simpa using hys, fun r => hmi' r.val (by omega), ⟨by omega, fun r => by simpa using hvm' r.val (by omega)⟩⟩

theorem applyVGoWith9_sound {a b used : ℕ} (ha : a < 512) (hb : b < 512) (hused : used ≤ 4)
    {pos : X → Finset Slot} (v : V) {w w9 : ℕ} (hw : w < 2 ^ (2 * used)) (hposv : pos (some v) = slots w)
    (hw9 : w9 < 256) (hw9b : w9 < 2 ^ (2 * used)) (hpos9 : pos none = slots w9)
    (vms : List ℕ) (hmi : ∀ r : Fin 16, MaskInv used (vms.getD r.val 0))
    (hvm : ValidMInv a b pos vms) :
    ∃ vms', applyVGoWith9 (inMask v.val) (stMask a b (hotMask a b) v.val) (disj81 w) (meet81 w)
        (meet81 w ||| meet81 w9) vms = some vms' ∧
      (∀ r : Fin 16, MaskInv used (vms'.getD r.val 0)) ∧ ValidMInv a b pos vms' := by
  have hw256 : w < 256 := lt_of_lt_of_le hw (show 2 ^ (2 * used) ≤ 2 ^ 8 from Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  have go : ∀ (k : ℕ) (xs : List ℕ) (hklen : k + xs.length = 16),
      (∀ (j : ℕ) (hj : j < xs.length), MaskInv used (xs.getD j 0)) →
      (∀ (j : ℕ) (hj : j < xs.length),
        let r : Fin 16 := ⟨k + j, by omega⟩
        ∃ idx : Fin 81,
          (xs.getD j 0).testBit idx.val = true ∧
          (∀ z : X, present (decode a) (decode b) (rows r) z → Disjoint (slots (consMask idx.val)) (pos z)) ∧
          (∀ u : V, u ∉ rows r →
            (∃ s ∈ slots (consMask idx.val), s ∈ pos (some u)) ∨
            (¬ fires (decode a) (decode b) (rows r) ∧ fires (decode a) (decode b) (insert u (rows r)) ∧
              ∃ s ∈ slots (consMask idx.val), s ∈ pos none))) →
      ∃ ys, applyVGoWith9 (inMask v.val >>> k) (stMask a b (hotMask a b) v.val >>> k) (disj81 w) (meet81 w)
          (meet81 w ||| meet81 w9) xs = some ys ∧
        ∃ hylen : ys.length = xs.length,
        (∀ (j : ℕ) (hj : j < ys.length), MaskInv used (ys.getD j 0)) ∧
        (∀ (j : ℕ) (hj : j < ys.length),
          let r : Fin 16 := ⟨k + j, by omega⟩
          ∃ idx : Fin 81,
            (ys.getD j 0).testBit idx.val = true ∧
            (∀ z : X, present (decode a) (decode b) (rows r) z → Disjoint (slots (consMask idx.val)) (pos z)) ∧
            (∀ u : V, u ∉ rows r →
              (∃ s ∈ slots (consMask idx.val), s ∈ pos (some u)) ∨
              (¬ fires (decode a) (decode b) (rows r) ∧ fires (decode a) (decode b) (insert u (rows r)) ∧
                ∃ s ∈ slots (consMask idx.val), s ∈ pos none))) := by
    intro k xs
    induction xs generalizing k with
    | nil => intro _ _ _; exact ⟨[], rfl, rfl, fun _ hj => by simp at hj, fun _ hj => by simp at hj⟩
    | cons vm rest ih =>
      intro hlen hmi_xs hvm_xs
      have hkr : k < 16 := by simp at hlen; omega
      have hmi0 : MaskInv used vm := by simpa using hmi_xs 0 (by simp)
      obtain ⟨idx0, hbit0, hdisj0, hhit0⟩ := hvm_xs 0 (by simp)
      simp only [List.getD_cons_zero] at hbit0
      let r0 : Fin 16 := ⟨k, hkr⟩
      have hdisj0' : ∀ z : X, present (decode a) (decode b) (rows r0) z → Disjoint (slots (consMask idx0.val)) (pos z) := by
        simpa only [Nat.add_zero] using hdisj0
      have hhit0' : ∀ u : V, u ∉ rows r0 →
          (∃ s ∈ slots (consMask idx0.val), s ∈ pos (some u)) ∨
          (¬ fires (decode a) (decode b) (rows r0) ∧ fires (decode a) (decode b) (insert u (rows r0)) ∧
            ∃ s ∈ slots (consMask idx0.val), s ∈ pos none) := by
        simpa only [Nat.add_zero] using hhit0
      set vm' := if ((inMask v.val >>> k) &&& 1) != 0 then vm &&& disj81 w
        else if ((stMask a b (hotMask a b) v.val >>> k) &&& 1) != 0 then vm &&& meet81 w
        else vm &&& (meet81 w ||| meet81 w9)
      have hstep : MaskInv used vm' ∧ vm'.testBit idx0.val = true := by
        dsimp [vm']
        split_ifs with hin hst
        · refine ⟨maskInv_land hmi0 (maskInv_disj81 hused hw), ?_⟩
          rw [Nat.testBit_and, hbit0, Bool.true_and]
          rw [land1_ne_zero_eq_testBit, ← bitOn_eq_testBit _ _ hkr] at hin
          have hvr : v ∈ rows r0 := of_decide_eq_true ((bitOn_inMask v r0).symm.trans hin)
          exact disj81_of_disjoint hw256 idx0 (hposv ▸ hdisj0' (some v) hvr)
        · refine ⟨maskInv_land hmi0 (maskInv_meet81 hused hw), ?_⟩
          rw [Nat.testBit_and, hbit0, Bool.true_and]
          have hinf : bitOn (inMask v.val) k = false := by
            rw [bitOn_eq_testBit _ _ hkr, ← land1_ne_zero_eq_testBit]
            exact Bool.eq_false_iff.mpr hin
          have hvr : v ∉ rows r0 := of_decide_eq_false ((bitOn_inMask v r0).symm.trans hinf)
          rw [land1_ne_zero_eq_testBit, ← bitOn_eq_testBit _ _ hkr] at hst
          have hst' : Stable (decode a) (decode b) r0 v := by
            rw [← stableB_iff a b ha hb r0 v, ← bitOn_stMask a b v r0]; exact hst
          rcases hhit0' v hvr with hm | ⟨hnf, hfi, _⟩
          · exact meet81_of_exists hw256 idx0 (hposv ▸ hm)
          · exact (hnf (hst'.2 hfi)).elim
        · refine ⟨maskInv_land hmi0 (maskInv_lor (maskInv_meet81 hused hw) (maskInv_meet81 hused hw9b)), ?_⟩
          rw [Nat.testBit_and, Nat.testBit_or, hbit0, Bool.true_and]
          have hinf : bitOn (inMask v.val) k = false := by
            rw [bitOn_eq_testBit _ _ hkr, ← land1_ne_zero_eq_testBit]
            exact Bool.eq_false_iff.mpr hin
          have hvr : v ∉ rows r0 := of_decide_eq_false ((bitOn_inMask v r0).symm.trans hinf)
          rcases hhit0' v hvr with hm | ⟨_, _, hm⟩
          · rw [meet81_of_exists hw256 idx0 (hposv ▸ hm)]; rfl
          · rw [meet81_of_exists hw9 idx0 (hpos9 ▸ hm)]; simp
      have hne0 : vm' ≠ 0 := fun h0 => by
        have := hstep.2; rw [h0, Nat.zero_testBit] at this; simp at this
      have hne0b : (vm' == 0) = false := by simp [hne0]
      obtain ⟨tail, htail_eq, htail_len, htail_mi, htail_vm⟩ := ih (k + 1) (by simp at hlen; omega)
        (fun j hj => by simpa using hmi_xs (j + 1) (by simp; omega))
        (fun j hj => by
          have := hvm_xs (j + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 j] using this)
      refine ⟨vm' :: tail, ?_, by simp [htail_len], ?_, ?_⟩
      · unfold applyVGoWith9
        dsimp only
        rw [shiftRight_one_add, shiftRight_one_add]
        change (if (vm' == 0) = true then none else match applyVGoWith9 _ _ _ _ _ _ with | none => none | some t => some (vm' :: t)) = some (vm' :: tail)
        rw [hne0b, htail_eq]; rfl
      · intro j hj
        cases j with
        | zero => exact hstep.1
        | succ j' => exact htail_mi j' (by simp at hj; omega)
      · intro j hj
        cases j with
        | zero => exact ⟨idx0, hstep.2, by simpa using hdisj0, by simpa using hhit0⟩
        | succ j' =>
          have := htail_vm j' (by simp at hj; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 j'] using this
  have hvlen : vms.length = 16 := hvm.1
  obtain ⟨ys, hys, hlen, hmi', hvm'⟩ := go 0 vms (by omega)
    (fun j hj => hmi ⟨j, by omega⟩) (fun j hj => by simpa using hvm.2 ⟨j, by omega⟩)
  refine ⟨ys, by simpa using hys, fun r => hmi' r.val (by omega), ⟨by omega, fun r => by simpa using hvm' r.val (by omega)⟩⟩

theorem prepNList_sound {a b used : ℕ} {pos : X → Finset Slot} {L : List (ℕ × ℕ)}
    (hL : MatchesL pos L) (hB : BoundsL used L) :
    ∀ t ∈ prepNList (stMask a b (hotMask a b) 0) (stMask a b (hotMask a b) 1)
      (stMask a b (hotMask a b) 2) (stMask a b (hotMask a b) 3) (stMask a b (hotMask a b) 4)
      (stMask a b (hotMask a b) 5) (stMask a b (hotMask a b) 6) (stMask a b (hotMask a b) 7)
      (stMask a b (hotMask a b) 8) L,
      ∃ (v : V) (wv : ℕ), wv < 256 ∧ wv < 2 ^ (2 * used) ∧ pos (some v) = slots wv ∧
        t.1 = (inMask v.val ||| stMask a b (hotMask a b) v.val) ∧ t.2 = meet81 wv := by
  induction L with
  | nil => intro _ ht; simp [prepNList] at ht
  | cons hd tl ih =>
    rcases hd with ⟨k, wv⟩
    have hhd := hL (k, wv) (by simp)
    have hbhd := hB (k, wv) (by simp)
    have htl : MatchesL pos tl := fun t ht => hL t (by simp [ht])
    have hbtl : BoundsL used tl := fun t ht => hB t (by simp [ht])
    intro t ht
    simp only [prepNList] at ht
    by_cases hk : k < 9
    · simp only [hk, ↓reduceIte, List.mem_cons] at ht
      rcases ht with rfl | hmem
      · refine ⟨⟨k, hk⟩, wv, hhd.1, hbhd, ?_, ?_, rfl⟩
        · rcases hhd.2 with ⟨_, hp⟩ | ⟨he, _⟩
          · exact hp
          · omega
        · dsimp only; rw [stAt_stMask a b ⟨k, hk⟩]
      · exact ih htl hbtl t hmem
    · simp only [hk, ↓reduceIte] at ht
      exact ih htl hbtl t ht

theorem preNReqRow_sound {a b used : ℕ} (hused : used ≤ 4)
    {pos : X → Finset Slot} {w : ℕ} (hw : w < 2 ^ (2 * used)) (hpos9 : pos none = slots w)
    (r : Fin 16) (idx : Fin 81)
    (hhit : ∀ u : V, u ∉ rows r →
      (∃ s ∈ slots (consMask idx.val), s ∈ pos (some u)) ∨
      (¬ fires (decode a) (decode b) (rows r) ∧ fires (decode a) (decode b) (insert u (rows r)) ∧
        ∃ s ∈ slots (consMask idx.val), s ∈ pos none))
    (pL : List (ℕ × ℕ))
    (hpL : ∀ t ∈ pL, ∃ (v : V) (wv : ℕ), wv < 256 ∧ wv < 2 ^ (2 * used) ∧ pos (some v) = slots wv ∧
      t.1 = (inMask v.val ||| stMask a b (hotMask a b) v.val) ∧ t.2 = meet81 wv) :
    MaskInv used (preNReqRow r.val pL all81) ∧
    (preNReqRow r.val pL all81 ||| meet81 w).testBit idx.val = true := by
  have hw256 : w < 256 := lt_of_lt_of_le hw (show 2 ^ (2 * used) ≤ 2 ^ 8 from Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  have hmi_go : ∀ (xs : List (ℕ × ℕ)),
      (∀ t ∈ xs, ∃ (v : V) (wv : ℕ), wv < 256 ∧ wv < 2 ^ (2 * used) ∧ pos (some v) = slots wv ∧
        t.1 = (inMask v.val ||| stMask a b (hotMask a b) v.val) ∧ t.2 = meet81 wv) →
      ∀ acc, MaskInv used acc → MaskInv used (preNReqRow r.val xs acc) := by
    intro xs
    induction xs with
    | nil => intro _ acc h; exact h
    | cons hd tl ih =>
      intro hxs acc hacc
      rcases hd with ⟨sk, mwv⟩
      obtain ⟨v, wv, _, hwvb, _, _, rfl⟩ := hxs (sk, mwv) (by simp)
      have htl : ∀ t ∈ tl, ∃ (v : V) (wv : ℕ), wv < 256 ∧ wv < 2 ^ (2 * used) ∧ pos (some v) = slots wv ∧
        t.1 = (inMask v.val ||| stMask a b (hotMask a b) v.val) ∧ t.2 = meet81 wv := fun t ht => hxs t (by simp [ht])
      simp only [preNReqRow]
      split_ifs
      · exact ih htl _ (maskInv_land hacc (maskInv_meet81 hused hwvb))
      · exact ih htl _ hacc
  refine ⟨hmi_go pL hpL all81 (maskInv_all81 used), ?_⟩
  rw [Nat.testBit_or]
  by_cases hmw : (meet81 w).testBit idx.val = true
  · simp [hmw]
  · have hno9 : ¬ ∃ s ∈ slots (consMask idx.val), s ∈ pos none := fun h =>
      hmw (meet81_of_exists hw256 idx (hpos9 ▸ h))
    have hbit_go : ∀ (xs : List (ℕ × ℕ)),
        (∀ t ∈ xs, ∃ (v : V) (wv : ℕ), wv < 256 ∧ wv < 2 ^ (2 * used) ∧ pos (some v) = slots wv ∧
          t.1 = (inMask v.val ||| stMask a b (hotMask a b) v.val) ∧ t.2 = meet81 wv) →
        ∀ acc, acc.testBit idx.val = true → (preNReqRow r.val xs acc).testBit idx.val = true := by
      intro xs
      induction xs with
      | nil => intro _ acc h; exact h
      | cons hd tl ih =>
        intro hxs acc hacc
        rcases hd with ⟨sk, mwv⟩
        obtain ⟨v, wv, hwv256, _, hposv, rfl, rfl⟩ := hxs (sk, mwv) (by simp)
        have htl : ∀ t ∈ tl, ∃ (v : V) (wv : ℕ), wv < 256 ∧ wv < 2 ^ (2 * used) ∧ pos (some v) = slots wv ∧
          t.1 = (inMask v.val ||| stMask a b (hotMask a b) v.val) ∧ t.2 = meet81 wv := fun t ht => hxs t (by simp [ht])
        simp only [preNReqRow]
        split_ifs with hcond
        · apply ih htl
          rw [Nat.testBit_and, hacc, Bool.true_and]
          have hzero : (((inMask v.val ||| stMask a b (hotMask a b) v.val) >>> r.val) &&& 1) = 0 := beq_iff_eq.mp hcond
          have htb_f : (inMask v.val ||| stMask a b (hotMask a b) v.val).testBit r.val = false := by
            rw [← land1_ne_zero_eq_testBit, hzero]; rfl
          rw [Nat.testBit_or, Bool.or_eq_false_iff] at htb_f
          have hinf : bitOn (inMask v.val) r.val = false := by
            rw [bitOn_eq_testBit _ _ r.isLt]; exact htb_f.1
          have hvr : v ∉ rows r := of_decide_eq_false ((bitOn_inMask v r).symm.trans hinf)
          rcases hhit v hvr with hm | ⟨_, _, hm⟩
          · exact meet81_of_exists hwv256 idx (hposv ▸ hm)
          · exact (hno9 hm).elim
        · exact ih htl acc hacc
    rw [hbit_go pL hpL all81 (all81_testBit idx)]; rfl

theorem applyNGo_sound {a b used : ℕ} (ha : a < 512) (hb : b < 512) (hused : used ≤ 4)
    {pos : X → Finset Slot} {L : List (ℕ × ℕ)} (hL : MatchesL pos L) (hB : BoundsL used L)
    {w : ℕ} (hw : w < 2 ^ (2 * used)) (hpos9 : pos none = slots w)
    (vms : List ℕ) (hmi : ∀ r : Fin 16, MaskInv used (vms.getD r.val 0))
    (hvm : ValidMInv a b pos vms) :
    ∃ vms', applyNGo (hotMask a b) (disj81 w) (meet81 w)
        (preNReqs (prepNList (stMask a b (hotMask a b) 0) (stMask a b (hotMask a b) 1)
          (stMask a b (hotMask a b) 2) (stMask a b (hotMask a b) 3) (stMask a b (hotMask a b) 4)
          (stMask a b (hotMask a b) 5) (stMask a b (hotMask a b) 6) (stMask a b (hotMask a b) 7)
          (stMask a b (hotMask a b) 8) L)) vms = some vms' ∧
      (∀ r : Fin 16, MaskInv used (vms'.getD r.val 0)) ∧ ValidMInv a b pos vms' := by
  have hw256 : w < 256 := lt_of_lt_of_le hw (show 2 ^ (2 * used) ≤ 2 ^ 8 from Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  set pL := prepNList (stMask a b (hotMask a b) 0) (stMask a b (hotMask a b) 1)
    (stMask a b (hotMask a b) 2) (stMask a b (hotMask a b) 3) (stMask a b (hotMask a b) 4)
    (stMask a b (hotMask a b) 5) (stMask a b (hotMask a b) 6) (stMask a b (hotMask a b) 7)
    (stMask a b (hotMask a b) 8) L
  have hpL := prepNList_sound (a := a) (b := b) hL hB
  have go : ∀ (k : ℕ) (xs : List ℕ) (hklen : k + xs.length = 16),
      (∀ (j : ℕ) (hj : j < xs.length), MaskInv used (xs.getD j 0)) →
      (∀ (j : ℕ) (hj : j < xs.length),
        let r : Fin 16 := ⟨k + j, by omega⟩
        ∃ idx : Fin 81,
          (xs.getD j 0).testBit idx.val = true ∧
          (∀ z : X, present (decode a) (decode b) (rows r) z → Disjoint (slots (consMask idx.val)) (pos z)) ∧
          (∀ u : V, u ∉ rows r →
            (∃ s ∈ slots (consMask idx.val), s ∈ pos (some u)) ∨
            (¬ fires (decode a) (decode b) (rows r) ∧ fires (decode a) (decode b) (insert u (rows r)) ∧
              ∃ s ∈ slots (consMask idx.val), s ∈ pos none))) →
      ∃ ys, applyNGo (hotMask a b >>> k) (disj81 w) (meet81 w) (preNReqsGo pL k xs.length) xs = some ys ∧
        ∃ hylen : ys.length = xs.length,
        (∀ (j : ℕ) (hj : j < ys.length), MaskInv used (ys.getD j 0)) ∧
        (∀ (j : ℕ) (hj : j < ys.length),
          let r : Fin 16 := ⟨k + j, by omega⟩
          ∃ idx : Fin 81,
            (ys.getD j 0).testBit idx.val = true ∧
            (∀ z : X, present (decode a) (decode b) (rows r) z → Disjoint (slots (consMask idx.val)) (pos z)) ∧
            (∀ u : V, u ∉ rows r →
              (∃ s ∈ slots (consMask idx.val), s ∈ pos (some u)) ∨
              (¬ fires (decode a) (decode b) (rows r) ∧ fires (decode a) (decode b) (insert u (rows r)) ∧
                ∃ s ∈ slots (consMask idx.val), s ∈ pos none))) := by
    intro k xs
    induction xs generalizing k with
    | nil => intro _ _ _; exact ⟨[], rfl, rfl, fun _ hj => by simp at hj, fun _ hj => by simp at hj⟩
    | cons vm rest ih =>
      intro hlen hmi_xs hvm_xs
      have hkr : k < 16 := by simp at hlen; omega
      have hmi0 : MaskInv used vm := by simpa using hmi_xs 0 (by simp)
      obtain ⟨idx0, hbit0, hdisj0, hhit0⟩ := hvm_xs 0 (by simp)
      simp only [List.getD_cons_zero] at hbit0
      let r0 : Fin 16 := ⟨k, hkr⟩
      have hdisj0' : ∀ z : X, present (decode a) (decode b) (rows r0) z → Disjoint (slots (consMask idx0.val)) (pos z) := by
        simpa only [Nat.add_zero] using hdisj0
      have hhit0' : ∀ u : V, u ∉ rows r0 →
          (∃ s ∈ slots (consMask idx0.val), s ∈ pos (some u)) ∨
          (¬ fires (decode a) (decode b) (rows r0) ∧ fires (decode a) (decode b) (insert u (rows r0)) ∧
            ∃ s ∈ slots (consMask idx0.val), s ∈ pos none) := by
        simpa only [Nat.add_zero] using hhit0
      set vm' := if ((hotMask a b >>> k) &&& 1) != 0 then vm &&& disj81 w else vm &&& (preNReqRow k pL all81 ||| meet81 w)
      have hstep : MaskInv used vm' ∧ vm'.testBit idx0.val = true := by
        dsimp [vm']
        split_ifs with hhot
        · refine ⟨maskInv_land hmi0 (maskInv_disj81 hused hw), ?_⟩
          rw [Nat.testBit_and, hbit0, Bool.true_and]
          rw [land1_ne_zero_eq_testBit, ← bitOn_eq_testBit _ _ hkr] at hhot
          change bitOn (hotMask a b) r0.val = true at hhot
          rw [bitOn_hotMask, firesB_iff a b (rowAt r0.val) ha hb, decode_rowAt r0] at hhot
          exact disj81_of_disjoint hw256 idx0 (hpos9 ▸ hdisj0' none hhot)
        · obtain ⟨hreq_mi, hreq_bit⟩ := preNReqRow_sound hused hw hpos9 r0 idx0 hhit0' pL hpL
          refine ⟨maskInv_land hmi0 (maskInv_lor hreq_mi (maskInv_meet81 hused hw)), ?_⟩
          rw [Nat.testBit_and, hbit0, Bool.true_and]
          exact hreq_bit
      have hne0 : vm' ≠ 0 := fun h0 => by
        have := hstep.2; rw [h0, Nat.zero_testBit] at this; simp at this
      have hne0b : (vm' == 0) = false := by simp [hne0]
      obtain ⟨tail, htail_eq, htail_len, htail_mi, htail_vm⟩ := ih (k + 1) (by simp at hlen; omega)
        (fun j hj => by simpa using hmi_xs (j + 1) (by simp; omega))
        (fun j hj => by
          have := hvm_xs (j + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 j] using this)
      refine ⟨vm' :: tail, ?_, by simp [htail_len], ?_, ?_⟩
      · simp only [List.length_cons, preNReqsGo, applyNGo]
        rw [shiftRight_one_add]
        change (if (vm' == 0) = true then none else match applyNGo _ _ _ _ _ with | none => none | some t => some (vm' :: t)) = some (vm' :: tail)
        rw [hne0b, htail_eq]; rfl
      · intro j hj
        cases j with
        | zero => exact hstep.1
        | succ j' => exact htail_mi j' (by simp at hj; omega)
      · intro j hj
        cases j with
        | zero => exact ⟨idx0, hstep.2, by simpa using hdisj0, by simpa using hhit0⟩
        | succ j' =>
          have := htail_vm j' (by simp at hj; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 j'] using this
  have hvlen : vms.length = 16 := hvm.1
  obtain ⟨ys, hys, hlen, hmi', hvm'⟩ := go 0 vms (by omega)
    (fun j hj => hmi ⟨j, by omega⟩) (fun j hj => by simpa using hvm.2 ⟨j, by omega⟩)
  rw [hvlen] at hys
  refine ⟨ys, by simpa [preNReqs] using hys, fun r => hmi' r.val (by omega), ⟨by omega, fun r => by simpa using hvm' r.val (by omega)⟩⟩

def lookupV (v : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 256
  | (k, w) :: rest => if k == v then w else lookupV v rest

theorem lookupV_sound {pos : X → Finset Slot} {L : List (ℕ × ℕ)} (hL : MatchesL pos L)
    (v : V) {w : ℕ} (h : lookupV v.val L = w) (hw : w < 256) : pos (some v) = slots w := by
  induction L with
  | nil => simp [lookupV] at h; omega
  | cons hd tl ih =>
    rcases hd with ⟨k, wk⟩
    have hhd := hL (k, wk) (by simp)
    have htl : MatchesL pos tl := fun t ht => hL t (by simp [ht])
    simp only [lookupV] at h
    by_cases hk : k = v.val
    · subst hk
      simp only [beq_self_eq_true, ↓reduceIte] at h
      subst h
      rcases hhd.2 with ⟨_, hp⟩ | ⟨he, _⟩
      · exact hp
      · omega
    · have hne : (k == v.val) = false := by simp [hk]
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
      exact ih htl h

def matchLeafGo (L : List (ℕ × ℕ)) : ℕ → List ℕ → Bool
  | _, [] => true
  | v, w :: rest => if lookupV v L == w then matchLeafGo L (v + 1) rest else false

def matchLeaf (L : List (ℕ × ℕ)) (lf : List ℕ) : Bool := matchLeafGo L 0 lf

theorem matchLeaf_sound {pos : X → Finset Slot} {L : List (ℕ × ℕ)} (hL : MatchesL pos L)
    (lf : List ℕ) (hlen : lf.length = 9) (hlt : ∀ w ∈ lf, w < 256)
    (hm : matchLeaf L lf = true) (v : V) : pos (some v) = slots (lf.getD v.val 256) := by
  have go : ∀ (k : ℕ) (xs : List ℕ),
      (∀ w ∈ xs, w < 256) →
      matchLeafGo L k xs = true →
      ∀ (j : ℕ) (hj : j < xs.length) (h9 : k + j < 9),
        pos (some ⟨k + j, h9⟩) = slots (xs.getD j 256) := by
    intro k xs
    induction xs generalizing k with
    | nil => intro _ _ _ hj; simp at hj
    | cons w rest ih =>
      intro hxs hm j hj h9
      simp only [matchLeafGo] at hm
      by_cases heq : (lookupV k L == w) = true
      · simp only [heq, ↓reduceIte] at hm
        cases j with
        | zero =>
          simp only [List.getD_cons_zero]
          exact lookupV_sound hL ⟨k, by omega⟩ (beq_iff_eq.mp heq) (hxs w (by simp))
        | succ j' =>
          have hrest := ih (k + 1) (fun x hx => hxs x (by simp [hx])) hm j' (by simp at hj; omega) (by omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 j'] using hrest
      · simp [heq] at hm
  simpa using go 0 lf hlt hm v.val (by omega) (by omega)


def checkTreeListVNo9 (im sm : ℕ)
    (f : List (ℕ × ℕ) → List ℕ → ℕ → List ℕ → Option (List ℕ))
    (op : ℕ) (L : List (ℕ × ℕ)) (vms : List ℕ) :
    List (ℕ × ℕ × ℕ × ℕ) → List ℕ → Option (List ℕ)
  | [], cur => some cur
  | (w, nu, dw, mw) :: ds', cur =>
    match applyVGoNo9 im sm dw mw vms with
    | none => checkTreeListVNo9 im sm f op L vms ds' cur
    | some vms' =>
      match f ((op, w) :: L) vms' nu cur with
      | none => none
      | some cur' => checkTreeListVNo9 im sm f op L vms ds' cur'

def checkTreeListVWith9 (im sm m9 : ℕ)
    (f : List (ℕ × ℕ) → List ℕ → ℕ → List ℕ → Option (List ℕ))
    (op : ℕ) (L : List (ℕ × ℕ)) (vms : List ℕ) :
    List (ℕ × ℕ × ℕ × ℕ) → List ℕ → Option (List ℕ)
  | [], cur => some cur
  | (w, nu, dw, mw) :: ds', cur =>
    match applyVGoWith9 im sm dw mw (mw ||| m9) vms with
    | none => checkTreeListVWith9 im sm m9 f op L vms ds' cur
    | some vms' =>
      match f ((op, w) :: L) vms' nu cur with
      | none => none
      | some cur' => checkTreeListVWith9 im sm m9 f op L vms ds' cur'

def checkTreeListN (hm : ℕ) (reqs : List ℕ)
    (f : List (ℕ × ℕ) → List ℕ → ℕ → List ℕ → Option (List ℕ))
    (L : List (ℕ × ℕ)) (vms : List ℕ) :
    List (ℕ × ℕ × ℕ × ℕ) → List ℕ → Option (List ℕ)
  | [], cur => some cur
  | (w, nu, dw, mw) :: ds', cur =>
    match applyNGo hm dw mw reqs vms with
    | none => checkTreeListN hm reqs f L vms ds' cur
    | some vms' =>
      match f ((9, w) :: L) vms' nu cur with
      | none => none
      | some cur' => checkTreeListN hm reqs f L vms ds' cur'

theorem checkTreeListVNo9_mem {im sm : ℕ}
    {f : List (ℕ × ℕ) → List ℕ → ℕ → List ℕ → Option (List ℕ)}
    {op : ℕ} {L : List (ℕ × ℕ)} {vms : List ℕ} {ds : List (ℕ × ℕ × ℕ × ℕ)} {cur res : List ℕ}
    (h : checkTreeListVNo9 im sm f op L vms ds cur = some res)
    {w nu dw mw : ℕ} (hmem : (w, nu, dw, mw) ∈ ds) {vms' : List ℕ}
    (happ : applyVGoNo9 im sm dw mw vms = some vms') :
    ∃ cur0 cur1, f ((op, w) :: L) vms' nu cur0 = some cur1 := by
  induction ds generalizing cur with
  | nil => simp at hmem
  | cons hd tl ih =>
    rcases hd with ⟨w0, nu0, dw0, mw0⟩
    simp only [checkTreeListVNo9] at h
    rcases List.mem_cons.mp hmem with heq | htl
    · rcases Prod.mk.inj heq with ⟨rfl, heq1⟩
      rcases Prod.mk.inj heq1 with ⟨rfl, heq2⟩
      rcases Prod.mk.inj heq2 with ⟨rfl, rfl⟩
      rw [happ] at h; dsimp only at h
      cases hf : f ((op, w) :: L) vms' nu cur with
      | none => rw [hf] at h; simp at h
      | some cur1 => exact ⟨cur, cur1, hf⟩
    · cases happ0 : applyVGoNo9 im sm dw0 mw0 vms with
      | none => rw [happ0] at h; exact ih h htl
      | some vms0 =>
        rw [happ0] at h; dsimp only at h
        cases hf0 : f ((op, w0) :: L) vms0 nu0 cur with
        | none => rw [hf0] at h; simp at h
        | some cur0 => rw [hf0] at h; exact ih h htl

theorem checkTreeListVWith9_mem {im sm m9 : ℕ}
    {f : List (ℕ × ℕ) → List ℕ → ℕ → List ℕ → Option (List ℕ)}
    {op : ℕ} {L : List (ℕ × ℕ)} {vms : List ℕ} {ds : List (ℕ × ℕ × ℕ × ℕ)} {cur res : List ℕ}
    (h : checkTreeListVWith9 im sm m9 f op L vms ds cur = some res)
    {w nu dw mw : ℕ} (hmem : (w, nu, dw, mw) ∈ ds) {vms' : List ℕ}
    (happ : applyVGoWith9 im sm dw mw (mw ||| m9) vms = some vms') :
    ∃ cur0 cur1, f ((op, w) :: L) vms' nu cur0 = some cur1 := by
  induction ds generalizing cur with
  | nil => simp at hmem
  | cons hd tl ih =>
    rcases hd with ⟨w0, nu0, dw0, mw0⟩
    simp only [checkTreeListVWith9] at h
    rcases List.mem_cons.mp hmem with heq | htl
    · rcases Prod.mk.inj heq with ⟨rfl, heq1⟩
      rcases Prod.mk.inj heq1 with ⟨rfl, heq2⟩
      rcases Prod.mk.inj heq2 with ⟨rfl, rfl⟩
      rw [happ] at h; dsimp only at h
      cases hf : f ((op, w) :: L) vms' nu cur with
      | none => rw [hf] at h; simp at h
      | some cur1 => exact ⟨cur, cur1, hf⟩
    · cases happ0 : applyVGoWith9 im sm dw0 mw0 (mw0 ||| m9) vms with
      | none => rw [happ0] at h; exact ih h htl
      | some vms0 =>
        rw [happ0] at h; dsimp only at h
        cases hf0 : f ((op, w0) :: L) vms0 nu0 cur with
        | none => rw [hf0] at h; simp at h
        | some cur0 => rw [hf0] at h; exact ih h htl

theorem checkTreeListN_mem {hm : ℕ} {reqs : List ℕ}
    {f : List (ℕ × ℕ) → List ℕ → ℕ → List ℕ → Option (List ℕ)}
    {L : List (ℕ × ℕ)} {vms : List ℕ} {ds : List (ℕ × ℕ × ℕ × ℕ)} {cur res : List ℕ}
    (h : checkTreeListN hm reqs f L vms ds cur = some res)
    {w nu dw mw : ℕ} (hmem : (w, nu, dw, mw) ∈ ds) {vms' : List ℕ}
    (happ : applyNGo hm dw mw reqs vms = some vms') :
    ∃ cur0 cur1, f ((9, w) :: L) vms' nu cur0 = some cur1 := by
  induction ds generalizing cur with
  | nil => simp at hmem
  | cons hd tl ih =>
    rcases hd with ⟨w0, nu0, dw0, mw0⟩
    simp only [checkTreeListN] at h
    rcases List.mem_cons.mp hmem with heq | htl
    · rcases Prod.mk.inj heq with ⟨rfl, heq1⟩
      rcases Prod.mk.inj heq1 with ⟨rfl, heq2⟩
      rcases Prod.mk.inj heq2 with ⟨rfl, rfl⟩
      rw [happ] at h; dsimp only at h
      cases hf : f ((9, w) :: L) vms' nu cur with
      | none => rw [hf] at h; simp at h
      | some cur1 => exact ⟨cur, cur1, hf⟩
    · cases happ0 : applyNGo hm dw0 mw0 reqs vms with
      | none => rw [happ0] at h; exact ih h htl
      | some vms0 =>
        rw [happ0] at h; dsimp only at h
        cases hf0 : f ((9, w0) :: L) vms0 nu0 cur with
        | none => rw [hf0] at h; simp at h
        | some cur0 => rw [hf0] at h; exact ih h htl

def checkTree (hm st0 st1 st2 st3 st4 st5 st6 st7 st8 cap1Mask noneGcap : ℕ)
    (allowed : List (List ℕ)) (proved : List (List (ℕ × ℕ) × ℕ)) :
    ℕ → List (ℕ × ℕ) → List ℕ → ℕ → List ℕ → Option (List ℕ)
  | 0, _, _, _, _ => none
  | fuel + 1, L, vms, used, buf =>
    match buf with
    | [] => none
    | op :: rest =>
      if op == 10 then
        if allowed.any (matchLeaf L) then some rest else none
      else if op == 11 then
        if proved.any (fun p => p.1 == L && p.2 == used) then some rest else none
      else if op < 9 then
        let im := inMask op
        let sm := stAt st0 st1 st2 st3 st4 st5 st6 st7 st8 op
        let dom := canonDomV (bitOn cap1Mask op) used
        match findNoneM9 L with
        | none =>
          checkTreeListVNo9 im sm
            (checkTree hm st0 st1 st2 st3 st4 st5 st6 st7 st8 cap1Mask noneGcap allowed proved fuel)
            op L vms dom rest
        | some m9 =>
          checkTreeListVWith9 im sm m9
            (checkTree hm st0 st1 st2 st3 st4 st5 st6 st7 st8 cap1Mask noneGcap allowed proved fuel)
            op L vms dom rest
      else if op == 9 then
        let reqs := preNReqs (prepNList st0 st1 st2 st3 st4 st5 st6 st7 st8 L)
        let dom := canonDomN noneGcap used
        checkTreeListN hm reqs
          (checkTree hm st0 st1 st2 st3 st4 st5 st6 st7 st8 cap1Mask noneGcap allowed proved fuel)
          L vms dom rest
      else none

def canonFlip (used w : ℕ) : Fin 16 :=
  let b0 := if 0 < used then 0 else if (w &&& 3) == 2 then 1 else 0
  let b1 := if 1 < used then 0 else if ((w >>> 2) &&& 3) == 2 then 2 else 0
  let b2 := if 2 < used then 0 else if ((w >>> 4) &&& 3) == 2 then 4 else 0
  let b3 := if 3 < used then 0 else if ((w >>> 6) &&& 3) == 2 then 8 else 0
  ⟨(b0 + b1 + b2 + b3) % 16, Nat.mod_lt _ (by decide)⟩

def canonPair (used w : ℕ) : ℕ × Fin 5 :=
  let low := w &&& ((1 <<< (2 * used)) - 1)
  let b0 := if 0 < used then 0 else (w &&& 3)
  let b1 := if 1 < used then 0 else ((w >>> 2) &&& 3)
  let b2 := if 2 < used then 0 else ((w >>> 4) &&& 3)
  let b3 := if 3 < used then 0 else ((w >>> 6) &&& 3)
  let c2 := (if b0 == 3 then 1 else 0) + (if b1 == 3 then 1 else 0) +
            (if b2 == 3 then 1 else 0) + (if b3 == 3 then 1 else 0)
  let c1 := (if b0 == 1 || b0 == 2 then 1 else 0) + (if b1 == 1 || b1 == 2 then 1 else 0) +
            (if b2 == 1 || b2 == 2 then 1 else 0) + (if b3 == 1 || b3 == 2 then 1 else 0)
  let addC2 := if c2 == 0 then 0 else ((1 <<< (2 * c2)) - 1) <<< (2 * used)
  let u1 := used + c2
  let addC1 :=
    (if 0 < c1 then 1 <<< (2 * u1) else 0) +
    (if 1 < c1 then 1 <<< (2 * (u1 + 1)) else 0) +
    (if 2 < c1 then 1 <<< (2 * (u1 + 2)) else 0) +
    (if 3 < c1 then 1 <<< (2 * (u1 + 3)) else 0)
  let nu := used + c2 + c1
  (low ||| addC2 ||| addC1, ⟨min nu 4, by omega⟩)

def findPerm4Go (used w cw : ℕ) (f : Fin 16) : ℕ → Fin 24
  | 0 => ⟨0, by decide⟩
  | k + 1 =>
    if hk : k < 24 then
      let p : Fin 24 := ⟨k, hk⟩
      if fixes4 used p f && applySym4 p f w == cw then p
      else findPerm4Go used w cw f k
    else findPerm4Go used w cw f k

def findPerm4 (used w : ℕ) : Fin 24 :=
  findPerm4Go used w (canonPair used w).1 (canonFlip used w) 24


theorem sym4_canonDomV_ok : ∀ (isCap1 : Bool) (used : Fin 5) (w : Fin 256),
    (if isCap1 then isCap1Mask w.val else isCap2Mask w.val) = true →
    let f := canonFlip used.val w.val
    let p := findPerm4 used.val w.val
    let cw := applySym4 p f w.val
    let nu := (canonPair used.val w.val).2
    fixes4 used.val p f = true ∧
      (cw, nu.val, disj81 cw, meet81 cw) ∈ canonDomV isCap1 used.val ∧
      used.val ≤ nu.val ∧ cw < 2 ^ (2 * nu.val) := by
  decide +kernel

theorem sym4_canonDomN_ok : ∀ (gcap : Fin 4) (used : Fin 5) (w : Fin 256),
    gateCountB w.val ≤ gcap.val + 1 →
    let f := canonFlip used.val w.val
    let p := findPerm4 used.val w.val
    let cw := applySym4 p f w.val
    let nu := (canonPair used.val w.val).2
    fixes4 used.val p f = true ∧
      (cw, nu.val, disj81 cw, meet81 cw) ∈ canonDomN (gcap.val + 1) used.val ∧
      used.val ≤ nu.val ∧ cw < 2 ^ (2 * nu.val) := by
  decide +kernel

theorem sym4_mem_canonDomV (isCap1 : Bool) (used : Fin 5) (w : Fin 256)
    (h : (if isCap1 then isCap1Mask w.val else isCap2Mask w.val) = true) :
    ∃ p : Fin 24, ∃ f : Fin 16, fixes4 used.val p f = true ∧
      ∃ nu : Fin 5,
        (applySym4 p f w.val, nu.val, disj81 (applySym4 p f w.val), meet81 (applySym4 p f w.val)) ∈ canonDomV isCap1 used.val ∧
        used.val ≤ nu.val ∧ applySym4 p f w.val < 2 ^ (2 * nu.val) :=
  let h0 := sym4_canonDomV_ok isCap1 used w h
  ⟨findPerm4 used.val w.val, canonFlip used.val w.val, h0.1, (canonPair used.val w.val).2, h0.2⟩

theorem sym4_mem_canonDomN (gcap : Fin 4) (used : Fin 5) (w : Fin 256)
    (h : gateCountB w.val ≤ gcap.val + 1) :
    ∃ p : Fin 24, ∃ f : Fin 16, fixes4 used.val p f = true ∧
      ∃ nu : Fin 5,
        (applySym4 p f w.val, nu.val, disj81 (applySym4 p f w.val), meet81 (applySym4 p f w.val)) ∈ canonDomN (gcap.val + 1) used.val ∧
        used.val ≤ nu.val ∧ applySym4 p f w.val < 2 ^ (2 * nu.val) :=
  let h0 := sym4_canonDomN_ok gcap used w h
  ⟨findPerm4 used.val w.val, canonFlip used.val w.val, h0.1, (canonPair used.val w.val).2, h0.2⟩

theorem checkTree_sound {a b cap1Mask noneGcap : ℕ} (ha : a < 512) (hb : b < 512)
    (hng_pos : 1 ≤ noneGcap) (hng_le : noneGcap ≤ 4)
    (allowed : List (List ℕ)) (proved : List (List (ℕ × ℕ) × ℕ))
    (hallow : ∀ lf ∈ allowed, lf.length = 9 ∧ ∀ w ∈ lf, w < 256)
    (hcap1 : ∀ v : V, bitOn cap1Mask v.val = true → Strong (decode a) (decode b) v)
    (hng : ∀ pos : X → Finset Slot, Cap (decode a) (decode b) pos → ((pos none).image Prod.fst).card ≤ noneGcap)
    (hproved : ∀ p ∈ proved, ∀ pos : X → Finset Slot,
      Cover (decode a) (decode b) pos → Cap (decode a) (decode b) pos → MatchesL pos p.1 →
      ∃ (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Bool),
        ∃ lf ∈ allowed, ∀ v : V, (pos (some v)).image (symSlot σ f) = slots (lf.getD v.val 256)) :
    ∀ (fuel : ℕ) (L : List (ℕ × ℕ)) (vms : List ℕ) (used : ℕ) (buf res : List ℕ),
      used ≤ 4 → BoundsL used L →
      (∀ r : Fin 16, MaskInv used (vms.getD r.val 0)) →
      checkTree (hotMask a b) (stMask a b (hotMask a b) 0) (stMask a b (hotMask a b) 1)
        (stMask a b (hotMask a b) 2) (stMask a b (hotMask a b) 3) (stMask a b (hotMask a b) 4)
        (stMask a b (hotMask a b) 5) (stMask a b (hotMask a b) 6) (stMask a b (hotMask a b) 7)
        (stMask a b (hotMask a b) 8) cap1Mask noneGcap allowed proved fuel L vms used buf = some res →
      ∀ pos : X → Finset Slot,
        Cover (decode a) (decode b) pos → Cap (decode a) (decode b) pos →
        MatchesL pos L → ValidMInv a b pos vms →
        ∃ (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Bool),
          ∃ lf ∈ allowed, ∀ v : V, (pos (some v)).image (symSlot σ f) = slots (lf.getD v.val 256) := by
  intro fuel
  induction fuel with
  | zero => intro L vms used buf res _ _ _ h; simp [checkTree] at h
  | succ fuel ih =>
    intro L vms used buf res hused hB hmi hchk pos hcov hcap hL hvm
    cases buf with
    | nil => simp [checkTree] at hchk
    | cons op rest =>
      simp only [checkTree] at hchk
      by_cases h10 : op = 10
      · subst h10
        simp only [beq_self_eq_true, ↓reduceIte] at hchk
        by_cases hany : allowed.any (matchLeaf L) = true
        · rw [List.any_eq_true] at hany
          obtain ⟨lf, hlf_mem, hlf_ok⟩ := hany
          obtain ⟨hlen, hlt⟩ := hallow lf hlf_mem
          refine ⟨Equiv.refl _, fun _ => false, lf, hlf_mem, fun v => ?_⟩
          have hid : (pos (some v)).image (symSlot (Equiv.refl (Fin 4)) (fun _ => false)) = pos (some v) := by
            ext s; simp [symSlot]
          rw [hid]
          exact matchLeaf_sound hL lf hlen hlt hlf_ok v
        · simp [hany] at hchk
      · have hne10 : (op == 10) = false := by simp [h10]
        simp only [hne10, Bool.false_eq_true, ↓reduceIte] at hchk
        by_cases h11 : op = 11
        · subst h11
          simp only [beq_self_eq_true, ↓reduceIte] at hchk
          by_cases hany : proved.any (fun p => p.1 == L && p.2 == used) = true
          · rw [List.any_eq_true] at hany
            obtain ⟨p, hp_mem, hp_eq⟩ := hany
            simp only [Bool.and_eq_true, beq_iff_eq] at hp_eq
            exact hproved p hp_mem pos hcov hcap (hp_eq.1.symm ▸ hL)
          · simp [hany] at hchk
        · have hne11 : (op == 11) = false := by simp [h11]
          simp only [hne11, Bool.false_eq_true, ↓reduceIte] at hchk
          by_cases hlt9 : op < 9
          · simp only [hlt9, ↓reduceIte] at hchk
            let v : V := ⟨op, hlt9⟩
            obtain ⟨w, hw_eq⟩ := slotsSurj (pos (some v))
            have hcons_w : Consistent (slots w.val) := hw_eq.symm ▸ (hcap.1 v).1
            have hcard2_w : (slots w.val).card ≤ 2 := hw_eq.symm ▸ (hcap.1 v).2
            have hmask_ok : (if bitOn cap1Mask op then isCap1Mask w.val else isCap2Mask w.val) = true := by
              cases hcb : bitOn cap1Mask op
              · exact isCap2Mask_of_cap w hcons_w hcard2_w
              · exact isCap1Mask_of_cap w hcons_w (hw_eq.symm ▸ hcap.2.1 v (hcap1 v hcb))
            obtain ⟨p, f, hfixb, nu, hmem, hle_nu, hw_lt⟩ :=
              sym4_mem_canonDomV (bitOn cap1Mask op) ⟨used, by omega⟩ w hmask_ok
            have hnu4 : nu.val ≤ 4 := by omega
            have hfix := fixes4_spec used p f hfixb
            let σ := perm4Equiv p
            let fb := flip4 f
            let pos1 : X → Finset Slot := fun z => (pos z).image (symSlot σ fb)
            have hcov1 : Cover (decode a) (decode b) pos1 := symSlot_cover σ fb hcov
            have hcap1' : Cap (decode a) (decode b) pos1 := symSlot_cap σ fb hcap
            have hL1 : MatchesL pos1 L := matchesL_sym4 σ fb hfix hL hB
            have hvm1 : ValidMInv a b pos1 vms := validMInv_sym4 σ fb hfix hmi hvm
            have hBnu : BoundsL nu.val L := boundsL_mono hle_nu hB
            have hminu : ∀ r : Fin 16, MaskInv nu.val (vms.getD r.val 0) := fun r => maskInv_mono hle_nu (hmi r)
            have hpos1v : pos1 (some v) = slots (applySym4 p f w.val) := by
              dsimp [pos1]; rw [← hw_eq, applySym4_slots]
            have hL' : MatchesL pos1 ((op, applySym4 p f w.val) :: L) := by
              intro t ht
              rcases List.mem_cons.mp ht with rfl | htl
              · exact ⟨applySym4_lt p f w, Or.inl ⟨hlt9, hpos1v⟩⟩
              · exact hL1 t htl
            have hB' : BoundsL nu.val ((op, applySym4 p f w.val) :: L) := by
              intro t ht
              rcases List.mem_cons.mp ht with rfl | htl
              · exact hw_lt
              · exact hBnu t htl
            have hst_eq : stAt (stMask a b (hotMask a b) 0) (stMask a b (hotMask a b) 1)
                (stMask a b (hotMask a b) 2) (stMask a b (hotMask a b) 3) (stMask a b (hotMask a b) 4)
                (stMask a b (hotMask a b) 5) (stMask a b (hotMask a b) 6) (stMask a b (hotMask a b) 7)
                (stMask a b (hotMask a b) 8) op = stMask a b (hotMask a b) v.val := stAt_stMask a b v
            cases hfn : findNoneM9 L with
            | none =>
              rw [hfn] at hchk; dsimp only at hchk
              rw [hst_eq] at hchk
              obtain ⟨vms', happ, hmi', hvm'⟩ :=
                applyVGoNo9_sound ha hb hnu4 v hw_lt hpos1v vms hminu hvm1
              obtain ⟨cur0, cur1, hsub⟩ := checkTreeListVNo9_mem hchk hmem happ
              obtain ⟨σ2, f2, lf, hlf_mem, hlf_eq⟩ := ih ((op, applySym4 p f w.val) :: L) vms' nu.val cur0 cur1 hnu4 hB' hmi' hsub pos1 hcov1 hcap1' hL' hvm'
              refine ⟨σ.trans σ2, fun g => xor (fb g) (f2 (σ g)), lf, hlf_mem, fun u => ?_⟩
              rw [← image_symSlot_comp σ σ2 fb f2]; exact hlf_eq u
            | some m9 =>
              rw [hfn] at hchk; dsimp only at hchk
              rw [hst_eq] at hchk
              obtain ⟨w9, hw9, hw9b, hpos9, rfl⟩ := findNoneM9_sound hL1 hBnu hfn
              obtain ⟨vms', happ, hmi', hvm'⟩ :=
                applyVGoWith9_sound ha hb hnu4 v hw_lt hpos1v hw9 hw9b hpos9 vms hminu hvm1
              obtain ⟨cur0, cur1, hsub⟩ := checkTreeListVWith9_mem hchk hmem happ
              obtain ⟨σ2, f2, lf, hlf_mem, hlf_eq⟩ := ih ((op, applySym4 p f w.val) :: L) vms' nu.val cur0 cur1 hnu4 hB' hmi' hsub pos1 hcov1 hcap1' hL' hvm'
              refine ⟨σ.trans σ2, fun g => xor (fb g) (f2 (σ g)), lf, hlf_mem, fun u => ?_⟩
              rw [← image_symSlot_comp σ σ2 fb f2]; exact hlf_eq u
          · simp only [hlt9, ↓reduceIte] at hchk
            by_cases h9 : op = 9
            · subst h9
              simp only [beq_self_eq_true, ↓reduceIte] at hchk
              obtain ⟨w, hw_eq⟩ := slotsSurj (pos none)
              have hgc : gateCountB w.val ≤ (noneGcap - 1) + 1 := by
                rw [← gateCountB_eq w, hw_eq]
                have := hng pos hcap; omega
              obtain ⟨p, f, hfixb, nu, hmem, hle_nu, hw_lt⟩ :=
                sym4_mem_canonDomN ⟨noneGcap - 1, by omega⟩ ⟨used, by omega⟩ w hgc
              have hnu4 : nu.val ≤ 4 := by omega
              have hng_eq : (noneGcap - 1) + 1 = noneGcap := by omega
              rw [hng_eq] at hmem
              have hfix := fixes4_spec used p f hfixb
              let σ := perm4Equiv p
              let fb := flip4 f
              let pos1 : X → Finset Slot := fun z => (pos z).image (symSlot σ fb)
              have hcov1 : Cover (decode a) (decode b) pos1 := symSlot_cover σ fb hcov
              have hcap1' : Cap (decode a) (decode b) pos1 := symSlot_cap σ fb hcap
              have hL1 : MatchesL pos1 L := matchesL_sym4 σ fb hfix hL hB
              have hvm1 : ValidMInv a b pos1 vms := validMInv_sym4 σ fb hfix hmi hvm
              have hBnu : BoundsL nu.val L := boundsL_mono hle_nu hB
              have hminu : ∀ r : Fin 16, MaskInv nu.val (vms.getD r.val 0) := fun r => maskInv_mono hle_nu (hmi r)
              have hpos19 : pos1 none = slots (applySym4 p f w.val) := by
                dsimp [pos1]; rw [← hw_eq, applySym4_slots]
              obtain ⟨vms', happ, hmi', hvm'⟩ :=
                applyNGo_sound ha hb hnu4 hL1 hBnu hw_lt hpos19 vms hminu hvm1
              obtain ⟨cur0, cur1, hsub⟩ := checkTreeListN_mem hchk hmem happ
              have hL' : MatchesL pos1 ((9, applySym4 p f w.val) :: L) := by
                intro t ht
                rcases List.mem_cons.mp ht with rfl | htl
                · exact ⟨applySym4_lt p f w, Or.inr ⟨rfl, hpos19⟩⟩
                · exact hL1 t htl
              have hB' : BoundsL nu.val ((9, applySym4 p f w.val) :: L) := by
                intro t ht
                rcases List.mem_cons.mp ht with rfl | htl
                · exact hw_lt
                · exact hBnu t htl
              obtain ⟨σ2, f2, lf, hlf_mem, hlf_eq⟩ := ih ((9, applySym4 p f w.val) :: L) vms' nu.val cur0 cur1 hnu4 hB' hmi' hsub pos1 hcov1 hcap1' hL' hvm'
              refine ⟨σ.trans σ2, fun g => xor (fb g) (f2 (σ g)), lf, hlf_mem, fun u => ?_⟩
              rw [← image_symSlot_comp σ σ2 fb f2]; exact hlf_eq u
            · have hne9 : (op == 9) = false := by simp [h9]
              simp [hne9] at hchk

def initApplyGo (st0 st1 st2 st3 st4 st5 st6 st7 st8 : ℕ) :
    ℕ → List ℕ → List (ℕ × ℕ) → List ℕ → Option (List (ℕ × ℕ) × List ℕ)
  | _, [], L, vms => some (L, vms)
  | j, v :: cs', L, vms =>
    let w := pow2 (2 * j)
    match applyVGoNo9 (inMask v) (stAt st0 st1 st2 st3 st4 st5 st6 st7 st8 v) (disj81 w) (meet81 w) vms with
    | none => none
    | some vms' => initApplyGo st0 st1 st2 st3 st4 st5 st6 st7 st8 (j + 1) cs' ((v, w) :: L) vms'

def initApply (st0 st1 st2 st3 st4 st5 st6 st7 st8 : ℕ) (clq : List ℕ) :
    Option (List (ℕ × ℕ) × List ℕ) :=
  initApplyGo st0 st1 st2 st3 st4 st5 st6 st7 st8 0 clq []
    [all81, all81, all81, all81, all81, all81, all81, all81,
     all81, all81, all81, all81, all81, all81, all81, all81]

theorem slots_pow2_even (j : Fin 4) : slots (pow2 (2 * j.val)) = {(j, false)} := by
  fin_cases j <;> decide +kernel

theorem initApply_sound {a b : ℕ} (ha : a < 512) (hb : b < 512)
    (clq : List ℕ) (hclq_len : clq.length ≤ 4) (hclq_lt : ∀ v ∈ clq, v < 9)
    {pos : X → Finset Slot} (hcov : Cover (decode a) (decode b) pos)
    (hinit : ∀ (j : Fin clq.length), pos (some ⟨clq.get j, hclq_lt _ (List.get_mem clq j)⟩) =
      {(Fin.castLE hclq_len j, false)}) :
    ∃ L vms, initApply (stMask a b (hotMask a b) 0) (stMask a b (hotMask a b) 1)
        (stMask a b (hotMask a b) 2) (stMask a b (hotMask a b) 3) (stMask a b (hotMask a b) 4)
        (stMask a b (hotMask a b) 5) (stMask a b (hotMask a b) 6) (stMask a b (hotMask a b) 7)
        (stMask a b (hotMask a b) 8) clq = some (L, vms) ∧
      BoundsL clq.length L ∧
      (∀ r : Fin 16, MaskInv clq.length (vms.getD r.val 0)) ∧
      MatchesL pos L ∧ ValidMInv a b pos vms := by
  have go : ∀ (k : ℕ) (cs : List ℕ) (L : List (ℕ × ℕ)) (vms : List ℕ)
      (hlen : k + cs.length ≤ 4) (hlt : ∀ v ∈ cs, v < 9),
      (∀ (j : Fin cs.length), pos (some ⟨cs.get j, hlt _ (List.get_mem cs j)⟩) =
        {(⟨k + j.val, by have := j.isLt; omega⟩, false)}) →
      BoundsL k L →
      (∀ r : Fin 16, MaskInv k (vms.getD r.val 0)) →
      MatchesL pos L → ValidMInv a b pos vms →
      ∃ L' vms', initApplyGo (stMask a b (hotMask a b) 0) (stMask a b (hotMask a b) 1)
          (stMask a b (hotMask a b) 2) (stMask a b (hotMask a b) 3) (stMask a b (hotMask a b) 4)
          (stMask a b (hotMask a b) 5) (stMask a b (hotMask a b) 6) (stMask a b (hotMask a b) 7)
          (stMask a b (hotMask a b) 8) k cs L vms = some (L', vms') ∧
        BoundsL (k + cs.length) L' ∧
        (∀ r : Fin 16, MaskInv (k + cs.length) (vms'.getD r.val 0)) ∧
        MatchesL pos L' ∧ ValidMInv a b pos vms' := by
    intro k cs
    induction cs generalizing k with
    | nil =>
      intro L vms _ _ _ hB hmi hL hvm
      exact ⟨L, vms, rfl, by simpa using hB, by simpa using hmi, hL, hvm⟩
    | cons v rest ih =>
      intro L vms hlen hlt hpos hB hmi hL hvm
      have hk4 : k < 4 := by simp at hlen; omega
      have hv9 : v < 9 := hlt v (by simp)
      have hposv : pos (some ⟨v, hv9⟩) = slots (pow2 (2 * k)) := by
        have h0 := hpos ⟨0, by simp⟩
        rw [slots_pow2_even ⟨k, hk4⟩]; simpa using h0
      have hwlt : pow2 (2 * k) < 2 ^ (2 * (k + 1)) := by
        rw [pow2_eq (2 * k) (by omega)]
        exact Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega)
      have hBk1 : BoundsL (k + 1) L := boundsL_mono (by omega) hB
      have hmik1 : ∀ r : Fin 16, MaskInv (k + 1) (vms.getD r.val 0) := fun r => maskInv_mono (by omega) (hmi r)
      obtain ⟨vms1, happ, hmi1, hvm1⟩ :=
        applyVGoNo9_sound ha hb (by omega) ⟨v, hv9⟩ hwlt hposv vms hmik1 hvm
      have hL1 : MatchesL pos ((v, pow2 (2 * k)) :: L) := by
        intro t ht
        rcases List.mem_cons.mp ht with rfl | htl
        · exact ⟨lt_of_lt_of_le hwlt (show 2 ^ (2 * (k + 1)) ≤ 2 ^ 8 from Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)), Or.inl ⟨hv9, hposv⟩⟩
        · exact hL t htl
      have hB1 : BoundsL (k + 1) ((v, pow2 (2 * k)) :: L) := by
        intro t ht
        rcases List.mem_cons.mp ht with rfl | htl
        · exact hwlt
        · exact hBk1 t htl
      obtain ⟨L', vms', hrec, hB', hmi', hL', hvm'⟩ :=
        ih (k + 1) ((v, pow2 (2 * k)) :: L) vms1 (by simp at hlen ⊢; omega)
          (fun x hx => hlt x (by simp [hx]))
          (fun j => by
            have := hpos ⟨j.val + 1, by simp⟩
            simpa [Nat.add_assoc, Nat.add_comm 1 j.val] using this)
          hB1 hmi1 hL1 hvm1
      refine ⟨L', vms', ?_, ?_, ?_, hL', hvm'⟩
      · simp only [initApplyGo, stAt_stMask a b ⟨v, hv9⟩, happ, hrec]
      · simpa [Nat.add_assoc, Nat.add_comm 1 rest.length] using hB'
      · simpa [Nat.add_assoc, Nat.add_comm 1 rest.length] using hmi'
  have hmi0 : ∀ r : Fin 16, MaskInv 0 (([all81, all81, all81, all81, all81, all81, all81, all81,
      all81, all81, all81, all81, all81, all81, all81, all81] : List ℕ).getD r.val 0) := by
    intro r
    have hget : ([all81, all81, all81, all81, all81, all81, all81, all81,
      all81, all81, all81, all81, all81, all81, all81, all81] : List ℕ).getD r.val 0 = all81 := by
      fin_cases r <;> rfl
    rw [hget]; exact maskInv_all81 0
  simpa [initApply] using go 0 clq [] _ (by simpa using hclq_len) hclq_lt (fun j => by simpa [Fin.castLE] using hinit j)
    (fun _ h => by simp at h) hmi0 (fun _ h => by simp at h) (validMInv_init hcov)

def applyPairsGo (hm st0 st1 st2 st3 st4 st5 st6 st7 st8 : ℕ) :
    List (ℕ × ℕ) → List (ℕ × ℕ) → List ℕ → Option (List (ℕ × ℕ) × List ℕ)
  | [], L, vms => some (L, vms)
  | (var, w) :: ps, L, vms =>
    let res :=
      if var < 9 then
        match findNoneM9 L with
        | none => applyVGoNo9 (inMask var) (stAt st0 st1 st2 st3 st4 st5 st6 st7 st8 var) (disj81 w) (meet81 w) vms
        | some m9 => applyVGoWith9 (inMask var) (stAt st0 st1 st2 st3 st4 st5 st6 st7 st8 var) (disj81 w) (meet81 w) (meet81 w ||| m9) vms
      else
        applyNGo hm (disj81 w) (meet81 w) (preNReqs (prepNList st0 st1 st2 st3 st4 st5 st6 st7 st8 L)) vms
    match res with
    | none => none
    | some vms' => applyPairsGo hm st0 st1 st2 st3 st4 st5 st6 st7 st8 ps ((var, w) :: L) vms'

theorem applyPairsGo_sound {a b used : ℕ} (ha : a < 512) (hb : b < 512) (hused : used ≤ 4)
    {pos : X → Finset Slot} :
    ∀ (ps L : List (ℕ × ℕ)) (vms : List ℕ),
      MatchesL pos ps → BoundsL used ps →
      MatchesL pos L → BoundsL used L →
      (∀ r : Fin 16, MaskInv used (vms.getD r.val 0)) →
      ValidMInv a b pos vms →
      ∃ vms', applyPairsGo (hotMask a b) (stMask a b (hotMask a b) 0) (stMask a b (hotMask a b) 1)
          (stMask a b (hotMask a b) 2) (stMask a b (hotMask a b) 3) (stMask a b (hotMask a b) 4)
          (stMask a b (hotMask a b) 5) (stMask a b (hotMask a b) 6) (stMask a b (hotMask a b) 7)
          (stMask a b (hotMask a b) 8) ps L vms = some (ps.reverse ++ L, vms') ∧
        (∀ r : Fin 16, MaskInv used (vms'.getD r.val 0)) ∧
        ValidMInv a b pos vms' := by
  intro ps
  induction ps with
  | nil => intro L vms _ _ _ _ hmi hvm; exact ⟨vms, rfl, hmi, hvm⟩
  | cons hd tl ih =>
    intro L vms hLps hBps hL hB hmi hvm
    rcases hd with ⟨var, w⟩
    have hhd := hLps (var, w) (by simp)
    have hbhd := hBps (var, w) (by simp)
    have hLtl : MatchesL pos tl := fun t ht => hLps t (by simp [ht])
    have hBtl : BoundsL used tl := fun t ht => hBps t (by simp [ht])
    have hL1 : MatchesL pos ((var, w) :: L) := fun t ht => by
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact hhd
      · exact hL t hmem
    have hB1 : BoundsL used ((var, w) :: L) := fun t ht => by
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact hbhd
      · exact hB t hmem
    have hstep : ∃ vms1,
        (if var < 9 then
          match findNoneM9 L with
          | none => applyVGoNo9 (inMask var) (stAt (stMask a b (hotMask a b) 0) (stMask a b (hotMask a b) 1)
              (stMask a b (hotMask a b) 2) (stMask a b (hotMask a b) 3) (stMask a b (hotMask a b) 4)
              (stMask a b (hotMask a b) 5) (stMask a b (hotMask a b) 6) (stMask a b (hotMask a b) 7)
              (stMask a b (hotMask a b) 8) var) (disj81 w) (meet81 w) vms
          | some m9 => applyVGoWith9 (inMask var) (stAt (stMask a b (hotMask a b) 0) (stMask a b (hotMask a b) 1)
              (stMask a b (hotMask a b) 2) (stMask a b (hotMask a b) 3) (stMask a b (hotMask a b) 4)
              (stMask a b (hotMask a b) 5) (stMask a b (hotMask a b) 6) (stMask a b (hotMask a b) 7)
              (stMask a b (hotMask a b) 8) var) (disj81 w) (meet81 w) (meet81 w ||| m9) vms
        else
          applyNGo (hotMask a b) (disj81 w) (meet81 w)
            (preNReqs (prepNList (stMask a b (hotMask a b) 0) (stMask a b (hotMask a b) 1)
              (stMask a b (hotMask a b) 2) (stMask a b (hotMask a b) 3) (stMask a b (hotMask a b) 4)
              (stMask a b (hotMask a b) 5) (stMask a b (hotMask a b) 6) (stMask a b (hotMask a b) 7)
              (stMask a b (hotMask a b) 8) L)) vms) = some vms1 ∧
        (∀ r : Fin 16, MaskInv used (vms1.getD r.val 0)) ∧ ValidMInv a b pos vms1 := by
      rcases hhd.2 with ⟨hv9, hposv⟩ | ⟨rfl, hpos9⟩
      · simp only [hv9, ↓reduceIte, stAt_stMask a b ⟨var, hv9⟩]
        cases hfn : findNoneM9 L with
        | none => exact applyVGoNo9_sound ha hb hused ⟨var, hv9⟩ hbhd hposv vms hmi hvm
        | some m9 =>
          obtain ⟨w9, hw9, hw9b, hpos9, rfl⟩ := findNoneM9_sound hL hB hfn
          exact applyVGoWith9_sound ha hb hused ⟨var, hv9⟩ hbhd hposv hw9 hw9b hpos9 vms hmi hvm
      · simp only [show ¬ (9 < 9) by omega, ↓reduceIte]
        exact applyNGo_sound ha hb hused hL hB hbhd hpos9 vms hmi hvm
    obtain ⟨vms1, happ, hmi1, hvm1⟩ := hstep
    obtain ⟨vms', hrec, hmi', hvm'⟩ := ih ((var, w) :: L) vms1 hLtl hBtl hL1 hB1 hmi1 hvm1
    refine ⟨vms', ?_, hmi', hvm'⟩
    simp only [applyPairsGo, happ, hrec, List.reverse_cons, List.append_assoc, List.singleton_append]

def pairsApart (a b hm : ℕ) : List ℕ → Bool
  | [] => true
  | r :: rs => rs.all (fun s => r != s && apartB a b hm r s) && pairsApart a b hm rs

theorem pairsApart_sound {a b : ℕ} (ha : a < 512) (hb : b < 512) (nw : List ℕ)
    (hlt : ∀ r ∈ nw, r < 16) (hp : pairsApart a b (hotMask a b) nw = true) :
    ∀ (i j : Fin nw.length), i ≠ j →
      Apart (decode a) (decode b) ⟨nw.get i, hlt _ (List.get_mem nw i)⟩ ⟨nw.get j, hlt _ (List.get_mem nw j)⟩ := by
  have go : ∀ (xs : List ℕ) (hxs : ∀ r ∈ xs, r < 16), pairsApart a b (hotMask a b) xs = true →
      ∀ (i j : Fin xs.length), i.val < j.val →
        Apart (decode a) (decode b) ⟨xs.get i, hxs _ (List.get_mem xs i)⟩
          ⟨xs.get j, hxs _ (List.get_mem xs j)⟩ := by
    intro xs
    induction xs with
    | nil => intro _ _ i; exact Fin.elim0 i
    | cons r rs ih =>
      intro hxs hp i j hij
      simp only [pairsApart, Bool.and_eq_true, List.all_eq_true] at hp
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j' =>
          have hmem : rs.get j' ∈ rs := List.get_mem rs j'
          have hpair := hp.1 (rs.get j') hmem
          simp only [bne_iff_ne, ne_eq] at hpair
          have hne : (⟨r, hxs r (by simp)⟩ : Fin 16) ≠ ⟨rs.get j', hxs _ (by simp)⟩ :=
            fun h => hpair.1 (congrArg Fin.val h)
          exact apartB_sound a b ha hb ⟨r, hxs r (by simp)⟩ ⟨rs.get j', hxs _ (by simp)⟩ hne hpair.2
      | succ i' =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j' =>
          exact ih (fun x hx => hxs x (by simp [hx])) hp.2 i' j' (by simpa using hij)
  intro i j hne
  by_cases hlt' : i.val < j.val
  · exact go nw hlt hp i j hlt'
  · have hgt : j.val < i.val := by omega
    exact (go nw hlt hp j i hgt).symm

def checkNoneWit (a b hm gcap : ℕ) (nw : List ℕ) : Bool :=
  let req := match gcap with | 1 => 5 | 2 => 3 | 3 => 2 | _ => 0
  if req == 0 then true
  else
    nw.length == req &&
    nw.all (fun r => r < 16 && bitOn hm r) &&
    pairsApart a b hm nw

theorem checkNoneWit_sound {a b gcap : ℕ} (ha : a < 512) (hb : b < 512)
    (h1 : 1 ≤ gcap) (h4 : gcap ≤ 4) (nw : List ℕ)
    (hchk : checkNoneWit a b (hotMask a b) gcap nw = true)
    (pos : X → Finset Slot) (hcap : Cap (decode a) (decode b) pos) :
    ((pos none).image Prod.fst).card ≤ gcap := by
  by_cases hg4 : gcap = 4
  · subst hg4
    have hle : ((pos none).image Prod.fst).card ≤ (Finset.univ : Finset (Fin 4)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    simpa using hle
  · have hcases : gcap = 1 ∨ gcap = 2 ∨ gcap = 3 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp only [checkNoneWit, beq_iff_eq, show ¬ (5 = 0) by omega, ↓reduceIte, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq] at hchk
      have hlen : nw.length = 5 := hchk.1.1
      have hlt : ∀ r ∈ nw, r < 16 := fun r hr => (hchk.1.2 r hr).1
      let rs : Fin (2 ^ 2 + 1) → Fin 16 := fun i =>
        ⟨nw.get ⟨i.val, by omega⟩, hlt _ (List.get_mem nw ⟨i.val, by omega⟩)⟩
      have hhot : ∀ i, fires (decode a) (decode b) (rows (rs i)) := fun i => by
        have hbit : bitOn (hotMask a b) (rs i).val = true := (hchk.1.2 _ (List.get_mem nw ⟨i.val, by omega⟩)).2
        rw [bitOn_hotMask, firesB_iff a b (rowAt _) ha hb, decode_rowAt] at hbit
        exact hbit
      have hap : ∀ i j, i ≠ j → Apart (decode a) (decode b) (rs i) (rs j) := fun i j hne =>
        pairsApart_sound ha hb nw hlt hchk.2 ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
          (fun h => hne (Fin.ext (congrArg (fun x : Fin nw.length => x.val) h)))
      have := hcap.2.2 2 rs hhot hap
      omega
    · simp only [checkNoneWit, beq_iff_eq, show ¬ (3 = 0) by omega, ↓reduceIte, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq] at hchk
      have hlen : nw.length = 3 := hchk.1.1
      have hlt : ∀ r ∈ nw, r < 16 := fun r hr => (hchk.1.2 r hr).1
      let rs : Fin (2 ^ 1 + 1) → Fin 16 := fun i =>
        ⟨nw.get ⟨i.val, by omega⟩, hlt _ (List.get_mem nw ⟨i.val, by omega⟩)⟩
      have hhot : ∀ i, fires (decode a) (decode b) (rows (rs i)) := fun i => by
        have hbit : bitOn (hotMask a b) (rs i).val = true := (hchk.1.2 _ (List.get_mem nw ⟨i.val, by omega⟩)).2
        rw [bitOn_hotMask, firesB_iff a b (rowAt _) ha hb, decode_rowAt] at hbit
        exact hbit
      have hap : ∀ i j, i ≠ j → Apart (decode a) (decode b) (rs i) (rs j) := fun i j hne =>
        pairsApart_sound ha hb nw hlt hchk.2 ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
          (fun h => hne (Fin.ext (congrArg (fun x : Fin nw.length => x.val) h)))
      have := hcap.2.2 1 rs hhot hap
      omega
    · simp only [checkNoneWit, beq_iff_eq, show ¬ (2 = 0) by omega, ↓reduceIte, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq] at hchk
      have hlen : nw.length = 2 := hchk.1.1
      have hlt : ∀ r ∈ nw, r < 16 := fun r hr => (hchk.1.2 r hr).1
      let rs : Fin (2 ^ 0 + 1) → Fin 16 := fun i =>
        ⟨nw.get ⟨i.val, by omega⟩, hlt _ (List.get_mem nw ⟨i.val, by omega⟩)⟩
      have hhot : ∀ i, fires (decode a) (decode b) (rows (rs i)) := fun i => by
        have hbit : bitOn (hotMask a b) (rs i).val = true := (hchk.1.2 _ (List.get_mem nw ⟨i.val, by omega⟩)).2
        rw [bitOn_hotMask, firesB_iff a b (rowAt _) ha hb, decode_rowAt] at hbit
        exact hbit
      have hap : ∀ i j, i ≠ j → Apart (decode a) (decode b) (rs i) (rs j) := fun i j hne =>
        pairsApart_sound ha hb nw hlt hchk.2 ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
          (fun h => hne (Fin.ext (congrArg (fun x : Fin nw.length => x.val) h)))
      have := hcap.2.2 0 rs hhot hap
      omega

def pairsConf (a b hm : ℕ) : List ℕ → Bool
  | [] => true
  | v :: vs => vs.all (fun w => v != w && conflictB a b hm v w) && pairsConf a b hm vs

def checkInitClq (a b hm sub0 : ℕ) (clq : List ℕ) : Bool :=
  clq.length <= 4 &&
  clq.all (fun v => v < 9 && strongB a b hm sub0 v && hasStableB a b hm v) &&
  pairsConf a b hm clq

theorem checkInitClq_sound {a b sub0 : ℕ} (ha : a < 512) (hb : b < 512) (hsub : sub0 < 56)
    (clq : List ℕ) (hchk : checkInitClq a b (hotMask a b) sub0 clq = true) :
    ∃ (_ : clq.length ≤ 4) (hlt : ∀ v ∈ clq, v < 9),
      Clique (decode a) (decode b) (fun j : Fin clq.length => ⟨clq.get j, hlt _ (List.get_mem clq j)⟩) := by
  simp only [checkInitClq, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
  have hlen : clq.length ≤ 4 := hchk.1.1
  have hlt : ∀ v ∈ clq, v < 9 := fun v hv => (hchk.1.2 v hv).1.1
  have hconf_symm : ∀ {v w : V}, Conflict (decode a) (decode b) v w → Conflict (decode a) (decode b) w v := by
    intro v w ⟨⟨r, h1, h2⟩, h3⟩
    exact ⟨⟨r, h2, h1⟩, h3.symm⟩
  have hpairs : ∀ (xs : List ℕ) (hxs : ∀ v ∈ xs, v < 9), pairsConf a b (hotMask a b) xs = true →
      ∀ (i j : Fin xs.length), i.val < j.val →
        Conflict (decode a) (decode b) ⟨xs.get i, hxs _ (List.get_mem xs i)⟩
          ⟨xs.get j, hxs _ (List.get_mem xs j)⟩ := by
    intro xs
    induction xs with
    | nil => intro _ _ i; exact Fin.elim0 i
    | cons v vs ih =>
      intro hxs hp i j hij
      simp only [pairsConf, Bool.and_eq_true, List.all_eq_true] at hp
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j' =>
          have hmem := List.get_mem vs j'
          have hpair := hp.1 (vs.get j') hmem
          exact conflictB_sound a b ha hb ⟨v, hxs v (by simp)⟩ ⟨vs.get j', hxs _ (by simp)⟩ hpair.2
      | succ i' =>
        cases j using Fin.cases with
        | zero => simp at hij
        | succ j' => exact ih (fun x hx => hxs x (by simp [hx])) hp.2 i' j' (by simpa using hij)
  refine ⟨hlen, hlt, ?_, ?_, ?_⟩
  · intro j
    have hv := (hchk.1.2 _ (List.get_mem clq j)).1.2
    exact strongB_sound a b sub0 ha hb hsub ⟨clq.get j, hlt _ (List.get_mem clq j)⟩ hv
  · intro j
    have hv := (hchk.1.2 _ (List.get_mem clq j)).2
    exact hasStableB_sound a b ha hb ⟨clq.get j, hlt _ (List.get_mem clq j)⟩ hv
  · intro i j hne
    by_cases hlt' : i.val < j.val
    · exact hpairs clq hlt hchk.2 i j hlt'
    · exact hconf_symm (hpairs clq hlt hchk.2 j i (by omega))

def checkCap1MaskGo (a b hm sub0 cap1Mask : ℕ) : ℕ → Bool
  | 0 => true
  | v' + 1 =>
    if bitOn cap1Mask v' then
      if strongB a b hm sub0 v' then checkCap1MaskGo a b hm sub0 cap1Mask v' else false
    else checkCap1MaskGo a b hm sub0 cap1Mask v'

def checkCap1Mask (a b hm sub0 cap1Mask : ℕ) : Bool :=
  checkCap1MaskGo a b hm sub0 cap1Mask 9

theorem checkCap1Mask_sound {a b sub0 cap1Mask : ℕ} (ha : a < 512) (hb : b < 512) (hsub : sub0 < 56)
    (hchk : checkCap1Mask a b (hotMask a b) sub0 cap1Mask = true) (v : V)
    (hbv : bitOn cap1Mask v.val = true) : Strong (decode a) (decode b) v := by
  have go : ∀ k : ℕ, checkCap1MaskGo a b (hotMask a b) sub0 cap1Mask k = true →
      ∀ j < k, bitOn cap1Mask j = true → strongB a b (hotMask a b) sub0 j = true := by
    intro k
    induction k with
    | zero => intro _ j hj; omega
    | succ k ih =>
      intro h j hj hbj
      simp only [checkCap1MaskGo] at h
      by_cases hjk : j = k
      · subst hjk
        simp only [hbj, ↓reduceIte] at h
        by_cases hs : strongB a b (hotMask a b) sub0 j = true
        · exact hs
        · simp [hs] at h
      · have hprev : checkCap1MaskGo a b (hotMask a b) sub0 cap1Mask k = true := by
          by_cases hbk : bitOn cap1Mask k = true
          · simp only [hbk, ↓reduceIte] at h
            by_cases hs : strongB a b (hotMask a b) sub0 k = true
            · simpa [hs] using h
            · simp [hs] at h
          · simpa [hbk] using h
        exact ih hprev j (by omega) hbj
  exact strongB_sound a b sub0 ha hb hsub v (go 9 hchk v.val v.isLt hbv)


def checkSub (a b cap1Mask noneGcap used : ℕ) (path : List (ℕ × ℕ)) (buf : List ℕ)
    (allowed : List (List ℕ)) : Bool :=
  let hm := hotMask a b
  let st0 := stMask a b hm 0
  let st1 := stMask a b hm 1
  let st2 := stMask a b hm 2
  let st3 := stMask a b hm 3
  let st4 := stMask a b hm 4
  let st5 := stMask a b hm 5
  let st6 := stMask a b hm 6
  let st7 := stMask a b hm 7
  let st8 := stMask a b hm 8
  used <= 4 &&
  path.all (fun p => p.2 < pow2 (2 * used)) &&
  match applyPairsGo hm st0 st1 st2 st3 st4 st5 st6 st7 st8 path.reverse []
      [all81, all81, all81, all81, all81, all81, all81, all81,
       all81, all81, all81, all81, all81, all81, all81, all81] with
  | none => true
  | some (L, vms) =>
    match checkTree hm st0 st1 st2 st3 st4 st5 st6 st7 st8 cap1Mask noneGcap allowed [] 12 L vms used buf with
    | some [] => true
    | _ => false

theorem checkSub_sound {a b cap1Mask noneGcap used : ℕ} (ha : a < 512) (hb : b < 512)
    (hng1 : 1 ≤ noneGcap) (hng4 : noneGcap ≤ 4)
    (path : List (ℕ × ℕ)) (buf : List ℕ) (allowed : List (List ℕ))
    (hallow : ∀ lf ∈ allowed, lf.length = 9 ∧ ∀ w ∈ lf, w < 256)
    (hcap1 : ∀ v : V, bitOn cap1Mask v.val = true → Strong (decode a) (decode b) v)
    (hng : ∀ pos : X → Finset Slot, Cap (decode a) (decode b) pos → ((pos none).image Prod.fst).card ≤ noneGcap)
    (hchk : checkSub a b cap1Mask noneGcap used path buf allowed = true)
    (pos : X → Finset Slot) (hcov : Cover (decode a) (decode b) pos) (hcap : Cap (decode a) (decode b) pos)
    (hL : MatchesL pos path) :
    ∃ (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Bool),
      ∃ lf ∈ allowed, ∀ v : V, (pos (some v)).image (symSlot σ f) = slots (lf.getD v.val 256) := by
  unfold checkSub at hchk
  dsimp only at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
  obtain ⟨⟨hused, hball⟩, hrun⟩ := hchk
  have hB : BoundsL used path := fun t ht => by
    have hlt := hball t ht
    rwa [pow2_eq (2 * used) (by omega)] at hlt
  have hLrev : MatchesL pos path.reverse := fun t ht => hL t (List.mem_reverse.mp ht)
  have hBrev : BoundsL used path.reverse := fun t ht => hB t (List.mem_reverse.mp ht)
  have hmi0 : ∀ r : Fin 16, MaskInv used (([all81, all81, all81, all81, all81, all81, all81, all81,
      all81, all81, all81, all81, all81, all81, all81, all81] : List ℕ).getD r.val 0) := by
    intro r
    have hget : ([all81, all81, all81, all81, all81, all81, all81, all81,
      all81, all81, all81, all81, all81, all81, all81, all81] : List ℕ).getD r.val 0 = all81 := by
      fin_cases r <;> rfl
    rw [hget]; exact maskInv_all81 used
  obtain ⟨vms, happ, hmi, hvm⟩ :=
    applyPairsGo_sound ha hb hused path.reverse [] _ hLrev hBrev
      (fun _ h => by simp at h) (fun _ h => by simp at h) hmi0 (validMInv_init hcov)
  simp only [List.reverse_reverse, List.append_nil] at happ
  rw [happ] at hrun
  dsimp only at hrun
  cases hct : checkTree (hotMask a b) (stMask a b (hotMask a b) 0) (stMask a b (hotMask a b) 1)
      (stMask a b (hotMask a b) 2) (stMask a b (hotMask a b) 3) (stMask a b (hotMask a b) 4)
      (stMask a b (hotMask a b) 5) (stMask a b (hotMask a b) 6) (stMask a b (hotMask a b) 7)
      (stMask a b (hotMask a b) 8) cap1Mask noneGcap allowed [] 12 path vms used buf with
  | none => rw [hct] at hrun; simp at hrun
  | some rem =>
    exact checkTree_sound ha hb hng1 hng4 allowed [] hallow hcap1 hng (by simp)
      12 path vms used buf rem hused hB hmi hct pos hcov hcap hL hvm

def checkSpecialSplit (a b sub0 cap1Mask noneGcap : ℕ) (clq nw buf : List ℕ)
    (allowed : List (List ℕ)) (proved : List (List (ℕ × ℕ) × ℕ)) : Bool :=
  let hm := hotMask a b
  let st0 := stMask a b hm 0
  let st1 := stMask a b hm 1
  let st2 := stMask a b hm 2
  let st3 := stMask a b hm 3
  let st4 := stMask a b hm 4
  let st5 := stMask a b hm 5
  let st6 := stMask a b hm 6
  let st7 := stMask a b hm 7
  let st8 := stMask a b hm 8
  sub0 < 56 && 1 <= noneGcap && noneGcap <= 4 &&
  checkInitClq a b hm sub0 clq &&
  checkCap1Mask a b hm sub0 cap1Mask &&
  checkNoneWit a b hm noneGcap nw &&
  match initApply st0 st1 st2 st3 st4 st5 st6 st7 st8 clq with
  | none => true
  | some (L, vms) =>
    match checkTree hm st0 st1 st2 st3 st4 st5 st6 st7 st8 cap1Mask noneGcap allowed proved 12 L vms clq.length buf with
    | some [] => true
    | _ => false

theorem checkSpecialSplit_sound {a b sub0 cap1Mask noneGcap : ℕ} (ha : a < 512) (hb : b < 512)
    (clq nw buf : List ℕ) (allowed : List (List ℕ)) (proved : List (List (ℕ × ℕ) × ℕ))
    (hallow : ∀ lf ∈ allowed, lf.length = 9 ∧ ∀ w ∈ lf, w < 256)
    (hchk : checkSpecialSplit a b sub0 cap1Mask noneGcap clq nw buf allowed proved = true)
    (hproved : ∀ p ∈ proved,
      (∀ v : V, bitOn cap1Mask v.val = true → Strong (decode a) (decode b) v) →
      (∀ pos : X → Finset Slot, Cap (decode a) (decode b) pos → ((pos none).image Prod.fst).card ≤ noneGcap) →
      ∀ pos : X → Finset Slot, Cover (decode a) (decode b) pos → Cap (decode a) (decode b) pos →
        MatchesL pos p.1 →
        ∃ (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Bool),
          ∃ lf ∈ allowed, ∀ v : V, (pos (some v)).image (symSlot σ f) = slots (lf.getD v.val 256))
    (pos : X → Finset Slot) (hcov : Cover (decode a) (decode b) pos) (hcap : Cap (decode a) (decode b) pos) :
    ∃ (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Bool),
      ∃ lf ∈ allowed, ∀ v : V, (pos (some v)).image (symSlot σ f) = slots (lf.getD v.val 256) := by
  unfold checkSpecialSplit at hchk
  dsimp only at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨hsub, hng1⟩, hng4⟩, hclq_ok⟩, hcap1_ok⟩, hnw_ok⟩, htree_ok⟩ := hchk
  obtain ⟨hclq_len, hclq_lt, hclq⟩ := checkInitClq_sound ha hb hsub clq hclq_ok
  obtain ⟨σ0, f0, hcov0, hcap0, hinit0⟩ := normalize_places_sym hclq_len hcov hcap hclq
  let pos0 : X → Finset Slot := fun z => (pos z).image (symSlot σ0 f0)
  obtain ⟨L, vms, hinit_eq, hB, hmi, hL, hvm⟩ :=
    initApply_sound ha hb clq hclq_len hclq_lt hcov0 hinit0
  rw [hinit_eq] at htree_ok
  dsimp only at htree_ok
  have hcap1 := checkCap1Mask_sound ha hb hsub hcap1_ok
  have hng := checkNoneWit_sound ha hb hng1 hng4 nw hnw_ok
  cases hct : checkTree (hotMask a b) (stMask a b (hotMask a b) 0) (stMask a b (hotMask a b) 1)
      (stMask a b (hotMask a b) 2) (stMask a b (hotMask a b) 3) (stMask a b (hotMask a b) 4)
      (stMask a b (hotMask a b) 5) (stMask a b (hotMask a b) 6) (stMask a b (hotMask a b) 7)
      (stMask a b (hotMask a b) 8) cap1Mask noneGcap allowed proved 12 L vms clq.length buf with
  | none => rw [hct] at htree_ok; simp at htree_ok
  | some rem =>
    obtain ⟨σ1, f1, lf, hlf_mem, hlf_eq⟩ :=
      checkTree_sound ha hb hng1 hng4 allowed proved hallow hcap1 hng
        (fun p hp => hproved p hp hcap1 hng)
        12 L vms clq.length buf rem hclq_len hB hmi hct pos0 hcov0 hcap0 hL hvm
    refine ⟨σ0.trans σ1, fun g => xor (f0 g) (f1 (σ0 g)), lf, hlf_mem, fun v => ?_⟩
    rw [← image_symSlot_comp σ0 σ1 f0 f1]
    exact hlf_eq v

def checkSpecial (a b sub0 cap1Mask noneGcap : ℕ) (clq nw buf : List ℕ) (allowed : List (List ℕ)) : Bool :=
  checkSpecialSplit a b sub0 cap1Mask noneGcap clq nw buf allowed []

theorem checkSpecial_sound {a b sub0 cap1Mask noneGcap : ℕ} (ha : a < 512) (hb : b < 512)
    (clq nw buf : List ℕ) (allowed : List (List ℕ))
    (hallow : ∀ lf ∈ allowed, lf.length = 9 ∧ ∀ w ∈ lf, w < 256)
    (hchk : checkSpecial a b sub0 cap1Mask noneGcap clq nw buf allowed = true)
    (pos : X → Finset Slot) (hcov : Cover (decode a) (decode b) pos) (hcap : Cap (decode a) (decode b) pos) :
    ∃ (σ : Equiv.Perm (Fin 4)) (f : Fin 4 → Bool),
      ∃ lf ∈ allowed, ∀ v : V, (pos (some v)).image (symSlot σ f) = slots (lf.getD v.val 256) :=
  checkSpecialSplit_sound ha hb clq nw buf allowed [] hallow hchk (by simp) pos hcov hcap

def wits_0 : List ℕ := [414769, 0, 344865, 484673, 0, 414753, 414753, 0, 414497, 414769, 0, 0, 0, 414497, 414753, 484657, 0, 484673, 344865, 344865, 414753, 344865, 414497, 0, 344865, 0, 414753, 344865, 0, 0, 344865, 414497, 0, 344865, 414769, 414769, 0, 0, 410401, 410401, 545842, 344865, 0, 545842, 344865, 0, 484673, 0, 0, 27742736, 550177, 414753, 27743009, 545825, 27742736, 0, 414753, 344865, 484675, 414769, 0, 344865, 484385, 410401, 0, 344865, 414497, 545842, 545569, 344865, 549937, 414769, 545840, 344865, 484129, 410401, 0, 344865, 414753, 545842, 0, 4674337, 344865, 414753, 0, 549937, 0, 4674576, 0, 484673, 4674610, 414770, 414770, 4670241, 410401, 274960, 4539169, 344865, 414753, 4539169, 344865, 414753, 4539169, 344865, 545825, 4539169, 344865, 414753, 344865, 414768, 414769, 0, 344865, 410401, 344865, 0, 344865, 344865, 344865, 545842, 344865, 344865, 344865, 480305, 484401, 484673, 480305, 0, 344865, 414497, 414753, 344865, 484385, 344865, 0, 414753, 344865, 344865, 414753, 414769, 545841, 0, 484401, 484401, 484673, 414770, 414770, 414770, 344865, 344865, 410401, 344865, 410401, 414753, 410401, 344865, 414753, 344865, 344865, 484385, 410401, 410401, 414753, 11874832, 344865, 0, 414769, 549937, 11879201, 344865, 11944737, 344865, 410401, 344865, 344865, 484401, 414769, 484401, 344865, 344865, 410401, 344865, 410401, 344865, 344865, 414769, 344865, 0, 414770, 21451553, 344865, 414753, 21386017, 344865, 344865, 21456144, 414769, 484673, 0, 0, 0, 21386017, 344865, 414497, 0, 414769, 0, 21386017, 414497, 414753, 21386017, 414497, 414753, 21386017, 414497, 414753, 484675, 414769, 484675, 414497, 414497, 414770, 5517840, 344865, 0, 414769, 0, 0, 414769, 5657377, 344865, 414497, 5587745, 344865, 5657377, 344865, 414497, 414753, 344865, 414753, 414736, 414769, 550209, 484673, 414769, 484673, 0, 414770, 0, 344865, 344865, 344865, 414753, 344865, 414753, 414753, 344865, 414753, 414753, 344865, 414753, 414753, 344865, 414753, 344865, 414768, 414769, 414768, 344865, 414769, 344865, 414769, 414770, 344865, 414770, 344865]
def specs_0 : List ℕ := [1029, 522, 3081, 1548, 1037, 526, 4626, 5141, 4630, 1560, 538, 3097, 1053, 542, 1572, 4642, 6178, 6179, 4646, 1065, 3113, 3121, 566, 5168, 5169, 4658, 1081, 3129, 6211, 4678, 5201, 24650, 1636, 6240, 6752, 6241, 6242, 6243, 12386, 12387, 14434, 6256, 6257]
set_option maxRecDepth 20000 in
theorem chunk_ok_0 : checkChunk 0 2187 wits_0 specs_0 = true := by decide +kernel

def wits_1 : List ℕ := []
def specs_1 : List ℕ := []
set_option maxRecDepth 20000 in
theorem chunk_ok_1 : checkChunk 2187 2187 wits_1 specs_1 = true := by decide +kernel

def wits_2 : List ℕ := [344865, 344865, 344865, 475936, 475937, 344865, 344865, 0, 344865, 0, 475936, 0, 550193, 554577, 2642704, 550193, 0, 0, 484624, 2642721, 344865, 414497, 2642721, 344865, 0, 2577185, 0, 484641, 2651425, 484641, 414753, 2577185, 414497, 475664, 2651425, 0, 414753, 344865, 484675, 414769, 0, 475937, 344865, 344865, 475920, 344865, 410401, 344865, 475936, 475937, 344865, 344865, 344865, 344865, 344865, 475937, 0, 0, 484657, 344865, 344865, 344865, 344865, 344865, 475937, 344865, 0, 344865, 344865, 344865, 344865, 344865, 344865, 475937, 344865, 0, 414497, 344865, 344865, 344865, 475936, 475937, 344865, 344865, 0, 414753, 344865, 414753, 475936, 0, 480033, 344865, 414753, 545569, 344865, 0, 480272, 0, 484673, 344865, 344865, 344865, 344865, 344865, 274960, 344865, 475937, 414753, 475937, 344865, 414753, 344865, 344865, 475664, 475937, 475937, 414753, 344865, 484675, 414769, 0, 475937, 344865, 344865, 475920, 344865, 410401, 344865, 475936, 475937, 0, 554288, 2642704, 550193, 0, 0, 0, 484112, 2642721, 344865, 480033, 2651441, 414497, 344865, 2650640, 0, 410401, 545842, 545842, 480306, 344865, 344865, 344865, 541473, 475937, 344865, 344865, 344865, 480289, 480306, 0, 480032, 344865, 414753, 344865, 475937, 475664, 410401, 545842, 545842, 480306, 344865, 344865, 344865, 0, 0, 414769, 545842, 545842, 480306, 344865, 344865, 344865, 545569, 344865, 344865, 0, 0, 480306, 344865, 344865, 344865, 475937, 475937, 344865, 4674610, 480306, 480306, 4539152, 414769, 480305, 4665872, 475937, 410401, 4539169, 344865, 344865, 4674336, 480306, 480032, 4539169, 344865, 344865, 4665872, 475937, 410401, 480306, 480306, 480306, 545569, 344865, 344865, 475920, 480305, 484401, 480033, 344865, 344865, 480288, 480306, 480288, 344865, 344865, 344865, 475937, 344865, 410401, 414753, 344865, 484673, 414753, 484641, 414770, 484657, 554577, 0, 550193, 554577, 0, 484624, 0, 414770, 0, 47526416, 344865, 414497, 0, 344865, 484641, 47665680, 484641, 414753, 47665952, 414497, 414753, 47665680, 0, 414753, 344865, 484675, 414769, 484675, 344865, 414769, 344865, 414769, 414770, 344865, 414770, 344865, 5587745, 344865, 344865, 5587745, 344865, 344865, 0, 0, 484657, 0, 414770, 414770, 5587745, 344865, 344865, 5722913, 344865, 344865, 5722913, 344865, 414497, 5587745, 344865, 344865, 5722913, 344865, 414497, 344865, 414753, 344865, 484673, 344865, 344865, 344865, 484674, 414753, 414753, 414753, 414770, 414753, 5723169, 344865, 414753, 5722640, 344865, 414753, 5723152, 480305, 484673, 0, 414770, 484674, 5722913, 344865, 344865, 5723185, 344865, 414753, 5723169, 344865, 414753, 5723169, 344865, 414753, 5723169, 344865, 414753, 344865, 484675, 414769, 484675, 344865, 414769, 344865, 414769, 344865, 414770, 344865, 414770, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 414769, 414769, 414769, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 484402, 344865, 484641, 484402, 1602865, 484657, 554577, 1533233, 550193, 0, 1533200, 0, 484624, 1594145, 344865, 414497, 1463073, 344865, 484129, 1528609, 410401, 484641, 1532705, 414497, 414753, 1463073, 414497, 484385, 1532705, 484129, 414753, 484401, 414769, 484400, 410401, 344865, 484402, 5784353, 344865, 344865, 5653281, 344865, 410401, 0, 0, 484657, 5718817, 344865, 344865, 5653281, 344865, 410401, 5718817, 410401, 344865, 5653281, 344865, 344865, 5653281, 344865, 410401, 5653281, 410401, 414497, 344865, 344865, 344865, 484402, 410401, 344865, 344865, 0, 344865, 414753, 484402, 484385, 344865, 344865, 414753, 344865, 344865, 484385, 484401, 484401, 484673, 344865, 344865, 344865, 344865, 344865, 410401, 344865, 410401, 414753, 410401, 344865, 414753, 344865, 344865, 484385, 410401, 410401, 414753, 344865, 484401, 414769, 484400, 410401, 344865, 344865, 484401, 344865, 410401, 344865, 484402, 410401, 1602865, 550193, 484657, 1463073, 414497, 344865, 12080161, 344865, 344865, 11949089, 344865, 344865, 11949089, 344865, 344865, 11949089, 344865, 414753, 12014624, 480288, 484402, 11949089, 414753, 344865, 11949089, 414753, 410401, 344865, 344865, 344865, 344865, 344865, 344865, 414769, 414769, 414769, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 414770, 414770, 414770, 344865, 344865, 344865, 344865, 344865, 344865, 11879201, 344865, 344865, 11949105, 414769, 414769, 11944737, 344865, 410401, 11879201, 344865, 344865, 12010272, 414770, 484402, 11879201, 344865, 344865, 11944737, 344865, 410401, 344865, 344865, 344865, 344865, 344865, 344865, 484401, 414769, 484401, 344865, 344865, 344865, 344865, 344865, 344865, 410401, 344865, 410401, 414753, 344865, 484673, 414753, 484641, 414770, 24601872, 484657, 554577, 24601904, 484657, 554577, 24601872, 484657, 484624, 0, 414770, 0, 24531745, 344865, 414497, 24597264, 344865, 484641, 24601889, 414497, 414753, 24601889, 414497, 414753, 24601889, 414497, 414753, 484675, 414769, 484675, 414770, 344865, 414770, 5587745, 344865, 344865, 5587745, 344865, 344865, 5722896, 414769, 484657, 5723186, 414770, 414770, 5587745, 344865, 344865, 5587745, 344865, 344865, 5657377, 344865, 414497, 5587745, 344865, 344865, 5657377, 344865, 414497, 414753, 344865, 484673, 414753, 414753, 414770, 414753, 344865, 414753, 414753, 344865, 414753, 484673, 414769, 484673, 484674, 414770, 484674, 344865, 344865, 344865, 414753, 344865, 414753, 414753, 344865, 414753, 414753, 344865, 414753, 414753, 344865, 414753, 344865, 484675, 414769, 484675, 344865, 414769, 344865, 414769, 414770, 344865, 414770, 344865]
def specs_2 : List ℕ := [3201, 1668, 646, 5249, 4738, 7297, 6786, 4742, 1161, 12418, 12930, 14978, 12934, 3217, 662, 5265, 4754, 1177, 21120, 21633, 20610, 21122, 21126, 25220, 28802, 29314, 28804, 29316, 5280, 4770, 6304, 6305, 6306, 4774, 12450, 12962, 14496, 6320, 5313, 4802, 12482, 12994, 3281, 6368, 6369]
set_option maxRecDepth 20000 in
theorem chunk_ok_2 : checkChunk 4374 2187 wits_2 specs_2 = true := by decide +kernel

def wits_3 : List ℕ := []
def specs_3 : List ℕ := []
set_option maxRecDepth 20000 in
theorem chunk_ok_3 : checkChunk 6561 2187 wits_3 specs_3 = true := by decide +kernel

def wits_4 : List ℕ := []
def specs_4 : List ℕ := []
set_option maxRecDepth 20000 in
theorem chunk_ok_4 : checkChunk 8748 2187 wits_4 specs_4 = true := by decide +kernel

def wits_5 : List ℕ := []
def specs_5 : List ℕ := []
set_option maxRecDepth 20000 in
theorem chunk_ok_5 : checkChunk 10935 2187 wits_5 specs_5 = true := by decide +kernel

def wits_6 : List ℕ := [344865, 344865, 344865, 344865, 344865, 541473, 344865, 541473, 414753, 344865, 344865, 414497, 344865, 344865, 0, 344865, 0, 550177, 344865, 414497, 414753, 344865, 414497, 541200, 344865, 0, 414753, 344865, 344865, 414753, 414769, 414769, 0, 344865, 541473, 414753, 344865, 344865, 344865, 344865, 344865, 541473, 344865, 541473, 414753, 344865, 344865, 414753, 344865, 344865, 541200, 344865, 541473, 414753, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 545569, 344865, 414497, 344865, 344865, 545569, 410401, 484673, 484673, 0, 414753, 414753, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 414769, 344848, 414769, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 4674337, 344865, 344865, 4539169, 344865, 344865, 344865, 344865, 344865, 414769, 414769, 545841, 344865, 344865, 410401, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 410401, 27817249, 344865, 344865, 27743009, 344865, 344865, 27817249, 344865, 414753, 27743009, 344865, 414497, 27743009, 344865, 545569, 27743009, 344865, 550177, 27808545, 414497, 414753, 27743009, 414497, 545825, 27808545, 0, 414753, 4539169, 344865, 414753, 4740145, 414769, 545808, 4539169, 344865, 414753, 4539169, 344865, 344865, 4539169, 344865, 344865, 4539169, 344865, 414753, 4539169, 344865, 414753, 4539169, 344865, 545825, 4539169, 344865, 414753, 344865, 344865, 414753, 344865, 344865, 344865, 414497, 344865, 414753, 414770, 414770, 0, 344865, 344865, 414497, 344865, 344865, 550177, 414497, 414497, 414753, 344865, 414497, 414753, 414497, 414497, 414753, 414753, 344865, 414753, 550209, 414769, 550209, 414753, 344865, 414753, 550210, 414770, 550210, 344865, 344865, 344865, 414753, 344865, 414753, 414753, 344865, 414753, 414753, 344865, 414753, 414753, 344865, 414753, 344865, 344865, 344865, 344865, 414497, 344865, 12997648, 484673, 484673, 12997665, 414753, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 414769, 414769, 414769, 414770, 414770, 414770, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 12997409, 344865, 344865, 12927777, 344865, 344865, 344865, 344865, 344865, 414769, 414769, 414769, 410401, 344865, 410401, 344865, 344865, 344865, 344865, 344865, 344865, 410401, 344865, 410401, 21386017, 344865, 414753, 21386017, 344865, 344865, 21386017, 344865, 414753, 21521714, 414770, 0, 21386017, 344865, 414497, 21386017, 344865, 550177, 21386017, 414497, 414753, 21386017, 414497, 414753, 21386017, 414497, 414753, 414753, 344865, 414753, 550209, 414769, 550209, 414753, 344865, 414753, 550210, 414770, 550210, 344865, 344865, 344865, 414753, 344865, 414753, 414753, 344865, 414753, 414753, 344865, 414753, 414753, 344865, 414753]
def specs_6 : List ℕ := [7425, 6914, 4870, 5393, 25857, 4902, 6465, 6497]
set_option maxRecDepth 20000 in
theorem chunk_ok_6 : checkChunk 13122 2187 wits_6 specs_6 = true := by decide +kernel

def wits_7 : List ℕ := [484675, 344865, 541473, 344865, 344865, 541473, 344865, 0, 344865, 554579, 550192, 0, 484657, 0, 2642704, 0, 550193, 2577185, 344865, 553761, 2642721, 414497, 344865, 2577185, 414497, 541473, 2642721, 553761, 344865, 0, 484675, 0, 541456, 414769, 475937, 344865, 344865, 475937, 344865, 475937, 475937, 475937, 344865, 550211, 484675, 550211, 344865, 344865, 274960, 344865, 475937, 344865, 344865, 344865, 475937, 344865, 344865, 344865, 344865, 344865, 541473, 344865, 475937, 344865, 484675, 484675, 344865, 475937, 344865, 344865, 344865, 344865, 344865, 344865, 475937, 344865, 475937, 344865, 545840, 484675, 550211, 344848, 414769, 0, 344865, 475937, 344865, 344865, 344865, 475937, 344865, 344865, 344865, 344865, 344865, 541473, 344865, 475937, 344865, 2577185, 344865, 344865, 2577185, 484641, 344865, 0, 0, 554304, 27743009, 344865, 344865, 27808272, 344865, 344865, 0, 480306, 554290, 27743009, 344865, 480033, 27742736, 344865, 414497, 27817248, 480306, 545842, 27743009, 344865, 344865, 27808545, 344865, 344865, 0, 0, 0, 484657, 0, 2642704, 0, 550193, 2650640, 344865, 480033, 2651442, 414497, 344865, 2642721, 480033, 344865, 0, 0, 0, 554304, 550209, 554017, 414753, 554306, 554306, 545842, 480289, 344865, 480289, 480289, 344865, 0, 554307, 554288, 480305, 414769, 480305, 545552, 545841, 414769, 480306, 480306, 480306, 344865, 344865, 344865, 344865, 344865, 344865, 554290, 480306, 545842, 344865, 344865, 344865, 480033, 344865, 344865, 545840, 554307, 545840, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 545842, 480306, 545842, 344865, 344865, 344865, 344865, 344865, 344865, 4748608, 554307, 545840, 4539169, 344865, 344865, 4539169, 344865, 344865, 4674610, 480306, 480306, 4539169, 344865, 344865, 4539169, 344865, 344865, 4740146, 480306, 545842, 4539169, 344865, 344865, 4539169, 344865, 344865, 545840, 554307, 545840, 545552, 414769, 545841, 344865, 344865, 344865, 344865, 344865, 344865, 545842, 480306, 545842, 545569, 344865, 344865, 344865, 344865, 344865, 484675, 484675, 414769, 414769, 414769, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 484641, 344865, 484675, 550211, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 1533233, 484657, 550193, 1463073, 414497, 344865, 0, 484675, 554579, 7894577, 414769, 414769, 7889680, 484401, 414769, 7750433, 344865, 344865, 7750433, 344865, 344865, 7750433, 410401, 344865, 7750433, 344865, 344865, 7750433, 344865, 344865, 7750433, 410401, 344865, 550211, 484675, 550211, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 550211, 484675, 550211, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 550211, 484675, 550211, 414769, 414769, 414769, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 11040339, 484675, 10970417, 414769, 414769, 10830625, 344865, 344865, 10830625, 344865, 344865, 10830625, 344865, 344865, 484675, 484675, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 1463073, 344865, 344865, 1463073, 484641, 344865, 21526096, 484675, 550211, 21386017, 344865, 344865, 21386017, 344865, 344865, 21456178, 414770, 484658, 21386017, 344865, 414497, 21386017, 344865, 414497, 21386017, 344865, 344865, 21386017, 344865, 344865, 21386017, 344865, 344865, 1603155, 484657, 550193, 1463073, 414497, 344865, 0, 554580, 0, 15164737, 484673, 484673, 15229968, 484673, 550209, 0, 414770, 484674, 15094817, 344865, 414753, 15164449, 344865, 414753, 15094817, 414753, 344865, 15094817, 414753, 344865, 15094817, 414753, 344865, 4748867, 484675, 4678705, 414769, 414769, 4604705, 344865, 4539169, 344865, 344865, 4539169, 344865, 4539169, 344865, 344865, 1594416, 484675, 554579, 1463345, 414769, 414769, 1463345, 414769, 414769, 1463346, 414770, 414770, 1393441, 344865, 344865, 1393441, 344865, 344865, 1393441, 344865, 344865, 1393441, 344865, 344865, 1393441, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 550211, 484675, 550211, 344865, 344865, 344865, 344865, 344865, 344865, 414770, 414770, 414770, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 550211, 484675, 550211, 414769, 414769, 414769, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865]
def specs_7 : List ℕ := [66310, 66824, 66825, 66314, 73992, 73994, 66841, 69920, 70432, 71968, 66344, 65833, 66856, 66857, 66346, 74016, 74017, 74018, 74024, 74056, 74080, 74081, 76128]
set_option maxRecDepth 20000 in
theorem chunk_ok_7 : checkChunk 15309 2187 wits_7 specs_7 = true := by decide +kernel

def wits_8 : List ℕ := [344865, 344865, 344865, 554034, 475937, 344865, 344865, 0, 344865, 484641, 554034, 0, 2651408, 484657, 554577, 2651441, 484657, 0, 2651408, 0, 554577, 2577185, 344865, 414497, 2577185, 344865, 553761, 2577185, 475937, 484641, 2650913, 414497, 414753, 2577185, 414497, 554017, 2650913, 553761, 414753, 344865, 410401, 344865, 554034, 475937, 344865, 344865, 554033, 344865, 410401, 344865, 554034, 475937, 274960, 344865, 344865, 475937, 344865, 475937, 0, 554033, 484657, 475937, 344865, 344865, 475937, 344865, 475937, 475937, 475937, 344865, 475937, 344865, 344865, 475937, 344865, 475937, 475937, 475937, 414497, 475937, 344865, 414753, 344865, 344865, 554017, 475937, 475937, 414753, 344865, 344865, 344865, 344865, 344865, 475937, 344865, 475937, 414753, 475937, 344865, 414753, 344865, 344865, 554017, 475937, 475937, 414753, 344865, 475937, 344865, 554034, 475937, 344865, 344865, 554033, 344865, 475937, 344865, 554034, 475937, 0, 0, 0, 2577168, 484657, 554289, 2650896, 554289, 554545, 2577185, 344865, 480033, 2577185, 414497, 344865, 2650913, 480033, 410401, 0, 0, 0, 554305, 484673, 554305, 545808, 554305, 554561, 480289, 344865, 480289, 480289, 414753, 344865, 480289, 480289, 410401, 344864, 480306, 480306, 344865, 344865, 344865, 545841, 480305, 414769, 480306, 480306, 480306, 344865, 344865, 344865, 344865, 344865, 344865, 480306, 480306, 480306, 344865, 344865, 344865, 344865, 344865, 344865, 4670240, 480306, 554034, 4539169, 344865, 344865, 4670241, 344865, 410401, 4539169, 344865, 344865, 4670240, 480306, 554034, 4539169, 344865, 344865, 4670241, 344865, 410401, 554034, 480306, 554034, 344865, 344865, 344865, 475937, 344865, 410401, 344865, 344865, 344865, 554034, 480306, 554034, 344865, 344865, 344865, 475937, 344865, 410401, 414753, 344865, 554577, 414753, 484641, 414770, 35157264, 484657, 554577, 35157296, 484657, 554577, 35157264, 554289, 554577, 35157297, 344865, 484641, 35083041, 344865, 414497, 35157297, 344865, 484641, 35157281, 414497, 414753, 35157281, 414497, 414753, 35157281, 480033, 414753, 344865, 414770, 344865, 414770, 344865, 414769, 344865, 414769, 414770, 344865, 414770, 344865, 5722913, 344865, 414497, 5587745, 344865, 344865, 5722896, 480305, 484657, 5587745, 344865, 344865, 5587745, 344865, 344865, 5587745, 344865, 344865, 5722913, 344865, 414497, 5587745, 344865, 344865, 5722913, 344865, 414497, 344865, 480289, 344865, 414770, 344865, 344865, 344865, 414769, 480289, 344865, 414770, 344865, 5723169, 344865, 414753, 5723169, 344865, 414753, 5723169, 344865, 414753, 5723169, 344865, 414753, 5587745, 344865, 344865, 5723169, 344865, 414753, 5723169, 344865, 414753, 5723169, 344865, 414753, 5723169, 344865, 414753, 344865, 414770, 344865, 414770, 344865, 414769, 344865, 414769, 344865, 414770, 344865, 414770, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 414769, 414769, 414769, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 1603121, 484657, 554577, 1533233, 484657, 554577, 1603121, 484657, 554577, 1463073, 344865, 484641, 1463073, 344865, 414497, 1463073, 344865, 484641, 1532705, 414497, 414753, 1463073, 414497, 414753, 1532705, 414497, 414753, 414753, 344865, 414753, 414753, 344865, 414753, 414753, 344865, 414753, 414753, 344865, 414753, 344865, 344865, 344865, 414753, 344865, 414753, 414753, 344865, 414753, 414753, 344865, 414753, 414753, 344865, 414753, 1533233, 484657, 484657, 1463073, 414497, 344865, 13067585, 484673, 484673, 12997665, 414753, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 414769, 414769, 414769, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 344865, 12993313, 344865, 410401, 12927777, 344865, 344865, 12993313, 344865, 410401, 12927777, 344865, 344865, 12927777, 344865, 344865, 12993313, 344865, 410401, 410401, 344865, 410401, 344865, 344865, 344865, 410401, 344865, 410401, 344865, 344865, 344865, 344865, 344865, 344865, 410401, 344865, 410401, 484641, 344865, 554577, 484641, 484641, 414770, 24671825, 484657, 554577, 24671825, 484657, 554577, 24671825, 484657, 554577, 24601889, 344865, 484641, 24531745, 344865, 414497, 24601889, 344865, 484641, 24601889, 414497, 414753, 24601889, 414497, 414753, 24601889, 414497, 414753, 414770, 344865, 414770, 414770, 344865, 414770, 5657377, 344865, 414497, 5587745, 344865, 344865, 5727537, 414769, 484657, 5587745, 344865, 344865, 5587745, 344865, 344865, 5587745, 344865, 344865, 5657377, 344865, 414497, 5587745, 344865, 344865, 5657377, 344865, 414497, 414753, 344865, 414753, 414753, 344865, 414753, 414753, 344865, 414753, 414753, 344865, 414753, 344865, 344865, 344865, 414753, 344865, 414753, 414753, 344865, 414753, 414753, 344865, 414753, 414753, 344865, 414753, 344865, 414770, 344865, 414770, 344865, 414769, 344865, 414769, 414770, 344865, 414770, 344865]
def specs_8 : List ℕ := [3457, 902, 5505, 4994, 12674, 20864, 21376, 20865, 24960, 25472, 24961]
set_option maxRecDepth 20000 in
theorem chunk_ok_8 : checkChunk 17496 2187 wits_8 specs_8 = true := by decide +kernel

set_option maxRecDepth 20000 in
theorem split_0_sub_0 : checkSub 9 130 139 3 2 [(5, 4), (7, 2), (3, 1)] [8, 6, 2, 2, 2, 6, 2, 2, 2, 2, 4, 6, 4, 1, 4, 9, 4, 6, 4, 1, 4, 9, 4] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_1 : checkSub 9 130 139 3 3 [(6, 8), (5, 20), (7, 2), (3, 1)] [8, 2, 2, 2] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_2 : checkSub 9 130 139 3 3 [(6, 24), (5, 20), (7, 2), (3, 1)] [8, 0, 4, 2, 4, 2, 0, 1, 4, 2, 4, 0, 1, 2, 9, 9, 0, 1, 4, 9] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_3 : checkSub 9 130 139 3 3 [(6, 32), (5, 20), (7, 2), (3, 1)] [8, 2, 2, 2] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_4 : checkSub 9 130 139 3 3 [(6, 36), (5, 20), (7, 2), (3, 1)] [8, 0, 4, 2, 4, 2, 0, 1, 4, 2, 0, 1, 4, 9, 4, 0, 1, 2, 9, 9] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_5 : checkSub 9 130 139 3 3 [(6, 40), (5, 20), (7, 2), (3, 1)] [8, 2, 2, 2, 2, 2] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_6 : checkSub 9 130 139 3 4 [(6, 64), (5, 20), (7, 2), (3, 1)] [8, 2, 0, 1, 4, 2, 2, 0, 1, 4, 2, 2, 2, 2] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_7 : checkSub 9 130 139 3 4 [(6, 68), (5, 20), (7, 2), (3, 1)] [8, 2, 4, 0, 1, 2, 9, 9, 4, 4, 2, 0, 1, 4, 9, 2] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_8 : checkSub 9 130 139 3 4 [(6, 72), (5, 20), (7, 2), (3, 1)] [8, 2, 0, 1, 4, 2, 9, 9, 2, 0, 1, 2, 4, 9, 2, 0, 4, 2, 1, 4, 9, 0, 1, 2, 9, 0, 1, 2, 9, 9, 2, 4, 4] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_9 : checkSub 9 130 139 3 4 [(6, 80), (5, 20), (7, 2), (3, 1)] [8, 2, 4, 0, 1, 2, 9, 9, 4, 0, 1, 4, 9, 2, 4, 2] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_10 : checkSub 9 130 139 3 4 [(6, 96), (5, 20), (7, 2), (3, 1)] [8, 2, 0, 1, 4, 2, 9, 9, 2, 0, 1, 2, 9, 4, 2, 0, 1, 2, 9, 9, 2, 4, 4, 0, 4, 2, 1, 4, 9, 0, 1, 2, 9] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_11 : checkSub 9 130 139 3 2 [(8, 10), (7, 4), (3, 1)] [5, 6, 2, 2, 6, 2, 0, 4, 2, 2, 0, 4, 2, 2] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_12 : checkSub 9 130 139 3 3 [(8, 16), (7, 4), (3, 1)] [6, 5, 2, 2, 5, 2, 4, 4, 2, 2, 1, 4, 4, 5, 4, 2, 2, 1, 4, 5] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_13 : checkSub 9 130 139 3 3 [(8, 18), (7, 4), (3, 1)] [6, 5, 2, 2, 5, 4, 2, 1, 5, 4, 5, 4, 0, 4, 0] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_14 : checkSub 9 130 139 3 3 [(8, 24), (7, 4), (3, 1)] [6, 5, 2, 4, 0, 5, 2, 1, 2, 2, 4, 9, 0, 5, 2, 0, 2, 1, 2, 1, 2, 4, 4, 5, 2, 1, 4, 0, 5, 1, 0, 4, 1, 5, 5, 2, 5, 2, 1, 4, 0, 5, 9, 9, 5, 9, 5, 1, 4, 5, 9, 0, 5, 5, 1, 5, 0, 5] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_15 : checkSub 9 130 139 3 4 [(6, 10), (8, 80), (7, 4), (3, 1)] [5, 2, 1, 2, 4, 2, 1, 2, 4, 2] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_16 : checkSub 9 130 139 3 4 [(6, 32), (8, 80), (7, 4), (3, 1)] [5, 4, 0, 2] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_17 : checkSub 9 130 139 3 4 [(6, 34), (8, 80), (7, 4), (3, 1)] [5, 1, 2, 4, 0, 2, 0, 9, 9, 2, 1, 1] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_18 : checkSub 9 130 139 3 4 [(6, 40), (8, 80), (7, 4), (3, 1)] [5, 2, 1, 4, 2, 4, 2, 2] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_19 : checkSub 9 130 139 3 4 [(6, 96), (8, 80), (7, 4), (3, 1)] [2, 1, 5, 5, 5, 0, 9, 9] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_20 : checkSub 9 130 139 3 4 [(6, 128), (8, 80), (7, 4), (3, 1)] [5, 4, 0, 2] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_21 : checkSub 9 130 139 3 4 [(6, 130), (8, 80), (7, 4), (3, 1)] [5, 1, 2, 4, 0, 2, 0, 9, 9, 2, 1, 1] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_22 : checkSub 9 130 139 3 4 [(6, 136), (8, 80), (7, 4), (3, 1)] [5, 4, 2, 4, 2, 2, 1, 2] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_23 : checkSub 9 130 139 3 4 [(6, 144), (8, 80), (7, 4), (3, 1)] [2, 1, 5, 5, 5, 0, 9, 9] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_0_sub_24 : checkSub 9 130 139 3 4 [(6, 160), (8, 80), (7, 4), (3, 1)] [4, 2, 5, 5, 2, 2, 5, 2, 1, 0, 9, 9, 5, 2, 1, 0, 9, 9] [] = true := by decide +kernel
def split_0_proved : List (List (ℕ × ℕ) × ℕ) := [([(5, 4), (7, 2), (3, 1)], 2), ([(6, 8), (5, 20), (7, 2), (3, 1)], 3), ([(6, 24), (5, 20), (7, 2), (3, 1)], 3), ([(6, 32), (5, 20), (7, 2), (3, 1)], 3), ([(6, 36), (5, 20), (7, 2), (3, 1)], 3), ([(6, 40), (5, 20), (7, 2), (3, 1)], 3), ([(6, 64), (5, 20), (7, 2), (3, 1)], 4), ([(6, 68), (5, 20), (7, 2), (3, 1)], 4), ([(6, 72), (5, 20), (7, 2), (3, 1)], 4), ([(6, 80), (5, 20), (7, 2), (3, 1)], 4), ([(6, 96), (5, 20), (7, 2), (3, 1)], 4), ([(8, 10), (7, 4), (3, 1)], 2), ([(8, 16), (7, 4), (3, 1)], 3), ([(8, 18), (7, 4), (3, 1)], 3), ([(8, 24), (7, 4), (3, 1)], 3), ([(6, 10), (8, 80), (7, 4), (3, 1)], 4), ([(6, 32), (8, 80), (7, 4), (3, 1)], 4), ([(6, 34), (8, 80), (7, 4), (3, 1)], 4), ([(6, 40), (8, 80), (7, 4), (3, 1)], 4), ([(6, 96), (8, 80), (7, 4), (3, 1)], 4), ([(6, 128), (8, 80), (7, 4), (3, 1)], 4), ([(6, 130), (8, 80), (7, 4), (3, 1)], 4), ([(6, 136), (8, 80), (7, 4), (3, 1)], 4), ([(6, 144), (8, 80), (7, 4), (3, 1)], 4), ([(6, 160), (8, 80), (7, 4), (3, 1)], 4)]
set_option maxRecDepth 20000 in
theorem split_0_skel : checkSpecialSplit 9 130 0 139 3 [3] [7, 9] [7, 5, 11, 6, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 8, 11, 11, 11, 11, 6, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11] [] split_0_proved = true := by decide +kernel
theorem not_bad_split_0 : ¬ Bad (decode 9) (decode 130) := by
  apply not_bad_of_empty_allowed
  apply checkSpecialSplit_sound (by decide) (by decide) _ _ _ [] split_0_proved (by simp) split_0_skel
  intro p hp hcap1 hng pos hcov hcap hL
  simp only [split_0_proved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_0 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_1 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_2 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_3 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_4 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_5 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_6 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_7 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_8 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_9 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_10 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_11 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_12 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_13 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_14 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_15 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_16 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_17 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_18 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_19 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_20 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_21 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_22 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_23 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_0_sub_24 pos hcov hcap hL

set_option maxRecDepth 20000 in
theorem split_1_sub_0 : checkSub 6 9 15 3 2 [(8, 4), (3, 2), (0, 1)] [5, 4, 6, 7, 6, 4, 6, 7, 7, 4, 6, 6, 7, 4, 6, 7, 6, 7, 6, 7, 6, 7, 6] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_1 : checkSub 6 9 15 3 3 [(4, 8), (8, 20), (3, 2), (0, 1)] [7, 5, 5, 5, 5] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_2 : checkSub 6 9 15 3 3 [(4, 24), (8, 20), (3, 2), (0, 1)] [5, 2, 7, 9, 7, 6, 2, 1, 10, 9, 1, 9, 2, 7, 9] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_3 : checkSub 6 9 15 3 3 [(4, 32), (8, 20), (3, 2), (0, 1)] [7, 5, 5, 5, 5] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_4 : checkSub 6 9 15 3 3 [(4, 36), (8, 20), (3, 2), (0, 1)] [5, 2, 7, 9, 7, 6, 2, 1, 10, 9, 1, 9, 2, 7, 9] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_5 : checkSub 6 9 15 3 3 [(4, 40), (8, 20), (3, 2), (0, 1)] [5, 2, 1, 6, 7, 7, 7, 6, 6, 7, 2, 1, 6, 7, 7, 7, 6, 6, 7, 1, 7, 6, 6, 7, 6, 6, 1, 6, 7, 6, 7, 1, 6, 7, 6, 7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_6 : checkSub 6 9 15 3 4 [(4, 64), (8, 20), (3, 2), (0, 1)] [5, 6, 7, 2, 1, 6, 7, 6, 7, 2, 1, 6, 7, 6, 7, 7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_7 : checkSub 6 9 15 3 4 [(4, 68), (8, 20), (3, 2), (0, 1)] [7, 5, 1, 2, 1, 5, 6, 1, 5, 9, 5, 5] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_8 : checkSub 6 9 15 3 4 [(5, 24), (4, 72), (8, 20), (3, 2), (0, 1)] [6, 1, 2, 9, 7, 9] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_9 : checkSub 6 9 15 3 4 [(5, 32), (4, 72), (8, 20), (3, 2), (0, 1)] [7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_10 : checkSub 6 9 15 3 4 [(5, 33), (4, 72), (8, 20), (3, 2), (0, 1)] [7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_11 : checkSub 6 9 15 3 4 [(5, 36), (4, 72), (8, 20), (3, 2), (0, 1)] [2, 1, 6, 7, 9, 9, 6] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_12 : checkSub 6 9 15 3 4 [(5, 40), (4, 72), (8, 20), (3, 2), (0, 1)] [6] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_13 : checkSub 6 9 15 3 4 [(5, 68), (4, 72), (8, 20), (3, 2), (0, 1)] [6, 1, 2, 9, 7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_14 : checkSub 6 9 15 3 4 [(5, 96), (4, 72), (8, 20), (3, 2), (0, 1)] [2, 7, 9, 9, 7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_15 : checkSub 6 9 15 3 4 [(5, 128), (4, 72), (8, 20), (3, 2), (0, 1)] [7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_16 : checkSub 6 9 15 3 4 [(5, 129), (4, 72), (8, 20), (3, 2), (0, 1)] [7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_17 : checkSub 6 9 15 3 4 [(5, 132), (4, 72), (8, 20), (3, 2), (0, 1)] [6] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_18 : checkSub 6 9 15 3 4 [(5, 136), (4, 72), (8, 20), (3, 2), (0, 1)] [2, 7, 1, 6, 9, 9, 7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_19 : checkSub 6 9 15 3 4 [(5, 144), (4, 72), (8, 20), (3, 2), (0, 1)] [1, 2, 6, 7, 7, 9, 9, 7, 9, 6, 7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_20 : checkSub 6 9 15 3 4 [(5, 160), (4, 72), (8, 20), (3, 2), (0, 1)] [6, 7, 7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_21 : checkSub 6 9 15 3 4 [(4, 80), (8, 20), (3, 2), (0, 1)] [7, 5, 1, 2, 1, 5, 6, 1, 5, 9, 5, 5] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_22 : checkSub 6 9 15 3 4 [(5, 8), (4, 96), (8, 20), (3, 2), (0, 1)] [7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_23 : checkSub 6 9 15 3 4 [(5, 9), (4, 96), (8, 20), (3, 2), (0, 1)] [7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_24 : checkSub 6 9 15 3 4 [(5, 24), (4, 96), (8, 20), (3, 2), (0, 1)] [2, 1, 6, 7, 9, 9, 6] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_25 : checkSub 6 9 15 3 4 [(5, 36), (4, 96), (8, 20), (3, 2), (0, 1)] [6, 1, 2, 9, 7, 9] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_26 : checkSub 6 9 15 3 4 [(5, 40), (4, 96), (8, 20), (3, 2), (0, 1)] [6] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_27 : checkSub 6 9 15 3 4 [(5, 72), (4, 96), (8, 20), (3, 2), (0, 1)] [2, 7, 9, 9, 7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_28 : checkSub 6 9 15 3 4 [(5, 80), (4, 96), (8, 20), (3, 2), (0, 1)] [6, 1, 2, 9, 7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_29 : checkSub 6 9 15 3 4 [(5, 128), (4, 96), (8, 20), (3, 2), (0, 1)] [7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_30 : checkSub 6 9 15 3 4 [(5, 129), (4, 96), (8, 20), (3, 2), (0, 1)] [7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_31 : checkSub 6 9 15 3 4 [(5, 132), (4, 96), (8, 20), (3, 2), (0, 1)] [1, 2, 6, 7, 7, 9, 9, 7, 9, 6, 7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_32 : checkSub 6 9 15 3 4 [(5, 136), (4, 96), (8, 20), (3, 2), (0, 1)] [6, 7, 7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_33 : checkSub 6 9 15 3 4 [(5, 144), (4, 96), (8, 20), (3, 2), (0, 1)] [6] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_34 : checkSub 6 9 15 3 4 [(5, 160), (4, 96), (8, 20), (3, 2), (0, 1)] [2, 7, 9, 1, 6, 9, 7] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_35 : checkSub 6 9 15 3 2 [(4, 10), (3, 4), (0, 1)] [6, 8, 5, 5, 8, 5, 5, 8, 5, 5, 8, 5, 5, 5, 5, 2, 7, 5, 5, 7, 5, 5] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_36 : checkSub 6 9 15 3 3 [(4, 16), (3, 4), (0, 1)] [7, 8, 5, 5, 6, 5, 6, 5, 5, 6, 5, 5, 6, 5, 5, 6, 5] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_37 : checkSub 6 9 15 3 3 [(4, 18), (3, 4), (0, 1)] [7, 8, 5, 5, 8, 5, 6, 8, 5, 6, 8, 5, 5, 8, 6, 6, 8, 8, 8, 6, 8, 8, 5, 2, 1, 8, 9, 5, 6, 5, 5, 5] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_38 : checkSub 6 9 15 3 3 [(4, 24), (3, 4), (0, 1)] [8, 7, 5, 5, 6, 1, 7, 5, 7, 6, 6, 5, 5, 6] sat0Allowed = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_1_sub_39 : checkSub 6 9 15 3 4 [(4, 80), (3, 4), (0, 1)] [7, 8, 5, 5, 5, 5, 1, 6, 5, 5, 6, 5, 6, 5, 5, 5, 6, 6, 6, 8, 1, 6, 5, 2, 6, 8, 1, 9, 10, 1, 6, 6, 8, 6, 5, 6, 5, 5, 5, 6, 6, 6, 8, 1, 6, 5, 2, 6, 8, 1, 9, 10, 1, 6, 6, 8, 5, 6, 6, 6] sat0Allowed = true := by decide +kernel
def split_1_proved : List (List (ℕ × ℕ) × ℕ) := [([(8, 4), (3, 2), (0, 1)], 2), ([(4, 8), (8, 20), (3, 2), (0, 1)], 3), ([(4, 24), (8, 20), (3, 2), (0, 1)], 3), ([(4, 32), (8, 20), (3, 2), (0, 1)], 3), ([(4, 36), (8, 20), (3, 2), (0, 1)], 3), ([(4, 40), (8, 20), (3, 2), (0, 1)], 3), ([(4, 64), (8, 20), (3, 2), (0, 1)], 4), ([(4, 68), (8, 20), (3, 2), (0, 1)], 4), ([(5, 24), (4, 72), (8, 20), (3, 2), (0, 1)], 4), ([(5, 32), (4, 72), (8, 20), (3, 2), (0, 1)], 4), ([(5, 33), (4, 72), (8, 20), (3, 2), (0, 1)], 4), ([(5, 36), (4, 72), (8, 20), (3, 2), (0, 1)], 4), ([(5, 40), (4, 72), (8, 20), (3, 2), (0, 1)], 4), ([(5, 68), (4, 72), (8, 20), (3, 2), (0, 1)], 4), ([(5, 96), (4, 72), (8, 20), (3, 2), (0, 1)], 4), ([(5, 128), (4, 72), (8, 20), (3, 2), (0, 1)], 4), ([(5, 129), (4, 72), (8, 20), (3, 2), (0, 1)], 4), ([(5, 132), (4, 72), (8, 20), (3, 2), (0, 1)], 4), ([(5, 136), (4, 72), (8, 20), (3, 2), (0, 1)], 4), ([(5, 144), (4, 72), (8, 20), (3, 2), (0, 1)], 4), ([(5, 160), (4, 72), (8, 20), (3, 2), (0, 1)], 4), ([(4, 80), (8, 20), (3, 2), (0, 1)], 4), ([(5, 8), (4, 96), (8, 20), (3, 2), (0, 1)], 4), ([(5, 9), (4, 96), (8, 20), (3, 2), (0, 1)], 4), ([(5, 24), (4, 96), (8, 20), (3, 2), (0, 1)], 4), ([(5, 36), (4, 96), (8, 20), (3, 2), (0, 1)], 4), ([(5, 40), (4, 96), (8, 20), (3, 2), (0, 1)], 4), ([(5, 72), (4, 96), (8, 20), (3, 2), (0, 1)], 4), ([(5, 80), (4, 96), (8, 20), (3, 2), (0, 1)], 4), ([(5, 128), (4, 96), (8, 20), (3, 2), (0, 1)], 4), ([(5, 129), (4, 96), (8, 20), (3, 2), (0, 1)], 4), ([(5, 132), (4, 96), (8, 20), (3, 2), (0, 1)], 4), ([(5, 136), (4, 96), (8, 20), (3, 2), (0, 1)], 4), ([(5, 144), (4, 96), (8, 20), (3, 2), (0, 1)], 4), ([(5, 160), (4, 96), (8, 20), (3, 2), (0, 1)], 4), ([(4, 10), (3, 4), (0, 1)], 2), ([(4, 16), (3, 4), (0, 1)], 3), ([(4, 18), (3, 4), (0, 1)], 3), ([(4, 24), (3, 4), (0, 1)], 3), ([(4, 80), (3, 4), (0, 1)], 4)]
set_option maxRecDepth 20000 in
theorem split_1_skel : checkSpecialSplit 6 9 0 15 3 [0] [1, 13] [3, 8, 11, 4, 11, 11, 11, 11, 11, 11, 11, 5, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 5, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 4, 11, 11, 11, 11, 11] sat0Allowed split_1_proved = true := by decide +kernel
theorem not_bad_split_1 : ¬ Bad (decode 6) (decode 9) := by
  apply not_bad_of_sat0_pos
  apply checkSpecialSplit_sound (by decide) (by decide) _ _ _ sat0Allowed split_1_proved sat0Allowed_ok split_1_skel
  intro p hp hcap1 hng pos hcov hcap hL
  simp only [split_1_proved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_0 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_1 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_2 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_3 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_4 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_5 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_6 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_7 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_8 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_9 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_10 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_11 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_12 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_13 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_14 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_15 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_16 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_17 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_18 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_19 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_20 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_21 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_22 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_23 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_24 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_25 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_26 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_27 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_28 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_29 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_30 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_31 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_32 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_33 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_34 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_35 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_36 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_37 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_38 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ sat0Allowed sat0Allowed_ok hcap1 hng split_1_sub_39 pos hcov hcap hL

set_option maxRecDepth 20000 in
theorem split_2_sub_0 : checkSub 6 129 135 2 2 [(4, 10), (1, 4), (0, 1)] [7, 8, 3, 3, 3, 3] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_2_sub_1 : checkSub 6 129 135 2 3 [(4, 16), (1, 4), (0, 1)] [2, 8, 6, 7, 3, 5, 6, 6, 6, 7, 5, 8] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_2_sub_2 : checkSub 6 129 135 2 3 [(4, 18), (1, 4), (0, 1)] [6, 7, 3, 2, 7, 8, 7, 3, 2, 7, 5, 3, 3, 3, 5, 2, 7, 8, 7, 2, 8, 3, 2, 8] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_2_sub_3 : checkSub 6 129 135 2 3 [(4, 24), (1, 4), (0, 1)] [3, 6, 2, 7, 2, 2, 2, 8, 5, 2, 5, 6, 7, 8, 2, 7, 8, 6, 5, 5, 8, 5, 6, 5, 2, 2, 2, 8, 7, 5, 7, 5, 7, 7, 5, 7, 5, 7, 5, 6, 7, 5, 2, 2, 7, 8, 2, 8, 2, 2, 2, 7, 5, 2, 2, 2] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_2_sub_4 : checkSub 6 129 135 2 4 [(4, 80), (1, 4), (0, 1)] [8, 3, 2, 2, 2, 2, 2, 2, 5, 2, 6, 7, 3, 5, 5, 3, 2, 2, 6, 3, 2, 7, 5, 2, 2, 2, 3, 5, 2, 2, 6, 7, 3, 5, 5, 3, 2, 2, 6, 3, 2, 7, 5, 2, 2, 2, 3, 5, 2, 6, 5, 5, 5, 3, 5, 5, 3, 5] [] = true := by decide +kernel
def split_2_proved : List (List (ℕ × ℕ) × ℕ) := [([(4, 10), (1, 4), (0, 1)], 2), ([(4, 16), (1, 4), (0, 1)], 3), ([(4, 18), (1, 4), (0, 1)], 3), ([(4, 24), (1, 4), (0, 1)], 3), ([(4, 80), (1, 4), (0, 1)], 4)]
set_option maxRecDepth 20000 in
theorem split_2_skel : checkSpecialSplit 6 129 0 135 2 [0, 1] [6, 8, 10] [4, 11, 11, 11, 11, 11] [] split_2_proved = true := by decide +kernel
theorem not_bad_split_2 : ¬ Bad (decode 6) (decode 129) := by
  apply not_bad_of_empty_allowed
  apply checkSpecialSplit_sound (by decide) (by decide) _ _ _ [] split_2_proved (by simp) split_2_skel
  intro p hp hcap1 hng pos hcov hcap hL
  simp only [split_2_proved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_2_sub_0 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_2_sub_1 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_2_sub_2 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_2_sub_3 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_2_sub_4 pos hcov hcap hL

set_option maxRecDepth 20000 in
theorem split_3_sub_0 : checkSub 10 129 139 1 1 [(3, 2), (1, 1)] [9, 8, 2, 6, 6, 6, 6, 2, 2, 2, 6, 2, 2, 7, 5, 2, 2, 7, 5, 7, 2, 4, 4, 2, 8, 4, 4, 4, 4, 8, 4, 4, 0, 4, 8, 4, 0, 4, 4, 8, 4, 4, 4, 4, 5, 4, 4, 4, 4, 5, 4] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_3_sub_1 : checkSub 10 129 139 1 2 [(3, 4), (1, 1)] [9, 7, 0, 4, 0, 6, 4, 4, 8, 4, 7, 2, 4, 4, 0, 4, 8, 2, 6, 6, 7, 0, 0, 6, 7, 4, 6, 2, 0, 0, 2, 0, 6, 0, 0, 2, 2, 0, 6, 0, 0, 0, 2, 2, 7, 0, 6, 2, 0, 0, 2, 2, 0, 6, 2, 4, 4, 4, 5, 2, 4, 2, 5, 2, 4, 2, 4, 2] [] = true := by decide +kernel
def split_3_proved : List (List (ℕ × ℕ) × ℕ) := [([(3, 2), (1, 1)], 1), ([(3, 4), (1, 1)], 2)]
set_option maxRecDepth 20000 in
theorem split_3_skel : checkSpecialSplit 10 129 0 139 1 [1] [0, 3, 6, 10, 12] [3, 11, 11] [] split_3_proved = true := by decide +kernel
theorem not_bad_split_3 : ¬ Bad (decode 10) (decode 129) := by
  apply not_bad_of_empty_allowed
  apply checkSpecialSplit_sound (by decide) (by decide) _ _ _ [] split_3_proved (by simp) split_3_skel
  intro p hp hcap1 hng pos hcov hcap hL
  simp only [split_3_proved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_3_sub_0 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_3_sub_1 pos hcov hcap hL

set_option maxRecDepth 20000 in
theorem split_4_sub_0 : checkSub 136 288 425 3 2 [(5, 8), (3, 4), (0, 1)] [2, 4, 6, 6, 6, 6, 6, 4, 4, 4, 7, 8, 4, 1, 9, 9, 1, 4, 1, 9, 4, 1, 8, 7, 4, 6, 7, 4, 6, 6, 9, 4, 8, 7, 4, 6, 6, 8, 7, 4, 6, 7, 4, 6, 6, 9, 4, 8, 7, 4, 6, 6, 4] [] = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem split_4_sub_1 : checkSub 136 288 425 3 3 [(5, 16), (3, 4), (0, 1)] [1, 2, 4, 6, 4, 6, 6, 7, 6, 4, 6, 4, 6, 4, 2, 2, 6, 4, 4] [] = true := by decide +kernel
def split_4_proved : List (List (ℕ × ℕ) × ℕ) := [([(5, 8), (3, 4), (0, 1)], 2), ([(5, 16), (3, 4), (0, 1)], 3)]
set_option maxRecDepth 20000 in
theorem split_4_skel : checkSpecialSplit 136 288 26 425 3 [0, 3] [12, 13] [5, 11, 11] [] split_4_proved = true := by decide +kernel
theorem not_bad_split_4 : ¬ Bad (decode 136) (decode 288) := by
  apply not_bad_of_empty_allowed
  apply checkSpecialSplit_sound (by decide) (by decide) _ _ _ [] split_4_proved (by simp) split_4_skel
  intro p hp hcap1 hng pos hcov hcap hL
  simp only [split_4_proved, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_4_sub_0 pos hcov hcap hL
  · exact checkSub_sound (by decide) (by decide) (by decide) (by decide) _ _ [] (by simp) hcap1 hng split_4_sub_1 pos hcov hcap hL

def sat1Buf : List ℕ := [5, 8, 1, 2, 3, 6, 6, 3, 3, 2, 2, 3, 6, 6, 2, 1, 6, 2, 6, 2, 8, 1, 3, 6, 2, 10]
set_option maxRecDepth 20000 in
theorem sat1_ok : checkSpecial 144 288 0 433 4 [0, 4, 7] [] sat1Buf sat1Allowed = true := by decide +kernel
theorem not_bad_sat1 : ¬ Bad (decode 144) (decode 288) :=
  not_bad_of_sat1_pos (checkSpecial_sound (by decide) (by decide) _ _ _ sat1Allowed sat1Allowed_ok sat1_ok)

def checkUnsatEntry (e : ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ) : Bool :=
  let (a, b, sub0, cap1Mask, noneGcap, clq, nw, buf) := e
  a < 512 && b < 512 && checkSpecial a b sub0 cap1Mask noneGcap clq nw buf []

def checkUnsatBatch (es : List (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ)) : Bool :=
  es.all checkUnsatEntry

theorem not_bad_of_unsatBatch
    (es : List (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ))
    (hok : checkUnsatBatch es = true)
    (a b : Fin 512)
    (hmem : es.any (fun e => e.1 * 512 + e.2.1 == a.val * 512 + b.val) = true) :
    ¬ Bad (decode a.val) (decode b.val) := by
  rw [List.any_eq_true] at hmem
  obtain ⟨e, he_mem, he_eq⟩ := hmem
  rcases e with ⟨ea, eb, sub0, cap1, ng, clq, nw, buf⟩
  have hchk : checkUnsatEntry (ea, eb, sub0, cap1, ng, clq, nw, buf) = true :=
    List.all_eq_true.mp hok _ he_mem
  simp only [checkUnsatEntry, Bool.and_eq_true, decide_eq_true_eq] at hchk
  have hcode : ea * 512 + eb = a.val * 512 + b.val := beq_iff_eq.mp he_eq
  have hea : ea = a.val := by omega
  have heb : eb = b.val := by omega
  rw [hea, heb] at hchk
  exact not_bad_of_empty_allowed (checkSpecial_sound hchk.1.1 hchk.1.2 clq nw buf [] (by simp) hchk.2)

def unsatBatch_0 : List (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ) := [
  (9, 18, 0, 27, 2, [0, 1], [0, 1, 2], [3, 5, 7, 2, 6, 2, 2, 2, 7, 8, 2, 6, 2, 4, 8, 6, 8, 2, 7, 7, 4, 6, 4, 7, 8, 2, 4, 6, 7, 2, 4, 2, 7, 2, 4, 6, 7, 2, 4, 2, 7, 4, 7, 7, 8, 5, 4, 5, 6, 5, 5, 8, 8, 2, 5, 6, 8, 8, 6, 6, 2, 5, 8, 6, 8, 5, 4, 8, 4, 2, 8, 6, 2, 4, 6, 9, 5])
]
set_option maxRecDepth 20000 in
theorem unsatBatch_ok_0 : checkUnsatBatch unsatBatch_0 = true := by decide +kernel

def unsatBatch_1 : List (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ) := [
  (40, 130, 2, 171, 3, [0, 1], [5, 15], [3, 4, 6, 8, 8, 8, 6, 8, 2, 8, 8, 6, 6, 6, 5, 2, 7, 6, 9, 6, 6, 6, 5, 2, 7, 6, 9, 5, 6, 9, 9, 6, 4, 8, 8, 8, 4, 8, 4, 4, 8, 5, 7, 2, 4, 4, 5, 2, 5, 8]),
  (9, 22, 0, 31, 1, [0, 1, 4], [0, 1, 2, 7, 13], [2, 3, 8, 5, 5, 7, 5, 3, 9, 8, 5])
]
set_option maxRecDepth 20000 in
theorem unsatBatch_ok_1 : checkUnsatBatch unsatBatch_1 = true := by decide +kernel

def unsatBatch_2 : List (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ) := [
  (12, 160, 45, 173, 3, [0, 3], [6, 8], [4, 8, 6, 6, 7, 1, 5, 6, 8, 6, 6, 7, 1, 5, 6, 8, 7, 1, 7, 1, 7, 7, 1, 8, 5, 6, 5, 6, 7, 1, 6, 5, 7, 9, 1, 5, 6, 5, 6, 7, 1, 6, 5, 7, 9, 1, 6, 1, 1]),
  (130, 265, 0, 395, 2, [0, 3, 8], [7, 9, 11], [1, 7, 2, 4, 4, 4, 2, 4, 4, 2, 4, 7, 6, 5, 5, 5, 5, 5, 6, 6, 2, 6, 5, 2, 6, 2])
]
set_option maxRecDepth 20000 in
theorem unsatBatch_ok_2 : checkUnsatBatch unsatBatch_2 = true := by decide +kernel

def unsatBatch_3 : List (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ) := [
  (41, 130, 0, 171, 2, [0, 3, 5], [5, 7, 9], [1, 7, 4, 2, 8, 2, 6, 2, 4, 2, 6, 2, 7, 6, 4, 4, 4, 8, 8, 6, 4, 4, 8, 2, 6, 4, 6, 2]),
  (25, 130, 0, 155, 2, [0, 1, 4], [7, 8, 9], [3, 7, 2, 5, 5, 5, 5, 6, 6, 2, 6, 2, 6, 8, 5, 6, 5, 5, 6, 5, 2, 5, 5, 6, 5, 7, 2]),
  (48, 384, 0, 433, 2, [0, 4, 5], [7, 8, 14], [7, 8, 1, 2, 3, 6, 6, 3, 6, 2, 6, 2, 2, 3, 6, 8, 1, 6, 3]),
  (1, 10, 0, 31, 2, [1, 2, 3, 4], [0, 3, 12], [5])
]
set_option maxRecDepth 20000 in
theorem unsatBatch_ok_3 : checkUnsatBatch unsatBatch_3 = true := by decide +kernel

def unsatBatch_4 : List (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ) := [
  (6, 41, 0, 47, 2, [0, 3, 5], [1, 5, 13], [1, 2, 4, 6, 6, 7, 8, 4, 4, 6, 8, 4, 2, 8, 4, 4, 6, 4, 6, 6, 4, 4, 7, 8, 4, 8, 4]),
  (9, 134, 0, 143, 2, [1, 2, 7], [1, 7, 9], [3, 0, 4, 6, 6, 8, 6, 4, 6, 6, 8, 8, 6, 4, 6, 0, 8, 4, 4, 8, 4, 4, 4, 4, 5, 4, 5]),
  (12, 97, 0, 109, 2, [0, 5, 6], [0, 3, 12], [7, 8, 1, 3, 9, 1, 4, 8, 1, 3, 9, 9, 4, 1, 4]),
  (28, 160, 5, 189, 2, [0, 3, 4, 5], [2, 6, 7], [2, 6, 7, 1])
]
set_option maxRecDepth 20000 in
theorem unsatBatch_ok_4 : checkUnsatBatch unsatBatch_4 = true := by decide +kernel

def unsatBatch_5 : List (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ) := [
  (24, 98, 5, 123, 3, [0, 5, 6], [2, 3], [1, 3, 7, 2, 2, 4, 7, 8, 8, 2, 2, 8, 8, 2, 2, 8, 9, 7, 2, 8, 7, 8]),
  (6, 25, 0, 31, 2, [0, 3, 4], [1, 8, 13], [1, 2, 7, 6, 6, 6, 7, 5, 5, 6, 5, 8, 5, 6, 5, 5, 5, 6, 6, 6, 7, 8, 2, 6, 5]),
  (40, 384, 2, 425, 2, [0, 3, 7], [12, 13, 14], [5, 8, 4, 6, 6, 6, 4, 6, 8, 6, 1, 4, 6, 6, 6, 4, 1]),
  (3, 36, 0, 103, 1, [0, 2, 6], [2, 4, 5, 6, 11], [1, 5, 9, 4, 4, 9, 7, 4, 7])
]
set_option maxRecDepth 20000 in
theorem unsatBatch_ok_5 : checkUnsatBatch unsatBatch_5 = true := by decide +kernel

def unsatBatch_6 : List (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ) := [
  (6, 49, 0, 55, 2, [0, 4, 5], [1, 5, 8], [1, 2, 8, 3, 3, 3, 7, 3, 6, 8, 3, 2, 7, 6, 6, 6, 6, 7, 3, 6, 6, 8, 3, 7, 3]),
  (28, 98, 5, 127, 2, [0, 3, 4], [2, 3, 6], [1, 5, 6, 2, 7, 8, 8, 9, 8, 9, 7, 7, 7, 5, 6, 7, 8]),
  (12, 96, 20, 109, 4, [0, 3, 5], [], [4, 7, 1, 1, 6, 8, 6, 8, 8, 1, 7, 1, 1, 6, 7, 7]),
  (10, 48, 4, 59, 2, [0, 1, 3], [0, 1, 5], [4, 5, 8, 6, 2, 2, 6, 7, 2, 6, 2, 8, 6, 2, 8]),
  (24, 386, 0, 411, 2, [0, 1, 3, 4], [7, 8, 12], [7, 8, 5, 6]),
  (3, 12, 0, 367, 1, [0, 5, 6, 8], [0, 3, 6, 11, 12], [4])
]
set_option maxRecDepth 20000 in
theorem unsatBatch_ok_6 : checkUnsatBatch unsatBatch_6 = true := by decide +kernel

def unsatBatch_7 : List (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ) := [
  (144, 264, 0, 409, 3, [0, 3, 7], [0, 1], [4, 8, 2, 5, 6, 5, 6, 6, 5, 6, 5, 1, 6, 2, 2]),
  (9, 38, 0, 47, 1, [1, 2, 5], [1, 2, 4, 13, 14], [3, 0, 9, 8, 4, 9, 8, 4, 4, 8, 9, 8, 4, 8, 4]),
  (6, 145, 0, 151, 2, [0, 1, 7], [1, 6, 8], [4, 2, 8, 3, 3, 5, 3, 8, 5, 5, 2, 8, 6, 3]),
  (9, 262, 0, 271, 2, [0, 1, 8], [1, 12, 13], [2, 3, 7, 4, 5, 4, 7, 4, 3, 5, 4, 4, 5]),
  (9, 34, 0, 59, 2, [0, 1, 4], [2, 4, 14], [3, 5, 6, 8, 8, 8, 2, 8, 2, 6, 8, 6]),
  (49, 132, 0, 181, 2, [0, 4, 5], [1, 7, 8], [7, 2, 1, 3, 6, 3, 3, 8, 1, 8, 3])
]
set_option maxRecDepth 20000 in
theorem unsatBatch_ok_7 : checkUnsatBatch unsatBatch_7 = true := by decide +kernel

def unsatBatch_8 : List (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ) := [
  (9, 162, 0, 171, 1, [1, 5, 7], [2, 4, 7, 9, 14], [3, 9, 0, 8, 2, 2, 6, 2, 6, 4, 4, 4]),
  (12, 34, 26, 175, 3, [0, 3, 7], [6, 11], [1, 5, 2, 4, 6, 6, 6, 4, 4, 5, 6, 4]),
  (10, 160, 45, 171, 2, [0, 3, 5], [5, 6, 10], [7, 1, 6, 2, 4, 4, 2, 8, 2]),
  (12, 35, 0, 111, 1, [0, 5, 6], [0, 3, 6, 11, 12], [1, 3, 2, 9, 4, 4, 4, 7, 4, 7]),
  (12, 99, 0, 111, 1, [0, 5, 6], [0, 3, 6, 11, 12], [3, 2, 1, 9, 4, 4, 4, 4, 7, 7]),
  (41, 134, 0, 175, 1, [0, 1, 2], [1, 5, 7, 9, 13], [3, 5, 7, 9, 4, 4, 4, 4, 4]),
  (2, 5, 0, 31, 3, [0, 3, 4], [6, 11], [2, 7, 5, 6, 5, 5, 6]),
  (2, 13, 0, 31, 3, [0, 3, 4], [6, 11], [2, 7, 5, 6, 5, 5, 6]),
  (2, 29, 0, 31, 3, [0, 3, 4], [6, 11], [2, 7, 5, 6, 5, 5, 6]),
  (14, 257, 0, 271, 1, [0, 1, 2, 3], [0, 3, 11, 12, 13], [5, 8, 4])
]
set_option maxRecDepth 20000 in
theorem unsatBatch_ok_8 : checkUnsatBatch unsatBatch_8 = true := by decide +kernel

def unsatBatch_9 : List (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ) := [
  (14, 129, 0, 143, 1, [0, 1, 2], [0, 3, 6, 8, 10], [7, 3, 9, 4, 4, 6, 8, 4]),
  (10, 193, 0, 203, 1, [0, 6, 7], [0, 3, 5, 6, 10], [1, 3, 9, 2, 2, 4, 8, 2]),
  (129, 266, 0, 395, 1, [0, 3, 8], [0, 3, 6, 10, 12], [7, 1, 9, 2, 2, 4, 6, 2]),
  (1, 134, 0, 135, 3, [1, 2, 7], [7, 9], [4, 6, 6, 8, 8, 6]),
  (9, 70, 0, 79, 1, [1, 2, 3], [1, 3, 4, 9, 13], [6, 9, 7, 4, 4, 7, 4]),
  (10, 21, 0, 31, 1, [0, 1, 4], [0, 1, 3, 6, 11], [3, 2, 9, 6, 6, 9, 7, 6]),
  (129, 262, 0, 391, 1, [0, 1, 2], [6, 8, 10, 12, 14], [7, 8, 9, 4, 3, 9, 3, 4]),
  (1, 14, 0, 15, 2, [1, 2, 3], [0, 3, 12], [8, 5, 6, 5, 5]),
  (144, 289, 0, 433, 2, [0, 5, 8], [0, 2, 7], [4, 7, 1, 7, 1, 2, 3]),
  (10, 81, 0, 91, 1, [0, 1, 4, 6], [0, 1, 3, 5, 10], [8, 5]),
  (9, 146, 0, 155, 1, [1, 3, 4, 7], [0, 1, 2, 7, 9], [8, 2]),
  (9, 194, 0, 203, 2, [1, 3, 6, 7], [3, 4, 7], [2, 4]),
  (10, 273, 0, 283, 1, [0, 1, 4, 8], [0, 1, 3, 11, 12], [5, 6]),
  (41, 384, 0, 425, 1, [0, 3, 5, 7], [7, 9, 12, 13, 14], [4, 1]),
  (24, 194, 5, 219, 2, [0, 1, 3, 4], [3, 7, 8], [7, 6, 5]),
  (144, 290, 0, 435, 2, [0, 1, 4, 8], [2, 6, 10], [7, 5, 6]),
  (12, 162, 45, 175, 2, [0, 1, 3, 7], [6, 8, 11], [5, 6]),
  (25, 162, 0, 187, 1, [0, 1, 4, 5], [2, 4, 7, 8, 9], [7, 2]),
  (12, 176, 5, 189, 2, [0, 3, 4, 5], [0, 1, 6], [7, 6]),
  (49, 384, 0, 433, 1, [0, 4, 5, 7], [7, 8, 9, 12, 14], [8, 9])
]
set_option maxRecDepth 20000 in
theorem unsatBatch_ok_9 : checkUnsatBatch unsatBatch_9 = true := by decide +kernel

def unsatBatch_10 : List (ℕ × ℕ × ℕ × ℕ × ℕ × List ℕ × List ℕ × List ℕ) := [
  (6, 209, 0, 215, 1, [0, 1, 6, 7], [1, 5, 6, 8, 10], [4, 3]),
  (140, 288, 26, 429, 2, [0, 2, 3, 5], [11, 12, 13], [7, 4]),
  (144, 296, 0, 441, 2, [0, 3, 5, 7], [0, 1, 2], [8, 6]),
  (144, 353, 0, 497, 1, [0, 4, 5, 8], [0, 2, 7, 9, 10], [6, 2]),
  (3, 24, 0, 123, 1, [1, 3, 5, 6], [0, 2, 3, 7, 12], [8]),
  (1, 26, 0, 31, 1, [1, 2, 3, 4], [0, 2, 3, 7, 12], [5]),
  (1, 30, 0, 31, 1, [1, 2, 3, 4], [0, 2, 3, 7, 12], [5]),
  (2, 41, 0, 59, 3, [0, 3, 4, 5], [5, 15], [6]),
  (1, 54, 0, 55, 1, [1, 2, 4, 5], [0, 2, 4, 7, 14], [3]),
  (10, 49, 0, 315, 1, [0, 1, 4, 8], [0, 1, 3, 5, 12], [7]),
  (9, 50, 0, 59, 1, [1, 3, 4, 5], [0, 1, 2, 4, 7], [6]),
  (2, 57, 0, 59, 3, [0, 3, 4, 5], [5, 15], [6]),
  (6, 57, 0, 63, 1, [0, 1, 3, 4], [1, 5, 8, 13, 15], [6]),
  (12, 67, 0, 367, 1, [0, 5, 6, 8], [0, 3, 6, 11, 12], [4]),
  (48, 74, 11, 123, 1, [0, 1, 3, 6], [0, 1, 4, 5, 15], [7]),
  (3, 100, 0, 103, 1, [0, 2, 5, 6], [2, 3, 4, 5, 6], [3]),
  (13, 96, 0, 125, 1, [2, 3, 4, 5], [2, 3, 4, 9, 14], [8]),
  (12, 98, 20, 239, 2, [0, 3, 5, 7], [3, 6, 11], [4]),
  (24, 99, 0, 123, 1, [1, 3, 5, 6], [0, 2, 3, 7, 12], [8]),
  (12, 112, 0, 125, 2, [0, 3, 5, 6], [0, 1, 3], [1]),
  (12, 113, 0, 125, 1, [0, 3, 5, 6], [0, 1, 3, 8, 12], [1]),
  (3, 132, 0, 231, 1, [0, 2, 5, 6], [6, 7, 9, 10, 11], [8]),
  (13, 130, 0, 159, 1, [0, 1, 3, 4], [6, 7, 8, 9, 11], [8]),
  (2, 137, 0, 155, 3, [0, 3, 4, 7], [6, 10], [6]),
  (24, 130, 0, 187, 3, [0, 1, 4, 5], [7, 8], [6]),
  (29, 130, 0, 159, 1, [0, 1, 3, 4], [6, 7, 8, 9, 11], [8]),
  (25, 134, 0, 159, 1, [0, 1, 3, 4], [1, 7, 8, 9, 13], [6]),
  (1, 150, 0, 151, 2, [1, 2, 4, 7], [0, 2, 7], [3]),
  (10, 145, 0, 159, 1, [0, 1, 2, 4], [0, 1, 3, 6, 10], [8]),
  (2, 153, 0, 155, 3, [0, 3, 4, 7], [6, 10], [6]),
  (41, 128, 0, 425, 3, [0, 3, 5, 8], [7, 9], [4]),
  (42, 129, 0, 427, 1, [0, 3, 5, 8], [0, 2, 3, 4, 6], [2]),
  (56, 130, 0, 187, 2, [0, 3, 4, 5], [5, 7, 8], [6]),
  (57, 130, 0, 187, 1, [0, 1, 3, 4], [5, 7, 8, 9, 15], [8]),
  (56, 132, 0, 189, 2, [0, 2, 3, 5], [1, 7, 8], [8]),
  (57, 132, 0, 189, 1, [0, 3, 4, 5], [1, 7, 8, 9, 13], [6]),
  (12, 161, 0, 237, 1, [0, 5, 6, 7], [0, 3, 6, 8, 12], [4]),
  (9, 166, 0, 175, 1, [0, 1, 5, 7], [1, 2, 4, 7, 9], [4]),
  (24, 162, 5, 187, 2, [0, 1, 5, 7], [2, 7, 8], [6]),
  (25, 194, 0, 219, 1, [0, 1, 3, 4], [3, 4, 7, 8, 9], [5]),
  (12, 224, 23, 237, 2, [0, 5, 6, 7], [3, 6, 8], [4]),
  (12, 225, 0, 237, 1, [0, 5, 6, 7], [0, 3, 6, 8, 12], [4]),
  (13, 258, 0, 287, 1, [0, 1, 3, 4], [6, 11, 12, 13, 14], [7]),
  (50, 257, 0, 307, 1, [1, 4, 5, 8], [0, 2, 4, 7, 11], [3]),
  (9, 294, 0, 303, 1, [0, 1, 5, 8], [1, 2, 4, 12, 13], [6]),
  (12, 321, 0, 365, 1, [0, 3, 5, 6], [0, 3, 11, 12, 13], [7]),
  (12, 353, 0, 365, 1, [0, 3, 5, 6], [0, 3, 11, 12, 13], [7]),
  (130, 264, 2, 427, 3, [0, 1, 3, 5], [11, 15], [6]),
  (144, 266, 0, 411, 2, [0, 1, 3, 8], [0, 1, 6], [6]),
  (130, 281, 0, 411, 1, [0, 1, 3, 4], [7, 8, 9, 11, 15], [5]),
  (137, 288, 0, 441, 1, [0, 3, 4, 7], [2, 4, 12, 13, 14], [1]),
  (129, 296, 0, 425, 1, [3, 5, 7, 8], [0, 2, 3, 4, 12], [4]),
  (128, 297, 0, 425, 3, [0, 3, 5, 8], [7, 9], [4]),
  (130, 296, 2, 427, 2, [0, 3, 5, 8], [5, 11, 15], [4]),
  (130, 297, 0, 427, 1, [0, 3, 5, 8], [5, 7, 9, 11, 15], [4]),
  (129, 298, 0, 427, 1, [0, 3, 5, 8], [0, 2, 3, 4, 6], [2]),
  (144, 328, 7, 473, 2, [0, 3, 6, 8], [0, 1, 9], [2]),
  (144, 352, 14, 497, 2, [0, 5, 6, 8], [2, 9, 10], [2]),
  (148, 352, 14, 501, 1, [0, 2, 4, 6], [2, 9, 10, 11, 13], [3]),
  (6, 385, 0, 391, 1, [0, 1, 7, 8], [6, 8, 10, 11, 13], [5]),
  (1, 390, 0, 391, 2, [1, 2, 7, 8], [7, 9, 12], [3]),
  (10, 385, 0, 395, 1, [0, 1, 7, 8], [0, 3, 6, 10, 11], [4]),
  (9, 386, 0, 395, 1, [1, 3, 7, 8], [7, 9, 12, 13, 14], [4]),
  (40, 385, 0, 425, 1, [0, 3, 7, 8], [0, 2, 3, 4, 12], [4]),
  (48, 385, 0, 433, 1, [0, 4, 7, 8], [0, 2, 4, 7, 8], [3])
]
set_option maxRecDepth 20000 in
theorem unsatBatch_ok_10 : checkUnsatBatch unsatBatch_10 = true := by decide +kernel

def specCovered (c : ℕ) : Bool :=
  c == 4738 ||
  c == 3081 ||
  c == 3201 ||
  c == 5249 ||
  c == 69920 ||
  c == 74016 ||
  unsatBatch_0.any (fun e => e.1 * 512 + e.2.1 == c) ||
  unsatBatch_1.any (fun e => e.1 * 512 + e.2.1 == c) ||
  unsatBatch_2.any (fun e => e.1 * 512 + e.2.1 == c) ||
  unsatBatch_3.any (fun e => e.1 * 512 + e.2.1 == c) ||
  unsatBatch_4.any (fun e => e.1 * 512 + e.2.1 == c) ||
  unsatBatch_5.any (fun e => e.1 * 512 + e.2.1 == c) ||
  unsatBatch_6.any (fun e => e.1 * 512 + e.2.1 == c) ||
  unsatBatch_7.any (fun e => e.1 * 512 + e.2.1 == c) ||
  unsatBatch_8.any (fun e => e.1 * 512 + e.2.1 == c) ||
  unsatBatch_9.any (fun e => e.1 * 512 + e.2.1 == c) ||
  unsatBatch_10.any (fun e => e.1 * 512 + e.2.1 == c)

theorem all_specs_covered :
    (specs_0 ++ specs_1 ++ specs_2 ++ specs_3 ++ specs_4 ++ specs_5 ++ specs_6 ++ specs_7 ++ specs_8).all
      specCovered = true := by
  decide +kernel

theorem not_bad_of_spec (a b : Fin 512)
    (hc : specCovered (a.val * 512 + b.val) = true) :
    ¬ Bad (decode a.val) (decode b.val) := by
  unfold specCovered at hc
  simp only [Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc with ((((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
  · have ha : a.val = 9 := by omega
    have hb : b.val = 130 := by omega
    rw [ha, hb]; exact not_bad_split_0
  · have ha : a.val = 6 := by omega
    have hb : b.val = 9 := by omega
    rw [ha, hb]; exact not_bad_split_1
  · have ha : a.val = 6 := by omega
    have hb : b.val = 129 := by omega
    rw [ha, hb]; exact not_bad_split_2
  · have ha : a.val = 10 := by omega
    have hb : b.val = 129 := by omega
    rw [ha, hb]; exact not_bad_split_3
  · have ha : a.val = 136 := by omega
    have hb : b.val = 288 := by omega
    rw [ha, hb]; exact not_bad_split_4
  · have ha : a.val = 144 := by omega
    have hb : b.val = 288 := by omega
    rw [ha, hb]; exact not_bad_sat1
  · exact not_bad_of_unsatBatch unsatBatch_0 unsatBatch_ok_0 a b h
  · exact not_bad_of_unsatBatch unsatBatch_1 unsatBatch_ok_1 a b h
  · exact not_bad_of_unsatBatch unsatBatch_2 unsatBatch_ok_2 a b h
  · exact not_bad_of_unsatBatch unsatBatch_3 unsatBatch_ok_3 a b h
  · exact not_bad_of_unsatBatch unsatBatch_4 unsatBatch_ok_4 a b h
  · exact not_bad_of_unsatBatch unsatBatch_5 unsatBatch_ok_5 a b h
  · exact not_bad_of_unsatBatch unsatBatch_6 unsatBatch_ok_6 a b h
  · exact not_bad_of_unsatBatch unsatBatch_7 unsatBatch_ok_7 a b h
  · exact not_bad_of_unsatBatch unsatBatch_8 unsatBatch_ok_8 a b h
  · exact not_bad_of_unsatBatch unsatBatch_9 unsatBatch_ok_9 a b h
  · exact not_bad_of_unsatBatch unsatBatch_10 unsatBatch_ok_10 a b h

theorem noBad (A B : Finset V) : ¬ Bad A B := by
  intro hBad0
  obtain ⟨a, b, hBad, ha, hb, hab, hhot, hcanon⟩ := canonical hBad0
  have ht_lt : tritCodeB a.val b.val < 19683 := (tritCode_spec a b hab).1
  have hdisj : (a.val * 512 + b.val) ∈
      (specs_0 ++ specs_1 ++ specs_2 ++ specs_3 ++ specs_4 ++ specs_5 ++ specs_6 ++ specs_7 ++ specs_8) ∨
      ∃ f : Fin 5 → V, Clique (decode a.val) (decode b.val) f := by
    by_cases h0 : tritCodeB a.val b.val < 2187
    · rcases checkChunk_of_pair 0 2187 wits_0 specs_0 chunk_ok_0 a b hab (by omega) (by omega) ha hb hcanon hhot with hm | hc
      · exact Or.inl (by simp [hm])
      · exact Or.inr hc
    · by_cases h1 : tritCodeB a.val b.val < 4374
      · rcases checkChunk_of_pair 2187 2187 wits_1 specs_1 chunk_ok_1 a b hab (by omega) (by omega) ha hb hcanon hhot with hm | hc
        · exact Or.inl (by simp [hm])
        · exact Or.inr hc
      · by_cases h2 : tritCodeB a.val b.val < 6561
        · rcases checkChunk_of_pair 4374 2187 wits_2 specs_2 chunk_ok_2 a b hab (by omega) (by omega) ha hb hcanon hhot with hm | hc
          · exact Or.inl (by simp [hm])
          · exact Or.inr hc
        · by_cases h3 : tritCodeB a.val b.val < 8748
          · rcases checkChunk_of_pair 6561 2187 wits_3 specs_3 chunk_ok_3 a b hab (by omega) (by omega) ha hb hcanon hhot with hm | hc
            · exact Or.inl (by simp [hm])
            · exact Or.inr hc
          · by_cases h4 : tritCodeB a.val b.val < 10935
            · rcases checkChunk_of_pair 8748 2187 wits_4 specs_4 chunk_ok_4 a b hab (by omega) (by omega) ha hb hcanon hhot with hm | hc
              · exact Or.inl (by simp [hm])
              · exact Or.inr hc
            · by_cases h5 : tritCodeB a.val b.val < 13122
              · rcases checkChunk_of_pair 10935 2187 wits_5 specs_5 chunk_ok_5 a b hab (by omega) (by omega) ha hb hcanon hhot with hm | hc
                · exact Or.inl (by simp [hm])
                · exact Or.inr hc
              · by_cases h6 : tritCodeB a.val b.val < 15309
                · rcases checkChunk_of_pair 13122 2187 wits_6 specs_6 chunk_ok_6 a b hab (by omega) (by omega) ha hb hcanon hhot with hm | hc
                  · exact Or.inl (by simp [hm])
                  · exact Or.inr hc
                · by_cases h7 : tritCodeB a.val b.val < 17496
                  · rcases checkChunk_of_pair 15309 2187 wits_7 specs_7 chunk_ok_7 a b hab (by omega) (by omega) ha hb hcanon hhot with hm | hc
                    · exact Or.inl (by simp [hm])
                    · exact Or.inr hc
                  · rcases checkChunk_of_pair 17496 2187 wits_8 specs_8 chunk_ok_8 a b hab (by omega) (by omega) ha hb hcanon hhot with hm | hc
                    · exact Or.inl (by simp [hm])
                    · exact Or.inr hc
  rcases hdisj with hmem | ⟨f, hclq⟩
  · exact not_bad_of_spec a b (List.all_eq_true.mp all_specs_covered _ hmem) hBad
  · obtain ⟨_, _, pos, hcov, hcap⟩ := bad_frame hBad
    exact noFiveClique hcov hcap f hclq

theorem main :
    ∀ G : SimpleGraph (Fin 9), G = SimpleGraph.fromRel (fun a b : Fin 9 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6), (3, 5), (3, 7), (4, 6), (4, 8), (5, 7), (6, 8), (7, 8)] : List (ℕ × ℕ))) →
      ∀ C : PEqualNP.AndCount.AndCountCircuit 9, C.WellFormed →
        (∀ I : Finset (Fin 9), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 9, w ∉ I → ∃ a ∈ I, G.Adj a w) →
          C.eval I = false ∧ ∀ w : Fin 9, w ∉ I → C.eval (insert w I) = true) →
        6 ≤ C.size :=
  main_of_noBad noBad

end PEqualNP.Outside.L_meta_908_aux

theorem PEqualNP.Outside.L_meta_908 : ∀ G : SimpleGraph (Fin 9), G = SimpleGraph.fromRel (fun a b : Fin 9 => ((a : ℕ), (b : ℕ)) ∈ ([(0, 1), (0, 2), (1, 3), (1, 4), (2, 5), (2, 6), (3, 5), (3, 7), (4, 6), (4, 8), (5, 7), (6, 8), (7, 8)] : List (ℕ × ℕ))) →
  ∀ C : PEqualNP.AndCount.AndCountCircuit 9, C.WellFormed →
    (∀ I : Finset (Fin 9), (∀ a ∈ I, ∀ c ∈ I, ¬ G.Adj a c) → (∀ w : Fin 9, w ∉ I → ∃ a ∈ I, G.Adj a w) →
      C.eval I = false ∧ ∀ w : Fin 9, w ∉ I → C.eval (insert w I) = true) →
    6 ≤ C.size := by
  exact PEqualNP.Outside.L_meta_908_aux.main
