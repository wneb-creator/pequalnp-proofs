import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2584

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma exists_least_circuit (n : ℕ) (f : (Fin n → Bool) → Bool)
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hf : circuitFun n C = f) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = f ∧
      D.size ≤ C.size ∧
      ∀ E : Circuit, PEqualNP.TopForm.IsAO2 n E → circuitFun n E = f →
        D.size ≤ E.size := by
  classical
  let p : ℕ → Prop := fun s =>
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = f ∧ D.size = s
  have hp : ∃ s, p s := ⟨C.size, C, hC, hf, rfl⟩
  obtain ⟨D, hD, hDf, hsize⟩ := Nat.find_spec hp
  refine ⟨D, hD, hDf, ?_, ?_⟩
  · rw [hsize]
    exact Nat.find_min' hp ⟨C, hC, hf, rfl⟩
  · intro E hE hEf
    rw [hsize]
    exact Nat.find_min' hp ⟨E, hE, hEf, rfl⟩

lemma false_circuit_read (n k : ℕ) (C : Circuit)
    (hC : ∀ x : Fin n → Bool, circuitFun n C x = false) :
    PEqualNP.ReadK.IsReadK n C k := by
  intro S hS
  have htrue := hS.1
  rw [hC] at htrue
  cases htrue

lemma normalize_of_least_read (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hread : ∀ D : Circuit, PEqualNP.TopForm.IsAO2 n D → circuitFun n D = f →
      (∀ E : Circuit, PEqualNP.TopForm.IsAO2 n E → circuitFun n E = f →
        D.size ≤ E.size) → PEqualNP.ReadK.IsReadK n D 2)
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hf : circuitFun n C = f) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = f ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK n D 2 := by
  obtain ⟨D, hD, hDf, hsize, hleast⟩ := exists_least_circuit n f C hC hf
  exact ⟨D, hD, hDf, hsize, hread D hD hDf hleast⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma point_ne_line {P L : ℕ} (p : Fin P) (l : Fin L) :
    Fin.castAdd L p ≠ Fin.natAdd P l := by
  intro h
  have hval := congrArg Fin.val h
  change p.val = P + l.val at hval
  omega

lemma incidence_pair_prime {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    {p : Fin P} {l : Fin L} (hi : I p l) :
    IsPrimeImplicant (P + L) C {Fin.castAdd L p, Fin.natAdd P l} := by
  classical
  constructor
  · rw [hC, decide_eq_true_eq]
    exact ⟨p, l, hi, by simp [setInput], by simp [setInput]⟩
  · intro T hT
    have hT' := Finset.mem_ssubsets.mp hT
    rw [hC, decide_eq_false_iff_not]
    rintro ⟨p', l', _, hp, hl⟩
    have hp' : Fin.castAdd L p' ∈ T := of_decide_eq_true hp
    have hl' : Fin.natAdd P l' ∈ T := of_decide_eq_true hl
    have pe : Fin.castAdd L p' = Fin.castAdd L p := by
      have := Finset.mem_insert.mp (hT'.subset hp')
      exact this.resolve_right (fun hm => point_ne_line p' l (Finset.mem_singleton.mp hm))
    have le : Fin.natAdd P l' = Fin.natAdd P l := by
      have := Finset.mem_insert.mp (hT'.subset hl')
      exact Finset.mem_singleton.mp (this.resolve_left (fun e => point_ne_line p l' e.symm))
    exact hT'.not_ge (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · simpa only [pe] using hp'
      · rw [Finset.mem_singleton.mp hw, ← le]
        exact hl')

lemma incidence_prime_iff {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    (S : Finset (Fin (P + L))) :
    IsPrimeImplicant (P + L) C S ↔
      ∃ p : Fin P, ∃ l : Fin L, I p l ∧ S = {Fin.castAdd L p, Fin.natAdd P l} := by
  classical
  constructor
  · intro hS
    have hTrue := hS.1
    rw [hC, decide_eq_true_eq] at hTrue
    obtain ⟨p, l, hi, hp, hl⟩ := hTrue
    have hp' : Fin.castAdd L p ∈ S := of_decide_eq_true hp
    have hl' : Fin.natAdd P l ∈ S := of_decide_eq_true hl
    have hsub : ({Fin.castAdd L p, Fin.natAdd P l} : Finset (Fin (P + L))) ⊆ S := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hp'
      · exact hl'
    refine ⟨p, l, hi, ?_⟩
    by_contra hne
    have hss : ({Fin.castAdd L p, Fin.natAdd P l} : Finset (Fin (P + L))) ⊂ S :=
      lt_of_le_of_ne hsub (Ne.symm hne)
    have hFalse := hS.2 _ (Finset.mem_ssubsets.mpr hss)
    have hPair := (incidence_pair_prime I C hC hi).1
    exact Bool.noConfusion (hPair.symm.trans hFalse)
  · rintro ⟨p, l, hi, rfl⟩
    exact incidence_pair_prime I C hC hi

lemma incidence_prime_card {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    (S : Finset (Fin (P + L))) (hS : IsPrimeImplicant (P + L) C S) : S.card = 2 := by
  obtain ⟨p, l, _, rfl⟩ := (incidence_prime_iff I C hC S).mp hS
  exact Finset.card_pair (point_ne_line p l)

lemma incidence_read_iff {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) (k : ℕ) :
    IsReadK (P + L) C k ↔
      ∀ p : Fin P, ∀ l : Fin L, I p l →
        readsAtMost C (P + L) (setList {Fin.castAdd L p, Fin.natAdd P l}) k = true := by
  constructor
  · intro h p l hi
    exact h _ (incidence_pair_prime I C hC hi)
  · intro h S hS
    obtain ⟨p, l, hi, rfl⟩ := (incidence_prime_iff I C hC S).mp hS
    exact h p l hi

lemma incidence_biclique_star {P L : ℕ} (I : Fin P → Fin L → Prop)
    (h4 : ∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (A : Finset (Fin P)) (B : Finset (Fin L))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : ∀ p ∈ A, ∀ l ∈ B, I p l) : A.card = 1 ∨ B.card = 1 := by
  by_contra h
  obtain ⟨hAn, hBn⟩ := not_or.mp h
  have hAc : 1 < A.card := by have := Finset.card_pos.mpr hA; omega
  have hBc : 1 < B.card := by have := Finset.card_pos.mpr hB; omega
  obtain ⟨p, hp, p', hp', hpp⟩ := Finset.one_lt_card.mp hAc
  obtain ⟨l, hl, l', hl', hll⟩ := Finset.one_lt_card.mp hBc
  exact h4 p p' l l' hpp hll ⟨hAB p hp l hl, hAB p hp l' hl',
    hAB p' hp' l hl, hAB p' hp' l' hl'⟩

lemma incidence_biclique_cost {P L : ℕ} (I : Fin P → Fin L → Prop)
    (h4 : ∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (A : Finset (Fin P)) (B : Finset (Fin L))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : ∀ p ∈ A, ∀ l ∈ B, I p l) :
    A.card * B.card = A.card + B.card - 1 := by
  rcases incidence_biclique_star I h4 A B hA hB hAB with h | h
  · rw [h]
    omega
  · rw [h]
    omega

namespace FlatRead

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadK

private def evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
    List α :=
  gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

private lemma evalFrom_cons {α : Type} (d : α) (op : GateOp → List α → α) (g : Gate) (gs : List Gate)
    (xs : List α) :
    evalFrom d op (g :: gs) xs = evalFrom d op gs
      (xs ++ [op g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

private lemma evalFrom_length {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : (evalFrom d op gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalFrom]
  | cons g gs ih => rw [evalFrom_cons, ih]; simp; omega

private lemma evalFrom_input {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (evalFrom d op gs xs).getD i d = xs.getD i d := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [evalFrom_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

private def row (C : Circuit) (k : Fin C.size) : Gate := C.gates[k.val]'k.isLt

private def operand (C : Circuit) (k : Fin C.size) (b : Fin 2) : ℕ :=
  (row C k).inputs.getD b.val 0

private def outWire (n : ℕ) {s : ℕ} (k : Fin s) : ℕ := n + k.val

private lemma inputs_two {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).inputs = [operand C k 0, operand C k 1] := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 (row C k) (List.getElem_mem _))
  simp [operand, hab]

private lemma op_kind {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).op = GateOp.and ∨ (row C k).op = GateOp.or :=
  h.1 (row C k) (List.getElem_mem _)

private lemma earlier {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (k : Fin C.size) (b : Fin 2) : operand C k b < outWire n k := by
  have he : gateAt C k.val = row C k := List.getD_eq_getElem _ _ k.isLt
  have hm : operand C k b ∈ (row C k).inputs := by
    rw [inputs_two h k]
    fin_cases b <;> simp
  exact h.2.1 k.val k.isLt (operand C k b) (by simpa only [he] using hm)

private lemma evalFrom_gate {α : Type} (d : α) (op : GateOp → List α → α) {n : ℕ}
    {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (xs : List α) (hx : xs.length = n)
    (k : Fin C.size) :
    (evalFrom d op C.gates xs).getD (outWire n k) d =
      op (row C k).op ([(evalFrom d op C.gates xs).getD (operand C k 0) d,
        (evalFrom d op C.gates xs).getD (operand C k 1) d]) := by
  let front := evalFrom d op (C.gates.take k.val) xs
  have hf : front.length = outWire n k := by
    have hk : k.val ≤ C.gates.length := k.isLt.le
    simp [front, evalFrom_length, hx, outWire, Nat.min_eq_left hk]
  have hsplit : evalFrom d op C.gates xs =
      evalFrom d op (row C k :: C.gates.drop (k.val + 1)) front := by
    simp only [front, row, evalFrom, ← List.foldl_append, ← List.drop_eq_getElem_cons k.isLt,
      List.take_append_drop]
  have hread (i : ℕ) (hi : i < outWire n k) :
      (evalFrom d op C.gates xs).getD i d = front.getD i d := by
    rw [hsplit, evalFrom_input _ _ _ _ _ (by simpa only [hf] using hi)]
  change (evalFrom d op C.gates xs).getD (outWire n k) d = _
  rw [hread _ (earlier h k 0), hread _ (earlier h k 1), hsplit, evalFrom_cons]
  rw [evalFrom_input _ _ _ _ _ (by simp; omega)]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hf, inputs_two h k]

private lemma wire_cases (n s w : ℕ) :
    w < n ∨ (∃ k : Fin s, w = outWire n k) ∨ n + s ≤ w := by
  by_cases hb : w < n
  · exact Or.inl hb
  by_cases he : w < n + s
  · exact Or.inr (Or.inl ⟨⟨w - n, by omega⟩, by simp [outWire]; omega⟩)
  · exact Or.inr (Or.inr (by omega))

private def wordOp : GateOp → List (Set (List ℕ)) → Set (List ℕ)
  | .or, [a, b] => a ∪ b
  | .and, [a, b] => {t | ∃ u ∈ a, ∃ v ∈ b, t = u ++ v}
  | _, _ => ∅

private def wordList (n : ℕ) (C : Circuit) : List (Set (List ℕ)) :=
  evalFrom ∅ wordOp C.gates (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ))))

private def words (n : ℕ) (C : Circuit) (w : ℕ) : Set (List ℕ) :=
  (wordList n C).getD w ∅

private lemma words_input {n : ℕ} (C : Circuit) {w : ℕ} (hw : w < n) :
    words n C w = {[w]} := by
  unfold words wordList
  have hi : w < (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ)))).length := by
    simpa using hw
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private lemma words_missing (n : ℕ) (C : Circuit) {w : ℕ} (hw : n + C.size ≤ w) :
    words n C w = ∅ :=
  List.getD_eq_default _ _ (by simpa [wordList, evalFrom_length, Circuit.size] using hw)

private lemma words_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    words n C (outWire n k) =
      wordOp (row C k).op [words n C (operand C k 0), words n C (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

private def circuitValue {n : ℕ} (C : Circuit) (z : Fin n → Bool) (w : ℕ) : Bool :=
  (evalFrom false GateOp.eval C.gates (List.ofFn z)).getD w false

private lemma value_input {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ} (hw : w < n) :
    circuitValue C z w = z ⟨w, hw⟩ := by
  have hi : w < (List.ofFn z).length := by simpa using hw
  unfold circuitValue
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private lemma value_missing {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ}
    (hw : n + C.size ≤ w) : circuitValue C z w = false :=
  List.getD_eq_default _ _ (by simpa [evalFrom_length, Circuit.size] using hw)

private lemma value_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (k : Fin C.size) :
    circuitValue C z (outWire n k) = (row C k).op.eval
      [circuitValue C z (operand C k 0), circuitValue C z (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

private lemma value_eq_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (w : ℕ) :
    circuitValue C z w = true ↔
      ∃ t ∈ words n C w, ∀ i ∈ t, ∃ a : Fin n, a.val = i ∧ z a = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [value_input C z hb, words_input C hb]
      constructor
      · intro ht
        exact ⟨[w], rfl, fun i hi => ⟨⟨w, hb⟩, by simpa only [List.mem_singleton, eq_comm] using hi, ht⟩⟩
      · rintro ⟨t, ht, hp⟩
        have ht' : t = [w] := ht
        obtain ⟨a, ha, hz⟩ := hp w (by simp [ht'])
        exact (Fin.ext ha : a = ⟨w, hb⟩) ▸ hz
    · have h1 := ih _ (earlier h k 0)
      have h2 := ih _ (earlier h k 1)
      rw [value_gate h z k, words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho]
        simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
          Bool.and_eq_true, wordOp, Set.mem_ofPred_eq, h1, h2]
        constructor
        · rintro ⟨⟨t, ht, htz⟩, ⟨u, hu, huz⟩⟩
          exact ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, fun i hi =>
            (List.mem_append.mp hi).elim (htz i) (huz i)⟩
        · rintro ⟨_, ⟨t, ht, u, hu, rfl⟩, hh⟩
          exact ⟨⟨t, ht, fun i hi => hh i (List.mem_append_left _ hi)⟩,
            ⟨u, hu, fun i hi => hh i (List.mem_append_right _ hi)⟩⟩
      · rw [ho]
        simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
          Bool.or_eq_true, wordOp, Set.mem_union, h1, h2]
        exact ⟨fun h => h.elim (fun ⟨t, ht, ha⟩ => ⟨t, Or.inl ht, ha⟩)
          (fun ⟨t, ht, ha⟩ => ⟨t, Or.inr ht, ha⟩),
          fun ⟨t, ht, ha⟩ => ht.elim (fun h => Or.inl ⟨t, h, ha⟩) (fun h => Or.inr ⟨t, h, ha⟩)⟩
    · simp [value_missing C z hb, words_missing n C hb]

private lemma mem_insertNew (a v : List ℕ) (A : List (List ℕ)) :
    v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  unfold insertNew
  by_cases ha : a ∈ A
  · simp [ha, or_iff_left_of_imp (fun (e : v = a) => e.symm ▸ ha)]
  · simp [ha]

private lemma mem_fold_insertNew (v : List ℕ) (B A : List (List ℕ)) :
    v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih => simp [ih, mem_insertNew, or_assoc]

private lemma mem_andStep_two (v : List ℕ) (A B : List (List ℕ)) :
    v ∈ andStep 2 A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd 2 u w := by
  simp [andStep, mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

private def encode (S t : List ℕ) : List ℕ :=
  S.map fun j => min (t.count j) 3

private lemma encode_nil (S : List ℕ) : encode S [] = S.map (fun _ => 0) := by
  simp [encode]

private lemma encode_append (S t u : List ℕ) :
    capAdd 2 (encode S t) (encode S u) = encode S (t ++ u) := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    simp only [encode, capAdd, List.map_cons, List.zipWith_cons_cons, List.count_append] at ih ⊢
    rw [ih]
    congr 1
    omega

private def readOp (S : List ℕ) (o : GateOp) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match o with
  | .or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | .and => ins.foldl (andStep 2) [S.map fun _ => 0]
  | _ => []

private def vecs (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
  ((readVectors C n S 2).getD w [])

private lemma vec_eval (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) :
    vecs n C S w =
      (evalFrom [] (readOp S) C.gates ((List.range n).map (leafVectors S 2))).getD w [] :=
  rfl

private lemma encoded_mem {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (w : ℕ) (t : List ℕ) (ht : t ∈ words n C w)
    (hs : ∀ i ∈ t, i ∈ S) : encode S t ∈ vecs n C S w := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      subst t
      have hsw : w ∈ S := hs w (by simp)
      have hi : w < ((List.range n).map (leafVectors S 2)).length := by simpa using hb
      rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
      simp only [List.getElem_map, List.getElem_range, leafVectors, hsw, ite_true,
        List.mem_singleton]
      unfold encode
      apply List.map_congr_left
      intro a _
      by_cases hea : a = w
      · simp [hea]
      · simp [hea, Ne.symm hea]
    · rw [words_gate h k] at ht
      have hlen : ((List.range n).map (leafVectors S 2)).length = n := by simp
      have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
      rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
      rw [hvec]
      rcases op_kind h k with ho | ho
      · rw [ho] at ht ⊢
        obtain ⟨u, hu, v, hv, rfl⟩ := ht
        have hu' := ih _ (earlier h k 0) u hu (fun i hi => hs i (List.mem_append_left _ hi))
        have hv' := ih _ (earlier h k 1) v hv (fun i hi => hs i (List.mem_append_right _ hi))
        change encode S (u ++ v) ∈
          andStep 2 (andStep 2 [S.map (fun _ => 0)] (vecs n C S (operand C k 0)))
            (vecs n C S (operand C k 1))
        apply (mem_andStep_two _ _ _).2
        refine ⟨encode S u, ?_, encode S v, hv', (encode_append S u v).symm⟩
        apply (mem_andStep_two _ _ _).2
        refine ⟨encode S [], by simp [encode_nil], encode S u, hu', ?_⟩
        simp only [encode_append, List.nil_append]
      · rw [ho] at ht ⊢
        change encode S t ∈ (vecs n C S (operand C k 1)).foldl insertNew
          ((vecs n C S (operand C k 0)).foldl insertNew [])
        rw [mem_fold_insertNew, mem_fold_insertNew]
        simp only [List.not_mem_nil, false_or]
        exact ht.elim (fun ht => Or.inl (ih _ (earlier h k 0) t ht hs))
          (fun ht => Or.inr (ih _ (earlier h k 1) t ht hs))
    · simp [words_missing n C hb] at ht

private lemma pure_word_length {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (Q : Set ℕ)
    (hq : ∀ k : Fin C.size, outWire n k ∈ Q →
      (row C k).op = GateOp.or ∧ ∀ b : Fin 2, operand C k b ∈ Q)
    (w : ℕ) (hw : w ∈ Q) (t : List ℕ) (ht : t ∈ words n C w) : t.length = 1 := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      simp [ht']
    · obtain ⟨ho, hins⟩ := hq k hw
      rw [words_gate h k, ho] at ht
      exact ht.elim (fun ht => ih _ (earlier h k 0) (hins 0) t ht)
        (fun ht => ih _ (earlier h k 1) (hins 1) t ht)
    · simp [words_missing n C hb] at ht

private lemma flat_word_length {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (Q : Set ℕ)
    (hq : ∀ k : Fin C.size, outWire n k ∈ Q →
      (row C k).op = GateOp.or ∧ ∀ b : Fin 2, operand C k b ∈ Q)
    (ha : ∀ k : Fin C.size, (row C k).op = GateOp.and →
      ∀ b : Fin 2, operand C k b ∈ Q)
    (w : ℕ) (t : List ℕ) (ht : t ∈ words n C w) : t.length ≤ 2 := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      simp [ht']
    · rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht
        obtain ⟨u, hu, v, hv, rfl⟩ := ht
        have hu' := pure_word_length h Q hq _ (ha k ho 0) u hu
        have hv' := pure_word_length h Q hq _ (ha k ho 1) v hv
        simp [List.length_append, hu', hv']
      · rw [ho] at ht
        exact ht.elim (fun ht => ih _ (earlier h k 0) t ht)
          (fun ht => ih _ (earlier h k 1) t ht)
    · simp [words_missing n C hb] at ht

lemma flat_isReadTwo {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (Q : Set ℕ)
    (hq : ∀ j < C.size, n + j ∈ Q →
      (gateAt C j).op = GateOp.or ∧ ∀ w ∈ (gateAt C j).inputs, w ∈ Q)
    (ha : ∀ j < C.size, (gateAt C j).op = GateOp.and →
      ∀ w ∈ (gateAt C j).inputs, w ∈ Q) : IsReadK n C 2 := by
  have hrow (k : Fin C.size) : gateAt C k.val = row C k :=
    List.getD_eq_getElem _ _ k.isLt
  have hop (k : Fin C.size) (b : Fin 2) : operand C k b ∈ (row C k).inputs := by
    rw [inputs_two h k]
    fin_cases b <;> simp
  have hq' : ∀ k : Fin C.size, outWire n k ∈ Q →
      (row C k).op = GateOp.or ∧ ∀ b : Fin 2, operand C k b ∈ Q := by
    intro k hk
    obtain ⟨ho, hi⟩ := hq k.val k.isLt hk
    rw [hrow k] at ho hi
    exact ⟨ho, fun b => hi _ (hop k b)⟩
  have ha' : ∀ k : Fin C.size, (row C k).op = GateOp.and →
      ∀ b : Fin 2, operand C k b ∈ Q := by
    intro k hk b
    apply ha k.val k.isLt
    · simpa only [hrow k] using hk
    · simpa only [hrow k] using hop k b
  intro S hS
  obtain ⟨t, ht, hts⟩ := (value_eq_terms h (setInput S) C.output).1 hS.1
  have hlen := flat_word_length h Q hq' ha' C.output t ht
  have hs : ∀ i ∈ t, i ∈ setList S := by
    intro i hi
    obtain ⟨a, rfl, ha⟩ := hts i hi
    have hamem : a ∈ S := of_decide_eq_true ha
    simp only [setList, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq]
    exact ⟨a, hamem, rfl⟩
  apply List.any_eq_true.mpr
  refine ⟨encode (setList S) t, encoded_mem h _ _ _ ht hs, ?_⟩
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  apply decide_eq_true
  have hc := List.count_le_length (l := t) (a := i)
  exact (Nat.min_le_left _ _).trans (hc.trans hlen)

lemma separated_isReadTwo {P L : ℕ} {C : Circuit}
    (h : PEqualNP.TopForm.IsAO2 (P + L) C) (A B : Finset ℕ)
    (hA : ∀ w ∈ A, w < P ∨ ∃ j < C.gates.length, w = P + L + j ∧
      (gateAt C j).op = GateOp.or ∧ ∀ u ∈ (gateAt C j).inputs, u ∈ A)
    (hB : ∀ w ∈ B, (P ≤ w ∧ w < P + L) ∨ ∃ j < C.gates.length, w = P + L + j ∧
      (gateAt C j).op = GateOp.or ∧ ∀ u ∈ (gateAt C j).inputs, u ∈ B)
    (hAnd : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∃ a b, (gateAt C j).inputs = [a, b] ∧
        ((a ∈ A ∧ b ∈ B) ∨ (a ∈ B ∧ b ∈ A))) : IsReadK (P + L) C 2 := by
  apply flat_isReadTwo h {w | w ∈ A ∨ w ∈ B}
  · intro j hj hq
    rcases hq with hq | hq
    · rcases hA _ hq with hb | ⟨k, hk, he, ho, hi⟩
      · omega
      · have heq : j = k := by omega
        subst k
        exact ⟨ho, fun w hw => Or.inl (hi w hw)⟩
    · rcases hB _ hq with hb | ⟨k, hk, he, ho, hi⟩
      · omega
      · have heq : j = k := by omega
        subst k
        exact ⟨ho, fun w hw => Or.inr (hi w hw)⟩
  · intro j hj hand w hw
    obtain ⟨a, b, hab, hmem⟩ := hAnd j hj hand
    rw [hab] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> rcases hmem with hmem | hmem
    · exact Or.inl hmem.1
    · exact Or.inr hmem.1
    · exact Or.inr hmem.2
    · exact Or.inl hmem.2

private lemma count_lt_length_of_mem_ne (t : List ℕ) (i j : ℕ)
    (hj : j ∈ t) (hji : j ≠ i) : t.count i < t.length := by
  induction t with
  | nil => simp at hj
  | cons a t ih =>
    by_cases hai : a = i
    · subst a
      have hj' : j ∈ t := (List.mem_cons.mp hj).resolve_left hji
      have hlt := ih hj'
      simp only [List.count_cons_self, List.length_cons]
      omega
    · have hle := List.count_le_length (l := t) (a := i)
      simp [hai]
      omega

lemma short_isReadTwo {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (hsingle : ∀ a : Fin n, circuitFun n C (fun b => decide (b = a)) = false)
    (hshort : ∀ t ∈ words n C C.output, t.length ≤ 3) : IsReadK n C 2 := by
  intro S hS
  obtain ⟨t, ht, hts⟩ := (value_eq_terms h (setInput S) C.output).1 hS.1
  have hlen := hshort t ht
  have hcount (i : ℕ) : t.count i ≤ 2 := by
    by_contra hn
    have himem : i ∈ t := List.count_pos_iff.mp (by omega)
    obtain ⟨a, hai, _⟩ := hts i himem
    have hother : ∃ j ∈ t, j ≠ i := by
      by_contra hno
      have hall (j : ℕ) (hj : j ∈ t) : j = i := by
        by_contra hji
        exact hno ⟨j, hj, hji⟩
      have htrue : circuitValue C (fun b => decide (b = a)) C.output = true := by
        apply (value_eq_terms h _ _).2
        refine ⟨t, ht, ?_⟩
        intro j hj
        exact ⟨a, hai.trans (hall j hj).symm, by simp⟩
      have hfalse : circuitValue C (fun b => decide (b = a)) C.output = false := hsingle a
      exact Bool.false_ne_true (hfalse.symm.trans htrue)
    obtain ⟨j, hj, hji⟩ := hother
    have hlt := count_lt_length_of_mem_ne t i j hj hji
    omega
  have hs : ∀ i ∈ t, i ∈ setList S := by
    intro i hi
    obtain ⟨a, rfl, ha⟩ := hts i hi
    have hamem : a ∈ S := of_decide_eq_true ha
    simp only [setList, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq]
    exact ⟨a, hamem, rfl⟩
  apply List.any_eq_true.mpr
  refine ⟨encode (setList S) t, encoded_mem h _ _ _ ht hs, ?_⟩
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  exact decide_eq_true ((Nat.min_le_left _ _).trans (hcount i))


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



private def desc (n : ℕ) (C : Circuit) (w j : ℕ) : Prop :=
  ∃ k : Fin C.size, w = outWire n k ∧ (j = k.val ∨ InCone n C j k.val)

private lemma desc_operand {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (k : Fin C.size) (b : Fin 2) {j : ℕ}
    (hd : desc n C (operand C k b) j) : InCone n C j k.val := by
  obtain ⟨r, hr, hj⟩ := hd
  apply (inCone_iff n C j k.val).mpr
  have he : gateAt C k.val = row C k := List.getD_eq_getElem _ _ k.isLt
  have hm : operand C k b ∈ (row C k).inputs := by
    rw [inputs_two h k]
    fin_cases b <;> simp
  refine ⟨k.isLt, r.val, ?_, ?_, hj⟩
  · have hb := earlier h k b
    dsimp [outWire] at hr hb
    omega
  · rw [he]
    change outWire n r ∈ (row C k).inputs
    rw [← hr]
    exact hm

private lemma one_and_word {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (g w : ℕ)
    (hq : ∀ k : Fin C.size, desc n C w k.val → (row C k).op = GateOp.and → k.val = g)
    (t : List ℕ) (ht : t ∈ words n C w) :
    t.length = 1 ∨ (t.length = 2 ∧ n + g ≤ w ∧
      ∀ z : Fin n → Bool, circuitValue C z (n + g) = true → circuitValue C z w = true) := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      simp [ht']
    · have hchild (b : Fin 2) : ∀ i : Fin C.size,
          desc n C (operand C k b) i.val → (row C i).op = GateOp.and → i.val = g := by
        intro i hi hiand
        exact hq i ⟨k, rfl, Or.inr (desc_operand h k b hi)⟩ hiand
      rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · have hkg := hq k ⟨k, rfl, Or.inl rfl⟩ ho
        rw [ho] at ht
        obtain ⟨u, hu, v, hv, rfl⟩ := ht
        have hu' := ih _ (earlier h k 0) (hchild 0) u hu
        have hv' := ih _ (earlier h k 1) (hchild 1) v hv
        have hlen0 : u.length = 1 := by
          rcases hu' with hlen | ⟨_, hge, _⟩
          · exact hlen
          · have hb := earlier h k 0
            dsimp [outWire] at hb
            omega
        have hlen1 : v.length = 1 := by
          rcases hv' with hlen | ⟨_, hge, _⟩
          · exact hlen
          · have hb := earlier h k 1
            dsimp [outWire] at hb
            omega
        right
        refine ⟨by simp [hlen0, hlen1], ?_, ?_⟩
        · dsimp [outWire]
          omega
        · intro z hz
          simpa [outWire, hkg] using hz
      · rw [ho] at ht
        rcases ht with ht | ht
        · rcases ih _ (earlier h k 0) (hchild 0) t ht with hlen | ⟨hlen, hge, hval⟩
          · exact Or.inl hlen
          · refine Or.inr ⟨hlen, hge.trans (earlier h k 0).le, ?_⟩
            intro z hz
            rw [value_gate h z k, ho]
            simp [GateOp.eval, hval z hz]
        · rcases ih _ (earlier h k 1) (hchild 1) t ht with hlen | ⟨hlen, hge, hval⟩
          · exact Or.inl hlen
          · refine Or.inr ⟨hlen, hge.trans (earlier h k 1).le, ?_⟩
            intro z hz
            rw [value_gate h z k, ho]
            simp [GateOp.eval, hval z hz]
    · simp [words_missing n C hb] at ht

private lemma one_junk_word_length {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (hTop : PEqualNP.TopForm.TopForm G C) (g : ℕ)
    (hdirty : ¬ PEqualNP.TopForm.BelowF G C g)
    (hjunk : ∀ k : Fin C.size, (row C k).op = GateOp.and →
      ¬ PEqualNP.TopForm.BelowF G C k.val → k.val = g)
    (w : ℕ)
    (hbelow : ∀ z : Fin n → Bool, circuitValue C z w = true → graphFun G ∅ z = true)
    (t : List ℕ) (ht : t ∈ words n C w) : t.length ≤ 3 := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      simp [ht']
    · rw [words_gate h k] at ht
      have hrow (i : Fin C.size) : gateAt C i.val = row C i :=
        List.getD_eq_getElem _ _ i.isLt
      rcases op_kind h k with ho | ho
      · have hchild (b : Fin 2) : ∀ i : Fin C.size,
            desc n C (operand C k b) i.val → (row C i).op = GateOp.and → i.val = g := by
          intro i hi hiand
          apply hjunk i hiand
          intro hib
          apply hTop i.val i.isLt k.val k.isLt
          · simpa only [hrow i] using hiand
          · exact hib
          · simpa only [hrow k] using ho
          · exact desc_operand h k b hi
        rw [ho] at ht
        obtain ⟨u, hu, v, hv, rfl⟩ := ht
        have hu' := one_and_word h g _ (hchild 0) u hu
        have hv' := one_and_word h g _ (hchild 1) v hv
        rcases hu' with hlen0 | ⟨hlen0, _, hval0⟩
        · rcases hv' with hlen1 | ⟨hlen1, _, _⟩ <;> simp [List.length_append, hlen0, hlen1]
        · rcases hv' with hlen1 | ⟨hlen1, _, hval1⟩
          · simp [List.length_append, hlen0, hlen1]
          · exfalso
            apply hdirty
            intro z hz
            apply hbelow z
            rw [value_gate h z k, ho]
            have hz' : circuitValue C z (n + g) = true := hz
            simp [GateOp.eval, hval0 z hz', hval1 z hz']
      · rw [ho] at ht
        rcases ht with ht | ht
        · apply ih _ (earlier h k 0) _ t ht
          intro z hz
          apply hbelow z
          rw [value_gate h z k, ho]
          simp [GateOp.eval, hz]
        · apply ih _ (earlier h k 1) _ t ht
          intro z hz
          apply hbelow z
          rw [value_gate h z k, ho]
          simp [GateOp.eval, hz]
    · simp [words_missing n C hb] at ht

lemma one_junk_isReadTwo {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (hTop : PEqualNP.TopForm.TopForm G C) (g : ℕ)
    (hjunk : PEqualNP.TopForm.junk G C = {g})
    (hf : circuitFun n C = graphFun G ∅) : IsReadK n C 2 := by
  have hrow (i : Fin C.size) : gateAt C i.val = row C i :=
    List.getD_eq_getElem _ _ i.isLt
  have hgmem : g ∈ PEqualNP.TopForm.junk G C := by
    rw [hjunk]
    simp
  have hgdirty : PEqualNP.CleanedNonEdge.IsDirtyAnd n G C g :=
    (Finset.mem_filter.mp hgmem).2
  obtain ⟨z, hz, hzF⟩ := hgdirty.2.2
  have hdirty : ¬ PEqualNP.TopForm.BelowF G C g := by
    intro hb
    have hh := hb z hz
    rw [hzF] at hh
    cases hh
  have hj : ∀ k : Fin C.size, (row C k).op = GateOp.and →
      ¬ PEqualNP.TopForm.BelowF G C k.val → k.val = g := by
    intro k hkind hnot
    have hk : k.val ∈ PEqualNP.TopForm.junk G C := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr k.isLt, ?_⟩
      refine ⟨?_, k.isLt, ?_⟩
      · simpa only [hrow k] using hkind
      · by_contra hno
        apply hnot
        intro z hz
        by_cases hval : graphFun G ∅ z = true
        · exact hval
        · exact False.elim (hno ⟨z, hz, by simpa using hval⟩)
    rw [hjunk] at hk
    exact Finset.mem_singleton.mp hk
  apply short_isReadTwo h
  · intro a
    rw [hf]
    simp [graphFun, SimpleGraph.irrefl]
  · intro t ht
    apply one_junk_word_length G h hTop g hdirty hj C.output _ t ht
    intro z hz
    exact (congrFun hf z).symm.trans hz


private lemma desc_input {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (k : Fin C.size) {w j : ℕ} (hw : w ∈ (row C k).inputs)
    (hd : desc n C w j) : InCone n C j k.val := by
  obtain ⟨r, hr, hj⟩ := hd
  have he : gateAt C k.val = row C k := List.getD_eq_getElem _ _ k.isLt
  have hb : w < n + k.val := h.2.1 k.val k.isLt w (by simpa only [he] using hw)
  apply (inCone_iff n C j k.val).mpr
  refine ⟨k.isLt, r.val, ?_, ?_, hj⟩
  · dsimp [outWire] at hr
    omega
  · rw [he]
    change outWire n r ∈ (row C k).inputs
    rw [← hr]
    exact hw

lemma no_junk_isReadTwo {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (hTop : PEqualNP.TopForm.TopForm G C)
    (hjunk : PEqualNP.TopForm.junk G C = ∅) : IsReadK n C 2 := by
  have hrow (i : Fin C.size) : gateAt C i.val = row C i :=
    List.getD_eq_getElem _ _ i.isLt
  have hclean (k : Fin C.size) (hk : (row C k).op = GateOp.and) :
      PEqualNP.TopForm.BelowF G C k.val := by
    intro z hz
    by_contra hno
    have hm : k.val ∈ PEqualNP.TopForm.junk G C := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr k.isLt, ?_⟩
      refine ⟨?_, k.isLt, z, hz, ?_⟩
      · simpa only [hrow k] using hk
      · simpa using hno
    rw [hjunk] at hm
    exact Finset.notMem_empty k.val hm
  let Q : Set ℕ := {w | ∀ k : Fin C.size, desc n C w k.val →
    (row C k).op = GateOp.and → False}
  apply flat_isReadTwo h Q
  · intro j hj hw
    let k : Fin C.size := ⟨j, hj⟩
    have hk : gateAt C j = row C k := List.getD_eq_getElem _ _ hj
    have ho : (row C k).op = GateOp.or := by
      rcases op_kind h k with ho | ho
      · exact False.elim (hw k ⟨k, rfl, Or.inl rfl⟩ ho)
      · exact ho
    refine ⟨by simpa only [hk] using ho, ?_⟩
    intro u hu i hi hiand
    exact hw i ⟨k, rfl, Or.inr (desc_input h k (by simpa only [hk] using hu) hi)⟩ hiand
  · intro j hj hand u hu i hi hiand
    let k : Fin C.size := ⟨j, hj⟩
    have hk : gateAt C j = row C k := List.getD_eq_getElem _ _ hj
    apply hTop i.val i.isLt j hj
    · simpa only [hrow i] using hiand
    · exact hclean i hiand
    · exact hand
    · exact desc_input h k (by simpa only [hk] using hu) hi

lemma at_most_one_junk_isReadTwo {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (hTop : PEqualNP.TopForm.TopForm G C)
    (hjunk : (PEqualNP.TopForm.junk G C).card ≤ 1)
    (hf : circuitFun n C = graphFun G ∅) : IsReadK n C 2 := by
  by_cases he : PEqualNP.TopForm.junk G C = ∅
  · exact no_junk_isReadTwo G h hTop he
  · obtain ⟨g, hg⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hsg : PEqualNP.TopForm.junk G C = {g} := by
      apply Finset.ext
      intro a
      simp only [Finset.mem_singleton]
      constructor
      · intro ha
        exact Finset.card_le_one.mp hjunk a ha g hg
      · intro ha
        simpa [ha] using hg
    exact one_junk_isReadTwo G h hTop g hsg hf


lemma prime_short_isReadTwo {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (hsingle : ∀ a : Fin n, circuitFun n C (fun b => decide (b = a)) = false)
    (hshort : ∀ S : Finset (Fin n), IsPrimeImplicant n C S →
      ∃ t ∈ words n C C.output, t.length ≤ 3 ∧
        ∀ i ∈ t, ∃ a : Fin n, a.val = i ∧ a ∈ S) : IsReadK n C 2 := by
  intro S hS
  obtain ⟨t, ht, hlen, hts⟩ := hshort S hS
  have hcount (i : ℕ) : t.count i ≤ 2 := by
    by_contra hn
    have himem : i ∈ t := List.count_pos_iff.mp (by omega)
    obtain ⟨a, hai, _⟩ := hts i himem
    have hother : ∃ j ∈ t, j ≠ i := by
      by_contra hno
      have hall (j : ℕ) (hj : j ∈ t) : j = i := by
        by_contra hji
        exact hno ⟨j, hj, hji⟩
      have htrue : circuitValue C (fun b => decide (b = a)) C.output = true := by
        apply (value_eq_terms h _ _).2
        refine ⟨t, ht, ?_⟩
        intro j hj
        exact ⟨a, hai.trans (hall j hj).symm, by simp⟩
      have hfalse : circuitValue C (fun b => decide (b = a)) C.output = false := hsingle a
      exact Bool.false_ne_true (hfalse.symm.trans htrue)
    obtain ⟨j, hj, hji⟩ := hother
    have hlt := count_lt_length_of_mem_ne t i j hj hji
    omega
  have hs : ∀ i ∈ t, i ∈ setList S := by
    intro i hi
    obtain ⟨a, rfl, ha⟩ := hts i hi
    have hamem : a ∈ S := ha
    simp only [setList, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq]
    exact ⟨a, hamem, rfl⟩
  apply List.any_eq_true.mpr
  refine ⟨encode (setList S) t, encoded_mem h _ _ _ ht hs, ?_⟩
  apply List.all_eq_true.mpr
  intro a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  exact decide_eq_true ((Nat.min_le_left _ _).trans (hcount i))


private lemma local_junk_word_length {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (hlocal : ∀ k : Fin C.size, (row C k).op = GateOp.and →
      PEqualNP.TopForm.BelowF G C k.val → ∃ g : ℕ,
        (¬ PEqualNP.TopForm.BelowF G C g ∨ C.size ≤ g) ∧
        ∀ i : Fin C.size, InCone n C i.val k.val → (row C i).op = GateOp.and → i.val = g)
    (w : ℕ)
    (hbelow : ∀ z : Fin n → Bool, circuitValue C z w = true → graphFun G ∅ z = true)
    (t : List ℕ) (ht : t ∈ words n C w) : t.length ≤ 3 := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      simp [ht']
    · rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · obtain ⟨g, hdirty, hjunk⟩ := hlocal k ho hbelow
        have hchild (b : Fin 2) : ∀ i : Fin C.size,
            desc n C (operand C k b) i.val → (row C i).op = GateOp.and → i.val = g := by
          intro i hi hiand
          exact hjunk i (desc_operand h k b hi) hiand
        rw [ho] at ht
        obtain ⟨u, hu, v, hv, rfl⟩ := ht
        have hu' := one_and_word h g _ (hchild 0) u hu
        have hv' := one_and_word h g _ (hchild 1) v hv
        rcases hu' with hlen0 | ⟨hlen0, hge0, hval0⟩
        · rcases hv' with hlen1 | ⟨hlen1, _, _⟩ <;> simp [List.length_append, hlen0, hlen1]
        · rcases hv' with hlen1 | ⟨hlen1, _, hval1⟩
          · simp [List.length_append, hlen0, hlen1]
          · exfalso
            rcases hdirty with hdirty | hout
            · apply hdirty
              intro z hz
              apply hbelow z
              rw [value_gate h z k, ho]
              have hz' : circuitValue C z (n + g) = true := hz
              simp [GateOp.eval, hval0 z hz', hval1 z hz']
            · have he := earlier h k 0
              have hk := k.isLt
              dsimp [outWire] at he
              omega
      · rw [ho] at ht
        rcases ht with ht | ht
        · apply ih _ (earlier h k 0) _ t ht
          intro z hz
          apply hbelow z
          rw [value_gate h z k, ho]
          simp [GateOp.eval, hz]
        · apply ih _ (earlier h k 1) _ t ht
          intro z hz
          apply hbelow z
          rw [value_gate h z k, ho]
          simp [GateOp.eval, hz]
    · simp [words_missing n C hb] at ht

lemma one_junk_per_top_isReadTwo {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (hTop : PEqualNP.TopForm.TopForm G C)
    (hlocal : ∀ a ∈ PEqualNP.TopForm.tops G C,
      ((PEqualNP.TopForm.junk G C).filter fun j => InCone n C j a).card ≤ 1)
    (hf : circuitFun n C = graphFun G ∅) : IsReadK n C 2 := by
  letI : DecidableEq GateOp := gateOpDecEq
  classical
  have hrow (i : Fin C.size) : gateAt C i.val = row C i :=
    List.getD_eq_getElem _ _ i.isLt
  have hlocal' : ∀ k : Fin C.size, (row C k).op = GateOp.and →
      PEqualNP.TopForm.BelowF G C k.val → ∃ g : ℕ,
        (¬ PEqualNP.TopForm.BelowF G C g ∨ C.size ≤ g) ∧
        ∀ i : Fin C.size, InCone n C i.val k.val → (row C i).op = GateOp.and → i.val = g := by
    intro k hk hkb
    have hkmem : k.val ∈ PEqualNP.TopForm.tops G C := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr k.isLt, by simpa only [hrow k] using hk, hkb⟩
    let J : Finset ℕ := (PEqualNP.TopForm.junk G C).filter fun j => InCone n C j k.val
    have hcard : J.card ≤ 1 := hlocal k.val hkmem
    have hmem (i : Fin C.size) (hi : InCone n C i.val k.val)
        (hiand : (row C i).op = GateOp.and) : i.val ∈ J := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, hi⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr i.isLt, ?_⟩
      refine ⟨by simpa only [hrow i] using hiand, i.isLt, ?_⟩
      by_contra hno
      apply hTop i.val i.isLt k.val k.isLt
      · simpa only [hrow i] using hiand
      · intro z hz
        by_cases hval : graphFun G ∅ z = true
        · exact hval
        · exact False.elim (hno ⟨z, hz, by simpa using hval⟩)
      · simpa only [hrow k] using hk
      · exact hi
    by_cases he : J = ∅
    · refine ⟨C.size, Or.inr le_rfl, ?_⟩
      intro i hi hiand
      have hm := hmem i hi hiand
      rw [he] at hm
      exact False.elim (Finset.notMem_empty i.val hm)
    · obtain ⟨g, hg⟩ := Finset.nonempty_iff_ne_empty.mpr he
      have hgJ : g ∈ PEqualNP.TopForm.junk G C := (Finset.mem_filter.mp hg).1
      have hgd : PEqualNP.CleanedNonEdge.IsDirtyAnd n G C g :=
        (Finset.mem_filter.mp hgJ).2
      obtain ⟨z, hz, hzF⟩ := hgd.2.2
      refine ⟨g, Or.inl ?_, ?_⟩
      · intro hb
        have hh := hb z hz
        rw [hzF] at hh
        cases hh
      · intro i hi hiand
        exact Finset.card_le_one.mp hcard i.val (hmem i hi hiand) g hg
  apply short_isReadTwo h
  · intro a
    rw [hf]
    simp [graphFun, SimpleGraph.irrefl]
  · intro t ht
    apply local_junk_word_length G h hlocal' C.output _ t ht
    intro z hz
    exact (congrFun hf z).symm.trans hz


lemma two_dirty_in_some_top_of_not_read {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (hTop : PEqualNP.TopForm.TopForm G C) (hf : circuitFun n C = graphFun G ∅)
    (hnot : ¬ IsReadK n C 2) :
    ∃ a ∈ PEqualNP.TopForm.tops G C,
      2 ≤ ((PEqualNP.TopForm.junk G C).filter fun j => InCone n C j a).card := by
  by_contra hn
  apply hnot
  apply one_junk_per_top_isReadTwo G h hTop _ hf
  intro a ha
  by_contra hc
  exact hn ⟨a, ha, by omega⟩


end FlatRead


namespace CoverForm_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Inv (p q : ℕ → Prop) (B : ℕ) (L : List Gate) (S T : Finset ℕ) : Prop :=
  (∀ (k : ℕ) (g : Gate), L[k]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧
    ∀ i ∈ g.inputs, i < B + k) ∧
  (∀ w ∈ S, ∃ (k : ℕ) (g : Gate), L[k]? = some g ∧ w = B + k ∧ g.op = GateOp.or ∧ ∀ i ∈ g.inputs, p i ∨ i ∈ S) ∧
  (∀ w ∈ T, ∃ (k : ℕ) (g : Gate), L[k]? = some g ∧ w = B + k ∧ g.op = GateOp.or ∧ ∀ i ∈ g.inputs, q i ∨ i ∈ T) ∧
  (∀ (k : ℕ) (g : Gate), L[k]? = some g → g.op = GateOp.and → ∃ a b, g.inputs = [a, b] ∧
     (((p a ∨ a ∈ S) ∧ (q b ∨ b ∈ T)) ∨ ((q a ∨ a ∈ T) ∧ (p b ∨ b ∈ S))))

lemma inv_swap {p q : ℕ → Prop} {B : ℕ} {L : List Gate} {S T : Finset ℕ}
    (h : Inv p q B L S T) : Inv q p B L T S := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h3, h2, ?_⟩
  intro k g hk ho
  obtain ⟨a, b, e, h⟩ := h4 k g hk ho
  exact ⟨a, b, e, h.symm⟩

lemma inv_nil (p q : ℕ → Prop) (B : ℕ) : Inv p q B [] ∅ ∅ := by
  simp [Inv]

lemma app_cases {L1 L2 : List Gate} {k : ℕ} {g : Gate} (h : (L1 ++ L2)[k]? = some g) :
    L1[k]? = some g ∨ ∃ k2, k = L1.length + k2 ∧ L2[k2]? = some g := by
  rw [List.getElem?_append] at h
  split at h
  · exact Or.inl h
  · exact Or.inr ⟨k - L1.length, by omega, h⟩

lemma app_left {L1 L2 : List Gate} {k : ℕ} {g : Gate} (h : L1[k]? = some g) :
    (L1 ++ L2)[k]? = some g := by
  have hk : k < L1.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.getElem?_append_left hk]
  exact h

lemma app_right {L1 L2 : List Gate} {k : ℕ} {g : Gate} (h : L2[k]? = some g) :
    (L1 ++ L2)[L1.length + k]? = some g := by
  rw [List.getElem?_append_right (by omega)]
  simpa using h

lemma inv_app {p q : ℕ → Prop} {B : ℕ} {L1 L2 : List Gate} {S1 T1 S2 T2 : Finset ℕ}
    (h : Inv p q B L1 S1 T1) (h' : Inv p q (B + L1.length) L2 S2 T2) :
    Inv p q B (L1 ++ L2) (S1 ∪ S2) (T1 ∪ T2) := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := h'
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k g hk
    rcases app_cases hk with h | ⟨k2, rfl, h⟩
    · exact a1 k g h
    · obtain ⟨x, y, z⟩ := b1 k2 g h
      exact ⟨x, y, fun i hi => by have := z i hi; omega⟩
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨k, g, e1, e2, e3, e4⟩ := a2 w hw
      exact ⟨k, g, app_left e1, e2, e3, fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_left _ h)⟩
    · obtain ⟨k, g, e1, e2, e3, e4⟩ := b2 w hw
      exact ⟨L1.length + k, g, app_right e1, by omega, e3,
        fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_right _ h)⟩
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨k, g, e1, e2, e3, e4⟩ := a3 w hw
      exact ⟨k, g, app_left e1, e2, e3, fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_left _ h)⟩
    · obtain ⟨k, g, e1, e2, e3, e4⟩ := b3 w hw
      exact ⟨L1.length + k, g, app_right e1, by omega, e3,
        fun i hi => (e4 i hi).imp id (fun h => Finset.mem_union_right _ h)⟩
  · intro k g hk ho
    rcases app_cases hk with h | ⟨k2, rfl, h⟩
    · obtain ⟨a, b, e, hh⟩ := a4 k g h ho
      refine ⟨a, b, e, ?_⟩
      simp only [Finset.mem_union]
      tauto
    · obtain ⟨a, b, e, hh⟩ := b4 k2 g h ho
      refine ⟨a, b, e, ?_⟩
      simp only [Finset.mem_union]
      tauto

lemma cval (B v1 m i : ℕ) (hi : i ≤ m) :
    (i = 0 ∧ (v1 :: (List.range m).map (fun j => B + j)).getD i 0 = v1) ∨
    (0 < i ∧ (v1 :: (List.range m).map (fun j => B + j)).getD i 0 = B + (i - 1)) := by
  cases i with
  | zero => left; simp
  | succ j =>
    right
    have hj : j < m := by omega
    simp [List.getD_eq_getElem?_getD, hj]

lemma block_get {B a t v1 : ℕ} {rest : List ℕ} {lead : Bool} {k : ℕ} {g : Gate}
    (h : (blockGates B a t v1 rest lead)[k]? = some g) :
    (k < rest.length ∧ g = ⟨GateOp.or,
      [(v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0, rest.getD k 0]⟩) ∨
    (k = rest.length ∧ g = ⟨GateOp.and,
      [t, (v1 :: (List.range rest.length).map (fun j => B + j)).getD rest.length 0]⟩) ∨
    (k = rest.length + 1 ∧ lead = false ∧ g = ⟨GateOp.or, [a, B + rest.length]⟩) := by
  unfold blockGates at h
  rcases app_cases h with h | ⟨k2, hk, h⟩
  · left
    have hk : k < rest.length := by
      have := (List.getElem?_eq_some_iff.mp h).1
      simpa using this
    refine ⟨hk, ?_⟩
    simp only [List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.some.injEq] at h
    exact h.symm
  · right
    simp only [List.length_map, List.length_range] at hk
    cases k2 with
    | zero =>
      left
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      exact ⟨by omega, h.symm⟩
    | succ k3 =>
      right
      cases lead with
      | true => simp at h
      | false =>
        cases k3 with
        | zero =>
          simp only [List.getElem?_cons_succ, Bool.false_eq_true, ite_false,
            List.getElem?_cons_zero, Option.some.injEq] at h
          exact ⟨by omega, rfl, h.symm⟩
        | succ k4 => simp at h

lemma block_chain {B a t v1 : ℕ} {rest : List ℕ} {lead : Bool} {k : ℕ} (hk : k < rest.length) :
    (blockGates B a t v1 rest lead)[k]? = some ⟨GateOp.or,
      [(v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0, rest.getD k 0]⟩ := by
  unfold blockGates
  apply app_left
  simp [hk]

lemma rest_mem {rest : List ℕ} {k : ℕ} (hk : k < rest.length) : rest.getD k 0 ∈ rest := by
  simp [List.getD_eq_getElem?_getD, hk]

lemma inv_block {p q : ℕ → Prop} {B a t v1 : ℕ} {rest : List ℕ} {lead : Bool}
    (hp : ∀ i, p i → i < B) (hq : ∀ i, q i → i < B) (ha : lead = false → a < B)
    (ht : q t) (hv : p v1) (hr : ∀ v ∈ rest, p v) :
    Inv p q B (blockGates B a t v1 rest lead)
      ((Finset.range rest.length).image (fun j => B + j)) ∅ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k g hk
    rcases block_get hk with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
    · refine ⟨Or.inr rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · rcases cval B v1 rest.length k (by omega) with ⟨_, e⟩ | ⟨h0, e⟩
        · rw [e]; have := hp _ hv; omega
        · rw [e]; omega
      · have := hp _ (hr _ (rest_mem h1)); omega
    · refine ⟨Or.inl rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · have := hq _ ht; omega
      · rcases cval B v1 rest.length rest.length (le_refl _) with ⟨_, e⟩ | ⟨h0, e⟩
        · rw [e]; have := hp _ hv; omega
        · rw [e]; omega
    · refine ⟨Or.inr rfl, rfl, ?_⟩
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      have := ha h2
      rcases hi with rfl | rfl <;> omega
  · intro w hw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
    have hk : k < rest.length := Finset.mem_range.mp hk
    refine ⟨k, _, block_chain hk, rfl, rfl, ?_⟩
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · rcases cval B v1 rest.length k (by omega) with ⟨_, e⟩ | ⟨h0, e⟩
      · rw [e]; exact Or.inl hv
      · rw [e]; right
        exact Finset.mem_image.mpr ⟨k - 1, Finset.mem_range.mpr (by omega), rfl⟩
    · exact Or.inl (hr _ (rest_mem hk))
  · intro w hw
    simp at hw
  · intro k g hk ho
    rcases block_get hk with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩
    · simp at ho
    · refine ⟨_, _, rfl, Or.inr ⟨Or.inl ht, ?_⟩⟩
      rcases cval B v1 rest.length rest.length (le_refl _) with ⟨_, e⟩ | ⟨h0, e⟩
      · rw [e]; exact Or.inl hv
      · rw [e]; right
        exact Finset.mem_image.mpr ⟨rest.length - 1, Finset.mem_range.mpr (by omega), rfl⟩
    · simp at ho

lemma block_len (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    1 ≤ (blockGates B a t v1 rest lead).length := by
  unfold blockGates
  simp
  omega

lemma inv_cover (p q : ℕ → Prop) (own : List (ℕ × List ℕ)) :
    ∀ (B : ℕ) (lead : Bool) (a : ℕ), (∀ i, p i → i < B) → (∀ i, q i → i < B) →
      (lead = false → a < B) →
      (∀ o ∈ own, (q o.1 ∧ ∀ v ∈ o.2, p v) ∨ (p o.1 ∧ ∀ v ∈ o.2, q v)) →
      ∃ S T, Inv p q B (coverGatesB B lead a own) S T := by
  induction own with
  | nil =>
    intro B lead a _ _ _ _
    exact ⟨∅, ∅, by simpa [coverGatesB] using inv_nil p q B⟩
  | cons o os ih =>
    intro B lead a hp hq ha ho
    obtain ⟨t, l⟩ := o
    have hos : ∀ o ∈ os, (q o.1 ∧ ∀ v ∈ o.2, p v) ∨ (p o.1 ∧ ∀ v ∈ o.2, q v) :=
      fun o h => ho o (List.mem_cons_of_mem _ h)
    cases l with
    | nil =>
      simp only [coverGatesB]
      exact ih B lead a hp hq ha hos
    | cons v1 rest =>
      simp only [coverGatesB]
      have hl := block_len B a t v1 rest lead
      obtain ⟨S2, T2, h2⟩ := ih (B + (blockGates B a t v1 rest lead).length) false
        (B + (blockGates B a t v1 rest lead).length - 1)
        (fun i h => by have := hp i h; omega) (fun i h => by have := hq i h; omega)
        (fun _ => by omega) hos
      have h0 := ho (t, v1 :: rest) List.mem_cons_self
      simp only [List.mem_cons, forall_eq_or_imp] at h0
      rcases h0 with ⟨h1, h3, h4⟩ | ⟨h1, h3, h4⟩
      · exact ⟨_, _, inv_app (inv_block hp hq ha h1 h3 h4) h2⟩
      · exact ⟨_, _, inv_app (inv_swap (inv_block hq hp ha h1 h3 h4)) h2⟩

lemma gates_eq (n : ℕ) (own : List (ℕ × List ℕ)) :
    (coverCircuitB n own).gates = coverGatesB n true 0 own := by
  unfold coverCircuitB
  split <;> simp_all

lemma gateAt_get (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    C.gates[j]? = some (PEqualNP.MetaComplexity.NestedCover.gateAt C j) := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  simp [List.getD_eq_getElem?_getD, hj]

end CoverForm_aux

open PEqualNP.Outside.L_meta_2584.CoverForm_aux
namespace CoverForm

lemma cover_form : ∀ (x1 x2 : ℕ) (x3 : List (ℕ × List ℕ)),   have x4 : ℕ := x1 + x2;   (∀ x5 ∈ x3, x5.2 ≠ [] ∧ ((x5.1 < x1 ∧ ∀ x7 ∈ x5.2, x1 ≤ x7 ∧ x7 < x4) ∨ x1 ≤ x5.1 ∧ x5.1 < x4 ∧ ∀ x7 ∈ x5.2, x7 < x1)) →     have x6 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x4 x3;     have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x6;     ∃ (x8 : Finset ℕ) (x9 : Finset ℕ), PEqualNP.TopForm.IsAO2 x4 x6 ∧ (∀ x10 ∈ x8, x10 < x1 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x8) ∧ (∀ x10 ∈ x9, x1 ≤ x10 ∧ x10 < x4 ∨ ∃ x12 < x6.gates.length, x10 = x4 + x12 ∧ (x7 x12).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x13 ∈ (x7 x12).inputs, x13 ∈ x9) ∧ ∀ x10 < x6.gates.length, (x7 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x7 x10).inputs = [x13, x14] ∧ (x13 ∈ x8 ∧ x14 ∈ x9 ∨ x13 ∈ x9 ∧ x14 ∈ x8) := by
  intro x1 x2 x3 x4 hyp x6 x7
  obtain ⟨S, T, h1, h2, h3, h4⟩ := inv_cover (fun i => i < x1) (fun i => x1 ≤ i ∧ i < x4) x3 x4 true 0
    (fun i h => by show i < x1 + x2; omega) (fun i h => h.2) (fun h => by simp at h)
    (fun o ho => by
      rcases (hyp o ho).2 with h | h
      · exact Or.inr h
      · exact Or.inl ⟨⟨h.1, h.2.1⟩, h.2.2⟩)
  have hg : x6.gates = PEqualNP.MetaComplexity.coverGatesB x4 true 0 x3 := gates_eq x4 x3
  rw [← hg] at h1 h2 h3 h4
  have key : ∀ k g, x6.gates[k]? = some g → k < x6.gates.length ∧ x7 k = g := by
    intro k g h
    have hk : k < x6.gates.length := (List.getElem?_eq_some_iff.mp h).1
    refine ⟨hk, ?_⟩
    have := gateAt_get x6 k hk
    rw [h] at this
    exact (Option.some.inj this).symm
  refine ⟨Finset.range x1 ∪ S, Finset.Ico x1 x4 ∪ T, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g hg2
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg2
    exact (h1 k g hk).1
  · intro j hj i hi
    exact (h1 j _ (gateAt_get x6 j hj)).2.2 i hi
  · intro g hg2
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hg2
    exact (h1 k g hk).2.1
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Or.inl (Finset.mem_range.mp hw)
    · right
      obtain ⟨k, g, e1, e2, e3, e4⟩ := h2 w hw
      obtain ⟨hk, rfl⟩ := key k g e1
      refine ⟨k, hk, e2, e3, fun i hi => ?_⟩
      rcases e4 i hi with h | h
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr h)
      · exact Finset.mem_union_right _ h
  · intro w hw
    rcases Finset.mem_union.mp hw with hw | hw
    · exact Or.inl (Finset.mem_Ico.mp hw)
    · right
      obtain ⟨k, g, e1, e2, e3, e4⟩ := h3 w hw
      obtain ⟨hk, rfl⟩ := key k g e1
      refine ⟨k, hk, e2, e3, fun i hi => ?_⟩
      rcases e4 i hi with h | h
      · exact Finset.mem_union_left _ (Finset.mem_Ico.mpr h)
      · exact Finset.mem_union_right _ h
  · intro k hk ho
    obtain ⟨a, b, e, h⟩ := h4 k _ (gateAt_get x6 k hk) ho
    refine ⟨a, b, e, ?_⟩
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    exact h

end CoverForm

namespace CoverRead

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma canonical_cover_isReadTwo (P L : ℕ) (own : List (ℕ × List ℕ))
    (ho : ∀ o ∈ own, o.2 ≠ [] ∧
      ((o.1 < P ∧ ∀ r ∈ o.2, P ≤ r ∧ r < P + L) ∨
       P ≤ o.1 ∧ o.1 < P + L ∧ ∀ r ∈ o.2, r < P)) :
    IsReadK (P + L) (coverCircuitB (P + L) own) 2 := by
  obtain ⟨A, B, hao, hA, hB, hand⟩ :=
    PEqualNP.Outside.L_meta_2584.CoverForm.cover_form P L own ho
  exact PEqualNP.Outside.L_meta_2584.FlatRead.separated_isReadTwo hao A B hA hB hand

end CoverRead

def incidenceBit {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (u v : Fin (P + L)) : Bool :=
  Fin.addCases
    (fun p => Fin.addCases (fun _ => false) (fun l => decide (I p l)) v)
    (fun l => Fin.addCases (fun p => decide (I p l)) (fun _ => false) v) u

abbrev incidenceGraph {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I] :
    SimpleGraph (Fin (P + L)) where
  Adj u v := incidenceBit I u v = true
  symm := ⟨by
    intro a b
    induction a using Fin.addCases <;> induction b using Fin.addCases <;>
      simp [incidenceBit]⟩
  loopless := ⟨by
    intro a
    induction a using Fin.addCases <;> simp [incidenceBit]⟩

lemma incidenceGraph_noFourCycle {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (h4 : ∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) :
    PEqualNP.TopForm.NoFourCycle (incidenceGraph I) := by
  intro a b hab
  apply Finset.card_le_one.mpr
  intro c hc d hd
  have hac := (Finset.mem_filter.mp hc).2.1
  have hbc := (Finset.mem_filter.mp hc).2.2
  have had := (Finset.mem_filter.mp hd).2.1
  have hbd := (Finset.mem_filter.mp hd).2.2
  induction a using Fin.addCases <;> induction b using Fin.addCases <;>
    induction c using Fin.addCases <;> induction d using Fin.addCases <;>
      simp [incidenceBit] at *
  · by_contra hcd
    exact h4 _ _ _ _ hab hcd hac had hbc hbd
  · by_contra hcd
    exact h4 _ _ _ _ hcd hab hac hbc had hbd

lemma incidenceGraph_function {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (z : Fin (P + L) → Bool) :
    PEqualNP.MetaComplexity.NestedCover.graphFun (incidenceGraph I) ∅ z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true) := by
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
    false_and, exists_false, decide_false, Bool.false_or]
  congr 1
  apply propext
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    induction u using Fin.addCases <;> induction v using Fin.addCases <;>
      simp [incidenceBit] at huv
    · exact ⟨_, _, huv, hu, hv⟩
    · exact ⟨_, _, huv, hv, hu⟩
  · rintro ⟨p, l, hi, hp, hl⟩
    exact ⟨Fin.castAdd L p, Fin.natAdd P l, by simpa [incidenceBit] using hi, hp, hl⟩


namespace Support

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

variable {n : ℕ}

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp


def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

lemma mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

lemma mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _


def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L


def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}


def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

lemma agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

lemma agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]


def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

lemma cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

lemma cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

lemma cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this


lemma essential_count (n : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (S : Finset (Fin n))
    (hdep : ∀ i ∈ S, ∃ x : Fin n → Bool,
      circuitFun n C (Function.update x i (!x i)) ≠ circuitFun n C x) :
    S.card ≤ C.size + 1 := by
  set T := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hT
  have hsub : S ⊆ T := by
    intro i hiS
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiS
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) hfan cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hT] at hc
  exact (Finset.card_le_card hsub).trans hc

end Support


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma incidence_singleton_false {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    (i : Fin (P + L)) : circuitFun (P + L) C (setInput {i}) = false := by
  rw [hC, decide_eq_false_iff_not]
  rintro ⟨p, l, _, hp, hl⟩
  have hp' : Fin.castAdd L p = i := Finset.mem_singleton.mp (of_decide_eq_true hp)
  have hl' : Fin.natAdd P l = i := Finset.mem_singleton.mp (of_decide_eq_true hl)
  exact point_ne_line p l (hp'.trans hl'.symm)

lemma toggle_singleton {n : ℕ} (a b : Fin n) (hne : a ≠ b) :
    Function.update (setInput {b}) a (!(setInput {b}) a) = setInput {a, b} := by
  funext i
  by_cases hi : i = a
  · subst i
    simp [setInput, hne]
  · simp [Function.update_of_ne hi, setInput, hi]

lemma incidence_point_essential {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    {p : Fin P} {l : Fin L} (hi : I p l) :
    ∃ x : Fin (P + L) → Bool,
      circuitFun (P + L) C (Function.update x (Fin.castAdd L p) (!x (Fin.castAdd L p))) ≠
        circuitFun (P + L) C x := by
  refine ⟨setInput {Fin.natAdd P l}, ?_⟩
  rw [toggle_singleton _ _ (point_ne_line p l),
    (incidence_pair_prime I C hC hi).1, incidence_singleton_false I C hC]
  decide

lemma incidence_line_essential {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    {p : Fin P} {l : Fin L} (hi : I p l) :
    ∃ x : Fin (P + L) → Bool,
      circuitFun (P + L) C (Function.update x (Fin.natAdd P l) (!x (Fin.natAdd P l))) ≠
        circuitFun (P + L) C x := by
  refine ⟨setInput {Fin.castAdd L p}, ?_⟩
  rw [toggle_singleton _ _ (Ne.symm (point_ne_line p l)), Finset.pair_comm,
    (incidence_pair_prime I C hC hi).1, incidence_singleton_false I C hC]
  decide


namespace CoverEval

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma read {N : ℕ} (x : Fin N → Bool) (i : Fin N) : (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD]

def part (w : List Bool) (v : ℕ) (rest : List ℕ) (i : ℕ) : Bool :=
  w.getD v false || (rest.take i).any fun r => w.getD r false

def acc (w : List Bool) (v : ℕ) (rest : List ℕ) (k : ℕ) : List Bool :=
  w ++ (List.range k).map fun i => part w v rest (i + 1)

lemma acc_length (w v rest k) : (acc w v rest k).length = w.length + k := by simp [acc]

lemma acc_low (w v rest k) (i : ℕ) (h : i < w.length) :
    (acc w v rest k).getD i false = w.getD i false := List.getD_append _ _ _ _ h

lemma acc_chain (w : List Bool) (v : ℕ) (rest : List ℕ) (k : ℕ) (hv : v < w.length)
    (hk : k ≤ rest.length) :
    (acc w v rest k).getD ((v :: (List.range rest.length).map (fun j => w.length + j)).getD k 0) false =
      part w v rest k := by
  cases k with
  | zero =>
    rw [List.getD_cons_zero, acc_low _ _ _ _ _ hv]
    simp [part]
  | succ k =>
    rw [List.getD_cons_succ]
    have : ((List.range rest.length).map (fun j => w.length + j)).getD k 0 = w.length + k := by
      rw [List.getD_eq_getElem?_getD]
      simp [show k < rest.length by omega]
    rw [this, acc, List.getD_append_right _ _ _ _ (by omega)]
    rw [List.getD_eq_getElem?_getD]
    simp

lemma chain_run (w : List Bool) (v : ℕ) (rest : List ℕ) (hv : v < w.length)
    (hr : ∀ r ∈ rest, r < w.length) (k : ℕ) (hk : k ≤ rest.length) :
    ((List.range k).map (fun i => (⟨GateOp.or,
      [(v :: (List.range rest.length).map (fun j => w.length + j)).getD i 0, rest.getD i 0]⟩ : Gate))).foldl
        step w = acc w v rest k := by
  induction k with
  | zero => simp [acc]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, step, GateOp.eval]
    rw [acc_chain w v rest k hv (by omega)]
    have hk' : k < rest.length := by omega
    have g : rest.getD k 0 = rest[k] := by
      rw [List.getD_eq_getElem?_getD]
      simp [hk']
    rw [g, acc_low _ _ _ _ _ (hr _ (List.getElem_mem hk'))]
    rw [acc, acc, List.range_succ, List.map_append, List.append_assoc]
    congr 2
    simp only [List.map_cons, List.map_nil, part, List.any_cons, List.any_nil, id, Bool.or_false]
    rw [List.take_succ_eq_append_getElem hk', List.any_append]
    simp [Bool.or_assoc]

lemma block_length (B a t v : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v rest lead).length = rest.length + 1 + if lead then 0 else 1 := by
  cases lead <;> simp [blockGates]

lemma block_run (w : List Bool) (a t v : ℕ) (rest : List ℕ) (lead : Bool)
    (ha : lead = false → a < w.length) (ht : t < w.length) (hv : v < w.length)
    (hr : ∀ r ∈ rest, r < w.length) :
    ((blockGates w.length a t v rest lead).foldl step w).length =
        w.length + (blockGates w.length a t v rest lead).length ∧
      (∀ i < w.length, ((blockGates w.length a t v rest lead).foldl step w).getD i false = w.getD i false) ∧
      ((blockGates w.length a t v rest lead).foldl step w).getD
        (w.length + (blockGates w.length a t v rest lead).length - 1) false =
        ((!lead && w.getD a false) || (w.getD t false && (v :: rest).any fun r => w.getD r false)) := by
  have full : part w v rest rest.length = (v :: rest).any fun r => w.getD r false := by
    simp [part]
  let w1 := acc w v rest rest.length
  let b : Bool := w.getD t false && (v :: rest).any fun r => w.getD r false
  have l1 : w1.length = w.length + rest.length := acc_length _ _ _ _
  have first : step w1 ⟨GateOp.and, [t, (v :: (List.range rest.length).map
      (fun j => w.length + j)).getD rest.length 0]⟩ = w1 ++ [b] := by
    simp only [step, GateOp.eval, List.map_cons, List.map_nil, w1]
    rw [acc_chain w v rest _ hv le_rfl, acc_low _ _ _ _ _ ht, full]
    simp [b]
  have low (i : ℕ) (hi : i < w.length) (l : List Bool) : (w1 ++ l).getD i false = w.getD i false := by
    rw [List.getD_append _ _ _ _ (by omega)]
    exact acc_low _ _ _ _ _ hi
  have last (u : List Bool) (c : Bool) (j : ℕ) (hj : j = u.length) : (u ++ [c]).getD j false = c := by
    rw [hj, List.getD_append_right _ _ _ _ le_rfl]
    simp
  cases lead with
  | true =>
    have run : (blockGates w.length a t v rest true).foldl step w = w1 ++ [b] := by
      rw [blockGates, List.foldl_append, chain_run w v rest hv hr _ le_rfl]
      simp only [if_true, List.foldl_cons, List.foldl_nil]
      exact first
    rw [run, block_length]
    refine ⟨by simp [l1]; omega, fun i hi => low i hi _, ?_⟩
    rw [last _ _ _ (by rw [l1]; simp)]
    simp [b]
  | false =>
    have run : (blockGates w.length a t v rest false).foldl step w = (w1 ++ [b]) ++ [w.getD a false || b] := by
      rw [blockGates, List.foldl_append, chain_run w v rest hv hr _ le_rfl]
      simp only [Bool.false_eq_true, if_false, List.foldl_cons, List.foldl_nil]
      rw [show step (acc w v rest rest.length) _ = _ from first]
      simp only [step, GateOp.eval, List.map_cons, List.map_nil]
      rw [low a (ha rfl), last w1 b _ (by rw [l1])]
      simp
    rw [run, block_length]
    refine ⟨by simp [l1]; omega, fun i hi => ?_, ?_⟩
    · rw [List.append_assoc]
      exact low i hi _
    · rw [last _ _ _ (by simp [l1]; omega)]
      simp [b]

def hit (w : List Bool) (own : List (ℕ × List ℕ)) : Bool :=
  own.any fun o => w.getD o.1 false && o.2.any fun r => w.getD r false

lemma hit_congr (w w' : List Bool) (n : ℕ) (own : List (ℕ × List ℕ))
    (h : ∀ i < n, w.getD i false = w'.getD i false) (ho : ∀ o ∈ own, o.1 < n ∧ ∀ r ∈ o.2, r < n) :
    hit w own = hit w' own := by
  rw [Bool.eq_iff_iff]
  simp only [hit, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨o, hm, h1, r, hr, h2⟩
    exact ⟨o, hm, by rw [← h _ (ho o hm).1]; exact h1, r, hr, by rw [← h _ ((ho o hm).2 r hr)]; exact h2⟩
  · rintro ⟨o, hm, h1, r, hr, h2⟩
    exact ⟨o, hm, by rw [h _ (ho o hm).1]; exact h1, r, hr, by rw [h _ ((ho o hm).2 r hr)]; exact h2⟩

lemma cover_run (n : ℕ) (own : List (ℕ × List ℕ)) (ho : ∀ o ∈ own, o.1 < n ∧ ∀ r ∈ o.2, r < n)
    (w : List Bool) (hw : n ≤ w.length) (a : ℕ) (ha : a < w.length) :
    ((coverGatesB w.length false a own).foldl step w).getD
      (if (coverGatesB w.length false a own).length = 0 then a
        else w.length + (coverGatesB w.length false a own).length - 1) false =
      (w.getD a false || hit w own) := by
  induction own generalizing w a with
  | nil => simp [coverGatesB, hit]
  | cons o os ih =>
    have hos : ∀ o ∈ os, o.1 < n ∧ ∀ r ∈ o.2, r < n := fun o h => ho o (List.mem_cons_of_mem _ h)
    obtain ⟨t, l⟩ := o
    cases l with
    | nil =>
      rw [coverGatesB, ih hos w hw a ha]
      simp [hit]
    | cons v rest =>
      obtain ⟨h1, h2⟩ := ho (t, v :: rest) List.mem_cons_self
      have ht : t < w.length := by have : t < n := h1; omega
      have hr : ∀ r ∈ v :: rest, r < w.length := fun r h => lt_of_lt_of_le (h2 r h) hw
      obtain ⟨q1, q2, q3⟩ := block_run w a t v rest false (fun _ => ha) ht (hr v List.mem_cons_self)
        (fun r h => hr r (List.mem_cons_of_mem _ h))
      have pos : 0 < (blockGates w.length a t v rest false).length := by rw [block_length]; omega
      rw [coverGatesB, List.foldl_append]
      generalize hbg : blockGates w.length a t v rest false = bg at *
      have key := ih hos (bg.foldl step w) (by omega) (w.length + bg.length - 1) (by omega)
      rw [q1] at key
      rw [q3] at key
      rw [List.length_append]
      have idx : (if bg.length + (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length = 0
          then a else w.length + (bg.length +
            (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length) - 1) =
          if (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length = 0
            then w.length + bg.length - 1 else w.length + bg.length +
            (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length - 1 := by
        rw [if_neg (by omega)]
        split <;> omega
      rw [idx, key, hit_congr _ w n os (fun i hi => q2 i (by omega)) hos]
      simp [hit, Bool.or_assoc]

lemma cover_length (own : List (ℕ × List ℕ)) (ho : ∀ o ∈ own, o.2 ≠ []) (B a : ℕ) :
    (coverGatesB B false a own).length = (own.map fun o => o.2.length).sum + own.length := by
  induction own generalizing B a with
  | nil => simp [coverGatesB]
  | cons o os ih =>
    obtain ⟨t, l⟩ := o
    cases l with
    | nil => exact absurd rfl (ho (t, []) List.mem_cons_self)
    | cons v rest =>
      rw [coverGatesB, List.length_append, ih (fun o h => ho o (List.mem_cons_of_mem _ h)), block_length]
      simp
      omega

lemma cover_all (n : ℕ) (own : List (ℕ × List ℕ)) (ho : ∀ o ∈ own, o.1 < n ∧ ∀ r ∈ o.2, r < n)
    (hne : ∀ o ∈ own, o.2 ≠ []) :
    (coverCircuitB n own).size = (own.map fun o => o.2.length).sum + own.length - 1 ∧
      ∀ w : List Bool, w.length = n → (coverCircuitB n own).eval w = hit w own := by
  cases own with
  | nil =>
    refine ⟨by simp [coverCircuitB, coverGatesB, Circuit.size], ?_⟩
    intro w hw
    simp only [coverCircuitB, coverGatesB, if_true]
    change w.getD n false = false
    exact List.getD_eq_default _ _ hw.le
  | cons o os =>
    obtain ⟨t, l⟩ := o
    cases l with
    | nil => exact absurd rfl (hne (t, []) List.mem_cons_self)
    | cons v rest =>
      have hos : ∀ o ∈ os, o.1 < n ∧ ∀ r ∈ o.2, r < n := fun o h => ho o (List.mem_cons_of_mem _ h)
      have len := block_length n 0 t v rest true
      rw [coverCircuitB, if_neg (by
        rw [coverGatesB]
        intro h
        have := congrArg List.length h
        rw [List.length_append, len] at this
        simp at this)]
      constructor
      · change (coverGatesB n true 0 ((t, v :: rest) :: os)).length = _
        rw [coverGatesB, List.length_append, cover_length os (fun o h => hne o (List.mem_cons_of_mem _ h)), len]
        simp
        omega
      · intro w hw
        subst hw
        obtain ⟨h1, h2⟩ := ho (t, v :: rest) List.mem_cons_self
        obtain ⟨q1, q2, q3⟩ := block_run w 0 t v rest true (fun h => by cases h) h1
          (h2 v List.mem_cons_self) (fun r h => h2 r (List.mem_cons_of_mem _ h))
        change ((coverGatesB w.length true 0 ((t, v :: rest) :: os)).foldl step w).getD _ false = _
        rw [coverGatesB, List.foldl_append, List.length_append]
        generalize hbg : blockGates w.length 0 t v rest true = bg at *
        have pos : 0 < bg.length := by rw [len]; omega
        have key := cover_run w.length os hos (bg.foldl step w) (by omega) (w.length + bg.length - 1) (by omega)
        rw [q1, q3] at key
        have idx : w.length + (bg.length +
            (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length) - 1 =
          if (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length = 0
            then w.length + bg.length - 1 else w.length + bg.length +
            (coverGatesB (w.length + bg.length) false (w.length + bg.length - 1) os).length - 1 := by
          split <;> omega
        rw [idx, key, hit_congr _ w w.length os q2 hos]
        simp [hit]

lemma main : ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : List (ℕ × List ℕ)),   let x6 : ℕ := x1 + x2;   (∀ x7 ∈ x5, x7.2 ≠ [] ∧ ((x7.1 < x1 ∧ ∀ x9 ∈ x7.2, x1 ≤ x9 ∧ x9 < x6) ∨ x1 ≤ x7.1 ∧ x7.1 < x6 ∧ ∀ x9 ∈ x7.2, x9 < x1)) →     (∀ (x8 : Fin x1) (x9 : Fin x2), x3 x8 x9 ↔ ∃ x10 ∈ x5, x10.1 = ↑x8 ∧ x1 + ↑x9 ∈ x10.2 ∨ x10.1 = x1 + ↑x9 ∧ ↑x8 ∈ x10.2) →       have x9 : PEqualNP.CircuitLowerBounds.Circuit := PEqualNP.MetaComplexity.coverCircuitB x6 x5;       x9.size = (List.map (fun (x10 : ℕ × List ℕ) => x10.2.length) x5).sum + x5.length - (1 : ℕ) ∧ ∀ (x10 : Fin x6 → Bool), PEqualNP.MetaComplexity.circuitFun x6 x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true) := by
  intro n m R _ own N hshape hedge
  have hlt : ∀ o ∈ own, o.1 < n + m ∧ ∀ r ∈ o.2, r < n + m := by
    intro o ho
    rcases (hshape o ho).2 with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact ⟨by omega, fun r hr => (h2 r hr).2⟩
    · exact ⟨h2, fun r hr => by have := h3 r hr; omega⟩
  obtain ⟨hs, hv⟩ := cover_all (n + m) own hlt (fun o h => (hshape o h).1)
  refine ⟨hs, fun x => ?_⟩
  change (coverCircuitB (n + m) own).eval (List.ofFn x) = _
  rw [hv _ List.length_ofFn, Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [hit, List.any_eq_true, Bool.and_eq_true]
  have pt (p : Fin n) : (List.ofFn x).getD p.val false = x (Fin.castAdd m p) := read x (Fin.castAdd m p)
  have ln (l : Fin m) : (List.ofFn x).getD (n + l.val) false = x (Fin.natAdd n l) := read x (Fin.natAdd n l)
  constructor
  · rintro ⟨o, ho, h1, r, hr, h2⟩
    rcases (hshape o ho).2 with ⟨s1, s2⟩ | ⟨s1, s2, s3⟩
    · obtain ⟨r1, r2⟩ := s2 r hr
      obtain ⟨l, hl⟩ : ∃ l : Fin m, n + l.val = r := ⟨⟨r - n, by omega⟩, by simp; omega⟩
      refine ⟨⟨o.1, s1⟩, l, (hedge _ _).mpr ⟨o, ho, Or.inl ⟨rfl, hl ▸ hr⟩⟩, ?_, ?_⟩
      · rw [← pt]
        exact h1
      · rw [← ln, hl]
        exact h2
    · obtain ⟨l, hl⟩ : ∃ l : Fin m, n + l.val = o.1 := ⟨⟨o.1 - n, by omega⟩, by simp; omega⟩
      refine ⟨⟨r, s3 r hr⟩, l, (hedge _ _).mpr ⟨o, ho, Or.inr ⟨hl.symm, hr⟩⟩, ?_, ?_⟩
      · rw [← pt]
        exact h2
      · rw [← ln, hl]
        exact h1
  · rintro ⟨p, l, hR, h1, h2⟩
    obtain ⟨o, ho, ⟨e1, e2⟩ | ⟨e1, e2⟩⟩ := (hedge p l).mp hR
    · exact ⟨o, ho, by rw [e1, pt]; exact h1, _, e2, by rw [ln]; exact h2⟩
    · exact ⟨o, ho, by rw [e1, ln]; exact h2, _, e2, by rw [pt]; exact h1⟩

end CoverEval

namespace CoverCertificate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma replacement_of_star_cover (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (C : Circuit) (own : List (ℕ × List ℕ))
    (ho : ∀ o ∈ own, o.2 ≠ [] ∧
      ((o.1 < P ∧ ∀ r ∈ o.2, P ≤ r ∧ r < P + L) ∨
       P ≤ o.1 ∧ o.1 < P + L ∧ ∀ r ∈ o.2, r < P))
    (hedge : ∀ p : Fin P, ∀ l : Fin L, I p l ↔
      ∃ o ∈ own, (o.1 = p.val ∧ P + l.val ∈ o.2) ∨
        (o.1 = P + l.val ∧ p.val ∈ o.2))
    (hbudget : (own.map (fun o => o.2.length)).sum + own.length - 1 ≤ C.size) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧
      (∀ y : Fin (P + L) → Bool, circuitFun (P + L) D y =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧
      D.size ≤ C.size ∧ IsReadK (P + L) D 2 := by
  obtain ⟨A, B, hao, hA, hB, hand⟩ :=
    PEqualNP.Outside.L_meta_2584.CoverForm.cover_form P L own ho
  obtain ⟨hsize, hfun⟩ :=
    PEqualNP.Outside.L_meta_2584.CoverEval.main P L I own ho hedge
  refine ⟨coverCircuitB (P + L) own, hao, hfun, ?_, ?_⟩
  · rw [hsize]
    exact hbudget
  · exact PEqualNP.Outside.L_meta_2584.FlatRead.separated_isReadTwo hao A B hA hB hand

end CoverCertificate


namespace CycleSix

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

abbrev incident (p l : Fin 3) : Prop := l = p ∨ l.val = (p.val + 1) % 3

def circuit : Circuit :=
  ⟨[⟨.or, [3, 5]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 7]⟩,
    ⟨.and, [2, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [3, 4]⟩,
    ⟨.and, [0, 11]⟩, ⟨.or, [10, 12]⟩], 13⟩

lemma circuit_size : circuit.size = 8 := rfl

lemma circuit_ao2 : PEqualNP.TopForm.IsAO2 6 circuit := by decide

lemma incidence_four_free :
    ∀ p p' : Fin 3, ∀ l l' : Fin 3, p ≠ p' → l ≠ l' →
      ¬ (incident p l ∧ incident p l' ∧ incident p' l ∧ incident p' l') := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma circuit_computes :
    ∀ z : Fin (3 + 3) → Bool, circuitFun (3 + 3) circuit z =
      decide (∃ p : Fin 3, ∃ l : Fin 3, incident p l ∧
        z (Fin.castAdd 3 p) = true ∧ z (Fin.natAdd 3 l) = true) := by
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma circuit_read_two : IsReadK 6 circuit 2 := by
  decide

end CycleSix



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma line_star_size_bound (P : ℕ) (I : Fin P → Fin 1 → Prop) [DecidableRel I]
    (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 (P + 1) C)
    (hC : ∀ z : Fin (P + 1) → Bool, circuitFun (P + 1) C z =
      decide (∃ p : Fin P, ∃ l : Fin 1, I p l ∧
        z (Fin.castAdd 1 p) = true ∧ z (Fin.natAdd P l) = true)) :
    (Finset.univ.filter (fun p : Fin P => I p 0)).card ≤ C.size := by
  let N := Finset.univ.filter (fun p : Fin P => I p 0)
  change N.card ≤ C.size
  by_cases hN : N.Nonempty
  · let S := insert (Fin.natAdd P (0 : Fin 1)) (N.image (Fin.castAdd 1))
    have hc : S.card ≤ C.size + 1 := by
      apply Support.essential_count (P + 1) C (fun g hg => (hAO.2.2 g hg).le) S
      intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · obtain ⟨p, hp⟩ := hN
        exact incidence_line_essential I C hC (Finset.mem_filter.mp hp).2
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
        exact incidence_point_essential I C hC (Finset.mem_filter.mp hp).2
    have hnot : Fin.natAdd P (0 : Fin 1) ∉ N.image (Fin.castAdd 1) := by
      intro h
      obtain ⟨p, _, heq⟩ := Finset.mem_image.mp h
      exact point_ne_line p 0 heq
    have hinj : Function.Injective (Fin.castAdd 1 : Fin P → Fin (P + 1)) := by
      intro a b hab
      apply Fin.ext
      have h := congrArg Fin.val hab
      exact h
    have hcard : S.card = N.card + 1 := by
      dsimp [S]
      rw [Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective N hinj]
    omega
  · have hzero : N = ∅ := Finset.not_nonempty_iff_eq_empty.mp hN
    rw [hzero]
    simp

lemma incidence_active_size_bound {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 (P + L) C)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) :
    (Finset.univ.filter (fun p : Fin P => ∃ l : Fin L, I p l)).card +
      (Finset.univ.filter (fun l : Fin L => ∃ p : Fin P, I p l)).card ≤ C.size + 1 := by
  let A := Finset.univ.filter (fun p : Fin P => ∃ l : Fin L, I p l)
  let B := Finset.univ.filter (fun l : Fin L => ∃ p : Fin P, I p l)
  let SA := A.image (Fin.castAdd L)
  let SB := B.image (Fin.natAdd P)
  have hc : (SA ∪ SB).card ≤ C.size + 1 := by
    apply Support.essential_count (P + L) C (fun g hg => (hAO.2.2 g hg).le)
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨l, hl⟩ := (Finset.mem_filter.mp hp).2
      exact incidence_point_essential I C hC hl
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨p, hp⟩ := (Finset.mem_filter.mp hl).2
      exact incidence_line_essential I C hC hp
  have hd : Disjoint SA SB := by
    apply Finset.disjoint_left.mpr
    intro i ha hb
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨l, _, heq⟩ := Finset.mem_image.mp hb
    exact point_ne_line p l heq.symm
  have hAi : Function.Injective (Fin.castAdd L : Fin P → Fin (P + L)) := by
    intro a b hab
    have h := congrArg Fin.val hab
    exact Fin.ext h
  have hBi : Function.Injective (Fin.natAdd P : Fin L → Fin (P + L)) := by
    intro a b hab
    apply Fin.ext
    have h := congrArg Fin.val hab
    change P + a.val = P + b.val at h
    omega
  rw [Finset.card_union_of_disjoint hd] at hc
  change (A.image _).card + (B.image _).card ≤ C.size + 1 at hc
  rw [Finset.card_image_of_injective A hAi, Finset.card_image_of_injective B hBi] at hc
  exact hc


namespace CoverCertificate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma point_star_replacement_of_degree_bound (L : ℕ) (I : Fin 1 → Fin L → Prop)
    [DecidableRel I] (C : Circuit)
    (hbudget : (Finset.univ.filter (fun l => I 0 l)).card ≤ C.size) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (1 + L) D ∧
      (∀ y : Fin (1 + L) → Bool, circuitFun (1 + L) D y =
        decide (∃ p : Fin 1, ∃ l : Fin L, I p l ∧
          y (Fin.castAdd L p) = true ∧ y (Fin.natAdd 1 l) = true)) ∧
      D.size ≤ C.size ∧ IsReadK (1 + L) D 2 := by
  let N : Finset (Fin L) := Finset.univ.filter (fun l => I 0 l)
  let leaves : List ℕ := N.toList.map (fun l => 1 + l.val)
  have hp (p : Fin 1) : p = 0 := Subsingleton.elim _ _
  have hmem (w : ℕ) : w ∈ leaves ↔ ∃ l : Fin L, I 0 l ∧ 1 + l.val = w := by
    simp [leaves, N]
  by_cases hN : N.Nonempty
  · have hleaves : leaves ≠ [] := by
      intro he
      have hh : leaves.length = N.card := by simp [leaves]
      have hc := Finset.card_pos.mpr hN
      rw [he] at hh
      simp at hh
      omega
    apply replacement_of_star_cover 1 L I C [(0, leaves)]
    · intro o ho
      have ho' : o = (0, leaves) := List.mem_singleton.mp ho
      subst o
      refine ⟨hleaves, Or.inl ⟨by norm_num, ?_⟩⟩
      intro r hr
      obtain ⟨l, _, rfl⟩ := (hmem r).mp hr
      have := l.isLt
      omega
    · intro p l
      rw [hp p]
      constructor
      · intro hi
        exact ⟨(0, leaves), by simp, Or.inl ⟨rfl, (hmem _).mpr ⟨l, hi, rfl⟩⟩⟩
      · rintro ⟨o, ho, hh⟩
        have ho' : o = (0, leaves) := List.mem_singleton.mp ho
        subst o
        rcases hh with ⟨_, hleaf⟩ | ⟨he, _⟩
        · obtain ⟨k, hk, he⟩ := (hmem _).mp hleaf
          have hkl : k = l := Fin.ext (by omega)
          simpa only [hkl] using hk
        · change 0 = 1 + l.val at he
          omega
    · simpa [leaves, N] using hbudget
  · apply replacement_of_star_cover 1 L I C []
    · simp
    · intro p l
      have hn : ¬ I p l := by
        intro hi
        apply hN
        exact ⟨l, by simpa [N, hp p] using hi⟩
      simp [hn]
    · simp

end CoverCertificate

namespace CoverCertificate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma line_star_replacement_of_degree_bound (P : ℕ) (I : Fin P → Fin 1 → Prop)
    [DecidableRel I] (C : Circuit)
    (hbudget : (Finset.univ.filter (fun p => I p 0)).card ≤ C.size) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + 1) D ∧
      (∀ y : Fin (P + 1) → Bool, circuitFun (P + 1) D y =
        decide (∃ p : Fin P, ∃ l : Fin 1, I p l ∧
          y (Fin.castAdd 1 p) = true ∧ y (Fin.natAdd P l) = true)) ∧
      D.size ≤ C.size ∧ IsReadK (P + 1) D 2 := by
  let N : Finset (Fin P) := Finset.univ.filter (fun p => I p 0)
  let leaves : List ℕ := N.toList.map Fin.val
  have hl (l : Fin 1) : l = 0 := Subsingleton.elim _ _
  have hmem (w : ℕ) : w ∈ leaves ↔ ∃ p : Fin P, I p 0 ∧ p.val = w := by
    simp [leaves, N]
  by_cases hN : N.Nonempty
  · have hleaves : leaves ≠ [] := by
      intro he
      have hh : leaves.length = N.card := by simp [leaves]
      have hc := Finset.card_pos.mpr hN
      rw [he] at hh
      simp at hh
      omega
    apply replacement_of_star_cover P 1 I C [(P, leaves)]
    · intro o ho
      have ho' : o = (P, leaves) := List.mem_singleton.mp ho
      subst o
      refine ⟨hleaves, Or.inr ⟨by simp, by simp, ?_⟩⟩
      intro r hr
      obtain ⟨p, _, rfl⟩ := (hmem r).mp hr
      exact p.isLt
    · intro p l
      rw [hl l]
      constructor
      · intro hi
        exact ⟨(P, leaves), by simp, Or.inr ⟨by simp, (hmem _).mpr ⟨p, hi, rfl⟩⟩⟩
      · rintro ⟨o, ho, hh⟩
        have ho' : o = (P, leaves) := List.mem_singleton.mp ho
        subst o
        rcases hh with ⟨he, _⟩ | ⟨_, hleaf⟩
        · change P = p.val at he
          have := p.isLt
          omega
        · obtain ⟨k, hk, he⟩ := (hmem _).mp hleaf
          have hkp : k = p := Fin.ext he
          simpa only [hkp] using hk
    · simpa [leaves, N] using hbudget
  · apply replacement_of_star_cover P 1 I C []
    · simp
    · intro p l
      have hn : ¬ I p l := by
        intro hi
        apply hN
        exact ⟨p, by simpa [N, hl l] using hi⟩
      simp [hn]
    · simp

end CoverCertificate


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma star_forest_edge_count {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (huniq : ∀ p p' : Fin P, ∀ l : Fin L, I p l → I p' l → p = p') :
    (∑ p : Fin P, (Finset.univ.filter (fun l : Fin L => I p l)).card) =
      (Finset.univ.filter (fun l : Fin L => ∃ p : Fin P, I p l)).card := by
  have hcol (l : Fin L) : (Finset.univ.filter (fun p : Fin P => I p l)).card =
      if ∃ p : Fin P, I p l then 1 else 0 := by
    by_cases he : ∃ p : Fin P, I p l
    · rw [ite_eq_left he]
      have hpos : 0 < (Finset.univ.filter (fun p : Fin P => I p l)).card := by
        apply Finset.card_pos.mpr
        obtain ⟨p, hp⟩ := he
        exact ⟨p, by simp [hp]⟩
      have hle : (Finset.univ.filter (fun p : Fin P => I p l)).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro p hp p' hp'
        exact huniq p p' l (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hp').2
      omega
    · have hn : ∀ p : Fin P, ¬ I p l := by simpa using he
      simp [hn]
  calc
    (∑ p : Fin P, (Finset.univ.filter (fun l : Fin L => I p l)).card) =
        ∑ p : Fin P, ∑ l : Fin L, if I p l then 1 else 0 := by
      simp only [Finset.card_filter]
    _ = ∑ l : Fin L, ∑ p : Fin P, if I p l then 1 else 0 := Finset.sum_comm
    _ = ∑ l : Fin L, if ∃ p : Fin P, I p l then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro l _
      rw [← Finset.card_filter]
      exact hcol l
    _ = (Finset.univ.filter (fun l : Fin L => ∃ p : Fin P, I p l)).card := by
      rw [Finset.card_filter]

lemma star_forest_replacement (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (huniq : ∀ p p' : Fin P, ∀ l : Fin L, I p l → I p' l → p = p')
    (hAO : PEqualNP.TopForm.IsAO2 (P + L) C)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧
      (∀ y : Fin (P + L) → Bool, circuitFun (P + L) D y =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          y (Fin.castAdd L p) = true ∧ y (Fin.natAdd P l) = true)) ∧
      D.size ≤ C.size ∧ IsReadK (P + L) D 2 := by
  let A := Finset.univ.filter (fun p : Fin P => ∃ l : Fin L, I p l)
  let N := fun p : Fin P => Finset.univ.filter (fun l : Fin L => I p l)
  let leaves := fun p : Fin P => (N p).toList.map (fun l => P + l.val)
  let own := A.toList.map (fun p => (p.val, leaves p))
  have hleaf (p : Fin P) (w : ℕ) : w ∈ leaves p ↔
      ∃ l : Fin L, I p l ∧ P + l.val = w := by
    simp [leaves, N]
  apply CoverCertificate.replacement_of_star_cover P L I C own
  · intro o ho
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ho
    have hpA : p ∈ A := Finset.mem_toList.mp hp
    have hN : (N p).Nonempty := by
      obtain ⟨l, hl⟩ := (Finset.mem_filter.mp hpA).2
      exact ⟨l, by simp [N, hl]⟩
    have hne : leaves p ≠ [] := by
      intro h
      have hc : (leaves p).length = (N p).card := by simp [leaves]
      have hpos := Finset.card_pos.mpr hN
      rw [h] at hc
      simp at hc
      omega
    refine ⟨hne, Or.inl ⟨p.isLt, ?_⟩⟩
    intro r hr
    obtain ⟨l, _, rfl⟩ := (hleaf p r).mp hr
    have := l.isLt
    omega
  · intro p l
    constructor
    · intro hi
      refine ⟨(p.val, leaves p), ?_, Or.inl ⟨rfl, (hleaf p _).mpr ⟨l, hi, rfl⟩⟩⟩
      apply List.mem_map.mpr
      refine ⟨p, ?_, rfl⟩
      apply Finset.mem_toList.mpr
      simp [A]
      exact ⟨l, hi⟩
    · rintro ⟨o, ho, hh⟩
      obtain ⟨p', hp', rfl⟩ := List.mem_map.mp ho
      rcases hh with ⟨hp, hl⟩ | ⟨hp, _⟩
      · have hpp : p' = p := Fin.ext hp
        obtain ⟨l', hi, he⟩ := (hleaf p' _).mp hl
        have hll : l' = l := Fin.ext (by omega)
        simpa only [hpp, hll] using hi
      · have := p'.isLt
        change p'.val = P + l.val at hp
        omega
  · have hlen : own.length = A.card := by simp [own]
    have hsum : (own.map (fun o => o.2.length)).sum = ∑ p ∈ A, (N p).card := by
      simp [own, leaves, List.map_map, Function.comp_def, Finset.sum_map_toList]
    have hsum' : (∑ p ∈ A, (N p).card) = ∑ p : Fin P, (N p).card := by
      apply Finset.sum_subset (Finset.subset_univ A)
      intro p _ hp
      have hn : ∀ l : Fin L, ¬ I p l := by
        simpa [A] using hp
      simp [N, hn]
    have heq := star_forest_edge_count I huniq
    have hc := incidence_active_size_bound I C hAO hC
    rw [hsum, hsum', hlen]
    change (∑ p : Fin P, (Finset.univ.filter (fun l : Fin L => I p l)).card) + A.card - 1 ≤ C.size
    rw [heq]
    dsimp [A] at *
    omega



namespace TopFormExample

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev pathCircuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [2, 1]⟩, ⟨.and, [7, 5]⟩, ⟨.and, [6, 8]⟩], 9⟩

abbrev pathGraph : SimpleGraph (Fin 4) :=
  PEqualNP.EdgeOwnership.edgeGraph 4 [(0, 2), (1, 2), (1, 3)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma topForm_not_sufficient :
    PEqualNP.TopForm.NoFourCycle pathGraph ∧
    PEqualNP.TopForm.IsAO2 4 pathCircuit ∧
    PEqualNP.TopForm.TopForm pathGraph pathCircuit ∧
    (∀ z : Fin 4 → Bool, circuitFun 4 pathCircuit z = NestedCover.graphFun pathGraph ∅ z) ∧
    ¬ PEqualNP.ReadK.IsReadK 4 pathCircuit 2 := by
  decide

end TopFormExample

namespace Sharing

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

open PEqualNP.TopForm

lemma top_sides_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (a : ℕ) (ha : a ∈ tops G C) :
    ∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1, G.Adj u v := by
  obtain ⟨hAO, hRB, h2⟩ := hAO
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨halen, hop, hbel⟩ := ha
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have hp : p < n + a := hRB a halen p (by rw [hin]; simp)
  have hq : q < n + a := hRB a halen q (by rw [hin]; simp)
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  intro u hu v hv
  simp only [side, e0] at hu
  simp only [side, e1] at hv
  exact side_adj G (graphFun G ∅) (fun u v h => (graphFun_pair G u v).mp h) a halen hop hbel
    p q hin hp hq u v (mem_orIn_reach u hu) (mem_orIn_reach v hv)

lemma orIn_subset_of_orReaches {n : ℕ} {C : Circuit} {w g : ℕ}
    (hr : OrReaches n C w g) : orIn n C (n + g) ⊆ orIn n C w := by
  intro u hu
  exact reach_mem_orIn u ((orReaches_reach g w hr).1.trans (mem_orIn_reach u hu))

lemma top_opposite_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (a : ℕ) (ha : a ∈ tops G C)
    (b : Fin 2) {u v : Fin n} (hu : u ∈ side (n := n) C a b)
    (hv : v ∈ side (n := n) C a b.rev) : G.Adj u v := by
  have h := top_sides_adj G C hAO a ha
  fin_cases b
  · exact h u hu v hv
  · exact (h v hv u hu).symm

lemma shared_or_region_center_unique {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {a a' g : ℕ} (ha : a ∈ tops G C) (ha' : a' ∈ tops G C)
    (b b' : Fin 2) (hr : OrReaches n C (opnd C a b) g)
    (hr' : OrReaches n C (opnd C a' b') g)
    (hlarge : 1 < (orIn n C (n + g)).card) {u v : Fin n}
    (hu : u ∈ side (n := n) C a b.rev)
    (hv : v ∈ side (n := n) C a' b'.rev) : u = v := by
  by_contra hne
  have hsub : orIn n C (n + g) ⊆ Finset.univ.filter (fun x => G.Adj u x ∧ G.Adj v x) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(top_opposite_adj G C hAO a ha b (orIn_subset_of_orReaches hr hx) hu).symm,
      (top_opposite_adj G C hAO a' ha' b' (orIn_subset_of_orReaches hr' hx) hv).symm⟩
  have hcard := Finset.card_le_card hsub
  have hbound := h4 u v hne
  omega


lemma orIn_value {n : ℕ} {C : Circuit} {w : ℕ} {u : Fin n}
    (hu : u ∈ orIn n C w) (x : Fin n → Bool) (hx : x u = true) :
    val C (List.ofFn x) w = true :=
  reach_var_val x w u (mem_orIn_reach u hu) hx

lemma top_sides_disjoint {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (a : ℕ) (ha : a ∈ tops G C) :
    Disjoint (side (n := n) C a 0) (side (n := n) C a 1) := by
  rw [Finset.disjoint_left]
  intro u hu hv
  exact G.irrefl (top_sides_adj G C hAO a ha u hu u hv)

lemma top_sides_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (h4 : NoFourCycle G) (a : ℕ)
    (ha : a ∈ tops G C) :
    (side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1 := by
  by_contra hcon
  simp only [not_or, not_le] at hcon
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcon.1
  have hsub : side (n := n) C a 1 ⊆ Finset.univ.filter (fun w => G.Adj x w ∧ G.Adj y w) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨top_sides_adj G C hAO a ha x hx w hw, top_sides_adj G C hAO a ha y hy w hw⟩
  have hcard := Finset.card_le_card hsub
  have hbound := h4 x y hxy
  omega

lemma shared_or_region_center_union_card {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    (g : ℕ) (hlarge : 1 < (orIn n C (n + g)).card) :
    (Finset.univ.filter (fun u : Fin n => ∃ a ∈ tops G C, ∃ b : Fin 2,
      OrReaches n C (opnd C a b) g ∧ u ∈ side (n := n) C a b.rev)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro u hu v hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
  obtain ⟨a, ha, b, hr, hu⟩ := hu
  obtain ⟨a', ha', b', hr', hv⟩ := hv
  exact shared_or_region_center_unique G C hAO h4 ha ha' b b' hr hr' hlarge hu hv

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma belowF_orIn_empty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) {a : ℕ} (hbelow : BelowF G C a) : orIn n C (n + a) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  have hv := orIn_value hu (PEqualNP.EdgeOwnership.pairInput u u) (pairInput_left u u)
  exact G.irrefl ((graphFun_pair G u u).mp (hbelow _ hv))

lemma belowF_of_orReaches {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) {a g : ℕ} (hbelow : BelowF G C a)
    (hr : OrReaches n C (n + a) g) : BelowF G C g := by
  intro x hx
  exact hbelow x (orStep_up (by simp) (orReaches_reach g (n + a) hr).1 hx)

lemma top_orIn_empty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) {a : ℕ} (ha : a ∈ tops G C) : orIn n C (n + a) = ∅ := by
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  exact belowF_orIn_empty G C ha.2.2

lemma output_orIn_empty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hf : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅) : orIn n C C.output = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  have hv := orIn_value hu (PEqualNP.EdgeOwnership.pairInput u u) (pairInput_left u u)
  change PEqualNP.MetaComplexity.circuitFun n C (PEqualNP.EdgeOwnership.pairInput u u) = true at hv
  rw [hf] at hv
  exact G.irrefl ((graphFun_pair G u u).mp hv)

end Sharing

namespace GuardedErase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wf_append (pre post : List Gate) (w : List Bool) :
    wf (pre ++ post) w = wf post (wf pre w) := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

def sk (N i : ℕ) : ℕ := if i < N then i else i - 1

def rn (N a i : ℕ) : ℕ := if i < N then i else if i = N then a else i - 1

lemma sk_lt (N M i : ℕ) (hN0 : 0 < N) (hM : N ≤ M) (hi : i < M + 1) : sk N i < M := by
  unfold sk
  split_ifs <;> omega

lemma getD_mid (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) :
    (A ++ b :: E).getD N false = b := by
  subst hN
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl A.length),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

lemma getD_sk (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (i : ℕ) (hi : i ≠ N) :
    (A ++ E).getD (sk N i) false = (A ++ b :: E).getD i false := by
  subst hN
  unfold sk
  by_cases h : i < A.length
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [if_neg h]
    have h1 : A.length ≤ i - 1 := by omega
    have h2 : A.length ≤ i := by omega
    have h3 : i - A.length = (i - 1 - A.length) + 1 := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
      List.getElem?_append_right h2]
    rw [h3, List.getElem?_cons_succ]

lemma getD_rn (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (a : ℕ) (ha : a < N)
    (hb : A.getD a false = b) (i : ℕ) :
    (A ++ E).getD (rn N a i) false = (A ++ b :: E).getD i false := by
  by_cases h : i = N
  · have e : rn N a N = a := by
      unfold rn
      rw [if_neg (lt_irrefl _), if_pos rfl]
    have ha' : a < A.length := by omega
    rw [h, getD_mid A E b N hN, e, ← hb]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left ha']
  · have e : rn N a i = sk N i := by
      unfold rn sk
      by_cases h' : i < N
      · rw [if_pos h', if_pos h']
      · rw [if_neg h', if_neg h, if_neg h']
    rw [e]
    exact getD_sk A E b N hN i h

lemma surg (T : Gate → Gate) (A : List Bool) (b : Bool) :
    ∀ (post : List Gate) (E : List Bool),
      (∀ h ∈ post, ∀ E' : List Bool,
        h.op.eval (h.inputs.map fun i => (A ++ b :: E').getD i false)
          = (T h).op.eval ((T h).inputs.map fun i => (A ++ E').getD i false)) →
      ∃ E2 : List Bool, wf post (A ++ b :: E) = A ++ b :: E2 ∧
        wf (post.map T) (A ++ E) = A ++ E2 := by
  intro post
  induction post with
  | nil => intro E _; exact ⟨E, rfl, rfl⟩
  | cons h post ih =>
    intro E hT
    have e := hT h (List.mem_cons.mpr (Or.inl rfl)) E
    obtain ⟨E2, h1, h2⟩ :=
      ih (E ++ [h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)])
        (fun h' hh' E' => hT h' (List.mem_cons.mpr (Or.inr hh')) E')
    refine ⟨E2, ?_, ?_⟩
    · rw [wf_cons, List.append_assoc, List.cons_append]
      exact h1
    · rw [List.map_cons, wf_cons, ← e, List.append_assoc]
      exact h2

lemma ev (pre post : List Gate) (g : Gate) (T : Gate → Gate) (x : List Bool) (b : Bool)
    (hb : g.op.eval (g.inputs.map fun i => (wf pre x).getD i false) = b)
    (hT : ∀ h ∈ post, ∀ E' : List Bool,
        h.op.eval (h.inputs.map fun i => (wf pre x ++ b :: E').getD i false)
          = (T h).op.eval ((T h).inputs.map fun i => (wf pre x ++ E').getD i false)) :
    ∃ E2 : List Bool, wf (pre ++ g :: post) x = wf pre x ++ b :: E2 ∧
      wf (pre ++ post.map T) x = wf pre x ++ E2 := by
  obtain ⟨E2, h1, h2⟩ := surg T (wf pre x) b post [] hT
  rw [List.append_nil] at h2
  refine ⟨E2, ?_, ?_⟩
  · rw [wf_append, wf_cons, hb]
    exact h1
  · rw [wf_append]
    exact h2

def Tc (N a : ℕ) (h : Gate) : Gate := ⟨h.op, h.inputs.map (rn N a)⟩

lemma sound_c (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (a : ℕ) (ha : a < N)
    (hb : A.getD a false = b) (h : Gate) :
    h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)
      = (Tc N a h).op.eval ((Tc N a h).inputs.map fun i => (A ++ E).getD i false) := by
  have e : (h.inputs.map (rn N a)).map (fun i => (A ++ E).getD i false)
      = h.inputs.map fun i => (A ++ b :: E).getD i false := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact getD_rn A E b N hN a ha hb i
  show h.op.eval _ = h.op.eval ((h.inputs.map (rn N a)).map fun i => (A ++ E).getD i false)
  rw [e]

lemma Tc_legal (N a : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tc N a h).op = GateOp.and ∨ (Tc N a h).op = GateOp.or) ∧ (Tc N a h).inputs.length ≤ 2 := by
  refine ⟨hl.1, ?_⟩
  show (h.inputs.map (rn N a)).length ≤ 2
  rw [List.length_map]
  exact hl.2

lemma Tc_rb (N a : ℕ) (ha : a < N) (h : Gate) (M : ℕ) (hM : N ≤ M)
    (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tc N a h).inputs, i < M := by
  intro i hi'
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
  have := hi j hj
  unfold rn
  split_ifs <;> omega

lemma asm (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate)
    (hC : C.gates = pre ++ g :: post) (T : Gate → Gate) (o' : ℕ)
    (hmono : Monotone2 C) (hrb : ReadsBack n C)
    (hTm : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ((T h).op = GateOp.and ∨ (T h).op = GateOp.or) ∧ (T h).inputs.length ≤ 2)
    (hTr : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ∀ M : ℕ, n + pre.length ≤ M → (∀ i ∈ h.inputs, i < M + 1) → ∀ i ∈ (T h).inputs, i < M) :
    Monotone2 ⟨pre ++ post.map T, o'⟩ ∧ ReadsBack n ⟨pre ++ post.map T, o'⟩ ∧
      Circuit.size ⟨pre ++ post.map T, o'⟩ < C.size := by
  have legal := legal_of C hmono
  refine ⟨?_, ?_, ?_⟩
  · intro g' hg'
    have hg2 : g' ∈ pre ∨ g' ∈ post.map T := List.mem_append.mp hg'
    rcases hg2 with hp | hp
    · exact hmono g' (by rw [hC]; exact List.mem_append.mpr (Or.inl hp))
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      have hl := hTm h (legal h (by
        rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hh)))))
      refine ⟨?_, hl.2⟩
      rcases hl.1 with e | e
      · exact Or.inl e
      · exact Or.inr e
  · intro j hj i hi
    have hj' : j < pre.length + post.length := by simpa using hj
    by_cases hjp : j < pre.length
    · have e : gateAt ⟨pre ++ post.map T, o'⟩ j = gateAt C j := by
        simp only [gateAt, hC, List.getD_eq_getElem?_getD, List.getElem?_append_left hjp]
      rw [e] at hi
      exact hrb j (by rw [hC]; simp only [List.length_append, List.length_cons]; omega) i hi
    · have hjk : j - pre.length < post.length := by omega
      have e1 : gateAt ⟨pre ++ post.map T, o'⟩ j = T (post[j - pre.length]) := by
        simp [gateAt, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_of_not_lt hjp), hjk]
      have e2 : gateAt C (j + 1) = post[j - pre.length] := by
        have h3 : j + 1 - pre.length = (j - pre.length) + 1 := by omega
        simp [gateAt, hC, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (show pre.length ≤ j + 1 by omega), h3, hjk]
      rw [e1] at hi
      have hmem : post[j - pre.length] ∈ C.gates := by
        rw [hC]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.getElem_mem hjk))))
      have hold : ∀ i ∈ (post[j - pre.length]).inputs, i < (n + j) + 1 := by
        intro i hi2
        have := hrb (j + 1) (by rw [hC]; simp only [List.length_append, List.length_cons]; omega)
          i (by rw [e2]; exact hi2)
        omega
      exact hTr _ (legal _ hmem) (n + j) (by omega) hold i hi
  · show (pre ++ post.map T).length < C.gates.length
    rw [hC]
    simp


lemma getD_left (A L : List Bool) (a : ℕ) (ha : a < A.length) :
    (A ++ L).getD a false = A.getD a false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left ha]


lemma rn_eq_sk (N u i : ℕ) (hi : i ≠ N) : rn N u i = sk N i := by
  unfold rn sk
  split_ifs <;> simp_all

lemma erase_guarded_and (n : ℕ) (C : Circuit) (pre post : List Gate)
    (u v p : ℕ)
    (hC : C.gates = pre ++ ⟨GateOp.and, [u, v]⟩ :: post)
    (hao : PEqualNP.TopForm.IsAO2 n C)
    (hu : u < n + pre.length) (hv : v < n + pre.length) (hp : p < n + pre.length)
    (hguard : ∀ x : Fin n → Bool,
      (wf pre (List.ofFn x)).getD p false = true →
        (wf pre (List.ofFn x)).getD v false = true)
    (hread : ∀ g ∈ post, n + pre.length ∈ g.inputs →
      g.op = GateOp.and ∧ p ∈ g.inputs)
    (hout : C.output ≠ n + pre.length) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧
      circuitFun n D = circuitFun n C := by
  let N := n + pre.length
  let D : Circuit := ⟨pre ++ post.map (Tc N u), rn N u C.output⟩
  have hmono : Monotone2 C := by
    intro g hg
    exact ⟨hao.1 g hg, (hao.2.2 g hg).le⟩
  have hpost (g : Gate) (hg : g ∈ post) : g ∈ C.gates := by
    rw [hC]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hg)))
  obtain ⟨hm, hr, hs⟩ := asm n C pre post ⟨GateOp.and, [u, v]⟩ hC
    (Tc N u) (rn N u C.output) hmono hao.2.1 (Tc_legal N u)
      (fun g _ M hM hi => Tc_rb N u hu g M hM hi)
  have hAO : PEqualNP.TopForm.IsAO2 n D := by
    refine ⟨fun g hg => (legal_of D hm g hg).1, hr, ?_⟩
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hao.2.2 g (by rw [hC]; exact List.mem_append.mpr (Or.inl hg))
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      simpa [Tc] using hao.2.2 g' (hpost g' hg')
  refine ⟨D, hAO, hs, ?_⟩
  funext x
  let A := wf pre (List.ofFn x)
  let b := A.getD u false && A.getD v false
  have hN : A.length = N := by simp [A, N, wf_len]
  have hb : (GateOp.and).eval ([u, v].map fun i => A.getD i false) = b := by
    simp [GateOp.eval, b]
  have hTp : ∀ g ∈ post, ∀ E : List Bool,
      g.op.eval (g.inputs.map fun i => (A ++ b :: E).getD i false) =
        (Tc N u g).op.eval ((Tc N u g).inputs.map fun i => (A ++ E).getD i false) := by
    intro g hg E
    by_cases hn : N ∈ g.inputs
    · obtain ⟨hop, hpin⟩ := hread g hg hn
      obtain ⟨a, c, hac⟩ := List.length_eq_two.mp (hao.2.2 g (hpost g hg))
      have hn' : N = a ∨ N = c := by simpa [hac] using hn
      have hp' : p = a ∨ p = c := by simpa [hac] using hpin
      have hpair : g.inputs = [N, p] ∨ g.inputs = [p, N] := by
        rcases hn' with hn' | hn' <;> rcases hp' with hp' | hp'
        · omega
        · left; simpa only [← hn', ← hp'] using hac
        · right; simpa only [← hn', ← hp'] using hac
        · omega
      have rnN : rn N u N = u := by simp [rn]
      have hpN : p < N := hp
      have rnp : rn N u p = p := by simp [rn, hpN]
      have hmid := getD_mid A E b N hN
      have hpold : (A ++ b :: E).getD p false = A.getD p false :=
        getD_left A _ p (by omega)
      have hpnew : (A ++ E).getD p false = A.getD p false :=
        getD_left A _ p (by omega)
      have hunew : (A ++ E).getD u false = A.getD u false :=
        getD_left A _ u (by omega)
      have hgu : A.getD p false = true → A.getD v false = true := hguard x
      rcases hpair with hpair | hpair <;>
        simp only [Tc, hpair, hop, List.map_cons, List.map_nil, rnN, rnp,
          hmid, hpold, hpnew, hunew, GateOp.eval, List.all_cons, List.all_nil,
          id_eq, Bool.and_true]
      all_goals cases hpa : A.getD p false <;> cases hva : A.getD v false <;>
        cases hua : A.getD u false <;> simp_all [b]
    · change g.op.eval _ = g.op.eval ((g.inputs.map (rn N u)).map _)
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hiN : i ≠ N := fun e => hn (e ▸ hi)
      change (A ++ b :: E).getD i false = (A ++ E).getD (rn N u i) false
      rw [rn_eq_sk N u i hiN]
      exact (getD_sk A E b N hN i hiN).symm
  obtain ⟨E, hold, hnew⟩ := ev pre post ⟨GateOp.and, [u, v]⟩
    (Tc N u) (List.ofFn x) b hb hTp
  change (wf (pre ++ post.map (Tc N u)) (List.ofFn x)).getD (rn N u C.output) false =
    (wf C.gates (List.ofFn x)).getD C.output false
  rw [hC, hold, hnew, rn_eq_sk N u C.output hout]
  exact getD_sk A E b N hN C.output hout


lemma wf_ext : ∀ (gs : List Gate) (w : List Bool), ∃ E : List Bool, wf gs w = w ++ E := by
  intro gs
  induction gs with
  | nil => intro w; exact ⟨[], (List.append_nil w).symm⟩
  | cons g gs ih =>
    intro w
    obtain ⟨E, hE⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: E, ?_⟩
    rw [wf_cons, hE, List.append_assoc]
    rfl

lemma old_wires (pre post : List Gate) (g : Gate) (x : List Bool) :
    ∃ E : List Bool, wf (pre ++ g :: post) x
      = wf pre x ++ g.op.eval (g.inputs.map fun i => (wf pre x).getD i false) :: E := by
  obtain ⟨E, hE⟩ := wf_ext post
    (wf pre x ++ [g.op.eval (g.inputs.map fun i => (wf pre x).getD i false)])
  refine ⟨E, ?_⟩
  rw [wf_append, wf_cons, hE, List.append_assoc]
  rfl

lemma prefix_and_implies_input (n : ℕ) (pre : List Gate) (i a v : ℕ)
    (hfirst : pre[i]? = some ⟨GateOp.and, [a, v]⟩) (hv : v < n + i) :
    ∀ x : Fin n → Bool, (wf pre (List.ofFn x)).getD (n + i) false = true →
      (wf pre (List.ofFn x)).getD v false = true := by
  intro x hp
  have hi : i < pre.length := (List.getElem?_eq_some_iff.mp hfirst).1
  obtain ⟨before, after, g, hpre, hlen, hg⟩ := split_gates pre i hi
  have hgeq : g = ⟨GateOp.and, [a, v]⟩ := by
    simpa only [List.getElem?_eq_getElem hi, hg, Option.some.injEq] using hfirst
  subst g
  rw [hgeq] at hpre
  obtain ⟨E, hE⟩ := old_wires before after ⟨GateOp.and, [a, v]⟩ (List.ofFn x)
  rw [← hpre] at hE
  have hW : (wf before (List.ofFn x)).length = n + i := by simp [wf_len, hlen]
  rw [hE, getD_mid _ E _ (n + i) hW] at hp
  have hp' : (wf before (List.ofFn x)).getD a false = true ∧
      (wf before (List.ofFn x)).getD v false = true := by
    simpa [GateOp.eval] using hp
  rw [hE, getD_left _ _ v (by omega)]
  exact hp'.2

lemma erase_shared_factor (n : ℕ) (C : Circuit) (pre post : List Gate)
    (a u v i : ℕ)
    (hC : C.gates = pre ++ ⟨GateOp.and, [u, v]⟩ :: post)
    (hao : PEqualNP.TopForm.IsAO2 n C)
    (hfirst : pre[i]? = some ⟨GateOp.and, [a, v]⟩)
    (hu : u < n + pre.length) (hv : v < n + i)
    (hread : ∀ g ∈ post, n + pre.length ∈ g.inputs →
      g.op = GateOp.and ∧ n + i ∈ g.inputs)
    (hout : C.output ≠ n + pre.length) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧
      circuitFun n D = circuitFun n C := by
  have hi : i < pre.length := (List.getElem?_eq_some_iff.mp hfirst).1
  exact erase_guarded_and n C pre post u v (n + i) hC hao hu (by omega) (by omega)
    (prefix_and_implies_input n pre i a v hfirst hv) hread hout

lemma least_no_shared_factor (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (pre post : List Gate) (a u v i : ℕ)
    (hleast : PEqualNP.TopForm.IsLeastAO G C)
    (hC : C.gates = pre ++ ⟨GateOp.and, [u, v]⟩ :: post)
    (hfirst : pre[i]? = some ⟨GateOp.and, [a, v]⟩)
    (hu : u < n + pre.length) (hv : v < n + i)
    (hread : ∀ g ∈ post, n + pre.length ∈ g.inputs →
      g.op = GateOp.and ∧ n + i ∈ g.inputs)
    (hout : C.output ≠ n + pre.length) : False := by
  obtain ⟨D, hao, hsize, hfun⟩ := erase_shared_factor n C pre post a u v i hC
    hleast.1 hfirst hu hv hread hout
  have hle := hleast.2.2 D hao (hfun.trans hleast.2.1)
  omega

end GuardedErase

end PEqualNP.Outside.L_meta_2584
