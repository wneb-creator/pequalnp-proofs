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



lemma vector_decodes_word {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (w : ℕ) (v : List ℕ) (hv : v ∈ vecs n C S w) :
    ∃ t ∈ words n C w, (∀ i ∈ t, i ∈ S) ∧ encode S t = v := by
  induction w using Nat.strong_induction_on generalizing v with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · have hi : w < ((List.range n).map (leafVectors S 2)).length := by simpa using hb
      rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi] at hv
      simp only [List.getElem_map, List.getElem_range, leafVectors] at hv
      by_cases hsw : w ∈ S
      · simp only [hsw, ite_true, List.mem_singleton] at hv
        refine ⟨[w], ?_, ?_, ?_⟩
        · rw [words_input C hb]
          rfl
        · intro i hi
          simpa only [List.mem_singleton.mp hi] using hsw
        · rw [hv]
          unfold encode
          apply List.map_congr_left
          intro a _
          by_cases hea : a = w
          · simp [hea]
          · simp [hea, Ne.symm hea]
      · simp [hsw] at hv
    · have hlen : ((List.range n).map (leafVectors S 2)).length = n := by simp
      have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
      rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
      rw [hvec] at hv
      rcases op_kind h k with ho | ho
      · rw [ho] at hv
        change v ∈ andStep 2 (andStep 2 [S.map (fun _ => 0)]
          (vecs n C S (operand C k 0))) (vecs n C S (operand C k 1)) at hv
        obtain ⟨u, hu, b, hb, rfl⟩ := (mem_andStep_two _ _ _).mp hv
        obtain ⟨z, hz, a, ha, rfl⟩ := (mem_andStep_two _ _ _).mp hu
        have hz' : z = S.map (fun _ => 0) := List.mem_singleton.mp hz
        subst z
        obtain ⟨ta, hta, hsa, rfl⟩ := ih _ (earlier h k 0) a ha
        obtain ⟨tb, htb, hsb, rfl⟩ := ih _ (earlier h k 1) b hb
        refine ⟨ta ++ tb, ?_, ?_, ?_⟩
        · rw [words_gate h k, ho]
          exact ⟨ta, hta, tb, htb, rfl⟩
        · intro i hi
          exact (List.mem_append.mp hi).elim (hsa i) (hsb i)
        · rw [← encode_nil, encode_append, List.nil_append, encode_append]
      · rw [ho] at hv
        change v ∈ (vecs n C S (operand C k 1)).foldl insertNew
          ((vecs n C S (operand C k 0)).foldl insertNew []) at hv
        rw [mem_fold_insertNew, mem_fold_insertNew] at hv
        simp only [List.not_mem_nil, false_or] at hv
        rcases hv with hv | hv
        · obtain ⟨t, ht, hs, he⟩ := ih _ (earlier h k 0) v hv
          refine ⟨t, ?_, hs, he⟩
          rw [words_gate h k, ho]
          exact Or.inl ht
        · obtain ⟨t, ht, hs, he⟩ := ih _ (earlier h k 1) v hv
          refine ⟨t, ?_, hs, he⟩
          rw [words_gate h k, ho]
          exact Or.inr ht
    · rw [vec_eval, List.getD_eq_default _ _ (by simp [evalFrom_length, Circuit.size] at *; omega)] at hv
      simp at hv



lemma reads_two_iff_word {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) : readsAtMost C n S 2 = true ↔
      ∃ t ∈ words n C C.output, (∀ i ∈ t, i ∈ S) ∧ ∀ i ∈ S, t.count i ≤ 2 := by
  constructor
  · intro hr
    obtain ⟨v, hv, hbound⟩ := List.any_eq_true.mp hr
    obtain ⟨t, ht, hs, he⟩ := vector_decodes_word h S C.output v hv
    refine ⟨t, ht, hs, ?_⟩
    intro i hi
    have hm : min (t.count i) 3 ∈ v := by
      rw [← he]
      exact List.mem_map.mpr ⟨i, hi, rfl⟩
    have hc : min (t.count i) 3 ≤ 2 := of_decide_eq_true (List.all_eq_true.mp hbound _ hm)
    omega
  · rintro ⟨t, ht, hs, hc⟩
    apply List.any_eq_true.mpr
    refine ⟨encode S t, encoded_mem h _ _ _ ht hs, ?_⟩
    apply List.all_eq_true.mpr
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
    exact decide_eq_true ((Nat.min_le_left _ _).trans (hc i hi))

lemma read_two_of_word_sim {n : ℕ} {C D : Circuit}
    (hC : PEqualNP.TopForm.IsAO2 n C) (hD : PEqualNP.TopForm.IsAO2 n D)
    (hfun : circuitFun n D = circuitFun n C)
    (hsim : ∀ t ∈ words n C C.output,
      ∃ u ∈ words n D D.output, u.Sublist t)
    (hr : IsReadK n C 2) : IsReadK n D 2 := by
  intro S hS
  have hSC : IsPrimeImplicant n C S := by
    simpa only [IsPrimeImplicant, hfun] using hS
  obtain ⟨t, ht, hs, hc⟩ := (reads_two_iff_word hC (setList S)).mp (hr S hSC)
  obtain ⟨u, hu, hut⟩ := hsim t ht
  apply (reads_two_iff_word hD (setList S)).mpr
  exact ⟨u, hu, fun i hi => hs i (hut.subset hi),
    fun i hi => (List.Sublist.count_le i hut).trans (hc i hi)⟩



lemma reads_two_of_word_sim {n : ℕ} {C D : Circuit}
    (hC : PEqualNP.TopForm.IsAO2 n C) (hD : PEqualNP.TopForm.IsAO2 n D)
    (hsim : ∀ t ∈ words n C C.output,
      ∃ u ∈ words n D D.output, u.Sublist t)
    (S : List ℕ) (hr : readsAtMost C n S 2 = true) : readsAtMost D n S 2 = true := by
  obtain ⟨t, ht, hs, hc⟩ := (reads_two_iff_word hC S).mp hr
  obtain ⟨u, hu, hut⟩ := hsim t ht
  apply (reads_two_iff_word hD S).mpr
  exact ⟨u, hu, fun i hi => hs i (hut.subset hi),
    fun i hi => (List.Sublist.count_le i hut).trans (hc i hi)⟩


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

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma val_monotone {n : ℕ} {C : Circuit} (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) (w : ℕ) :
    val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · simpa only [val_ofFn C x ⟨w, hn⟩, val_ofFn C y ⟨w, hn⟩] using hxy ⟨w, hn⟩
    by_cases hw : w < n + C.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      rcases hAO _ (gateAt_mem hj) with hand | hor
      · rw [val_and (by simp) hj hand, val_and (by simp) hj hand]
        intro hx i hi
        exact ⟨(hx i hi).1, ih i (hx i hi).1 (hx i hi).2⟩
      · rw [val_or (by simp) hj hor, val_or (by simp) hj hor]
        rintro ⟨i, hi, hlt, hx⟩
        exact ⟨i, hi, hlt, ih i hlt hx⟩
    · rw [val_ge (n := n) (by simp) (by omega)]
      simp

def singletonInputs (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun u => val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u u)) w = true)

lemma singleton_input_pair_value {n : ℕ} {C : Circuit} (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    {w : ℕ} {u : Fin n} (hu : u ∈ singletonInputs n C w) (v : Fin n) :
    val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) w = true := by
  simp only [singletonInputs, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  exact val_monotone hAO _ _ (by
    intro p hp
    simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq, or_self] at hp
    subst p
    exact pairInput_left u v) w hu

lemma singletonInputs_subset_of_orReaches {n : ℕ} {C : Circuit} {w g : ℕ}
    (hr : OrReaches n C w g) : singletonInputs n C (n + g) ⊆ singletonInputs n C w := by
  intro u hu
  simp only [singletonInputs, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  exact orStep_up (by simp) (orReaches_reach g w hr).1 hu

lemma orIn_subset_singletonInputs {n : ℕ} {C : Circuit} {w : ℕ} :
    orIn n C w ⊆ singletonInputs n C w := by
  intro u hu
  simp only [singletonInputs, Finset.mem_filter, Finset.mem_univ, true_and]
  exact orIn_value hu _ (pairInput_left u u)

lemma singleton_sides_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (a : ℕ) (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ singletonInputs n C (opnd C a 0))
    (hv : v ∈ singletonInputs n C (opnd C a 1)) : G.Adj u v := by
  obtain ⟨hAO, hRB, h2⟩ := hAO
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨halen, hop, hbel⟩ := ha
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (h2 _ (gateAt_mem halen))
  have hp : p < n + a := hRB a halen p (by rw [hin]; simp)
  have hq : q < n + a := hRB a halen q (by rw [hin]; simp)
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  rw [e0] at hu
  rw [e1] at hv
  apply (graphFun_pair G u v).mp
  apply hbel
  rw [gateVal_eq_val, val_and (by simp) halen hop, hin]
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨hp, singleton_input_pair_value hAO hu v⟩
  · refine ⟨hq, ?_⟩
    have hcomm : PEqualNP.EdgeOwnership.pairInput v u = PEqualNP.EdgeOwnership.pairInput u v := by
      funext x
      simp only [PEqualNP.EdgeOwnership.pairInput, or_comm]
    rw [← hcomm]
    exact singleton_input_pair_value hAO hv u

lemma singleton_opposite_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (a : ℕ) (ha : a ∈ tops G C)
    (b : Fin 2) {u v : Fin n} (hu : u ∈ singletonInputs n C (opnd C a b))
    (hv : v ∈ singletonInputs n C (opnd C a b.rev)) : G.Adj u v := by
  fin_cases b
  · exact singleton_sides_adj G C hAO a ha hu hv
  · exact (singleton_sides_adj G C hAO a ha hv hu).symm

lemma shared_singleton_region_center_unique {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {a a' g : ℕ} (ha : a ∈ tops G C) (ha' : a' ∈ tops G C)
    (b b' : Fin 2) (hr : OrReaches n C (opnd C a b) g)
    (hr' : OrReaches n C (opnd C a' b') g)
    (hlarge : 1 < (singletonInputs n C (n + g)).card) {u v : Fin n}
    (hu : u ∈ singletonInputs n C (opnd C a b.rev))
    (hv : v ∈ singletonInputs n C (opnd C a' b'.rev)) : u = v := by
  by_contra hne
  have hsub : singletonInputs n C (n + g) ⊆ Finset.univ.filter (fun x => G.Adj u x ∧ G.Adj v x) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(singleton_opposite_adj G C hAO a ha b (singletonInputs_subset_of_orReaches hr hx) hu).symm,
      (singleton_opposite_adj G C hAO a' ha' b' (singletonInputs_subset_of_orReaches hr' hx) hv).symm⟩
  have hcard := Finset.card_le_card hsub
  have hbound := h4 u v hne
  omega

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma graphFun_eq_of_pair_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y : Fin n → Bool, (∀ u, x u = true → y u = true) → f x = true → f y = true)
    (hsound : ∀ x, f x = true → graphFun G ∅ x = true)
    (hpairs : ∀ u v, G.Adj u v → f (PEqualNP.EdgeOwnership.pairInput u v) = true) :
    f = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact hsound x
  · intro hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq] at hx
    obtain ⟨u, v, huv, hu, hv⟩ := hx
    apply hmono _ x _ (hpairs u v huv)
    intro w hw
    rcases (pairInput_true u v w).mp hw with rfl | rfl
    · exact hu
    · exact hv

lemma circuit_graphFun_eq_of_pair_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly D)
    (hsound : ∀ x, PEqualNP.MetaComplexity.circuitFun n D x = true → graphFun G ∅ x = true)
    (hpairs : ∀ u v, G.Adj u v →
      PEqualNP.MetaComplexity.circuitFun n D (PEqualNP.EdgeOwnership.pairInput u v) = true) :
    PEqualNP.MetaComplexity.circuitFun n D = graphFun G ∅ :=
  graphFun_eq_of_pair_cover G _ (fun x y hxy => val_monotone hAO x y hxy D.output) hsound hpairs

lemma incidence_eq_of_pair_cover {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (f : (Fin (P + L) → Bool) → Bool)
    (hmono : ∀ x y : Fin (P + L) → Bool,
      (∀ u, x u = true → y u = true) → f x = true → f y = true)
    (hsound : ∀ x, f x = true →
      decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) = true)
    (hpairs : ∀ p l, I p l →
      f (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd L p) (Fin.natAdd P l)) = true) :
    f = fun x => decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact hsound x
  · intro hx
    rw [decide_eq_true_eq] at hx
    obtain ⟨p, l, hpl, hp, hl⟩ := hx
    apply hmono _ x _ (hpairs p l hpl)
    intro w hw
    rcases (pairInput_true (Fin.castAdd L p) (Fin.natAdd P l) w).mp hw with rfl | rfl
    · exact hp
    · exact hl

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma opposite_singletons_empty_of_no_common_neighbor {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    (b : Fin 2) {u v : Fin n}
    (hu : u ∈ singletonInputs n C (opnd C a b))
    (hv : v ∈ singletonInputs n C (opnd C a b))
    (hnone : ∀ w, ¬(G.Adj u w ∧ G.Adj v w)) :
    singletonInputs n C (opnd C a b.rev) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  exact hnone w ⟨singleton_opposite_adj G C hAO a ha b hu hw,
    singleton_opposite_adj G C hAO a ha b hv hw⟩

lemma shared_region_opposite_empty_of_no_common_neighbor {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) {a g : ℕ} (ha : a ∈ tops G C)
    (b : Fin 2) (hr : OrReaches n C (opnd C a b) g) {u v : Fin n}
    (hu : u ∈ singletonInputs n C (n + g))
    (hv : v ∈ singletonInputs n C (n + g))
    (hnone : ∀ w, ¬(G.Adj u w ∧ G.Adj v w)) :
    singletonInputs n C (opnd C a b.rev) = ∅ :=
  opposite_singletons_empty_of_no_common_neighbor G C hAO ha b
    (singletonInputs_subset_of_orReaches hr hu) (singletonInputs_subset_of_orReaches hr hv) hnone

end Sharing

namespace ChoiceErase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2584.GuardedErase

lemma forall₂_getD {xs ys : List Bool}
    (h : List.Forall₂ (fun a b => a = true → b = true) xs ys) (i : ℕ) :
    xs.getD i false = true → ys.getD i false = true := by
  induction h generalizing i with
  | nil => simp
  | @cons a b xs ys hab h ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

lemma forall₂_prefix (A : List Bool) {xs ys : List Bool}
    (h : List.Forall₂ (fun a b => a = true → b = true) xs ys) :
    List.Forall₂ (fun a b => a = true → b = true) (A ++ xs) (A ++ ys) := by
  induction A with
  | nil => exact h
  | cons a A ih => exact .cons (fun h => h) ih

lemma forall₂_snoc {xs ys : List Bool} {a b : Bool}
    (h : List.Forall₂ (fun x y => x = true → y = true) xs ys) (hab : a = true → b = true) :
    List.Forall₂ (fun x y => x = true → y = true) (xs ++ [a]) (ys ++ [b]) := by
  induction h with
  | nil => exact .cons hab .nil
  | cons hxy h ih => exact .cons hxy ih

lemma gate_imp (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (f f' : ℕ → Bool) (hf : ∀ i ∈ g.inputs, f i = true → f' i = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hg with hg | hg
  · rw [hg]
    intro hv
    apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hf i hi ((List.all_eq_true.mp hv) _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · rw [hg]
    intro hv
    obtain ⟨b, hb, hbtrue⟩ := List.any_eq_true.mp hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact List.any_eq_true.mpr ⟨f' i, List.mem_map.mpr ⟨i, hi, rfl⟩, hf i hi hbtrue⟩

lemma surg_le (T : Gate → Gate) (A : List Bool) (b : Bool) (post : List Gate)
    (hT : ∀ g ∈ post, ∀ E E' : List Bool,
      List.Forall₂ (fun a b => a = true → b = true) E E' →
      g.op.eval (g.inputs.map fun i => (A ++ b :: E).getD i false) = true →
        (T g).op.eval ((T g).inputs.map fun i => (A ++ E').getD i false) = true) :
    ∀ E E' : List Bool,
      List.Forall₂ (fun a b => a = true → b = true) E E' →
      ∀ o, o ≠ A.length → (wf post (A ++ b :: E)).getD o false = true →
        (wf (post.map T) (A ++ E')).getD (sk A.length o) false = true := by
  induction post with
  | nil =>
    intro E E' h o ho hv
    apply forall₂_getD (forall₂_prefix A h) (sk A.length o)
    exact (getD_sk A E b A.length rfl o ho).trans hv
  | cons g post ih =>
    intro E E' h o ho hv
    let v := g.op.eval (g.inputs.map fun i => (A ++ b :: E).getD i false)
    let v' := (T g).op.eval ((T g).inputs.map fun i => (A ++ E').getD i false)
    have hvv : v = true → v' = true := hT g (by simp) E E' h
    have hh : List.Forall₂ (fun a b => a = true → b = true) (E ++ [v]) (E' ++ [v']) :=
      forall₂_snoc h hvv
    have htail := ih (fun g' hg' => hT g' (by simp [hg']))
      (E ++ [v]) (E' ++ [v']) hh o ho
    change (wf (post.map T) ((A ++ E') ++ [v'])).getD (sk A.length o) false = true
    rw [List.append_assoc]
    apply htail
    simpa only [wf_cons, List.append_assoc, List.cons_append] using hv

lemma erase_choice_and (n : ℕ) (C : Circuit) (pre post : List Gate)
    (u v : ℕ) (choose : Gate → ℕ)
    (hC : C.gates = pre ++ ⟨GateOp.and, [u, v]⟩ :: post)
    (hao : PEqualNP.TopForm.IsAO2 n C)
    (hu : u < n + pre.length) (hv : v < n + pre.length)
    (hchoose : ∀ g, choose g = u ∨ choose g = v)
    (hinputs : ∀ g ∈ post, n + pre.length ∈ g.inputs →
      ∀ i ∈ g.inputs, i < n + pre.length ∨ i = n + pre.length)
    (hbelow : ∀ x : Fin n → Bool, circuitFun n C x = false →
      ∀ g ∈ post, n + pre.length ∈ g.inputs →
      g.op.eval (g.inputs.map fun i =>
        if i = n + pre.length then (wf pre (List.ofFn x)).getD (choose g) false
        else (wf pre (List.ofFn x)).getD i false) = false)
    (hout : C.output ≠ n + pre.length) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧
      circuitFun n D = circuitFun n C := by
  let N := n + pre.length
  let T := fun g => Tc N (choose g) g
  let D : Circuit := ⟨pre ++ post.map T, sk N C.output⟩
  have hchoice (g : Gate) : choose g < N := by rcases hchoose g with h | h <;> omega
  have hmono : Monotone2 C := fun g hg => ⟨hao.1 g hg, (hao.2.2 g hg).le⟩
  have hpost (g : Gate) (hg : g ∈ post) : g ∈ C.gates := by
    rw [hC]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hg)))
  obtain ⟨hm, hr, hs⟩ := asm n C pre post ⟨GateOp.and, [u, v]⟩ hC T
    (sk N C.output) hmono hao.2.1 (fun g => Tc_legal N (choose g) g)
      (fun g _ M hM hi => Tc_rb N (choose g) (hchoice g) g M hM hi)
  have hAO : PEqualNP.TopForm.IsAO2 n D := by
    refine ⟨fun g hg => (legal_of D hm g hg).1, hr, ?_⟩
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hao.2.2 g (by rw [hC]; exact List.mem_append.mpr (Or.inl hg))
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
      simpa [T, Tc] using hao.2.2 g' (hpost g' hg')
  refine ⟨D, hAO, hs, ?_⟩
  funext x
  let A := wf pre (List.ofFn x)
  let b := A.getD u false && A.getD v false
  have hN : A.length = N := by simp [A, N, wf_len]
  have hb : (GateOp.and).eval ([u, v].map fun i => A.getD i false) = b := by
    simp [GateOp.eval, b]
  have hImp : ∀ g ∈ post, ∀ E E' : List Bool,
      List.Forall₂ (fun a b => a = true → b = true) E E' →
      g.op.eval (g.inputs.map fun i => (A ++ b :: E).getD i false) = true →
        (T g).op.eval ((T g).inputs.map fun i => (A ++ E').getD i false) = true := by
    intro g hg E E' hEE
    change g.op.eval _ = true → g.op.eval ((g.inputs.map (rn N (choose g))).map _) = true
    rw [List.map_map]
    apply gate_imp g (hao.1 g (hpost g hg))
    intro i hi htrue
    by_cases hiN : i = N
    · subst i
      rw [getD_mid A E b N hN] at htrue
      have hc : A.getD (choose g) false = true := by
        have hboth : A.getD u false = true ∧ A.getD v false = true := by
          simpa only [b, Bool.and_eq_true] using htrue
        rcases hchoose g with hc | hc
        · simpa only [hc] using hboth.1
        · simpa only [hc] using hboth.2
      change (A ++ E').getD (rn N (choose g) N) false = true
      have hrn : rn N (choose g) N = choose g := by simp [rn]
      rw [hrn, getD_left A E' _ (by have := hchoice g; omega)]
      exact hc
    · change (A ++ E').getD (rn N (choose g) i) false = true
      rw [rn_eq_sk N (choose g) i hiN]
      apply forall₂_getD (forall₂_prefix A hEE) (sk N i)
      exact (getD_sk A E b N hN i hiN).trans htrue
  cases hF : circuitFun n C x with
  | false =>
    have hEq : ∀ g ∈ post, ∀ E : List Bool,
        g.op.eval (g.inputs.map fun i => (A ++ b :: E).getD i false) =
          (T g).op.eval ((T g).inputs.map fun i => (A ++ E).getD i false) := by
      intro g hg E
      by_cases hn : N ∈ g.inputs
      · have hnew : (T g).op.eval ((T g).inputs.map fun i => (A ++ E).getD i false) = false := by
          have hbound := hbelow x hF g hg hn
          change g.op.eval ((g.inputs.map (rn N (choose g))).map _) = false
          rw [List.map_map]
          convert hbound using 1
          congr 1
          apply List.map_congr_left
          intro i hi
          rcases hinputs g hg hn i hi with hil | hie
          · have hiN : i ≠ N := ne_of_lt hil
            change (A ++ E).getD (rn N (choose g) i) false =
              if i = N then A.getD (choose g) false else A.getD i false
            rw [if_neg hiN]
            have hilN : i < N := hil
            have hrn : rn N (choose g) i = i := by simp [rn, hilN]
            rw [hrn, getD_left A E i (by omega)]
          · change i = N at hie
            subst i
            change (A ++ E).getD (rn N (choose g) N) false =
              if N = N then A.getD (choose g) false else A.getD N false
            simp only [ite_true]
            have hrn : rn N (choose g) N = choose g := by simp [rn]
            rw [hrn, getD_left A E _ (by have := hchoice g; omega)]
        have hold : g.op.eval (g.inputs.map fun i => (A ++ b :: E).getD i false) = false := by
          cases he : g.op.eval (g.inputs.map fun i => (A ++ b :: E).getD i false) with
          | false => rfl
          | true =>
            have hEE : List.Forall₂ (fun a b => a = true → b = true) E E := by
              simpa using forall₂_prefix E (List.Forall₂.nil (R := fun a b : Bool => a = true → b = true))
            have ht := hImp g hg E E hEE he
            rw [hnew] at ht
            cases ht
        exact hold.trans hnew.symm
      · change g.op.eval _ = g.op.eval ((g.inputs.map (rn N (choose g))).map _)
        rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hiN : i ≠ N := fun he => hn (he ▸ hi)
        change (A ++ b :: E).getD i false = (A ++ E).getD (rn N (choose g) i) false
        rw [rn_eq_sk N (choose g) i hiN]
        exact (getD_sk A E b N hN i hiN).symm
    obtain ⟨E, hold, hnew⟩ := ev pre post ⟨GateOp.and, [u, v]⟩ T (List.ofFn x) b hb hEq
    have heq : circuitFun n D x = circuitFun n C x := by
      change (wf (pre ++ post.map T) (List.ofFn x)).getD (sk N C.output) false =
        (wf C.gates (List.ofFn x)).getD C.output false
      rw [hC, hold, hnew]
      exact getD_sk A E b N hN C.output hout
    exact heq.trans hF
  | true =>
    have hold : (wf post (A ++ b :: [])).getD C.output false = true := by
      change (wf C.gates (List.ofFn x)).getD C.output false = true at hF
      rw [hC, wf_append, wf_cons, hb] at hF
      exact hF
    have hh := surg_le T A b post hImp [] [] .nil C.output (by simpa only [hN] using hout) hold
    change (wf (pre ++ post.map T) (List.ofFn x)).getD (sk N C.output) false = true
    rw [wf_append]
    simpa only [List.append_nil, hN] using hh

end ChoiceErase

namespace Rotation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

def AgreeExcept (k : ℕ) (w v : List Bool) : Prop :=
  w.length = v.length ∧ ∀ i, i ≠ k → w.getD i false = v.getD i false

lemma snoc_ne (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hlt : i < w.length
  · exact List.getD_append _ _ _ _ hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma snoc_eq (w : List Bool) (b : Bool) : (w ++ [b]).getD w.length false = b := by simp

lemma agree_step (k : ℕ) (w v : List Bool) (g : Gate)
    (h : AgreeExcept k w v) (hg : ∀ i ∈ g.inputs, i ≠ k) :
    AgreeExcept k (step w g) (step v g) := by
  obtain ⟨hlen, hget⟩ := h
  have he : g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => v.getD i false) := by
    congr 1
    exact List.map_congr_left (fun i hi => hget i (hg i hi))
  constructor
  · simp [step, hlen]
  · intro i hi
    unfold step
    by_cases hit : i = w.length
    · subst i
      rw [snoc_eq, hlen, snoc_eq]
      exact he
    · rw [snoc_ne _ _ _ hit, snoc_ne _ _ _ (by omega)]
      exact hget i hi

lemma agree_run (k : ℕ) (w v : List Bool) (gs : List Gate)
    (h : AgreeExcept k w v) (hg : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ≠ k) :
    AgreeExcept k (run gs w) (run gs v) := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    apply ih (step w g) (step v g)
    · exact agree_step k w v g h (hg g List.mem_cons_self)
    · exact fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')

lemma bool_rotate (x a b : Bool) (h : x = true → b = true) :
    ((x || a) && b) = (x || (a && b)) := by
  cases x <;> cases a <;> cases b <;> simp_all

lemma block (w : List Bool) (x a b : ℕ)
    (hx : x < w.length) (ha : a < w.length) (hb : b < w.length)
    (hdom : w.getD x false = true → w.getD b false = true) :
    AgreeExcept w.length
      (run [⟨.or, [x, a]⟩, ⟨.and, [w.length, b]⟩] w)
      (run [⟨.and, [a, b]⟩, ⟨.or, [x, w.length]⟩] w) := by
  let xv := w.getD x false
  let av := w.getD a false
  let bv := w.getD b false
  have he := bool_rotate xv av bv hdom
  have hold : run [⟨.or, [x, a]⟩, ⟨.and, [w.length, b]⟩] w =
      (w ++ [xv || av]) ++ [(xv || av) && bv] := by
    simp only [run, List.foldl_cons, List.foldl_nil, step, GateOp.eval,
      List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, Bool.or_false, Bool.and_true, id_eq]
    rw [snoc_eq, List.getD_append _ _ _ _ hb]
  have hnew : run [⟨.and, [a, b]⟩, ⟨.or, [x, w.length]⟩] w =
      (w ++ [av && bv]) ++ [xv || (av && bv)] := by
    simp only [run, List.foldl_cons, List.foldl_nil, step, GateOp.eval,
      List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      List.all_cons, List.all_nil, Bool.or_false, Bool.and_true, id_eq]
    rw [snoc_eq, List.getD_append _ _ _ _ hx]
  rw [hold, hnew, he]
  constructor
  · simp
  · intro i hi
    by_cases hl : i = w.length + 1
    · subst i
      have hlen (r : Bool) : (w ++ [r]).length = w.length + 1 := by simp
      rw [← hlen (xv || av), snoc_eq]
      rw [show (w ++ [xv || av]).length = (w ++ [av && bv]).length by simp, snoc_eq]
    · have skip (r s : Bool) : (w ++ [r] ++ [s]).getD i false = w.getD i false := by
        rw [snoc_ne _ _ _ (by simp; omega), snoc_ne _ _ _ hi]
      exact (skip _ _).trans (skip _ _).symm

lemma run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma adjacent_semantics (n : ℕ) (pre post : List Gate) (x a b o : ℕ)
    (hx : x < n + pre.length) (ha : a < n + pre.length) (hb : b < n + pre.length)
    (ho : o ≠ n + pre.length)
    (hprivate : ∀ g ∈ post, ∀ i ∈ g.inputs, i ≠ n + pre.length)
    (hdom : ∀ z : Fin n → Bool,
      (run pre (List.ofFn z)).getD x false = true →
      (run pre (List.ofFn z)).getD b false = true) :
    circuitFun n ⟨pre ++ [⟨.or, [x, a]⟩, ⟨.and, [n + pre.length, b]⟩] ++ post, o⟩ =
      circuitFun n ⟨pre ++ [⟨.and, [a, b]⟩, ⟨.or, [x, n + pre.length]⟩] ++ post, o⟩ := by
  funext z
  let w := run pre (List.ofFn z)
  have hw : w.length = n + pre.length := by simp [w, run_length]
  have hblock := block w x a b (by omega) (by omega) (by omega) (hdom z)
  rw [hw] at hblock
  have hpost := agree_run (n + pre.length) _ _ post hblock hprivate
  have hout := hpost.2 o ho
  dsimp only [run, w] at hout
  unfold step at hout
  simpa only [circuitFun, Circuit.eval, Circuit.wires, List.foldl_append] using hout

lemma adjacent_size (n : ℕ) (pre post : List Gate) (x a b o : ℕ) :
    (⟨pre ++ [⟨.or, [x, a]⟩, ⟨.and, [n + pre.length, b]⟩] ++ post, o⟩ : Circuit).size =
      (⟨pre ++ [⟨.and, [a, b]⟩, ⟨.or, [x, n + pre.length]⟩] ++ post, o⟩ : Circuit).size := by
  simp [Circuit.size]

lemma word_rotation (X A B : Set (List ℕ)) (t : List ℕ)
    (ht : ∃ u ∈ X ∪ A, ∃ v ∈ B, t = u ++ v) :
    ∃ s, (s ∈ X ∨ ∃ u ∈ A, ∃ v ∈ B, s = u ++ v) ∧ s.Sublist t := by
  obtain ⟨u, hu, v, hv, rfl⟩ := ht
  rcases hu with hu | hu
  · exact ⟨u, Or.inl hu, List.sublist_append_left _ _⟩
  · exact ⟨u ++ v, Or.inr ⟨u, hu, v, hv, rfl⟩, List.Sublist.refl _⟩


lemma block_get_other (pre post : List Gate) (u v u' v' : Gate) (j : ℕ)
    (hj : j ≠ pre.length) (hj' : j ≠ pre.length + 1) :
    (pre ++ [u, v] ++ post).getD j ⟨.or, []⟩ =
      (pre ++ [u', v'] ++ post).getD j ⟨.or, []⟩ := by
  by_cases hl : j < pre.length
  · rw [List.append_assoc, List.append_assoc]
    rw [List.getD_append pre _ _ j hl, List.getD_append pre _ _ j hl]
  · have hs (r s : Gate) : (pre ++ [r, s] ++ post).getD j ⟨.or, []⟩ =
        post.getD (j - pre.length - 2) ⟨.or, []⟩ := by
      rw [List.append_assoc]
      rw [List.getD_append_right pre _ _ j (by omega)]
      rw [List.getD_append_right [r, s] post _ (j - pre.length) (by simp; omega)]
      rfl
    exact (hs u v).trans (hs u' v').symm

lemma adjacent_ao2 (n : ℕ) (pre post : List Gate) (x a b o : ℕ)
    (hx : x < n + pre.length) (ha : a < n + pre.length) (hb : b < n + pre.length)
    (h : PEqualNP.TopForm.IsAO2 n
      ⟨pre ++ [⟨.or, [x, a]⟩, ⟨.and, [n + pre.length, b]⟩] ++ post, o⟩) :
    PEqualNP.TopForm.IsAO2 n
      ⟨pre ++ [⟨.and, [a, b]⟩, ⟨.or, [x, n + pre.length]⟩] ++ post, o⟩ := by
  let C : Circuit := ⟨pre ++ [⟨.or, [x, a]⟩, ⟨.and, [n + pre.length, b]⟩] ++ post, o⟩
  let D : Circuit := ⟨pre ++ [⟨.and, [a, b]⟩, ⟨.or, [x, n + pre.length]⟩] ++ post, o⟩
  have hc : C.gates.length = D.gates.length := by simp [C, D]
  have oldmem (g : Gate) (hm : g ∈ pre ∨ g ∈ post) : g ∈ C.gates := by
    simp only [C, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  have newcases (g : Gate) (hm : g ∈ D.gates) :
      (g ∈ pre ∨ g ∈ post) ∨ g = ⟨.and, [a, b]⟩ ∨ g = ⟨.or, [x, n + pre.length]⟩ := by
    simp only [D, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    tauto
  have hd0 : NestedCover.gateAt D pre.length = ⟨.and, [a, b]⟩ := by
    simp [NestedCover.gateAt, D, List.append_assoc, List.getD_eq_getElem?_getD]
  have hd1 : NestedCover.gateAt D (pre.length + 1) = ⟨.or, [x, n + pre.length]⟩ := by
    simp [NestedCover.gateAt, D, List.append_assoc, List.getD_eq_getElem?_getD]
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases newcases g hg with hm | rfl | rfl
    · exact h.1 g (oldmem g hm)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro j hj i hi
    by_cases hj0 : j = pre.length
    · subst j
      rw [hd0] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    by_cases hj1 : j = pre.length + 1
    · subst j
      rw [hd1] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
    have he : NestedCover.gateAt D j = NestedCover.gateAt C j := by
      exact block_get_other pre post _ _ _ _ j hj0 hj1
    rw [he] at hi
    exact h.2.1 j (by simpa [C, D] using hj) i hi
  · intro g hg
    rcases newcases g hg with hm | rfl | rfl
    · exact h.2.2 g (oldmem g hm)
    · rfl
    · rfl

lemma word_rotation_strict (X A B : Set (List ℕ)) (u v : List ℕ)
    (hu : u ∈ X) (hv : v ∈ B) (j : ℕ) (hj : j ∈ v) :
    (u ∈ X ∨ ∃ a ∈ A, ∃ b ∈ B, u = a ++ b) ∧
      u.Sublist (u ++ v) ∧ u.count j < (u ++ v).count j := by
  refine ⟨Or.inl hu, List.sublist_append_left _ _, ?_⟩
  rw [List.count_append]
  have := List.count_pos_iff.mpr hj
  omega


def wordOp : GateOp → List (Set (List ℕ)) → Set (List ℕ)
  | .or, [a, b] => a ∪ b
  | .and, [a, b] => {t | ∃ u ∈ a, ∃ v ∈ b, t = u ++ v}
  | _, _ => ∅

def wordStep (w : List (Set (List ℕ))) (g : Gate) : List (Set (List ℕ)) :=
  w ++ [wordOp g.op (g.inputs.map fun i => w.getD i ∅)]

def wordRun (gs : List Gate) (w : List (Set (List ℕ))) : List (Set (List ℕ)) :=
  gs.foldl wordStep w

def WSim (A B : Set (List ℕ)) : Prop := ∀ t ∈ A, ∃ s ∈ B, s.Sublist t

def WAgreeExcept (k : ℕ) (w v : List (Set (List ℕ))) : Prop :=
  w.length = v.length ∧ ∀ i, i ≠ k → WSim (w.getD i ∅) (v.getD i ∅)

lemma wsim_refl (A : Set (List ℕ)) : WSim A A := fun t ht => ⟨t, ht, List.Sublist.refl _⟩

lemma wsim_op (o : GateOp) (A B A' B' : Set (List ℕ))
    (ha : WSim A A') (hb : WSim B B') :
    WSim (wordOp o [A, B]) (wordOp o [A', B']) := by
  intro t ht
  cases o with
  | and =>
    obtain ⟨u, hu, v, hv, rfl⟩ := ht
    obtain ⟨u', hu', hus⟩ := ha u hu
    obtain ⟨v', hv', hvs⟩ := hb v hv
    exact ⟨u' ++ v', ⟨u', hu', v', hv', rfl⟩, hus.append hvs⟩
  | or =>
    rcases ht with ht | ht
    · obtain ⟨s, hs, hst⟩ := ha t ht
      exact ⟨s, Or.inl hs, hst⟩
    · obtain ⟨s, hs, hst⟩ := hb t ht
      exact ⟨s, Or.inr hs, hst⟩
  | not => simp [wordOp] at ht
  | mod m => simp [wordOp] at ht
  | maj => simp [wordOp] at ht

lemma wsnoc_ne (w : List (Set (List ℕ))) (b : Set (List ℕ)) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [b]).getD i ∅ = w.getD i ∅ := by
  by_cases hlt : i < w.length
  · exact List.getD_append _ _ _ _ hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma wsnoc_eq (w : List (Set (List ℕ))) (b : Set (List ℕ)) :
    (w ++ [b]).getD w.length ∅ = b := by simp

lemma wagree_step (k : ℕ) (w v : List (Set (List ℕ))) (g : Gate)
    (h : WAgreeExcept k w v) (hlen : g.inputs.length = 2)
    (hg : ∀ i ∈ g.inputs, i ≠ k) :
    WAgreeExcept k (wordStep w g) (wordStep v g) := by
  obtain ⟨hwv, hget⟩ := h
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  have ha := hg a (by simp [hab])
  have hb := hg b (by simp [hab])
  constructor
  · simp [wordStep, hwv]
  · intro i hi
    unfold wordStep
    by_cases hit : i = w.length
    · subst i
      rw [wsnoc_eq, hwv, wsnoc_eq, hab]
      exact wsim_op g.op _ _ _ _ (hget a ha) (hget b hb)
    · rw [wsnoc_ne _ _ _ hit, wsnoc_ne _ _ _ (by omega)]
      exact hget i hi

lemma wagree_run (k : ℕ) (w v : List (Set (List ℕ))) (gs : List Gate)
    (h : WAgreeExcept k w v)
    (hg : ∀ g ∈ gs, g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i ≠ k) :
    WAgreeExcept k (wordRun gs w) (wordRun gs v) := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    apply ih (wordStep w g) (wordStep v g)
    · exact wagree_step k w v g h (hg g List.mem_cons_self).1 (hg g List.mem_cons_self).2
    · exact fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')

lemma word_block (w : List (Set (List ℕ))) (x a b : ℕ)
    (hx : x < w.length) (ha : a < w.length) (hb : b < w.length) :
    WAgreeExcept w.length
      (wordRun [⟨.or, [x, a]⟩, ⟨.and, [w.length, b]⟩] w)
      (wordRun [⟨.and, [a, b]⟩, ⟨.or, [x, w.length]⟩] w) := by
  let X := w.getD x ∅
  let A := w.getD a ∅
  let B := w.getD b ∅
  let AB : Set (List ℕ) := {t | ∃ u ∈ A, ∃ v ∈ B, t = u ++ v}
  let XB : Set (List ℕ) := {t | ∃ u ∈ X ∪ A, ∃ v ∈ B, t = u ++ v}
  have hold : wordRun [⟨.or, [x, a]⟩, ⟨.and, [w.length, b]⟩] w =
      (w ++ [X ∪ A]) ++ [XB] := by
    simp only [wordRun, List.foldl_cons, List.foldl_nil, wordStep,
      List.map_cons, List.map_nil, wordOp]
    rw [wsnoc_eq, List.getD_append _ _ _ _ hb]
  have hnew : wordRun [⟨.and, [a, b]⟩, ⟨.or, [x, w.length]⟩] w =
      (w ++ [AB]) ++ [X ∪ AB] := by
    simp only [wordRun, List.foldl_cons, List.foldl_nil, wordStep,
      List.map_cons, List.map_nil, wordOp]
    rw [wsnoc_eq, List.getD_append _ _ _ _ hx]
  rw [hold, hnew]
  constructor
  · simp
  · intro i hi
    by_cases hl : i = w.length + 1
    · subst i
      have hlen (R : Set (List ℕ)) : (w ++ [R]).length = w.length + 1 := by simp
      rw [← hlen (X ∪ A), wsnoc_eq]
      rw [show (w ++ [X ∪ A]).length = (w ++ [AB]).length by simp, wsnoc_eq]
      exact fun t ht => word_rotation X A B t ht
    · have skip (R S : Set (List ℕ)) : (w ++ [R] ++ [S]).getD i ∅ = w.getD i ∅ := by
        rw [wsnoc_ne _ _ _ (by simp; omega), wsnoc_ne _ _ _ hi]
      rw [skip, skip]
      exact wsim_refl _

lemma adjacent_word_simulation (w : List (Set (List ℕ))) (post : List Gate) (x a b o : ℕ)
    (hx : x < w.length) (ha : a < w.length) (hb : b < w.length)
    (ho : o ≠ w.length)
    (hg : ∀ g ∈ post, g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i ≠ w.length) :
    WSim
      ((wordRun ([⟨.or, [x, a]⟩, ⟨.and, [w.length, b]⟩] ++ post) w).getD o ∅)
      ((wordRun ([⟨.and, [a, b]⟩, ⟨.or, [x, w.length]⟩] ++ post) w).getD o ∅) := by
  have hr := wagree_run w.length _ _ post (word_block w x a b hx ha hb) hg
  simpa only [wordRun, List.foldl_append] using hr.2 o ho



lemma wordRun_length (gs : List Gate) (w : List (Set (List ℕ))) :
    (wordRun gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wordRun]
  | cons g gs ih =>
    change (wordRun gs (wordStep w g)).length = _
    rw [ih]
    simp [wordStep]
    omega

lemma adjacent_preserves_read_two (n : ℕ) (pre post : List Gate) (x a b o : ℕ)
    (hx : x < n + pre.length) (ha : a < n + pre.length) (hb : b < n + pre.length)
    (ho : o ≠ n + pre.length)
    (hprivate : ∀ g ∈ post, ∀ i ∈ g.inputs, i ≠ n + pre.length)
    (hdom : ∀ z : Fin n → Bool,
      (run pre (List.ofFn z)).getD x false = true →
      (run pre (List.ofFn z)).getD b false = true)
    (hC : PEqualNP.TopForm.IsAO2 n
      ⟨pre ++ [⟨.or, [x, a]⟩, ⟨.and, [n + pre.length, b]⟩] ++ post, o⟩)
    (hr : IsReadK n
      ⟨pre ++ [⟨.or, [x, a]⟩, ⟨.and, [n + pre.length, b]⟩] ++ post, o⟩ 2) :
    IsReadK n
      ⟨pre ++ [⟨.and, [a, b]⟩, ⟨.or, [x, n + pre.length]⟩] ++ post, o⟩ 2 := by
  let C : Circuit := ⟨pre ++ [⟨.or, [x, a]⟩, ⟨.and, [n + pre.length, b]⟩] ++ post, o⟩
  let D : Circuit := ⟨pre ++ [⟨.and, [a, b]⟩, ⟨.or, [x, n + pre.length]⟩] ++ post, o⟩
  have hD := adjacent_ao2 n pre post x a b o hx ha hb hC
  have hf := adjacent_semantics n pre post x a b o hx ha hb ho hprivate hdom
  apply FlatRead.read_two_of_word_sim hC hD hf.symm ?_ hr
  let ins := List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ)))
  let w := wordRun pre ins
  have hw : w.length = n + pre.length := by simp [w, ins, wordRun_length]
  have hpost : ∀ g ∈ post, g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i ≠ w.length := by
    intro g hg
    refine ⟨hC.2.2 g ?_, ?_⟩
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr hg
    · rw [hw]
      exact hprivate g hg
  have hs := adjacent_word_simulation w post x a b o (by omega) (by omega) (by omega)
    (by omega) hpost
  rw [hw] at hs
  unfold WSim at hs
  dsimp only [w, ins, wordRun] at hs
  unfold wordStep at hs
  have hop : wordOp = FlatRead.wordOp := rfl
  rw [hop] at hs
  simpa only [FlatRead.words, FlatRead.wordList, FlatRead.evalFrom, List.foldl_append] using hs


lemma adjacent_preserves_reads_two (n : ℕ) (pre post : List Gate) (x a b o : ℕ)
    (hx : x < n + pre.length) (ha : a < n + pre.length) (hb : b < n + pre.length)
    (ho : o ≠ n + pre.length)
    (hprivate : ∀ g ∈ post, ∀ i ∈ g.inputs, i ≠ n + pre.length)
    (hC : PEqualNP.TopForm.IsAO2 n
      ⟨pre ++ [⟨.or, [x, a]⟩, ⟨.and, [n + pre.length, b]⟩] ++ post, o⟩)
    (S : List ℕ)
    (hr : readsAtMost
      ⟨pre ++ [⟨.or, [x, a]⟩, ⟨.and, [n + pre.length, b]⟩] ++ post, o⟩ n S 2 = true) :
    readsAtMost
      ⟨pre ++ [⟨.and, [a, b]⟩, ⟨.or, [x, n + pre.length]⟩] ++ post, o⟩ n S 2 = true := by
  let C : Circuit := ⟨pre ++ [⟨.or, [x, a]⟩, ⟨.and, [n + pre.length, b]⟩] ++ post, o⟩
  let D : Circuit := ⟨pre ++ [⟨.and, [a, b]⟩, ⟨.or, [x, n + pre.length]⟩] ++ post, o⟩
  have hD := adjacent_ao2 n pre post x a b o hx ha hb hC
  apply FlatRead.reads_two_of_word_sim hC hD ?_ S hr
  let ins := List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ)))
  let w := wordRun pre ins
  have hw : w.length = n + pre.length := by simp [w, ins, wordRun_length]
  have hpost : ∀ g ∈ post, g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i ≠ w.length := by
    intro g hg
    refine ⟨hC.2.2 g ?_, ?_⟩
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inr hg
    · rw [hw]
      exact hprivate g hg
  have hs := adjacent_word_simulation w post x a b o (by omega) (by omega) (by omega)
    (by omega) hpost
  rw [hw] at hs
  unfold WSim at hs
  dsimp only [w, ins, wordRun] at hs
  unfold wordStep at hs
  have hop : wordOp = FlatRead.wordOp := rfl
  rw [hop] at hs
  simpa only [FlatRead.words, FlatRead.wordList, FlatRead.evalFrom, List.foldl_append] using hs


end Rotation


namespace TwoJunkStructure

def fourClauseEdge {P L : ℕ} (A B C : Fin P → Prop) (D E F : Fin L → Prop)
    (p : Fin P) (l : Fin L) : Prop :=
  A p ∧ D l ∧ (B p ∨ E l) ∧ (C p ∨ F l)

lemma four_clause_noncentre_edges_same_line {P L : ℕ}
    (I : Fin P → Fin L → Prop) (A B C : Fin P → Prop) (D E F : Fin L → Prop)
    (hfour : ∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (hpair : ∀ p l, fourClauseEdge A B C D E F p l → I p l)
    (htriple : ∀ p q l, A p → A q → D l →
      (B p ∨ B q ∨ E l) → (C p ∨ C q ∨ F l) → I p l ∨ I q l)
    (p0 : Fin P) (l0 : Fin L) (hp0 : A p0 ∧ B p0 ∧ C p0)
    (hl0 : D l0 ∧ ¬ E l0 ∧ ¬ F l0)
    (p q : Fin P) (l m : Fin L)
    (hp : fourClauseEdge A B C D E F p l)
    (hq : fourClauseEdge A B C D E F q m)
    (hpp : p ≠ p0) (hqp : q ≠ p0) : l = m := by
  by_contra hlm
  have hcentre (t : Fin L) (ht : D t) : I p0 t :=
    hpair p0 t ⟨hp0.1, ht, Or.inl hp0.2.1, Or.inl hp0.2.2⟩
  have hpl := hpair p l hp
  have hqm := hpair q m hq
  have hpm : ¬ I p m := by
    intro hpm
    exact hfour p p0 l m hpp hlm ⟨hpl, hpm, hcentre l hp.2.1, hcentre m hq.2.1⟩
  have hql : ¬ I q l := by
    intro hql
    exact hfour q p0 l m hqp hlm ⟨hql, hqm, hcentre l hp.2.1, hcentre m hq.2.1⟩
  have hcrossp : ¬ ((B p ∨ E m) ∧ (C p ∨ F m)) := by
    intro hh
    exact hpm (hpair p m ⟨hp.1, hq.2.1, hh⟩)
  have hcrossq : ¬ ((B q ∨ E l) ∧ (C q ∨ F l)) := by
    intro hh
    exact hql (hpair q l ⟨hq.1, hp.2.1, hh⟩)
  have hB : B p ∨ B q := by
    have hp' := hp.2.2
    have hq' := hq.2.2
    tauto
  have hC : C p ∨ C q := by
    have hp' := hp.2.2
    have hq' := hq.2.2
    tauto
  have hll0 : l ≠ l0 := by
    intro he
    subst l
    have hBp : B p := hp.2.2.1.resolve_right hl0.2.1
    have hCp : C p := hp.2.2.2.resolve_right hl0.2.2
    exact hcrossp ⟨Or.inl hBp, Or.inl hCp⟩
  have hml0 : m ≠ l0 := by
    intro he
    subst m
    have hBq : B q := hq.2.2.1.resolve_right hl0.2.1
    have hCq : C q := hq.2.2.2.resolve_right hl0.2.2
    exact hcrossq ⟨Or.inl hBq, Or.inl hCq⟩
  have hpl0 : ¬ I p l0 := by
    intro hh
    exact hfour p p0 l l0 hpp hll0
      ⟨hpl, hh, hcentre l hp.2.1, hcentre l0 hl0.1⟩
  have hql0 : ¬ I q l0 := by
    intro hh
    exact hfour q p0 m l0 hqp hml0
      ⟨hqm, hh, hcentre m hq.2.1, hcentre l0 hl0.1⟩
  rcases htriple p q l0 hp.1 hq.1 hl0.1
      (hB.elim Or.inl (fun hq => Or.inr (Or.inl hq)))
      (hC.elim Or.inl (fun hq => Or.inr (Or.inl hq))) with hh | hh
  · exact hpl0 hh
  · exact hql0 hh

lemma four_clause_double_star {P L : ℕ}
    (I : Fin P → Fin L → Prop) (A B C : Fin P → Prop) (D E F : Fin L → Prop)
    (hfour : ∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (hpair : ∀ p l, fourClauseEdge A B C D E F p l → I p l)
    (htriple : ∀ p q l, A p → A q → D l →
      (B p ∨ B q ∨ E l) → (C p ∨ C q ∨ F l) → I p l ∨ I q l)
    (p0 : Fin P) (l0 : Fin L) (hp0 : A p0 ∧ B p0 ∧ C p0)
    (hl0 : D l0 ∧ ¬ E l0 ∧ ¬ F l0) :
    ∃ l1 : Fin L, ∀ p l, fourClauseEdge A B C D E F p l → p = p0 ∨ l = l1 := by
  classical
  by_cases hex : ∃ p l, fourClauseEdge A B C D E F p l ∧ p ≠ p0
  · obtain ⟨p, l, hp, hpp⟩ := hex
    refine ⟨l, ?_⟩
    intro q m hq
    by_cases hqp : q = p0
    · exact Or.inl hqp
    · exact Or.inr (four_clause_noncentre_edges_same_line I A B C D E F hfour hpair
        htriple p0 l0 hp0 hl0 q p m l hq hp hqp hpp)
  · refine ⟨l0, ?_⟩
    intro p l hp
    by_cases hpp : p = p0
    · exact Or.inl hpp
    · exact False.elim (hex ⟨p, l, hp, hpp⟩)

end TwoJunkStructure


lemma incidence_point_line_no_common_neighbor {P L : ℕ}
    (I : Fin P → Fin L → Prop) [DecidableRel I] (p : Fin P) (l : Fin L)
    (w : Fin (P + L)) :
    ¬((incidenceGraph I).Adj (Fin.castAdd L p) w ∧
      (incidenceGraph I).Adj (Fin.natAdd P l) w) := by
  induction w using Fin.addCases <;> simp [incidenceBit]


namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge
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

lemma pure_or_value_iff {n : ℕ} {C : Circuit} {w : ℕ}
    (hpure : ∀ g, OrReaches n C w g → (gateAt C g).op = GateOp.or)
    (x : Fin n → Bool) :
    val C (List.ofFn x) w = true ↔ ∃ u ∈ orIn n C w, x u = true := by
  constructor
  · intro hx
    obtain ⟨w', hr, hv, hw⟩ := or_trace (n := n) (by simp) w hx
    rcases hw with hw | ⟨g, hg, rfl, hnot⟩
    · refine ⟨⟨w', hw⟩, reach_mem_orIn _ hr, ?_⟩
      exact (val_ofFn C x ⟨w', hw⟩).symm.trans hv
    · exact (hnot (hpure g (reach_orReaches hr g rfl hg))).elim
  · rintro ⟨u, hu, hx⟩
    exact orIn_value hu x hx

lemma pure_or_singletons_eq {n : ℕ} {C : Circuit} {w : ℕ}
    (hpure : ∀ g, OrReaches n C w g → (gateAt C g).op = GateOp.or) :
    singletonInputs n C w = orIn n C w := by
  apply Finset.Subset.antisymm _ orIn_subset_singletonInputs
  intro u hu
  simp only [singletonInputs, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  obtain ⟨v, hv, hvu⟩ := (pure_or_value_iff hpure _).mp hu
  have heq : v = u := by simpa only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq, or_self] using hvu
  simpa only [heq] using hv

lemma pure_or_pair_support {n : ℕ} {C : Circuit} {w : ℕ}
    (hpure : ∀ g, OrReaches n C w g → (gateAt C g).op = GateOp.or)
    (S : Fin n → Prop) (hside : ∀ u ∈ orIn n C w, S u)
    (u v : Fin n) (hv : ¬S v)
    (htrue : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) w = true) :
    u ∈ orIn n C w := by
  obtain ⟨t, ht, htuv⟩ := (pure_or_value_iff hpure _).mp htrue
  rcases (pairInput_true u v t).mp htuv with rfl | rfl
  · exact ht
  · exact (hv (hside _ ht)).elim

lemma disjoint_pure_side_and_false {n : ℕ} {C : Circuit} {a p q : ℕ}
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (hin : (gateAt C a).inputs = [p, q])
    (hpure : ∀ g, OrReaches n C p g → (gateAt C g).op = GateOp.or)
    (qpure : ∀ g, OrReaches n C q g → (gateAt C g).op = GateOp.or)
    (S : Fin n → Prop) (hsidep : ∀ u ∈ orIn n C p, S u)
    (hsideq : ∀ u ∈ orIn n C q, S u)
    (hdisj : Disjoint (orIn n C p) (orIn n C q))
    (u v : Fin n) (hv : ¬S v) :
    val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) (n + a) = false := by
  apply Bool.eq_false_iff.mpr
  intro hx
  have hvals := (val_and (n := n) (by simp) ha hand).mp hx
  have hp := (hvals p (by rw [hin]; simp)).2
  have hq := (hvals q (by rw [hin]; simp)).2
  exact Finset.disjoint_left.mp hdisj
    (pure_or_pair_support hpure S hsidep u v hv hp)
    (pure_or_pair_support qpure S hsideq u v hv hq)

lemma disjoint_point_or_and_false_on_pairs {P L : ℕ} {C : Circuit} {a p q : ℕ}
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (hin : (gateAt C a).inputs = [p, q])
    (hpure : ∀ g, OrReaches (P + L) C p g → (gateAt C g).op = GateOp.or)
    (qpure : ∀ g, OrReaches (P + L) C q g → (gateAt C g).op = GateOp.or)
    (hsidep : ∀ u ∈ orIn (P + L) C p, u.val < P)
    (hsideq : ∀ u ∈ orIn (P + L) C q, u.val < P)
    (hdisj : Disjoint (orIn (P + L) C p) (orIn (P + L) C q))
    (x : Fin P) (y : Fin L) :
    PEqualNP.EdgeOwnership.gateVal (P + L) C a
      (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd L x) (Fin.natAdd P y)) = false :=
  disjoint_pure_side_and_false ha hand hin hpure qpure (fun u => u.val < P)
    hsidep hsideq hdisj _ _ (by simp)

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma choose_incident_factor {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (A B : Finset (Fin P)) (l : Fin L)
    (hsound : ∀ x : Fin (P + L) → Bool, x (Fin.natAdd P l) = true →
      (∃ a ∈ A, x (Fin.castAdd L a) = true) →
      (∃ b ∈ B, x (Fin.castAdd L b) = true) →
      decide (∃ p k, I p k ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P k) = true) = true) :
    (∀ a ∈ A, I a l) ∨ (∀ b ∈ B, I b l) := by
  classical
  by_contra h
  simp only [not_or, not_forall] at h
  obtain ⟨a, ha⟩ := h.1
  obtain ⟨haA, hal⟩ := ha
  obtain ⟨b, hb⟩ := h.2
  obtain ⟨hbB, hbl⟩ := hb
  let x : Fin (P + L) → Bool :=
    Fin.addCases (fun p => decide (p = a ∨ p = b)) (fun k => decide (k = l))
  have hval := hsound x (by simp [x]) ⟨a, haA, by simp [x]⟩ ⟨b, hbB, by simp [x]⟩
  rw [decide_eq_true_eq] at hval
  obtain ⟨p, k, hpk, hp, hk⟩ := hval
  have hk' : k = l := by simpa [x] using hk
  subst k
  have hp' : p = a ∨ p = b := by simpa [x] using hp
  rcases hp' with rfl | rfl
  · exact hal hpk
  · exact hbl hpk

lemma pure_point_or_times_line_sound {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    {C : Circuit} {w : ℕ} (l : Fin L)
    (hpure : ∀ g, OrReaches (P + L) C w g → (gateAt C g).op = GateOp.or)
    (hside : ∀ u ∈ orIn (P + L) C w, u.val < P)
    (hneighbors : ∀ p : Fin P, Fin.castAdd L p ∈ orIn (P + L) C w → I p l)
    (x : Fin (P + L) → Bool)
    (hw : val C (List.ofFn x) w = true) (hl : x (Fin.natAdd P l) = true) :
    decide (∃ p k, I p k ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P k) = true) = true := by
  obtain ⟨u, hu, hxu⟩ := (pure_or_value_iff hpure x).mp hw
  let p : Fin P := ⟨u.val, hside u hu⟩
  have hup : Fin.castAdd L p = u := Fin.ext rfl
  apply decide_eq_true_iff.mpr
  exact ⟨p, l, hneighbors p (by rwa [hup]), by rwa [hup], hl⟩

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma and_reader_choose_point_factor {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (P + L) C)
    {g r p q : ℕ} (hg : g < C.gates.length) (hga : (gateAt C g).op = GateOp.and)
    (hgin : (gateAt C g).inputs = [p, q])
    (hr : r < C.gates.length) (hra : (gateAt C r).op = GateOp.and) (l : Fin L)
    (hrin : ∀ w ∈ (gateAt C r).inputs, w = (Fin.natAdd P l).val ∨ w = P + L + g)
    (hbelow : ∀ x : Fin (P + L) → Bool, PEqualNP.EdgeOwnership.gateVal (P + L) C r x = true →
      decide (∃ a b, I a b ∧ x (Fin.castAdd L a) = true ∧ x (Fin.natAdd P b) = true) = true) :
    (∀ a : Fin P, Fin.castAdd L a ∈ orIn (P + L) C p → I a l) ∨
    (∀ b : Fin P, Fin.castAdd L b ∈ orIn (P + L) C q → I b l) := by
  let A := Finset.univ.filter (fun a : Fin P => Fin.castAdd L a ∈ orIn (P + L) C p)
  let B := Finset.univ.filter (fun b : Fin P => Fin.castAdd L b ∈ orIn (P + L) C q)
  have hchoice := choose_incident_factor I A B l (fun x hl hA hB => by
    obtain ⟨a, ha, hxa⟩ := hA
    obtain ⟨b, hb, hxb⟩ := hB
    have hpval := orIn_value (Finset.mem_filter.mp ha).2 x hxa
    have hqval := orIn_value (Finset.mem_filter.mp hb).2 x hxb
    have hgval : val C (List.ofFn x) (P + L + g) = true := by
      apply (val_and (by simp) hg hga).mpr
      intro w hw
      have hwlt := hRB g hg w hw
      rw [hgin] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨hwlt, hpval⟩
      · exact ⟨hwlt, hqval⟩
    apply hbelow x
    rw [gateVal_eq_val, val_and (by simp) hr hra]
    intro w hw
    refine ⟨hRB r hr w hw, ?_⟩
    rcases hrin w hw with rfl | rfl
    · simpa only [val_ofFn] using hl
    · exact hgval)
  simpa only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] using hchoice

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma shared_or_context_center_unique {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {h g a a' : ℕ} (ha : a ∈ tops G C) (ha' : a' ∈ tops G C)
    (b b' : Fin 2) (hr : OrReaches n C (opnd C a b) h)
    (hr' : OrReaches n C (opnd C a' b') h)
    (hg : OrReaches n C (n + h) g) {x d : Fin n}
    (hx : x ∈ singletonInputs n C (n + g)) (hd : d ∈ orIn n C (n + h)) (hxd : x ≠ d)
    {u v : Fin n} (hu : u ∈ singletonInputs n C (opnd C a b.rev))
    (hv : v ∈ singletonInputs n C (opnd C a' b'.rev)) : u = v := by
  apply shared_singleton_region_center_unique G C hAO h4 ha ha' b b' hr hr' _ hu hv
  exact Finset.one_lt_card.mpr ⟨x, singletonInputs_subset_of_orReaches hg hx,
    d, orIn_subset_singletonInputs hd, hxd⟩

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def forcedCircuit (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩

lemma forcedCircuit_length (C : Circuit) (j : ℕ) :
    (forcedCircuit C j).gates.length = C.gates.length := by
  simp [forcedCircuit]

lemma forcedCircuit_gateAt_self (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    gateAt (forcedCircuit C j) j = ⟨GateOp.or, []⟩ := by
  simp [forcedCircuit, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_self hj]

lemma forcedCircuit_gateAt_other (C : Circuit) (j k : ℕ) (hne : j ≠ k) :
    gateAt (forcedCircuit C j) k = gateAt C k := by
  simp [forcedCircuit, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma forcedCircuit_andOrOnly {C : Circuit} (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (j : ℕ) :
    PEqualNP.EdgeOwnership.AndOrOnly (forcedCircuit C j) := by
  intro g hg
  rcases List.mem_or_eq_of_mem_set hg with hg | rfl
  · exact hAO g hg
  · exact Or.inr rfl

lemma forcedCircuit_val_self {n : ℕ} (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (x : Fin n → Bool) : val (forcedCircuit C j) (List.ofFn x) (n + j) = false := by
  rw [val_gate (n := n) (by simp) (by simpa only [forcedCircuit_length] using hj),
    forcedCircuit_gateAt_self C hj]
  rfl

lemma forcedCircuit_val_le {n : ℕ} {C : Circuit}
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (j : ℕ) (x : Fin n → Bool) (w : ℕ) :
    val (forcedCircuit C j) (List.ofFn x) w = true → val C (List.ofFn x) w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input (n := n) (by simp) hn, val_input (n := n) (by simp) hn]
      exact id
    by_cases hw : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hk' : k < (forcedCircuit C j).gates.length := by simpa only [forcedCircuit_length] using hk
      by_cases heq : j = k
      · subst k
        rw [forcedCircuit_val_self C hk x]
        simp
      have he : gateAt (forcedCircuit C j) k = gateAt C k := forcedCircuit_gateAt_other C j k heq
      rcases hAO _ (gateAt_mem hk) with hand | hor
      · rw [val_and (n := n) (by simp) hk' (by rw [he]; exact hand),
          val_and (n := n) (by simp) hk hand, he]
        intro h i hi
        exact ⟨(h i hi).1, ih i (h i hi).1 (h i hi).2⟩
      · rw [val_or (n := n) (by simp) hk' (by rw [he]; exact hor),
          val_or (n := n) (by simp) hk hor, he]
        rintro ⟨i, hi, hlt, hv⟩
        exact ⟨i, hi, hlt, ih i hlt hv⟩
    · rw [val_ge (n := n) (by simp) (by rw [forcedCircuit_length]; omega)]
      simp

lemma forcedCircuit_val_eq_of_false {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool)
    (hj : PEqualNP.EdgeOwnership.gateVal n C j x = false) (w : ℕ) :
    val (forcedCircuit C j) (List.ofFn x) w = val C (List.ofFn x) w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input (n := n) (by simp) hn, val_input (n := n) (by simp) hn]
    by_cases hw : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hk' : k < (forcedCircuit C j).gates.length := by simpa only [forcedCircuit_length] using hk
      by_cases heq : j = k
      · subst k
        rw [forcedCircuit_val_self C hk x]
        exact hj.symm
      rw [val_gate (n := n) (by simp) hk', val_gate (n := n) (by simp) hk,
        forcedCircuit_gateAt_other C j k heq]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [ite_eq_left hi, ite_eq_left hi, ih i hi]
      · rw [ite_eq_right hi, ite_eq_right hi]
    · rw [val_ge (n := n) (by simp) (by rw [forcedCircuit_length]; omega),
        val_ge (n := n) (by simp) (by omega)]

lemma forcedCircuit_fun_le {n : ℕ} {C : Circuit}
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.MetaComplexity.circuitFun n (forcedCircuit C j) x = true →
      PEqualNP.MetaComplexity.circuitFun n C x = true :=
  forcedCircuit_val_le hAO j x C.output

lemma forcedCircuit_fun_eq_of_false {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool)
    (hj : PEqualNP.EdgeOwnership.gateVal n C j x = false) :
    PEqualNP.MetaComplexity.circuitFun n (forcedCircuit C j) x =
      PEqualNP.MetaComplexity.circuitFun n C x :=
  forcedCircuit_val_eq_of_false C j x hj C.output

end Sharing


namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

lemma forcedCircuit_graphFun_eq_of_edge_false {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (hf : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅) (j : ℕ)
    (hzero : ∀ u v, G.Adj u v →
      PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput u v) = false) :
    PEqualNP.MetaComplexity.circuitFun n (forcedCircuit C j) = graphFun G ∅ := by
  apply circuit_graphFun_eq_of_pair_cover G (forcedCircuit C j) (forcedCircuit_andOrOnly hAO j)
  · intro x hx
    have hx' := forcedCircuit_fun_le hAO j x hx
    simpa only [hf] using hx'
  · intro u v huv
    rw [forcedCircuit_fun_eq_of_false C j _ (hzero u v huv), hf]
    exact (graphFun_pair G u v).mpr huv

lemma forcedCircuit_incidence_eq_of_pair_false {P L : ℕ}
    (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit)
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (hf : PEqualNP.MetaComplexity.circuitFun (P + L) C = fun x =>
      decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (j : ℕ) (hzero : ∀ p l, I p l →
      PEqualNP.EdgeOwnership.gateVal (P + L) C j
        (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd L p) (Fin.natAdd P l)) = false) :
    PEqualNP.MetaComplexity.circuitFun (P + L) (forcedCircuit C j) = fun x =>
      decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) := by
  apply incidence_eq_of_pair_cover I
  · intro x y hxy hx
    exact val_monotone (forcedCircuit_andOrOnly hAO j) x y hxy C.output hx
  · intro x hx
    have hx' := forcedCircuit_fun_le hAO j x hx
    simpa only [hf] using hx'
  · intro p l hpl
    rw [forcedCircuit_fun_eq_of_false C j _ (hzero p l hpl), hf]
    simp only [decide_eq_true_eq]
    exact ⟨p, l, hpl, pairInput_left _ _, pairInput_right _ _⟩

end Sharing

namespace FalsePropagation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    change (wiresFrom gs (w ++ [_])).length = _
    rw [ih]
    simp
    omega

lemma wiresFrom_append (gs hs : List Gate) (w : List Bool) :
    wiresFrom (gs ++ hs) w = wiresFrom hs (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) (w : List Bool) :
    ∃ t, wiresFrom gs w = w ++ t := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [wiresFrom]⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨_ :: t, by simpa [wiresFrom, List.append_assoc] using ht⟩

lemma getD_snoc_ne {α : Type} (w : List α) (v d : α) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [v]).getD i d = w.getD i d := by
  by_cases hlt : i < w.length
  · exact List.getD_append _ _ _ _ hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def valid (m : ℕ) : Option ℕ → Prop
  | none => True
  | some j => j < m

def value (w : List Bool) : Option ℕ → Bool
  | none => false
  | some j => w.getD j false

lemma valid_mono {m m' : ℕ} (h : m ≤ m') (s : Option ℕ) : valid m s → valid m' s := by
  cases s <;> simp_all [valid]
  omega

lemma value_append (w t : List Bool) (s : Option ℕ) (h : valid w.length s) :
    value (w ++ t) s = value w s := by
  cases s with
  | none => rfl
  | some j => exact List.getD_append _ _ _ _ h

def simplify (op : GateOp) (m : ℕ) (ins : List (Option ℕ)) : Option Gate × Option ℕ :=
  match op, ins with
  | .and, [some a, some b] => (some ⟨.and, [a, b]⟩, some m)
  | .or, [some a, some b] => (some ⟨.or, [a, b]⟩, some m)
  | .or, [a, none] => (none, a)
  | .or, [none, b] => (none, b)
  | _, _ => (none, none)

def good (g : Gate) : Prop :=
  (g.op = .and ∨ g.op = .or) ∧
    (g.inputs.length = 2 ∨ (g.op = .or ∧ g.inputs = []))

lemma simplify_good (op : GateOp) (m : ℕ) (ins : List (Option ℕ))
    (hop : op = .and ∨ op = .or)
    (hlen : ins.length = 2 ∨ (op = .or ∧ ins = []))
    (hv : ∀ s ∈ ins, valid m s) :
    valid (m + (simplify op m ins).1.toList.length) (simplify op m ins).2 ∧
      ∀ g ∈ (simplify op m ins).1.toList,
        (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧
          ∀ i ∈ g.inputs, i < m := by
  rcases hlen with hlen | ⟨rfl, rfl⟩
  · obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
    rcases hop with rfl | rfl <;> cases a <;> cases b <;>
      simp_all [simplify, valid]
  · simp [simplify, valid]

lemma simplify_sound (op : GateOp) (w : List Bool) (ins : List (Option ℕ))
    (hop : op = .and ∨ op = .or)
    (hlen : ins.length = 2 ∨ (op = .or ∧ ins = [])) :
    value (wiresFrom (simplify op w.length ins).1.toList w)
      (simplify op w.length ins).2 = op.eval (ins.map (value w)) := by
  rcases hlen with hlen | ⟨rfl, rfl⟩
  · obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp hlen
    rcases hop with rfl | rfl <;> cases a <;> cases b <;>
      simp [simplify, value, wiresFrom, GateOp.eval]
  · simp [simplify, value, GateOp.eval]

def step (n : ℕ) (acc : List (Option ℕ) × List Gate) (g : Gate) :
    List (Option ℕ) × List Gate :=
  let r := simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i none)
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def run (n : ℕ) (gs : List Gate) (acc : List (Option ℕ) × List Gate) :
    List (Option ℕ) × List Gate := gs.foldl (step n) acc

lemma option_toList_length_le {α : Type} (a : Option α) : a.toList.length ≤ 1 := by
  cases a <;> simp

lemma run_length (n : ℕ) (gs : List Gate) (acc : List (Option ℕ) × List Gate) :
    (run n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [run]
  | cons g gs ih =>
    have h := ih (step n acc g)
    have h1 := option_toList_length_le
      (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i none)).1
    simp only [step, List.length_append] at h
    change (run n gs (step n acc g)).2.length ≤ _
    simp only [List.length_cons]
    simp only [step]
    omega

lemma run_length_strict (n : ℕ) (gs : List Gate) (acc : List (Option ℕ) × List Gate)
    (he : ∃ g ∈ gs, g.inputs = []) :
    (run n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp at he
  | cons g gs ih =>
    change (run n gs (step n acc g)).2.length + 1 ≤ _
    simp only [List.length_cons]
    by_cases hnil : g.inputs = []
    · have h := run_length n gs (step n acc g)
      have hop : (simplify g.op (n + acc.2.length) []).1 = none := by cases g.op <;> rfl
      simp only [step, hnil, List.map_nil, hop, Option.toList_none, List.append_nil] at h
      simp only [step, hnil, List.map_nil, hop, Option.toList_none, List.append_nil]
      omega
    · have hex : ∃ g' ∈ gs, g'.inputs = [] := by
        obtain ⟨g', hg', h⟩ := he
        rcases List.mem_cons.mp hg' with rfl | hg'
        · exact (hnil h).elim
        · exact ⟨g', hg', h⟩
      have h := ih (step n acc g) hex
      have h1 := option_toList_length_le
        (simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i none)).1
      simp only [step, List.length_append] at h
      simp only [step]
      omega

def built (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j g, gs[j]? = some g → (g.op = .and ∨ g.op = .or) ∧
    g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < n + j

lemma built_append (n : ℕ) (gs hs : List Gate) (hgs : built n gs)
    (hhs : ∀ g ∈ hs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 ∧
      ∀ i ∈ g.inputs, i < n + gs.length) : built n (gs ++ hs) := by
  intro j g hg
  rw [List.getElem?_append] at hg
  split at hg
  · exact hgs j g hg
  · have hm : g ∈ hs := List.mem_iff_getElem?.mpr ⟨_, hg⟩
    obtain ⟨hop, hlen, hi⟩ := hhs g hm
    exact ⟨hop, hlen, fun i h => by have := hi i h; omega⟩

def Inv (n : ℕ) (y w : List Bool) (acc : List (Option ℕ) × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i,
    valid (n + acc.2.length) (acc.1.getD i none) ∧
      value (wiresFrom acc.2 y) (acc.1.getD i none) = w.getD i false

lemma getD_snoc_eq {α : Type} (w : List α) (v d : α) :
    (w ++ [v]).getD w.length d = v := by simp

lemma step_inv (n : ℕ) (y w : List Bool) (acc : List (Option ℕ) × List Gate) (g : Gate)
    (hy : y.length = n) (hg : good g) (h : Inv n y w acc) :
    Inv n y (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (step n acc g) ∧
      (built n acc.2 → built n (step n acc g).2) := by
  obtain ⟨hl, hi⟩ := h
  let w' := wiresFrom acc.2 y
  have lw' : w'.length = n + acc.2.length := by simp [w', wiresFrom_length, hy]
  let ins := g.inputs.map fun i => acc.1.getD i none
  have hlen : ins.length = 2 ∨ (g.op = .or ∧ ins = []) := by
    rcases hg.2 with h | ⟨h, h'⟩
    · exact Or.inl (by simp [ins, h])
    · exact Or.inr ⟨h, by simp [ins, h']⟩
  have hv : ∀ s ∈ ins, valid (n + acc.2.length) s := by
    intro s hs
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hs
    exact (hi i).1
  have hsg := simplify_good g.op (n + acc.2.length) ins hg.1 hlen hv
  have hss := simplify_sound g.op w' ins hg.1 hlen
  rw [lw'] at hss
  let r := simplify g.op (n + acc.2.length) ins
  have hvals : ins.map (value w') = g.inputs.map fun i => w.getD i false := by
    simp only [ins, List.map_map]
    apply List.map_congr_left
    intro i _
    exact (hi i).2
  have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
    exact wiresFrom_append _ _ _
  obtain ⟨t, ht⟩ := wiresFrom_prefix r.1.toList w'
  change Inv n y (w ++ [_]) (acc.1 ++ [r.2], acc.2 ++ r.1.toList) ∧
    (built n acc.2 → built n (acc.2 ++ r.1.toList))
  constructor
  · refine ⟨by simp [hl], ?_⟩
    intro i
    change valid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i none) ∧
      value (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i none) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases he : i = acc.1.length
    · subst i
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hsg.1, by simpa only [hvals] using hss⟩
    · rw [getD_snoc_ne _ _ _ _ he, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, value_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2
  · intro hb
    exact built_append n acc.2 r.1.toList hb hsg.2

lemma run_inv (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate)
    (w : List Bool) (acc : List (Option ℕ) × List Gate)
    (hg : ∀ g ∈ gs, good g) (h : Inv n y w acc) (hb : built n acc.2) :
    Inv n y (wiresFrom gs w) (run n gs acc) ∧ built n (run n gs acc).2 := by
  induction gs generalizing w acc with
  | nil => exact ⟨h, hb⟩
  | cons g gs ih =>
    obtain ⟨h1, h2⟩ := step_inv n y w acc g hy (hg g List.mem_cons_self) h
    exact ih _ _ (fun g hg' => hg g (List.mem_cons_of_mem _ hg')) h1 (h2 hb)

def initial (n : ℕ) : List (Option ℕ) × List Gate :=
  ((List.range n).map some, [])

lemma initial_inv (n : ℕ) (y : List Bool) (hy : y.length = n) :
    Inv n y y (initial n) := by
  refine ⟨by simp [initial, hy], ?_⟩
  intro i
  by_cases hi : i < n
  · simp [initial, List.getD_eq_getElem?_getD, hi, valid, value, wiresFrom]
  · have h1 : ((initial n).1).getD i none = none :=
      List.getD_eq_default _ _ (by simp [initial]; omega)
    have h2 : y.getD i false = false := List.getD_eq_default _ _ (by omega)
    rw [h1, h2]
    exact ⟨trivial, rfl⟩

def propagate (n : ℕ) (C : Circuit) : Circuit :=
  let r := run n C.gates (initial n)
  ⟨r.2, (r.1.getD C.output none).getD (n + r.2.length)⟩

lemma built_ao2 (n : ℕ) (C : Circuit) (h : built n C.gates) :
    PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
    exact (h j g hj).1
  · intro j hj i hi
    have he : C.gates[j]? = some (NestedCover.gateAt C j) := by
      simp [NestedCover.gateAt, List.getD_eq_getElem?_getD, hj]
    exact (h j _ he).2.2 i hi
  · intro g hg
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
    exact (h j g hj).2.1

lemma propagate_ao2 (n : ℕ) (C : Circuit) (hg : ∀ g ∈ C.gates, good g) :
    PEqualNP.TopForm.IsAO2 n (propagate n C) := by
  have hy : (List.replicate n false).length = n := by simp
  have h := (run_inv n _ hy C.gates _ (initial n) hg (initial_inv n _ hy)
    (by simp [built, initial])).2
  exact built_ao2 n (propagate n C) h

lemma propagate_eval (n : ℕ) (C : Circuit) (y : List Bool) (hy : y.length = n)
    (hg : ∀ g ∈ C.gates, good g) : (propagate n C).eval y = C.eval y := by
  have h := (run_inv n y hy C.gates y (initial n) hg (initial_inv n y hy)
    (by simp [built, initial])).1.2 C.output
  let r := run n C.gates (initial n)
  change valid (n + r.2.length) (r.1.getD C.output none) ∧
    value (wiresFrom r.2 y) (r.1.getD C.output none) = (wiresFrom C.gates y).getD C.output false at h
  change (wiresFrom r.2 y).getD ((r.1.getD C.output none).getD (n + r.2.length)) false = _
  cases he : r.1.getD C.output none with
  | none =>
    have hz : (wiresFrom r.2 y).getD (n + r.2.length) false = false :=
      List.getD_eq_default _ _ (by simp [wiresFrom_length, hy])
    have hv := h.2
    rw [he] at hv
    change false = C.eval y at hv
    rw [Option.getD_none, hz]
    exact hv
  | some j =>
    have hv := h.2
    rw [he] at hv
    exact hv

def falseGate : Gate := ⟨.or, []⟩

def forcedCircuit (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.set j falseGate, C.output⟩

lemma good_falseGate : good falseGate := by simp [good, falseGate]

lemma good_set (gs : List Gate) (j : ℕ) (h : ∀ g ∈ gs, good g) :
    ∀ g ∈ gs.set j falseGate, good g := by
  induction gs generalizing j with
  | nil => simp
  | cons a gs ih =>
    intro g hg
    cases j with
    | zero =>
      change g ∈ falseGate :: gs at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact good_falseGate
      · exact h g (List.mem_cons_of_mem _ hg)
    | succ j =>
      change g ∈ a :: gs.set j falseGate at hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact h g List.mem_cons_self
      · exact ih j (fun g hg => h g (List.mem_cons_of_mem _ hg)) g hg

lemma falseGate_mem_set (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    falseGate ∈ gs.set j falseGate := by
  induction gs generalizing j with
  | nil => simp at hj
  | cons a gs ih =>
    cases j with
    | zero => exact List.mem_cons_self
    | succ j => exact List.mem_cons_of_mem _ (ih j (by simpa using hj))

lemma eliminate_false_gate (n : ℕ) (C : Circuit) (j : ℕ)
    (hC : PEqualNP.TopForm.IsAO2 n C) (hj : j < C.gates.length) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size + 1 ≤ C.size ∧
      ∀ x : Fin n → Bool, circuitFun n D x = circuitFun n (forcedCircuit C j) x := by
  have hg : ∀ g ∈ C.gates, good g :=
    fun g hg => ⟨hC.1 g hg, Or.inl (hC.2.2 g hg)⟩
  have hgf : ∀ g ∈ (forcedCircuit C j).gates, good g := good_set C.gates j hg
  refine ⟨propagate n (forcedCircuit C j), propagate_ao2 n _ hgf, ?_, ?_⟩
  · have he : ∃ g ∈ (forcedCircuit C j).gates, g.inputs = [] :=
      ⟨falseGate, falseGate_mem_set C.gates j hj, rfl⟩
    have hl := run_length_strict n (forcedCircuit C j).gates (initial n) he
    simpa [propagate, forcedCircuit, Circuit.size, initial] using hl
  · intro x
    exact propagate_eval n _ (List.ofFn x) (by simp) hgf

end FalsePropagation


namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma least_gate_productive {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ u v, G.Adj u v ∧
      PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput u v) = true := by
  by_contra hn
  have hzero : ∀ u v, G.Adj u v →
      PEqualNP.EdgeOwnership.gateVal n C j (PEqualNP.EdgeOwnership.pairInput u v) = false := by
    intro u v huv
    apply Bool.eq_false_iff.mpr
    intro hv
    exact hn ⟨u, v, huv, hv⟩
  have hforced := forcedCircuit_graphFun_eq_of_edge_false G C hL.1.1 hL.2.1 j hzero
  obtain ⟨D, hD, hsize, heq⟩ := FalsePropagation.eliminate_false_gate n C j hL.1 hj
  have hfun : PEqualNP.MetaComplexity.circuitFun n D = graphFun G ∅ := (funext heq).trans hforced
  have hmin := hL.2.2 D hD hfun
  omega

lemma least_incidence_gate_productive {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hAO : IsAO2 (P + L) C)
    (hf : PEqualNP.MetaComplexity.circuitFun (P + L) C = fun x =>
      decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (hmin : ∀ D : Circuit, IsAO2 (P + L) D →
      PEqualNP.MetaComplexity.circuitFun (P + L) D = (fun x =>
        decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) →
      C.size ≤ D.size)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ p l, I p l ∧ PEqualNP.EdgeOwnership.gateVal (P + L) C j
      (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd L p) (Fin.natAdd P l)) = true := by
  by_contra hn
  have hzero : ∀ p l, I p l → PEqualNP.EdgeOwnership.gateVal (P + L) C j
      (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd L p) (Fin.natAdd P l)) = false := by
    intro p l hpl
    apply Bool.eq_false_iff.mpr
    intro hv
    exact hn ⟨p, l, hpl, hv⟩
  have hforced := forcedCircuit_incidence_eq_of_pair_false I C hAO.1 hf j hzero
  obtain ⟨D, hD, hsize, heq⟩ := FalsePropagation.eliminate_false_gate (P + L) C j hAO hj
  have hfun : PEqualNP.MetaComplexity.circuitFun (P + L) D = (fun x =>
      decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) :=
    (funext heq).trans hforced
  have hsmall := hmin D hD hfun
  omega

lemma productive_pure_point_and_intersection {P L : ℕ} {C : Circuit} {a p q : ℕ}
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (hin : (gateAt C a).inputs = [p, q])
    (hpure : ∀ g, OrReaches (P + L) C p g → (gateAt C g).op = GateOp.or)
    (qpure : ∀ g, OrReaches (P + L) C q g → (gateAt C g).op = GateOp.or)
    (hsidep : ∀ u ∈ orIn (P + L) C p, u.val < P)
    (hsideq : ∀ u ∈ orIn (P + L) C q, u.val < P)
    (hprod : ∃ x : Fin P, ∃ y : Fin L, PEqualNP.EdgeOwnership.gateVal (P + L) C a
      (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd L x) (Fin.natAdd P y)) = true) :
    (orIn (P + L) C p ∩ orIn (P + L) C q).Nonempty := by
  by_contra hn
  have hdisj : Disjoint (orIn (P + L) C p) (orIn (P + L) C q) :=
    Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
  obtain ⟨x, y, hv⟩ := hprod
  have hz := disjoint_point_or_and_false_on_pairs ha hand hin hpure qpure hsidep hsideq hdisj x y
  rw [hz] at hv
  cases hv


lemma productive_pure_point_and_singleton {P L : ℕ} {C : Circuit} {a p q : ℕ}
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (hin : (gateAt C a).inputs = [p, q])
    (hpure : ∀ g, OrReaches (P + L) C p g → (gateAt C g).op = GateOp.or)
    (qpure : ∀ g, OrReaches (P + L) C q g → (gateAt C g).op = GateOp.or)
    (hsidep : ∀ u ∈ orIn (P + L) C p, u.val < P)
    (hsideq : ∀ u ∈ orIn (P + L) C q, u.val < P)
    (hprod : ∃ x : Fin P, ∃ y : Fin L, PEqualNP.EdgeOwnership.gateVal (P + L) C a
      (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd L x) (Fin.natAdd P y)) = true) :
    (singletonInputs (P + L) C (P + L + a)).Nonempty := by
  obtain ⟨u, hu⟩ := productive_pure_point_and_intersection ha hand hin hpure qpure hsidep hsideq hprod
  obtain ⟨hup, huq⟩ := Finset.mem_inter.mp hu
  obtain ⟨x, y, hxy⟩ := hprod
  have hvals := (val_and (n := P + L) (by simp) ha hand).mp hxy
  refine ⟨u, ?_⟩
  simp only [singletonInputs, Finset.mem_filter, Finset.mem_univ, true_and]
  apply (val_and (by simp) ha hand).mpr
  intro w hw
  have hwlt := (hvals w hw).1
  rw [hin] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact ⟨hwlt, orIn_value hup _ (pairInput_left u u)⟩
  · exact ⟨hwlt, orIn_value huq _ (pairInput_left u u)⟩

end Sharing

namespace ChoiceErase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2584.GuardedErase

lemma least_no_choice_and (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (pre post : List Gate)
    (u v : ℕ) (choose : Gate → ℕ)
    (hC : C.gates = pre ++ ⟨GateOp.and, [u, v]⟩ :: post)
    (hleast : PEqualNP.TopForm.IsLeastAO G C)
    (hu : u < n + pre.length) (hv : v < n + pre.length)
    (hchoose : ∀ g, choose g = u ∨ choose g = v)
    (hinputs : ∀ g ∈ post, n + pre.length ∈ g.inputs →
      ∀ i ∈ g.inputs, i < n + pre.length ∨ i = n + pre.length)
    (hbelow : ∀ x : Fin n → Bool, circuitFun n C x = false →
      ∀ g ∈ post, n + pre.length ∈ g.inputs →
      g.op.eval (g.inputs.map fun i =>
        if i = n + pre.length then (wf pre (List.ofFn x)).getD (choose g) false
        else (wf pre (List.ofFn x)).getD i false) = false)
    (hout : C.output ≠ n + pre.length) :
    False := by
  obtain ⟨D, hao, hsize, hfun⟩ := erase_choice_and n C pre post u v choose hC
    hleast.1 hu hv hchoose hinputs hbelow hout
  have hle := hleast.2.2 D hao (hfun.trans hleast.2.1)
  omega

end ChoiceErase


namespace TwoJunkStructure

lemma point_factors_cover_line {P L : ℕ} (I : Fin P → Fin L → Prop)
    (A B C : Finset (Fin P)) (l : Fin L)
    (hsound : ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, I a l ∨ I b l ∨ I c l) :
    (∀ a ∈ A, I a l) ∨ (∀ b ∈ B, I b l) ∨ (∀ c ∈ C, I c l) := by
  classical
  by_cases hA : ∀ a ∈ A, I a l
  · exact Or.inl hA
  by_cases hB : ∀ b ∈ B, I b l
  · exact Or.inr (Or.inl hB)
  right
  right
  push Not at hA hB
  obtain ⟨a, ha, hna⟩ := hA
  obtain ⟨b, hb, hnb⟩ := hB
  intro c hc
  exact ((hsound a ha b hb c hc).resolve_left hna).resolve_left hnb

lemma point_factor_covers_at_most_one_line {P L : ℕ}
    (I : Fin P → Fin L → Prop) (A : Finset (Fin P))
    (hfour : ∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (hA : 2 ≤ A.card) (l m : Fin L)
    (hl : ∀ a ∈ A, I a l) (hm : ∀ a ∈ A, I a m) : l = m := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  by_contra hlm
  exact hfour a b l m hab hlm ⟨hl a ha, hm a ha, hl b hb, hm b hb⟩

lemma three_point_factors_limit_lines {P L : ℕ}
    (I : Fin P → Fin L → Prop) (A B C : Finset (Fin P)) (D : Finset (Fin L))
    (hfour : ∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hC : 2 ≤ C.card)
    (hsound : ∀ l ∈ D, ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, I a l ∨ I b l ∨ I c l) :
    D.card ≤ 3 := by
  classical
  let lines (S : Finset (Fin P)) : Finset (Fin L) :=
    D.filter fun l => ∀ a ∈ S, I a l
  have hbound (S : Finset (Fin P)) (hS : 2 ≤ S.card) : (lines S).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro l hl m hm
    exact point_factor_covers_at_most_one_line I S hfour hS l m
      (Finset.mem_filter.mp hl).2 (Finset.mem_filter.mp hm).2
  have hcover : D ⊆ lines A ∪ lines B ∪ lines C := by
    intro l hl
    rcases point_factors_cover_line I A B C l (hsound l hl) with ha | hb | hc
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hl, ha⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hl, hb⟩))
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hl, hc⟩)
  have hAB := Finset.card_union_le (lines A) (lines B)
  have hABC := Finset.card_union_le (lines A ∪ lines B) (lines C)
  have hD := Finset.card_le_card hcover
  have ha := hbound A hA
  have hb := hbound B hB
  have hc := hbound C hC
  omega

lemma point_factors_small_line_side_or_singleton {P L : ℕ}
    (I : Fin P → Fin L → Prop) (A B C : Finset (Fin P)) (D : Finset (Fin L))
    (hfour : ∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (p : Fin P) (hp : p ∈ A ∧ p ∈ B ∧ p ∈ C)
    (hsound : ∀ l ∈ D, ∀ a ∈ A, ∀ b ∈ B, ∀ c ∈ C, I a l ∨ I b l ∨ I c l) :
    D.card ≤ 3 ∨ A = {p} ∨ B = {p} ∨ C = {p} := by
  have hsmall (S : Finset (Fin P)) (hp : p ∈ S) (hc : S.card ≤ 1) : S = {p} := by
    apply Finset.ext
    intro a
    simp only [Finset.mem_singleton]
    constructor
    · intro ha
      exact Finset.card_le_one.mp hc a ha p hp
    · intro ha
      simpa [ha] using hp
  by_cases hA : 2 ≤ A.card
  · by_cases hB : 2 ≤ B.card
    · by_cases hC : 2 ≤ C.card
      · exact Or.inl (three_point_factors_limit_lines I A B C D hfour hA hB hC hsound)
      · exact Or.inr (Or.inr (Or.inr (hsmall C hp.2.2 (by omega))))
    · exact Or.inr (Or.inr (Or.inl (hsmall B hp.2.1 (by omega))))
  · exact Or.inr (Or.inl (hsmall A hp.1 (by omega)))

end TwoJunkStructure

namespace DirectFactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_2584.GuardedErase
open PEqualNP.Outside.L_meta_2584.Sharing

lemma prefix_value {n : ℕ} {C : Circuit} {pre post : List Gate}
    (hC : C.gates = pre ++ post) (x : Fin n → Bool) {w : ℕ}
    (hw : w < n + pre.length) :
    val C (List.ofFn x) w = (wf pre (List.ofFn x)).getD w false := by
  unfold val
  rw [wires_eq_foldl, hC, List.foldl_append]
  apply foldl_getD_lt
  simpa only [foldl_length, List.length_ofFn] using hw

lemma erase_pure_point_and_direct_line_readers {P L : ℕ}
    (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (pre post : List Gate) (u v : ℕ)
    (hC : C.gates = pre ++ ⟨GateOp.and, [u, v]⟩ :: post)
    (hao : PEqualNP.TopForm.IsAO2 (P + L) C)
    (hf : circuitFun (P + L) C = fun x =>
      decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (hu : u < P + L + pre.length) (hv : v < P + L + pre.length)
    (hpureu : ∀ g, OrReaches (P + L) C u g → (gateAt C g).op = GateOp.or)
    (hpurev : ∀ g, OrReaches (P + L) C v g → (gateAt C g).op = GateOp.or)
    (hsideu : ∀ a ∈ orIn (P + L) C u, a.val < P)
    (hsidev : ∀ a ∈ orIn (P + L) C v, a.val < P)
    (hread : ∀ r ∈ post, P + L + pre.length ∈ r.inputs →
      ∃ l : Fin L, r.op = GateOp.and ∧ (Fin.natAdd P l).val ∈ r.inputs ∧
        (∀ i ∈ r.inputs, i = (Fin.natAdd P l).val ∨ i = P + L + pre.length) ∧
        ∀ x : Fin (P + L) → Bool,
          r.op.eval (r.inputs.map (val C (List.ofFn x))) = true →
          decide (∃ p k, I p k ∧ x (Fin.castAdd L p) = true ∧
            x (Fin.natAdd P k) = true) = true)
    (hout : C.output ≠ P + L + pre.length) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (P + L) D ∧ D.size < C.size ∧
      circuitFun (P + L) D = circuitFun (P + L) C := by
  classical
  let N := P + L + pre.length
  have hglt : pre.length < C.gates.length := by rw [hC]; simp
  have hgate : gateAt C pre.length = ⟨GateOp.and, [u, v]⟩ := by
    simp [gateAt, hC, List.getD_eq_getElem?_getD]
  have hprefix (x : Fin (P + L) → Bool) (w : ℕ) (hw : w < N) :
      val C (List.ofFn x) w = (wf pre (List.ofFn x)).getD w false :=
    prefix_value hC x hw
  have hex (r : Gate) : ∃ w : ℕ, (w = u ∨ w = v) ∧
      (r ∈ post → N ∈ r.inputs → ∀ x : Fin (P + L) → Bool,
        circuitFun (P + L) C x = false →
        r.op.eval (r.inputs.map fun i => if i = N then
          (wf pre (List.ofFn x)).getD w false
          else (wf pre (List.ofFn x)).getD i false) = false) := by
    by_cases hr : r ∈ post ∧ N ∈ r.inputs
    · obtain ⟨l, hrop, hlmem, hrinputs, hrsound⟩ := hread r hr.1 hr.2
      let A := Finset.univ.filter (fun a : Fin P => Fin.castAdd L a ∈ orIn (P + L) C u)
      let B := Finset.univ.filter (fun b : Fin P => Fin.castAdd L b ∈ orIn (P + L) C v)
      have hfactor := choose_incident_factor I A B l (fun x hl hA hB => by
        obtain ⟨a, ha, hxa⟩ := hA
        obtain ⟨b, hb, hxb⟩ := hB
        have huv : val C (List.ofFn x) N = true := by
          apply (val_and (by simp) hglt (by simp [hgate])).mpr
          intro i hi
          have hilt := hao.2.1 pre.length hglt i hi
          rw [hgate] at hi
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl
          · exact ⟨hilt, orIn_value (Finset.mem_filter.mp ha).2 x hxa⟩
          · exact ⟨hilt, orIn_value (Finset.mem_filter.mp hb).2 x hxb⟩
        apply hrsound x
        rw [hrop]
        apply List.all_eq_true.mpr
        intro b hb
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
        rcases hrinputs i hi with rfl | rfl
        · exact (val_ofFn C x _).trans hl
        · exact huv)
      have hchoice : ∃ w, (w = u ∨ w = v) ∧
          (∀ g, OrReaches (P + L) C w g → (gateAt C g).op = GateOp.or) ∧
          (∀ a ∈ orIn (P + L) C w, a.val < P) ∧
          ∀ a : Fin P, Fin.castAdd L a ∈ orIn (P + L) C w → I a l := by
        rcases hfactor with huadj | hvadj
        · exact ⟨u, Or.inl rfl, hpureu, hsideu,
            fun a ha => huadj a (by simp [A, ha])⟩
        · exact ⟨v, Or.inr rfl, hpurev, hsidev,
            fun a ha => hvadj a (by simp [B, ha])⟩
      obtain ⟨w, hwchoice, hwpure, hwside, hwadj⟩ := hchoice
      refine ⟨w, hwchoice, ?_⟩
      intro _ _ x hfalse
      apply Bool.eq_false_iff.mpr
      intro htrue
      rw [hrop] at htrue
      have hval := List.all_eq_true.mp htrue
      have hNmem := hval _ (List.mem_map.mpr ⟨N, hr.2, rfl⟩)
      have hwtrue : (wf pre (List.ofFn x)).getD w false = true := by simpa using hNmem
      have hlN : (Fin.natAdd P l).val ≠ N := by simp only [Fin.val_natAdd]; omega
      have hltrue := hval _ (List.mem_map.mpr ⟨(Fin.natAdd P l).val, hlmem, rfl⟩)
      rw [ite_eq_right hlN] at hltrue
      have hwlt : w < N := by rcases hwchoice with rfl | rfl <;> assumption
      have hline : x (Fin.natAdd P l) = true := by
        rw [← hprefix x _ (by simp only [Fin.val_natAdd]; omega)] at hltrue
        exact (val_ofFn C x _).symm.trans hltrue
      have htarget := pure_point_or_times_line_sound I l hwpure hwside hwadj x
        ((hprefix x w hwlt).trans hwtrue) hline
      have hctrue : circuitFun (P + L) C x = true := (congrFun hf x).trans htarget
      rw [hfalse] at hctrue
      cases hctrue
    · exact ⟨u, Or.inl rfl, fun h1 h2 => (hr ⟨h1, h2⟩).elim⟩
  choose pick hpick using hex
  apply ChoiceErase.erase_choice_and (P + L) C pre post u v pick hC hao hu hv
    (fun r => (hpick r).1) ?_ (fun x hx r hr hn => (hpick r).2 hr hn x hx) hout
  intro r hr hn i hi
  obtain ⟨l, _, _, hrinputs, _⟩ := hread r hr hn
  rcases hrinputs i hi with rfl | rfl
  · exact Or.inl (by simp only [Fin.val_natAdd]; omega)
  · exact Or.inr rfl

end DirectFactor

namespace AliasErase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2584.GuardedErase
open PEqualNP.Outside.L_meta_2584.ChoiceErase

lemma surg_alias_le (T : Gate → Gate) (A : List Bool) (b : Bool) (a : ℕ)
    (ha : a < A.length) (hb : A.getD a false = true → b = true) (post : List Gate)
    (hT : ∀ g ∈ post, ∀ E E' : List Bool,
      List.Forall₂ (fun a b => a = true → b = true) E' E →
      (T g).op.eval ((T g).inputs.map fun i => (A ++ E').getD i false) = true →
        g.op.eval (g.inputs.map fun i => (A ++ b :: E).getD i false) = true) :
    ∀ E E' : List Bool,
      List.Forall₂ (fun a b => a = true → b = true) E' E →
      ∀ o, (wf (post.map T) (A ++ E')).getD (rn A.length a o) false = true →
        (wf post (A ++ b :: E)).getD o false = true := by
  induction post with
  | nil =>
    intro E E' h o hv
    change (A ++ E').getD (rn A.length a o) false = true at hv
    change (A ++ b :: E).getD o false = true
    by_cases ho : o = A.length
    · subst o
      have hrn : rn A.length a A.length = a := by simp [rn]
      rw [hrn, getD_left A E' a ha] at hv
      rw [getD_mid A E b A.length rfl]
      exact hb hv
    · rw [rn_eq_sk A.length a o ho] at hv
      have hh := forall₂_getD (forall₂_prefix A h) (sk A.length o) hv
      exact (getD_sk A E b A.length rfl o ho).symm.trans hh
  | cons g post ih =>
    intro E E' h o hv
    let v := g.op.eval (g.inputs.map fun i => (A ++ b :: E).getD i false)
    let v' := (T g).op.eval ((T g).inputs.map fun i => (A ++ E').getD i false)
    have hvv : v' = true → v = true := hT g (by simp) E E' h
    have hh : List.Forall₂ (fun x y => x = true → y = true) (E' ++ [v']) (E ++ [v]) :=
      forall₂_snoc h hvv
    have htail := ih (fun g' hg' => hT g' (by simp [hg']))
      (E ++ [v]) (E' ++ [v']) hh o
    change (wf post ((A ++ b :: E) ++ [v])).getD o false = true
    rw [List.append_assoc, List.cons_append]
    apply htail
    simpa only [List.map_cons, wf_cons, List.append_assoc] using hv

lemma erase_alias (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate) (a : ℕ)
    (hC : C.gates = pre ++ g :: post)
    (hao : PEqualNP.TopForm.IsAO2 n C) (ha : a < n + pre.length)
    (hle : ∀ x : Fin n → Bool, (wf pre (List.ofFn x)).getD a false = true →
      g.op.eval (g.inputs.map fun i => (wf pre (List.ofFn x)).getD i false) = true) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧
      (∀ x, circuitFun n D x = true → circuitFun n C x = true) ∧
      ∀ x, (wf pre (List.ofFn x)).getD a false =
          g.op.eval (g.inputs.map fun i => (wf pre (List.ofFn x)).getD i false) →
        circuitFun n D x = circuitFun n C x := by
  let N := n + pre.length
  let T := Tc N a
  let D : Circuit := ⟨pre ++ post.map T, rn N a C.output⟩
  have hmono : Monotone2 C := fun g hg => ⟨hao.1 g hg, (hao.2.2 g hg).le⟩
  have hpost (r : Gate) (hr : r ∈ post) : r ∈ C.gates := by
    rw [hC]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hr)))
  obtain ⟨hm, hrb, hs⟩ := asm n C pre post g hC T (rn N a C.output) hmono hao.2.1
    (Tc_legal N a) (fun r _ M hM hi => Tc_rb N a ha r M hM hi)
  have hAO : PEqualNP.TopForm.IsAO2 n D := by
    refine ⟨fun r hr => (legal_of D hm r hr).1, hrb, ?_⟩
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hao.2.2 r (by rw [hC]; exact List.mem_append.mpr (Or.inl hr))
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      simpa [T, Tc] using hao.2.2 r' (hpost r' hr')
  refine ⟨D, hAO, hs, ?_, ?_⟩
  · intro x hD
    let A := wf pre (List.ofFn x)
    let b := g.op.eval (g.inputs.map fun i => A.getD i false)
    have hN : A.length = N := by simp [A, N, wf_len]
    have haA : a < A.length := by omega
    have hb : A.getD a false = true → b = true := hle x
    have hT : ∀ r ∈ post, ∀ E E' : List Bool,
        List.Forall₂ (fun a b => a = true → b = true) E' E →
        (T r).op.eval ((T r).inputs.map fun i => (A ++ E').getD i false) = true →
          r.op.eval (r.inputs.map fun i => (A ++ b :: E).getD i false) = true := by
      intro r hr E E' hEE htrue
      change r.op.eval ((r.inputs.map (rn N a)).map _) = true at htrue
      rw [List.map_map] at htrue
      apply gate_imp r (hao.1 r (hpost r hr)) _ _ ?_ htrue
      intro i hi hiv
      change (A ++ E').getD (rn N a i) false = true at hiv
      by_cases hiN : i = N
      · subst i
        have hrn : rn N a N = a := by simp [rn]
        rw [hrn, getD_left A E' a haA] at hiv
        rw [getD_mid A E b N hN]
        exact hb hiv
      · rw [rn_eq_sk N a i hiN] at hiv
        have hh := forall₂_getD (forall₂_prefix A hEE) (sk N i) hiv
        exact (getD_sk A E b N hN i hiN).symm.trans hh
    have hh := surg_alias_le T A b a haA hb post hT [] [] .nil C.output
    change (wf (pre ++ post.map T) (List.ofFn x)).getD (rn N a C.output) false = true at hD
    rw [wf_append] at hD
    have hval := hh (by simpa only [List.append_nil, hN] using hD)
    change (wf C.gates (List.ofFn x)).getD C.output false = true
    rw [hC, wf_append, wf_cons]
    exact hval
  · intro x heq
    let A := wf pre (List.ofFn x)
    let b := g.op.eval (g.inputs.map fun i => A.getD i false)
    have hN : A.length = N := by simp [A, N, wf_len]
    have hT : ∀ r ∈ post, ∀ E : List Bool,
        r.op.eval (r.inputs.map fun i => (A ++ b :: E).getD i false) =
          (T r).op.eval ((T r).inputs.map fun i => (A ++ E).getD i false) := by
      intro r _ E
      exact sound_c A E b N hN a ha heq r
    obtain ⟨E, hold, hnew⟩ := ev pre post g T (List.ofFn x) b rfl hT
    change (wf (pre ++ post.map T) (List.ofFn x)).getD (rn N a C.output) false =
      (wf C.gates (List.ofFn x)).getD C.output false
    rw [hC, hold, hnew]
    exact getD_rn A E b N hN a ha heq C.output

end AliasErase

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma common_or_input_implies_and {n : ℕ} {C : Circuit}
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C) {a p q : ℕ}
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (hin : (gateAt C a).inputs = [p, q]) {u : Fin n}
    (hu : u ∈ orIn n C p ∩ orIn n C q) (x : Fin n → Bool) (hx : x u = true) :
    PEqualNP.EdgeOwnership.gateVal n C a x = true := by
  obtain ⟨hup, huq⟩ := Finset.mem_inter.mp hu
  apply (val_and (by simp) ha hand).mpr
  intro w hw
  have hwlt := hRB a ha w hw
  rw [hin] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact ⟨hwlt, orIn_value hup x hx⟩
  · exact ⟨hwlt, orIn_value huq x hx⟩

lemma pure_point_and_pair_iff {P L : ℕ} {C : Circuit}
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (P + L) C) {a p q : ℕ}
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (hin : (gateAt C a).inputs = [p, q])
    (hpure : ∀ g, OrReaches (P + L) C p g → (gateAt C g).op = GateOp.or)
    (qpure : ∀ g, OrReaches (P + L) C q g → (gateAt C g).op = GateOp.or)
    (hsidep : ∀ u ∈ orIn (P + L) C p, u.val < P)
    (hsideq : ∀ u ∈ orIn (P + L) C q, u.val < P)
    (x : Fin P) (y : Fin L) :
    PEqualNP.EdgeOwnership.gateVal (P + L) C a
      (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd L x) (Fin.natAdd P y)) = true ↔
      Fin.castAdd L x ∈ orIn (P + L) C p ∩ orIn (P + L) C q := by
  constructor
  · intro hv
    have hvals := (val_and (n := P + L) (by simp) ha hand).mp hv
    have hpv := (hvals p (by rw [hin]; simp)).2
    have hqv := (hvals q (by rw [hin]; simp)).2
    exact Finset.mem_inter.mpr
      ⟨pure_or_pair_support hpure (fun u => u.val < P) hsidep _ _ (by simp) hpv,
       pure_or_pair_support qpure (fun u => u.val < P) hsideq _ _ (by simp) hqv⟩
  · intro hu
    exact common_or_input_implies_and hRB ha hand hin hu _ (pairInput_left _ _)

lemma pure_point_and_singleton_pair_value {P L : ℕ} {C : Circuit}
    (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (P + L) C) {a p q : ℕ}
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (hin : (gateAt C a).inputs = [p, q])
    (hpure : ∀ g, OrReaches (P + L) C p g → (gateAt C g).op = GateOp.or)
    (qpure : ∀ g, OrReaches (P + L) C q g → (gateAt C g).op = GateOp.or)
    (hsidep : ∀ v ∈ orIn (P + L) C p, v.val < P)
    (hsideq : ∀ v ∈ orIn (P + L) C q, v.val < P)
    (u : Fin (P + L)) (hmeet : orIn (P + L) C p ∩ orIn (P + L) C q = {u})
    (x : Fin P) (y : Fin L) :
    PEqualNP.EdgeOwnership.gateVal (P + L) C a
      (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd L x) (Fin.natAdd P y)) =
      PEqualNP.EdgeOwnership.pairInput (Fin.castAdd L x) (Fin.natAdd P y) u := by
  have hu : u ∈ orIn (P + L) C p ∩ orIn (P + L) C q := by rw [hmeet]; simp
  have hup := hsidep u (Finset.mem_inter.mp hu).1
  apply Bool.eq_iff_iff.mpr
  rw [pure_point_and_pair_iff hRB ha hand hin hpure qpure hsidep hsideq, hmeet,
    Finset.mem_singleton, pairInput_true]
  constructor
  · intro he
    exact Or.inl he.symm
  · rintro (he | he)
    · exact he.symm
    · have heval := congrArg Fin.val he
      simp only [Fin.val_natAdd] at heval
      omega

end Sharing

namespace MinimumPure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2584.GuardedErase
open PEqualNP.Outside.L_meta_2584.Sharing

lemma prefix_input_value {n : ℕ} (pre : List Gate) (x : Fin n → Bool) (u : Fin n) :
    (wf pre (List.ofFn x)).getD u.val false = x u := by
  change (pre.foldl stepWire (List.ofFn x)).getD u.val false = x u
  rw [foldl_getD_lt pre (List.ofFn x) u.val (by simpa using u.isLt)]
  simp [List.getD_eq_getElem?_getD]

lemma prefix_gate_value {n : ℕ} {C : Circuit} {pre post : List Gate} {g : Gate}
    (hC : C.gates = pre ++ g :: post) (x : Fin n → Bool) :
    gateVal n C pre.length x =
      g.op.eval (g.inputs.map fun i => (wf pre (List.ofFn x)).getD i false) := by
  change (wf C.gates (List.ofFn x)).getD (n + pre.length) false = _
  obtain ⟨E, hE⟩ := old_wires pre post g (List.ofFn x)
  rw [hC, hE]
  exact getD_mid _ E _ (n + pre.length) (by simp [wf_len])

lemma erase_pure_point_and_singleton {P L : ℕ}
    (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hAO : IsAO2 (P + L) C)
    (hf : circuitFun (P + L) C = fun x =>
      decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    {a p q : ℕ} (ha : a < C.gates.length)
    (hand : (gateAt C a).op = GateOp.and) (hin : (gateAt C a).inputs = [p, q])
    (hpure : ∀ g, OrReaches (P + L) C p g → (gateAt C g).op = GateOp.or)
    (qpure : ∀ g, OrReaches (P + L) C q g → (gateAt C g).op = GateOp.or)
    (hsidep : ∀ v ∈ orIn (P + L) C p, v.val < P)
    (hsideq : ∀ v ∈ orIn (P + L) C q, v.val < P)
    (u : Fin (P + L)) (hmeet : orIn (P + L) C p ∩ orIn (P + L) C q = {u}) :
    ∃ D : Circuit, IsAO2 (P + L) D ∧ D.size < C.size ∧
      circuitFun (P + L) D = fun x =>
        decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) := by
  obtain ⟨pre, post, g, hC, hlen, hg⟩ := split_gates C.gates a ha
  have hu : u ∈ orIn (P + L) C p ∩ orIn (P + L) C q := by rw [hmeet]; simp
  have hgate (x : Fin (P + L) → Bool) :
      gateVal (P + L) C a x =
        g.op.eval (g.inputs.map fun i => (wf pre (List.ofFn x)).getD i false) := by
    simpa only [hlen] using prefix_gate_value hC x
  obtain ⟨D, hD, hsize, hbelow, heq⟩ := AliasErase.erase_alias (P + L) C pre post g u.val
    hC hAO (by omega) (by
      intro x hx
      rw [prefix_input_value] at hx
      rw [← hgate]
      exact common_or_input_implies_and hAO.2.1 ha hand hin hu x hx)
  refine ⟨D, hD, hsize, incidence_eq_of_pair_cover I (circuitFun (P + L) D) ?_ ?_ ?_⟩
  · intro x y hxy
    exact val_monotone hD.1 x y hxy D.output
  · intro x hx
    simpa only [hf] using hbelow x hx
  · intro x y hxy
    have hvals := pure_point_and_singleton_pair_value hAO.2.1 ha hand hin hpure qpure
      hsidep hsideq u hmeet x y
    have hEq := heq (pairInput (Fin.castAdd L x) (Fin.natAdd P y)) (by
      rw [prefix_input_value, ← hgate]
      exact hvals.symm)
    rw [hEq, hf]
    exact decide_eq_true ⟨x, y, hxy, pairInput_left _ _, pairInput_right _ _⟩

lemma least_pure_point_and_intersection_card {P L : ℕ}
    (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hAO : IsAO2 (P + L) C)
    (hf : circuitFun (P + L) C = fun x =>
      decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (hmin : ∀ D : Circuit, IsAO2 (P + L) D →
      circuitFun (P + L) D = (fun x =>
        decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) →
      C.size ≤ D.size)
    {a p q : ℕ} (ha : a < C.gates.length)
    (hand : (gateAt C a).op = GateOp.and) (hin : (gateAt C a).inputs = [p, q])
    (hpure : ∀ g, OrReaches (P + L) C p g → (gateAt C g).op = GateOp.or)
    (qpure : ∀ g, OrReaches (P + L) C q g → (gateAt C g).op = GateOp.or)
    (hsidep : ∀ v ∈ orIn (P + L) C p, v.val < P)
    (hsideq : ∀ v ∈ orIn (P + L) C q, v.val < P) :
    2 ≤ (orIn (P + L) C p ∩ orIn (P + L) C q).card := by
  obtain ⟨x, y, hxy, hval⟩ := least_incidence_gate_productive I C hAO hf hmin a ha
  have hne := productive_pure_point_and_intersection ha hand hin hpure qpure hsidep hsideq
    ⟨x, y, hval⟩
  have hpos := Finset.card_pos.mpr hne
  by_contra hnot
  have hone : (orIn (P + L) C p ∩ orIn (P + L) C q).card = 1 := by omega
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hone
  obtain ⟨D, hD, hsmall, heq⟩ := erase_pure_point_and_singleton I C hAO hf ha hand hin
    hpure qpure hsidep hsideq u hu
  have := hmin D hD heq
  omega

lemma least_pure_point_and_singleton_card {P L : ℕ}
    (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hAO : IsAO2 (P + L) C)
    (hf : circuitFun (P + L) C = fun x =>
      decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (hmin : ∀ D : Circuit, IsAO2 (P + L) D →
      circuitFun (P + L) D = (fun x =>
        decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) →
      C.size ≤ D.size)
    {a p q : ℕ} (ha : a < C.gates.length)
    (hand : (gateAt C a).op = GateOp.and) (hin : (gateAt C a).inputs = [p, q])
    (hpure : ∀ g, OrReaches (P + L) C p g → (gateAt C g).op = GateOp.or)
    (qpure : ∀ g, OrReaches (P + L) C q g → (gateAt C g).op = GateOp.or)
    (hsidep : ∀ v ∈ orIn (P + L) C p, v.val < P)
    (hsideq : ∀ v ∈ orIn (P + L) C q, v.val < P) :
    2 ≤ (singletonInputs (P + L) C (P + L + a)).card := by
  apply (least_pure_point_and_intersection_card I C hAO hf hmin ha hand hin hpure qpure
    hsidep hsideq).trans
  apply Finset.card_le_card
  intro u hu
  simp only [singletonInputs, Finset.mem_filter, Finset.mem_univ, true_and]
  exact common_or_input_implies_and hAO.2.1 ha hand hin hu _ (pairInput_left u u)

end MinimumPure

namespace MinimumPure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2584.GuardedErase
open PEqualNP.Outside.L_meta_2584.Sharing

lemma prefix_wire_value {n : ℕ} {C : Circuit} {pre post : List Gate}
    (hC : C.gates = pre ++ post) (x : Fin n → Bool) {w : ℕ}
    (hw : w < n + pre.length) :
    val C (List.ofFn x) w = (wf pre (List.ofFn x)).getD w false := by
  unfold val
  rw [wires_eq_foldl, hC, List.foldl_append]
  apply foldl_getD_lt
  simpa only [foldl_length, List.length_ofFn] using hw

lemma erase_equivalent_wire {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    {j a : ℕ} (hj : j < C.gates.length) (ha : a < n + j)
    (hequiv : ∀ x : Fin n → Bool, gateVal n C j x = val C (List.ofFn x) a) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = circuitFun n C := by
  obtain ⟨pre, post, g, hC, hlen, hg⟩ := split_gates C.gates j hj
  have hgate (x : Fin n → Bool) :
      g.op.eval (g.inputs.map fun i => (wf pre (List.ofFn x)).getD i false) =
        (wf pre (List.ofFn x)).getD a false := by
    rw [← prefix_gate_value hC, hlen, hequiv]
    exact prefix_wire_value hC x (by omega)
  obtain ⟨D, hD, hsize, hbelow, heq⟩ := AliasErase.erase_alias n C pre post g a hC hAO
    (by omega) (by intro x hx; rw [hgate]; exact hx)
  exact ⟨D, hD, hsize, funext (fun x => heq x (hgate x).symm)⟩

lemma least_pure_or_and_factors_incomparable {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (hmin : ∀ D : Circuit, IsAO2 n D → circuitFun n D = circuitFun n C → C.size ≤ D.size)
    {a p q : ℕ} (ha : a < C.gates.length)
    (hand : (gateAt C a).op = GateOp.and) (hin : (gateAt C a).inputs = [p, q])
    (hpure : ∀ g, OrReaches n C p g → (gateAt C g).op = GateOp.or)
    (qpure : ∀ g, OrReaches n C q g → (gateAt C g).op = GateOp.or) :
    ¬orIn n C p ⊆ orIn n C q ∧ ¬orIn n C q ⊆ orIn n C p := by
  have hplt := hAO.2.1 a ha p (by rw [hin]; simp)
  have hqlt := hAO.2.1 a ha q (by rw [hin]; simp)
  have hcontra (w : ℕ) (hw : w < n + a)
      (heq : ∀ x : Fin n → Bool, gateVal n C a x = val C (List.ofFn x) w) : False := by
    obtain ⟨D, hD, hsize, heq⟩ := erase_equivalent_wire C hAO ha hw heq
    have := hmin D hD heq
    omega
  constructor
  · intro hsub
    apply hcontra p hplt
    intro x
    apply Bool.eq_iff_iff.mpr
    rw [gateVal_eq_val, val_and (by simp) ha hand]
    constructor
    · intro h
      exact (h p (by rw [hin]; simp)).2
    · intro hp w hw
      obtain ⟨u, hu, hxu⟩ := (pure_or_value_iff hpure x).mp hp
      have hq := orIn_value (hsub hu) x hxu
      rw [hin] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨hplt, hp⟩
      · exact ⟨hqlt, hq⟩
  · intro hsub
    apply hcontra q hqlt
    intro x
    apply Bool.eq_iff_iff.mpr
    rw [gateVal_eq_val, val_and (by simp) ha hand]
    constructor
    · intro h
      exact (h q (by rw [hin]; simp)).2
    · intro hq w hw
      obtain ⟨u, hu, hxu⟩ := (pure_or_value_iff qpure x).mp hq
      have hp := orIn_value (hsub hu) x hxu
      rw [hin] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨hplt, hp⟩
      · exact ⟨hqlt, hq⟩

lemma least_pure_point_and_four_inputs {P L : ℕ}
    (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hAO : IsAO2 (P + L) C)
    (hf : circuitFun (P + L) C = fun x =>
      decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (hmin : ∀ D : Circuit, IsAO2 (P + L) D →
      circuitFun (P + L) D = (fun x =>
        decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) →
      C.size ≤ D.size)
    {a p q : ℕ} (ha : a < C.gates.length)
    (hand : (gateAt C a).op = GateOp.and) (hin : (gateAt C a).inputs = [p, q])
    (hpure : ∀ g, OrReaches (P + L) C p g → (gateAt C g).op = GateOp.or)
    (qpure : ∀ g, OrReaches (P + L) C q g → (gateAt C g).op = GateOp.or)
    (hsidep : ∀ v ∈ orIn (P + L) C p, v.val < P)
    (hsideq : ∀ v ∈ orIn (P + L) C q, v.val < P) :
    4 ≤ (orIn (P + L) C p ∪ orIn (P + L) C q).card := by
  have hcommon := least_pure_point_and_intersection_card I C hAO hf hmin ha hand hin
    hpure qpure hsidep hsideq
  have hinc := least_pure_or_and_factors_incomparable C hAO
    (fun D hD heq => hmin D hD (heq.trans hf)) ha hand hin hpure qpure
  let A := orIn (P + L) C p
  let B := orIn (P + L) C q
  change ¬A ⊆ B ∧ ¬B ⊆ A at hinc
  have hBs : B ⊂ A ∪ B := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_right, ?_⟩
    intro heq
    apply hinc.1
    rw [heq]
    exact Finset.subset_union_left
  have hAB : (A ∩ B).card < B.card := by
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_right, ?_⟩
    intro heq
    apply hinc.2
    rw [← heq]
    exact Finset.inter_subset_left
  have hU := Finset.card_lt_card hBs
  change 2 ≤ (A ∩ B).card at hcommon
  change 4 ≤ (A ∪ B).card
  omega

end MinimumPure

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma or_context_choose_point_factor {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hRB : PEqualNP.MetaComplexity.NestedCover.ReadsBack (P + L) C)
    {g r p q w v : ℕ} (hg : g < C.gates.length) (hga : (gateAt C g).op = GateOp.and)
    (hgin : (gateAt C g).inputs = [p, q])
    (hr : r < C.gates.length) (hra : (gateAt C r).op = GateOp.and)
    (hrin : (gateAt C r).inputs = [w, v]) (hreach : OrReaches (P + L) C w g)
    (l : Fin L) (hl : Fin.natAdd P l ∈ orIn (P + L) C v)
    (hbelow : ∀ x : Fin (P + L) → Bool, PEqualNP.EdgeOwnership.gateVal (P + L) C r x = true →
      decide (∃ a b, I a b ∧ x (Fin.castAdd L a) = true ∧ x (Fin.natAdd P b) = true) = true) :
    (∀ a : Fin P, Fin.castAdd L a ∈ orIn (P + L) C p → I a l) ∨
    (∀ b : Fin P, Fin.castAdd L b ∈ orIn (P + L) C q → I b l) := by
  let A := Finset.univ.filter (fun a : Fin P => Fin.castAdd L a ∈ orIn (P + L) C p)
  let B := Finset.univ.filter (fun b : Fin P => Fin.castAdd L b ∈ orIn (P + L) C q)
  have hchoice := choose_incident_factor I A B l (fun x hxl hA hB => by
    obtain ⟨a, ha, hxa⟩ := hA
    obtain ⟨b, hb, hxb⟩ := hB
    have hpval := orIn_value (Finset.mem_filter.mp ha).2 x hxa
    have hqval := orIn_value (Finset.mem_filter.mp hb).2 x hxb
    have hgval : val C (List.ofFn x) (P + L + g) = true := by
      apply (val_and (by simp) hg hga).mpr
      intro u hu
      have hult := hRB g hg u hu
      rw [hgin] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact ⟨hult, hpval⟩
      · exact ⟨hult, hqval⟩
    apply hbelow x
    rw [gateVal_eq_val, val_and (by simp) hr hra]
    intro u hu
    refine ⟨hRB r hr u hu, ?_⟩
    rw [hrin] at hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact orStep_up (by simp) (orReaches_reach g _ hreach).1 hgval
    · exact orIn_value hl x hxl)
  simpa only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] using hchoice

lemma shared_pure_opposite_value_iff {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (h4 : NoFourCycle G)
    {a a' g : ℕ} (ha : a ∈ tops G C) (ha' : a' ∈ tops G C)
    (b b' : Fin 2) (hr : OrReaches n C (opnd C a b) g)
    (hr' : OrReaches n C (opnd C a' b') g)
    (hlarge : 1 < (singletonInputs n C (n + g)).card) {u : Fin n}
    (hu : u ∈ singletonInputs n C (opnd C a b.rev))
    (hpure : ∀ k, OrReaches n C (opnd C a' b'.rev) k → (gateAt C k).op = GateOp.or)
    (x : Fin n → Bool) :
    val C (List.ofFn x) (opnd C a' b'.rev) = true ↔
      (orIn n C (opnd C a' b'.rev)).Nonempty ∧ x u = true := by
  constructor
  · intro hv
    obtain ⟨v, hv, hxv⟩ := (pure_or_value_iff hpure x).mp hv
    have huv := shared_singleton_region_center_unique G C hAO h4 ha ha' b b' hr hr'
      hlarge hu (orIn_subset_singletonInputs hv)
    exact ⟨⟨v, hv⟩, huv ▸ hxv⟩
  · rintro ⟨⟨v, hv⟩, hxu⟩
    have huv := shared_singleton_region_center_unique G C hAO h4 ha ha' b b' hr hr'
      hlarge hu (orIn_subset_singletonInputs hv)
    exact orIn_value hv x (huv ▸ hxu)

end Sharing

namespace GuardedErase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma erase_unused_gate (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate) (a : ℕ)
    (hC : C.gates = pre ++ g :: post) (hao : PEqualNP.TopForm.IsAO2 n C)
    (ha : a < n + pre.length)
    (hread : ∀ r ∈ post, n + pre.length ∉ r.inputs)
    (hout : C.output ≠ n + pre.length) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧
      circuitFun n D = circuitFun n C := by
  let N := n + pre.length
  let D : Circuit := ⟨pre ++ post.map (Tc N a), rn N a C.output⟩
  have hmono : Monotone2 C := fun r hr => ⟨hao.1 r hr, (hao.2.2 r hr).le⟩
  have hpost (r : Gate) (hr : r ∈ post) : r ∈ C.gates := by
    rw [hC]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hr)))
  obtain ⟨hm, hr, hs⟩ := asm n C pre post g hC
    (Tc N a) (rn N a C.output) hmono hao.2.1 (Tc_legal N a)
      (fun r _ M hM hi => Tc_rb N a ha r M hM hi)
  have hAO : PEqualNP.TopForm.IsAO2 n D := by
    refine ⟨fun r hr => (legal_of D hm r hr).1, hr, ?_⟩
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hao.2.2 r (by rw [hC]; exact List.mem_append.mpr (Or.inl hr))
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      simpa [Tc] using hao.2.2 r' (hpost r' hr')
  refine ⟨D, hAO, hs, ?_⟩
  funext x
  let A := wf pre (List.ofFn x)
  let b := g.op.eval (g.inputs.map fun i => A.getD i false)
  have hN : A.length = N := by simp [A, N, wf_len]
  have hTp : ∀ r ∈ post, ∀ E : List Bool,
      r.op.eval (r.inputs.map fun i => (A ++ b :: E).getD i false) =
        (Tc N a r).op.eval ((Tc N a r).inputs.map fun i => (A ++ E).getD i false) := by
    intro r hr E
    change r.op.eval _ = r.op.eval ((r.inputs.map (rn N a)).map _)
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    have hn : N ∉ r.inputs := hread r hr
    have hiN : i ≠ N := fun e => hn (e ▸ hi)
    change (A ++ b :: E).getD i false = (A ++ E).getD (rn N a i) false
    rw [rn_eq_sk N a i hiN]
    exact (getD_sk A E b N hN i hiN).symm
  obtain ⟨E, hold, hnew⟩ := ev pre post g (Tc N a) (List.ofFn x) b rfl hTp
  change (wf (pre ++ post.map (Tc N a)) (List.ofFn x)).getD (rn N a C.output) false =
    (wf C.gates (List.ofFn x)).getD C.output false
  rw [hC, hold, hnew, rn_eq_sk N a C.output hout]
  exact getD_sk A E b N hN C.output hout

end GuardedErase

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_2584.GuardedErase

lemma least_gate_used {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) {j : ℕ} (hj : j < C.gates.length) :
    C.output = n + j ∨ ∃ k, k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
  by_contra h
  simp only [not_or, not_exists, not_and] at h
  obtain ⟨pre, post, g, hC, hlen, hg⟩ := split_gates C.gates j hj
  have hgj : gateAt C j = g := (GuardedErase.gateAt_eq C j hj).trans hg
  have hgmem : g ∈ C.gates := hg ▸ List.getElem_mem hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hL.1.2.2 g hgmem)
  have ha : a < n + pre.length := by
    rw [hlen]
    apply hL.1.2.1 j hj a
    rw [hgj, hab]
    simp
  have hread : ∀ r ∈ post, n + pre.length ∉ r.inputs := by
    intro r hr hn
    have hrC : r ∈ C.gates := by
      rw [hC]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hr)))
    obtain ⟨k, hk, hkr⟩ := List.mem_iff_getElem.mp hrC
    apply h.2 k hk
    rw [GuardedErase.gateAt_eq C k hk, hkr]
    simpa only [hlen] using hn
  obtain ⟨D, hD, hsmall, hfun⟩ := erase_unused_gate n C pre post g a hC hL.1 ha hread
    (by simpa only [hlen] using h.1)
  have hmin := hL.2.2 D hD (hfun.trans hL.2.1)
  omega

lemma least_gate_or_frontier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C C.output j ∨ ∃ k, k < C.gates.length ∧
      (gateAt C k).op = GateOp.and ∧
      ∃ w ∈ (gateAt C k).inputs, OrReaches n C w j := by
  have haux : ∀ m, ∀ j, C.gates.length - j = m → j < C.gates.length →
      OrReaches n C C.output j ∨ ∃ k, k < C.gates.length ∧
        (gateAt C k).op = GateOp.and ∧
        ∃ w ∈ (gateAt C k).inputs, OrReaches n C w j := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro j hm hj
      rcases least_gate_used G C hL hj with hout | ⟨k, hk, hread⟩
      · left
        rw [hout]
        exact (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩
      · have hjk : j < k := by have := hL.1.2.1 k hk (n + j) hread; omega
        rcases hL.1.1 _ (gateAt_mem hk) with hka | hko
        · exact Or.inr ⟨k, hk, hka, n + j, hread,
            (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩⟩
        · have hstep : OrStep n C (n + k) (n + j) :=
            ⟨k, hk, rfl, hko, hread, by omega⟩
          have hprop : ∀ w, OrReaches n C w k → OrReaches n C w j := by
            intro w hw
            exact reach_orReaches ((orReaches_reach k w hw).1.tail hstep) j rfl hj
          rcases ih (C.gates.length - k) (by omega) k rfl hk with hout | ⟨t, ht, hta, w, hw, hwr⟩
          · exact Or.inl (hprop C.output hout)
          · exact Or.inr ⟨t, ht, hta, w, hw, hprop w hwr⟩
  exact haux (C.gates.length - j) j rfl hj

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

lemma singleton_nonempty_of_and_ancestors {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (w : ℕ) (hw : w < n + C.gates.length)
    (hanc : ∀ j < C.gates.length,
      (w = n + j ∨ ∃ k < C.gates.length, w = n + k ∧ InCone n C j k) →
      (gateAt C j).op = GateOp.and → (singletonInputs n C (n + j)).Nonempty) :
    (singletonInputs n C w).Nonempty := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · refine ⟨⟨w, hn⟩, ?_⟩
      simp only [singletonInputs, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [val_ofFn C _ ⟨w, hn⟩]
      exact pairInput_left _ _
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    rcases hAO.1 _ (gateAt_mem hj) with hand | hor
    · exact hanc j hj (Or.inl rfl) hand
    · obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hj))
      have hpin : p ∈ (gateAt C j).inputs := by rw [hin]; simp
      have hplt : p < n + j := hAO.2.1 j hj p hpin
      have hpanc : ∀ i < C.gates.length,
          (p = n + i ∨ ∃ k < C.gates.length, p = n + k ∧ InCone n C i k) →
          (gateAt C i).op = GateOp.and → (singletonInputs n C (n + i)).Nonempty := by
        intro i hi hip hia
        apply hanc i hi (Or.inr ⟨j, hj, rfl, ?_⟩) hia
        apply (FlatRead.inCone_iff n C i j).mpr
        rcases hip with he | ⟨k, hk, he, hic⟩
        · refine ⟨hj, i, by omega, ?_, Or.inl rfl⟩
          simpa only [he] using hpin
        · refine ⟨hj, k, by omega, ?_, Or.inr hic⟩
          simpa only [he] using hpin
      obtain ⟨u, hu⟩ := ih p hplt (by omega) hpanc
      refine ⟨u, ?_⟩
      simp only [singletonInputs, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact (val_or (by simp) hj hor).mpr ⟨p, hpin, hplt, hu⟩

lemma top_operand_singleton_nonempty {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (hdirty : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → (singletonInputs n C (n + j)).Nonempty)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2) :
    (singletonInputs n C (opnd C a b)).Nonempty := by
  have ha' := ha
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha'
  obtain ⟨halen, hand, hbelow⟩ := ha'
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem halen))
  have hmem : opnd C a b ∈ (gateAt C a).inputs := by
    fin_cases b <;> simp [opnd, hin]
  have hlt := hAO.2.1 a halen (opnd C a b) hmem
  apply singleton_nonempty_of_and_ancestors hAO (opnd C a b) (by omega)
  intro j hj hanc hjand
  apply hdirty j hj hjand
  intro hjbelow
  apply hTop j hj a halen hjand hjbelow hand
  apply (FlatRead.inCone_iff n C j a).mpr
  rcases hanc with he | ⟨k, hk, he, hcone⟩
  · refine ⟨halen, j, by omega, ?_, Or.inl rfl⟩
    simpa only [he] using hmem
  · refine ⟨halen, k, by omega, ?_, Or.inr hcone⟩
    simpa only [he] using hmem

lemma mixed_region_not_top_operand {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (hdirty : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → (singletonInputs n C (n + j)).Nonempty)
    {a g : ℕ} (ha : a ∈ tops G C) (b : Fin 2) {u v : Fin n}
    (hu : u ∈ singletonInputs n C (n + g))
    (hv : v ∈ singletonInputs n C (n + g))
    (hnone : ∀ w, ¬(G.Adj u w ∧ G.Adj v w)) :
    ¬ OrReaches n C (opnd C a b) g := by
  intro hr
  have hempty := shared_region_opposite_empty_of_no_common_neighbor G C hAO ha b hr hu hv hnone
  have hnonempty := top_operand_singleton_nonempty G C hAO hTop hdirty ha b.rev
  rw [hempty] at hnonempty
  exact Finset.not_nonempty_empty hnonempty

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

lemma orReaches_gate_ancestor {n : ℕ} {C : Circuit} {g w : ℕ}
    (hr : OrReaches n C w g) :
    ∃ k < C.gates.length, w = n + k ∧ (g = k ∨ InCone n C g k) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have hwn := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, hh⟩ := (orReaches_iff n C k g).mp hr
    refine ⟨k, hk, rfl, ?_⟩
    rcases hh with he | ⟨hor, v, hvin, hvlt, hvr⟩
    · exact Or.inl he
    · obtain ⟨j, hj, hv, hg⟩ := ih v hvlt hvr
      right
      exact (FlatRead.inCone_iff n C g k).mpr
        ⟨hk, j, by omega, by simpa only [hv] using hvin, hg⟩

lemma orReaches_operand_inCone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a g : ℕ} (ha : a < C.gates.length) (b : Fin 2)
    (hr : OrReaches n C (opnd C a b) g) : InCone n C g a := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
  have hmem : opnd C a b ∈ (gateAt C a).inputs := by
    fin_cases b <;> simp [opnd, hin]
  have hlt := hAO.2.1 a ha (opnd C a b) hmem
  obtain ⟨k, hk, he, hcone⟩ := orReaches_gate_ancestor hr
  exact (FlatRead.inCone_iff n C g a).mpr
    ⟨ha, k, by omega, by simpa only [he] using hmem, hcone⟩

lemma two_dirty_mixed_unique_frontier {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h c : ℕ)
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = h)
    (hg : (singletonInputs n C (n + g)).Nonempty)
    (hh : (singletonInputs n C (n + h)).Nonempty)
    {u v : Fin n} (hu : u ∈ singletonInputs n C (n + c))
    (hv : v ∈ singletonInputs n C (n + c))
    (hnone : ∀ w, ¬(G.Adj u w ∧ G.Adj v w))
    (hcg : ¬ InCone n C c g)
    {a : ℕ} (ha : a < C.gates.length) (haand : (gateAt C a).op = GateOp.and)
    (b : Fin 2) (hr : OrReaches n C (opnd C a b) c) : a = h := by
  classical
  have hdirty : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → (singletonInputs n C (n + j)).Nonempty := by
    intro j hj hjand hjdirty
    rcases honly j hj hjand hjdirty with rfl | rfl
    · exact hg
    · exact hh
  have hnclean : ¬ BelowF G C a := by
    intro haclean
    have hatop : a ∈ tops G C := by
      simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
      exact ⟨ha, haand, haclean⟩
    exact mixed_region_not_top_operand G C hAO hTop hdirty hatop b hu hv hnone hr
  rcases honly a ha haand hnclean with he | he
  · subst a
    exact False.elim (hcg (orReaches_operand_inCone hAO ha b hr))
  · exact he

lemma singleton_region_not_output {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit)
    (hf : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    {g : ℕ} {u : Fin n} (hu : u ∈ singletonInputs n C (n + g)) :
    ¬ OrReaches n C C.output g := by
  intro hr
  have hval := singletonInputs_subset_of_orReaches hr hu
  simp only [singletonInputs, Finset.mem_filter, Finset.mem_univ, true_and] at hval
  change PEqualNP.MetaComplexity.circuitFun n C (pairInput u u) = true at hval
  rw [hf] at hval
  exact G.irrefl ((graphFun_pair G u u).mp hval)

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

lemma inCone_index_lt {n : ℕ} {C : Circuit} {i j : ℕ}
    (hij : InCone n C i j) : i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    obtain ⟨hj, k, hk, hmem, he⟩ := (FlatRead.inCone_iff n C i j).mp hij
    rcases he with rfl | he
    · exact hk
    · exact (ih k hk he).trans hk

lemma orReaches_wire_le {n : ℕ} {C : Circuit} {w g : ℕ}
    (hr : OrReaches n C w g) : n + g ≤ w := by
  obtain ⟨k, hk, rfl, he⟩ := orReaches_gate_ancestor hr
  rcases he with rfl | he
  · rfl
  · have := inCone_index_lt he
    omega

lemma orReaches_trans {n : ℕ} {C : Circuit} {w g c : ℕ}
    (hwg : OrReaches n C w g) (hgc : OrReaches n C (n + g) c) :
    OrReaches n C w c := by
  obtain ⟨hr1, hg⟩ := orReaches_reach g w hwg
  obtain ⟨hr2, hc⟩ := orReaches_reach c (n + g) hgc
  exact reach_orReaches (hr1.trans hr2) c rfl hc

lemma unique_frontier_private_reader {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (c h d : ℕ)
    (hinputs : (gateAt C h).inputs = [n + c, d])
    (hnotout : ¬ OrReaches n C C.output c)
    (hnotd : ¬ OrReaches n C d c)
    (hunique : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and →
      ∀ b : Fin 2, OrReaches n C (opnd C a b) c → a = h)
    (hlive : ∀ r < C.gates.length,
      OrReaches n C C.output r ∨ ∃ a < C.gates.length,
        (gateAt C a).op = GateOp.and ∧ ∃ b : Fin 2, OrReaches n C (opnd C a b) r)
    {r : ℕ} (hr : r < C.gates.length) (hread : n + c ∈ (gateAt C r).inputs) : r = h := by
  have hcr : c < r := by
    have := hAO.2.1 r hr (n + c) hread
    omega
  have hc : c < C.gates.length := hcr.trans hr
  have hself : OrReaches n C (n + c) c := (orReaches_iff n C c c).mpr ⟨hc, Or.inl rfl⟩
  rcases hAO.1 _ (gateAt_mem hr) with hand | hor
  · obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hr))
    rw [hin] at hread
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hread
    rcases hread with he | he
    · apply hunique r hr hand 0
      simpa [opnd, hin, ← he] using hself
    · apply hunique r hr hand 1
      simpa [opnd, hin, ← he] using hself
  · have hrc : OrReaches n C (n + r) c :=
      (orReaches_iff n C r c).mpr ⟨hr, Or.inr ⟨hor, n + c, hread, by omega, hself⟩⟩
    rcases hlive r hr with hout | ⟨a, ha, haand, b, har⟩
    · exact False.elim (hnotout (orReaches_trans hout hrc))
    · have hac := orReaches_trans har hrc
      have he := hunique a ha haand b hac
      subst a
      fin_cases b
      · have horle := orReaches_wire_le har
        simp only [opnd, hinputs, List.getD_cons_zero] at horle
        omega
      · apply False.elim
        apply hnotd
        simpa [opnd, hinputs] using hac

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

lemma least_gate_or_frontier_operand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C C.output j ∨ ∃ a < C.gates.length,
      (gateAt C a).op = GateOp.and ∧ ∃ b : Fin 2, OrReaches n C (opnd C a b) j := by
  rcases least_gate_or_frontier G C hL hj with hout | ⟨a, ha, haand, w, hw, hreach⟩
  · exact Or.inl hout
  · right
    refine ⟨a, ha, haand, ?_⟩
    obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hL.1.2.2 _ (gateAt_mem ha))
    rw [hin] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨0, by simpa [opnd, hin] using hreach⟩
    · exact ⟨1, by simpa [opnd, hin] using hreach⟩

lemma least_two_dirty_mixed_private_reader {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h c d : ℕ) (hinputs : (gateAt C h).inputs = [n + c, d])
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = h)
    (hg : (singletonInputs n C (n + g)).Nonempty)
    (hh : (singletonInputs n C (n + h)).Nonempty)
    {u v : Fin n} (hu : u ∈ singletonInputs n C (n + c))
    (hv : v ∈ singletonInputs n C (n + c))
    (hnone : ∀ w, ¬(G.Adj u w ∧ G.Adj v w))
    (hcg : ¬ InCone n C c g) (hnotd : ¬ OrReaches n C d c)
    {r : ℕ} (hr : r < C.gates.length) (hread : n + c ∈ (gateAt C r).inputs) : r = h := by
  apply unique_frontier_private_reader hL.1 c h d hinputs
    (singleton_region_not_output G C hL.2.1 hu) hnotd
  · intro a ha haand b har
    exact two_dirty_mixed_unique_frontier G C hL.1 hTop g h c honly hg hh
      hu hv hnone hcg ha haand b har
  · intro r hr
    exact least_gate_or_frontier_operand G C hL hr
  · exact hr
  · exact hread

end Sharing

namespace Reorder
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def sw (k i : ℕ) : ℕ := if i = k then k + 1 else if i = k + 1 then k else i

def rename (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sw k)⟩

def run {α : Type} (d : α) (op : GateOp → List α → α)
    (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [op g.op (g.inputs.map fun i => w.getD i d)]) w

lemma sw_below (k i : ℕ) (hi : i < k) : sw k i = i := by
  simp [sw, show i ≠ k by omega, show i ≠ k + 1 by omega]

lemma sw_involutive (k i : ℕ) : sw k (sw k i) = i := by
  unfold sw
  split_ifs <;> omega

lemma sw_lt (k m i : ℕ) (hm : k + 1 < m) (hi : i < m) : sw k i < m := by
  unfold sw
  split_ifs <;> omega

lemma getD_swap {α : Type} (d a b : α) (A E : List α) (i : ℕ) :
    (A ++ b :: a :: E).getD (sw A.length i) d = (A ++ a :: b :: E).getD i d := by
  by_cases hi : i < A.length
  · rw [sw_below _ _ hi, List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hi]
  · have hi' : A.length ≤ i := by omega
    by_cases he : i = A.length
    · subst i
      simp [sw, List.getD_eq_getElem?_getD]
    · by_cases he' : i = A.length + 1
      · subst i
        simp [sw, List.getD_eq_getElem?_getD]
      · have hs : sw A.length i = i := by simp [sw, he, he']
        rw [hs, List.getD_append_right _ _ _ _ hi', List.getD_append_right _ _ _ _ hi']
        have hi2 : 2 ≤ i - A.length := by omega
        obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hi2
        rw [hj]
        simp [List.getD_eq_getElem?_getD, Nat.add_comm]

lemma run_append {α : Type} (d : α) (op : GateOp → List α → α)
    (gs hs : List Gate) (w : List α) :
    run d op (gs ++ hs) w = run d op hs (run d op gs w) := by
  simp [run, List.foldl_append]

lemma run_length {α : Type} (d : α) (op : GateOp → List α → α)
    (gs : List Gate) (w : List α) : (run d op gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run d op gs (w ++ [_])).length = _
    rw [ih]
    simp
    omega

lemma run_renamed {α : Type} (d : α) (op : GateOp → List α → α)
    (A : List α) (a b : α) (post : List Gate) (E : List α) :
    ∃ F : List α,
      run d op post (A ++ a :: b :: E) = A ++ a :: b :: F ∧
      run d op (post.map (rename A.length)) (A ++ b :: a :: E) = A ++ b :: a :: F := by
  induction post generalizing E with
  | nil => exact ⟨E, rfl, rfl⟩
  | cons g post ih =>
    let v := op g.op (g.inputs.map fun i => (A ++ a :: b :: E).getD i d)
    have he : op (rename A.length g).op
        ((rename A.length g).inputs.map fun i => (A ++ b :: a :: E).getD i d) = v := by
      simp only [rename, List.map_map]
      congr 1
      exact List.map_congr_left (fun i _ => getD_swap d a b A E i)
    obtain ⟨F, h1, h2⟩ := ih (E ++ [v])
    refine ⟨F, ?_, ?_⟩
    · change run d op post ((A ++ a :: b :: E) ++ [v]) = _
      simpa only [List.append_assoc, List.cons_append] using h1
    · change run d op (post.map (rename A.length))
        ((A ++ b :: a :: E) ++ [op (rename A.length g).op
          ((rename A.length g).inputs.map fun i => (A ++ b :: a :: E).getD i d)]) = _
      rw [he]
      simpa only [List.append_assoc, List.cons_append] using h2

lemma block {α : Type} (d : α) (op : GateOp → List α → α)
    (A : List α) (a b : Gate)
    (ha : ∀ i ∈ a.inputs, i < A.length) (hb : ∀ i ∈ b.inputs, i < A.length) :
    run d op [a, b] A = A ++ [op a.op (a.inputs.map fun i => A.getD i d),
      op b.op (b.inputs.map fun i => A.getD i d)] := by
  have hb' (v : α) : b.inputs.map (fun i => (A ++ [v]).getD i d) =
      b.inputs.map (fun i => A.getD i d) :=
    List.map_congr_left (fun i hi => List.getD_append _ _ _ _ (hb i hi))
  simp only [run, List.foldl_cons, List.foldl_nil, hb', List.append_assoc]
  rfl

lemma adjacent_run {α : Type} (d : α) (op : GateOp → List α → α)
    (A : List α) (a b : Gate) (post : List Gate) (o : ℕ)
    (ha : ∀ i ∈ a.inputs, i < A.length) (hb : ∀ i ∈ b.inputs, i < A.length) :
    (run d op ([b, a] ++ post.map (rename A.length)) A).getD (sw A.length o) d =
      (run d op ([a, b] ++ post) A).getD o d := by
  rw [run_append, run_append, block d op A a b ha hb, block d op A b a hb ha]
  obtain ⟨F, hold, hnew⟩ := run_renamed d op A
    (op a.op (a.inputs.map fun i => A.getD i d))
    (op b.op (b.inputs.map fun i => A.getD i d)) post []
  rw [hold, hnew]
  exact getD_swap _ _ _ _ _ _

lemma adjacent_semantics (n : ℕ) (pre post : List Gate) (a b : Gate) (o : ℕ)
    (ha : ∀ i ∈ a.inputs, i < n + pre.length)
    (hb : ∀ i ∈ b.inputs, i < n + pre.length) :
    circuitFun n ⟨pre ++ [b, a] ++ post.map (rename (n + pre.length)), sw (n + pre.length) o⟩ =
      circuitFun n ⟨pre ++ [a, b] ++ post, o⟩ := by
  funext x
  let A := run false GateOp.eval pre (List.ofFn x)
  have hA : A.length = n + pre.length := by simp [A, run_length]
  have h := adjacent_run false GateOp.eval A a b post o
    (by simpa only [hA] using ha) (by simpa only [hA] using hb)
  rw [hA] at h
  simpa only [A, run, circuitFun, Circuit.eval, Circuit.wires, List.foldl_append] using h

lemma adjacent_wordRun (w : List (Set (List ℕ))) (pre post : List Gate) (a b : Gate) (o : ℕ)
    (ha : ∀ i ∈ a.inputs, i < w.length + pre.length)
    (hb : ∀ i ∈ b.inputs, i < w.length + pre.length) :
    (Rotation.wordRun (pre ++ [b, a] ++ post.map (rename (w.length + pre.length))) w).getD
      (sw (w.length + pre.length) o) ∅ =
      (Rotation.wordRun (pre ++ [a, b] ++ post) w).getD o ∅ := by
  let A := run ∅ Rotation.wordOp pre w
  have hA : A.length = w.length + pre.length := by simp [A, run_length]
  have h := adjacent_run ∅ Rotation.wordOp A a b post o
    (by simpa only [hA] using ha) (by simpa only [hA] using hb)
  rw [hA] at h
  have hs : Rotation.wordStep =
      (fun w g => w ++ [Rotation.wordOp g.op (g.inputs.map fun i => w.getD i ∅)]) := rfl
  simp only [Rotation.wordRun, hs, List.foldl_append]
  simpa only [A, run, List.foldl_append] using h

lemma adjacent_size (n : ℕ) (pre post : List Gate) (a b : Gate) (o : ℕ) :
    (⟨pre ++ [b, a] ++ post.map (rename (n + pre.length)), sw (n + pre.length) o⟩ : Circuit).size =
      (⟨pre ++ [a, b] ++ post, o⟩ : Circuit).size := by
  simp [Circuit.size]

lemma built_of_ao2 (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) :
    FalsePropagation.built n C.gates := by
  intro j g hg
  have hm : g ∈ C.gates := List.mem_iff_getElem?.mpr ⟨j, hg⟩
  have hj : j < C.gates.length := List.getElem?_eq_some_iff.mp hg |>.1
  have he : NestedCover.gateAt C j = g := by
    simp [NestedCover.gateAt, List.getD_eq_getElem?_getD, hg]
  exact ⟨h.1 g hm, h.2.2 g hm, fun i hi => h.2.1 j hj i (by simpa only [he] using hi)⟩

lemma adjacent_built (n : ℕ) (pre post : List Gate) (a b : Gate)
    (ha : ∀ i ∈ a.inputs, i < n + pre.length)
    (hb : ∀ i ∈ b.inputs, i < n + pre.length)
    (h : FalsePropagation.built n (pre ++ [a, b] ++ post)) :
    FalsePropagation.built n (pre ++ [b, a] ++ post.map (rename (n + pre.length))) := by
  intro j g hg
  by_cases hj : j < pre.length
  · have hg' : (pre ++ [a, b] ++ post)[j]? = some g := by
      simpa only [List.append_assoc, List.getElem?_append_left hj] using hg
    exact h j g hg'
  by_cases hj0 : j = pre.length
  · subst j
    have he : g = b := by
      simpa [List.append_assoc] using hg.symm
    subst g
    have h' := h (pre.length + 1) b (by simp [List.append_assoc])
    exact ⟨h'.1, h'.2.1, hb⟩
  by_cases hj1 : j = pre.length + 1
  · subst j
    have he : g = a := by
      simpa [List.append_assoc] using hg.symm
    subst g
    have h' := h pre.length a (by simp [List.append_assoc])
    exact ⟨h'.1, h'.2.1, fun i hi => by have := ha i hi; omega⟩
  have hj2 : pre.length + 2 ≤ j := by omega
  have hpost : (post.map (rename (n + pre.length)))[j - pre.length - 2]? = some g := by
    rw [List.getElem?_append_right (by simp; omega)] at hg
    simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero, Nat.sub_sub] using hg
  rw [List.getElem?_map] at hpost
  obtain ⟨g', hg', he⟩ := Option.map_eq_some_iff.mp hpost
  subst g
  have hold : (pre ++ [a, b] ++ post)[j]? = some g' := by
    rw [List.getElem?_append_right (by simp; omega)]
    simpa only [List.length_append, List.length_cons, List.length_nil, Nat.add_zero, Nat.sub_sub] using hg'
  have h' := h j g' hold
  refine ⟨h'.1, ?_, ?_⟩
  · simpa [rename] using h'.2.1
  · intro i hi
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
    exact sw_lt _ _ _ (by omega) (h'.2.2 i' hi')

lemma adjacent_ao2 (n : ℕ) (pre post : List Gate) (a b : Gate) (o : ℕ)
    (ha : ∀ i ∈ a.inputs, i < n + pre.length)
    (hb : ∀ i ∈ b.inputs, i < n + pre.length)
    (h : PEqualNP.TopForm.IsAO2 n ⟨pre ++ [a, b] ++ post, o⟩) :
    PEqualNP.TopForm.IsAO2 n
      ⟨pre ++ [b, a] ++ post.map (rename (n + pre.length)), sw (n + pre.length) o⟩ := by
  apply FalsePropagation.built_ao2
  exact adjacent_built n pre post a b ha hb (built_of_ao2 n _ h)

lemma adjacent_readsAtMost (n : ℕ) (pre post : List Gate) (a b : Gate) (o : ℕ)
    (ha : ∀ i ∈ a.inputs, i < n + pre.length)
    (hb : ∀ i ∈ b.inputs, i < n + pre.length) (S : List ℕ) (k : ℕ) :
    PEqualNP.ReadK.readsAtMost
      ⟨pre ++ [b, a] ++ post.map (rename (n + pre.length)), sw (n + pre.length) o⟩ n S k =
      PEqualNP.ReadK.readsAtMost ⟨pre ++ [a, b] ++ post, o⟩ n S k := by
  let op : GateOp → List (List (List ℕ)) → List (List ℕ) := fun op ins =>
    match op with
    | .or => ins.foldl (fun acc A => A.foldl PEqualNP.ReadK.insertNew acc) []
    | .and => ins.foldl (PEqualNP.ReadK.andStep k) [S.map fun _ => 0]
    | _ => []
  let A := run [] op pre ((List.range n).map (PEqualNP.ReadK.leafVectors S k))
  have hA : A.length = n + pre.length := by simp [A, run_length]
  have h := adjacent_run [] op A a b post o
    (by simpa only [hA] using ha) (by simpa only [hA] using hb)
  rw [hA] at h
  have hv (C : Circuit) : PEqualNP.ReadK.readVectors C n S k =
      run [] op C.gates ((List.range n).map (PEqualNP.ReadK.leafVectors S k)) := by
    unfold PEqualNP.ReadK.readVectors run
    rfl
  simp only [PEqualNP.ReadK.readsAtMost, hv]
  congr 1
  simpa only [A, run_append] using h

lemma adjacent_isReadK_iff (n : ℕ) (pre post : List Gate) (a b : Gate) (o : ℕ)
    (ha : ∀ i ∈ a.inputs, i < n + pre.length)
    (hb : ∀ i ∈ b.inputs, i < n + pre.length) (k : ℕ) :
    PEqualNP.ReadK.IsReadK n
      ⟨pre ++ [b, a] ++ post.map (rename (n + pre.length)), sw (n + pre.length) o⟩ k ↔
      PEqualNP.ReadK.IsReadK n ⟨pre ++ [a, b] ++ post, o⟩ k := by
  have hf := adjacent_semantics n pre post a b o ha hb
  simp only [PEqualNP.ReadK.IsReadK, PEqualNP.ReadK.IsPrimeImplicant, hf,
    adjacent_readsAtMost n pre post a b o ha hb]

end Reorder

namespace Reorder
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Same (n : ℕ) (C D : Circuit) : Prop :=
  circuitFun n D = circuitFun n C ∧ D.size = C.size ∧
    ∀ S k, PEqualNP.ReadK.readsAtMost D n S k = PEqualNP.ReadK.readsAtMost C n S k

lemma same_refl (n : ℕ) (C : Circuit) : Same n C C := ⟨rfl, rfl, fun _ _ => rfl⟩

lemma same_trans {n : ℕ} {C D E : Circuit} (h : Same n C D) (h' : Same n D E) :
    Same n C E := ⟨h'.1.trans h.1, h'.2.1.trans h.2.1,
      fun S k => (h'.2.2 S k).trans (h.2.2 S k)⟩

lemma adjacent_same (n : ℕ) (pre post : List Gate) (a b : Gate) (o : ℕ)
    (ha : ∀ i ∈ a.inputs, i < n + pre.length)
    (hb : ∀ i ∈ b.inputs, i < n + pre.length) :
    Same n ⟨pre ++ [a, b] ++ post, o⟩
      ⟨pre ++ [b, a] ++ post.map (rename (n + pre.length)), sw (n + pre.length) o⟩ :=
  ⟨adjacent_semantics n pre post a b o ha hb, adjacent_size n pre post a b o,
    adjacent_readsAtMost n pre post a b o ha hb⟩

lemma sw_self (k : ℕ) : sw k k = k + 1 := by simp [sw]

lemma sw_ne_succ (k i : ℕ) (hi : i ≠ k) : sw k i ≠ k + 1 := by
  unfold sw
  split_ifs <;> omega

lemma rename_avoids (k : ℕ) (gs : List Gate)
    (h : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ≠ k) :
    ∀ g ∈ gs.map (rename k), ∀ i ∈ g.inputs, i ≠ k + 1 := by
  intro g hg i hi
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
  exact sw_ne_succ k i' (h g' hg' i' hi')

def shape (n : ℕ) (pre : List Gate) (a : Gate) (mid : List Gate) (b : ℕ)
    (post : List Gate) (o : ℕ) : Circuit :=
  ⟨pre ++ a :: (mid ++ [⟨.and, [n + pre.length, b]⟩] ++ post), o⟩

lemma bubble_private (n : ℕ) (pre : List Gate) (a : Gate) (mid : List Gate) (b : ℕ)
    (post : List Gate) (o : ℕ)
    (ha : ∀ i ∈ a.inputs, i < n + pre.length)
    (hb : b < n + pre.length + 1 + mid.length) (hbne : b ≠ n + pre.length)
    (ho : o ≠ n + pre.length)
    (hprivate : ∀ g ∈ mid ++ post, ∀ i ∈ g.inputs, i ≠ n + pre.length)
    (hC : PEqualNP.TopForm.IsAO2 n (shape n pre a mid b post o)) :
    ∃ pre' post' b' o',
      pre'.length = pre.length + mid.length ∧
      PEqualNP.TopForm.IsAO2 n (shape n pre' a [] b' post' o') ∧
      Same n (shape n pre a mid b post o) (shape n pre' a [] b' post' o') ∧
      b' < n + pre'.length ∧ o' ≠ n + pre'.length ∧
      (∀ g ∈ post', ∀ i ∈ g.inputs, i ≠ n + pre'.length) ∧
      (∀ i, i < n + pre.length →
        circuitFun n ⟨(shape n pre' a [] b' post' o').gates, i⟩ =
          circuitFun n ⟨(shape n pre a mid b post o).gates, i⟩) ∧
      circuitFun n ⟨(shape n pre' a [] b' post' o').gates, b'⟩ =
        circuitFun n ⟨(shape n pre a mid b post o).gates, b⟩ := by
  generalize hm : mid.length = m
  induction m using Nat.strong_induction_on generalizing pre mid b post o with
  | _ m ih =>
    cases mid with
    | nil =>
      refine ⟨pre, post, b, o, by simp at hm; omega, hC, same_refl _ _, ?_, ho, ?_,
        fun _ _ => rfl, rfl⟩
      · simp only [List.length_nil] at hb
        omega
      · simpa only [List.nil_append] using hprivate
    | cons g mid =>
      let k := n + pre.length
      have hg : ∀ i ∈ g.inputs, i < k := by
        intro i hi
        have hidx : pre.length + 1 < (shape n pre a (g :: mid) b post o).gates.length := by
          simp [shape]
        have he : NestedCover.gateAt (shape n pre a (g :: mid) b post o) (pre.length + 1) = g := by
          simp [shape, NestedCover.gateAt, List.append_assoc, List.getD_eq_getElem?_getD]
        have hlt := hC.2.1 (pre.length + 1) hidx i (by simpa only [he] using hi)
        have hne := hprivate g (by simp) i hi
        dsimp [k]
        omega
      let tail := mid ++ [⟨.and, [k, b]⟩] ++ post
      let pre1 := pre ++ [g]
      let mid1 := mid.map (rename k)
      let post1 := post.map (rename k)
      let b1 := sw k b
      let o1 := sw k o
      have hsource : shape n pre a (g :: mid) b post o = ⟨pre ++ [a, g] ++ tail, o⟩ := by
        simp [shape, tail, k, List.append_assoc]
      have hdest : (⟨pre ++ [g, a] ++ tail.map (rename k), o1⟩ : Circuit) =
          shape n pre1 a mid1 b1 post1 o1 := by
        simp [shape, tail, pre1, mid1, post1, b1, rename, sw_self, k, List.map_append,
          List.append_assoc, Nat.add_assoc]
      have hao1 : PEqualNP.TopForm.IsAO2 n (shape n pre1 a mid1 b1 post1 o1) := by
        rw [← hdest]
        exact adjacent_ao2 n pre tail a g o ha hg (by rw [← hsource]; exact hC)
      have hs1 : Same n (shape n pre a (g :: mid) b post o)
          (shape n pre1 a mid1 b1 post1 o1) := by
        rw [hsource, ← hdest]
        exact adjacent_same n pre tail a g o ha hg
      have ha1 : ∀ i ∈ a.inputs, i < n + pre1.length := by
        intro i hi
        have := ha i hi
        simp [pre1]
        omega
      have hb1 : b1 < n + pre1.length + 1 + mid1.length := by
        have h := sw_lt k (n + pre.length + 2 + mid.length) b (by dsimp [k]; omega)
          (by simp only [List.length_cons] at hb; omega)
        simpa [b1, pre1, mid1, Nat.add_assoc] using h
      have hbne1 : b1 ≠ n + pre1.length := by
        simpa [b1, pre1, k, Nat.add_assoc] using sw_ne_succ k b hbne
      have ho1 : o1 ≠ n + pre1.length := by
        simpa [o1, pre1, k, Nat.add_assoc] using sw_ne_succ k o ho
      have hp1 : ∀ h ∈ mid1 ++ post1, ∀ i ∈ h.inputs, i ≠ n + pre1.length := by
        have hp : ∀ h ∈ mid ++ post, ∀ i ∈ h.inputs, i ≠ k := by
          intro h hh i hi
          apply hprivate h _ i hi
          simp only [List.mem_append, List.mem_cons] at hh ⊢
          tauto
        simpa [mid1, post1, pre1, k, List.map_append, Nat.add_assoc] using rename_avoids k (mid ++ post) hp
      have hvs (i : ℕ) :
          circuitFun n ⟨(shape n pre1 a mid1 b1 post1 o1).gates, sw k i⟩ =
            circuitFun n ⟨(shape n pre a (g :: mid) b post o).gates, i⟩ := by
        rw [congrArg Circuit.gates hsource, ← congrArg Circuit.gates hdest]
        exact adjacent_semantics n pre tail a g i ha hg
      obtain ⟨pre', post', b', o', hlen, hAO, hs, hb', ho', hp', hvals, hvalb⟩ :=
        ih mid.length (by simp only [List.length_cons] at hm; omega)
          pre1 mid1 b1 post1 o1 ha1 hb1 hbne1 ho1 hp1 hao1 (by simp [mid1])
      refine ⟨pre', post', b', o', ?_, hAO, same_trans hs1 hs, hb', ho', hp', ?_, ?_⟩
      · simp only [pre1, List.length_append, List.length_cons, List.length_nil] at hlen
        simp only [List.length_cons] at hm
        omega
      · intro i hi
        have hi1 : i < n + pre1.length := by simp [pre1]; omega
        exact (hvals i hi1).trans (by simpa only [sw_below k i hi] using hvs i)
      · exact hvalb.trans (hvs b)

lemma prefix_value (n : ℕ) (pre post : List Gate) (i : ℕ)
    (hi : i < n + pre.length) (z : Fin n → Bool) :
    circuitFun n ⟨pre ++ post, i⟩ z = (Rotation.run pre (List.ofFn z)).getD i false := by
  obtain ⟨E, he⟩ := GuardedErase.wf_ext post (GuardedErase.wf pre (List.ofFn z))
  change (GuardedErase.wf (pre ++ post) (List.ofFn z)).getD i false = _
  rw [GuardedErase.wf_append, he]
  exact List.getD_append _ _ _ _ (by simpa [GuardedErase.wf_len] using hi)

def rotated (n : ℕ) (pre : List Gate) (x a b : ℕ) (post : List Gate) (o : ℕ) : Circuit :=
  ⟨pre ++ [⟨.and, [a, b]⟩, ⟨.or, [x, n + pre.length]⟩] ++ post, o⟩

lemma nonadjacent_rotation (n : ℕ) (pre mid post : List Gate) (x a b o : ℕ)
    (hx : x < n + pre.length) (ha : a < n + pre.length)
    (hb : b < n + pre.length + 1 + mid.length) (hbne : b ≠ n + pre.length)
    (ho : o ≠ n + pre.length)
    (hprivate : ∀ g ∈ mid ++ post, ∀ i ∈ g.inputs, i ≠ n + pre.length)
    (hC : PEqualNP.TopForm.IsAO2 n (shape n pre ⟨.or, [x, a]⟩ mid b post o))
    (hdom : ∀ z : Fin n → Bool,
      circuitFun n ⟨(shape n pre ⟨.or, [x, a]⟩ mid b post o).gates, x⟩ z = true →
        circuitFun n ⟨(shape n pre ⟨.or, [x, a]⟩ mid b post o).gates, b⟩ z = true) :
    ∃ pre' post' b' o',
      pre'.length = pre.length + mid.length ∧
      PEqualNP.TopForm.IsAO2 n (rotated n pre' x a b' post' o') ∧
      (rotated n pre' x a b' post' o').size = (shape n pre ⟨.or, [x, a]⟩ mid b post o).size ∧
      circuitFun n (rotated n pre' x a b' post' o') =
        circuitFun n (shape n pre ⟨.or, [x, a]⟩ mid b post o) ∧
      (∀ S, PEqualNP.ReadK.readsAtMost (shape n pre ⟨.or, [x, a]⟩ mid b post o) n S 2 = true →
        PEqualNP.ReadK.readsAtMost (rotated n pre' x a b' post' o') n S 2 = true) ∧
      (PEqualNP.ReadK.IsReadK n (shape n pre ⟨.or, [x, a]⟩ mid b post o) 2 →
        PEqualNP.ReadK.IsReadK n (rotated n pre' x a b' post' o') 2) := by
  have hgate : ∀ i ∈ (⟨GateOp.or, [x, a]⟩ : Gate).inputs, i < n + pre.length := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  obtain ⟨pre', post', b', o', hlen, hAO, hs, hb', ho', hp', hvals, hvalb⟩ :=
    bubble_private n pre ⟨.or, [x, a]⟩ mid b post o hgate hb hbne ho hprivate hC
  have hx' : x < n + pre'.length := by omega
  have ha' : a < n + pre'.length := by omega
  let C' := shape n pre' ⟨.or, [x, a]⟩ [] b' post' o'
  have hdom' (z : Fin n → Bool) :
      (Rotation.run pre' (List.ofFn z)).getD x false = true →
        (Rotation.run pre' (List.ofFn z)).getD b' false = true := by
    have hpx : circuitFun n ⟨C'.gates, x⟩ z = (Rotation.run pre' (List.ofFn z)).getD x false := by
      simpa [C', shape, List.append_assoc, List.cons_append, List.nil_append] using
        prefix_value n pre' (⟨.or, [x, a]⟩ :: ⟨.and, [n + pre'.length, b']⟩ :: post') x hx' z
    have hpb : circuitFun n ⟨C'.gates, b'⟩ z = (Rotation.run pre' (List.ofFn z)).getD b' false := by
      simpa [C', shape, List.append_assoc, List.cons_append, List.nil_append] using
        prefix_value n pre' (⟨.or, [x, a]⟩ :: ⟨.and, [n + pre'.length, b']⟩ :: post') b' hb' z
    intro hz
    rw [← hpb]
    rw [hvalb]
    apply hdom z
    rw [← hvals x hx]
    exact hpx.trans hz
  have hAO' : PEqualNP.TopForm.IsAO2 n
      ⟨pre' ++ [⟨.or, [x, a]⟩, ⟨.and, [n + pre'.length, b']⟩] ++ post', o'⟩ := by
    simpa [shape, List.append_assoc] using hAO
  have hdAO : PEqualNP.TopForm.IsAO2 n (rotated n pre' x a b' post' o') :=
    Rotation.adjacent_ao2 n pre' post' x a b' o' hx' ha' hb' hAO'
  have hsize : (rotated n pre' x a b' post' o').size =
      (shape n pre ⟨.or, [x, a]⟩ mid b post o).size := by
    have hr := Rotation.adjacent_size n pre' post' x a b' o'
    have hr' : (rotated n pre' x a b' post' o').size = C'.size := by
      simpa [C', shape, rotated, List.append_assoc] using hr.symm
    exact hr'.trans hs.2.1
  have hfun : circuitFun n (rotated n pre' x a b' post' o') =
      circuitFun n (shape n pre ⟨.or, [x, a]⟩ mid b post o) := by
    have hr := Rotation.adjacent_semantics n pre' post' x a b' o' hx' ha' hb' ho' hp' hdom'
    have hr' : circuitFun n (rotated n pre' x a b' post' o') = circuitFun n C' := by
      simpa [C', shape, rotated, List.append_assoc] using hr.symm
    exact hr'.trans hs.1
  have hreads (S : List ℕ)
      (hr : PEqualNP.ReadK.readsAtMost (shape n pre ⟨.or, [x, a]⟩ mid b post o) n S 2 = true) :
      PEqualNP.ReadK.readsAtMost (rotated n pre' x a b' post' o') n S 2 = true := by
    apply Rotation.adjacent_preserves_reads_two n pre' post' x a b' o' hx' ha' hb' ho' hp' hAO'
    simpa [shape, List.append_assoc] using (hs.2.2 S 2).trans hr
  refine ⟨pre', post', b', o', hlen, hdAO, hsize, hfun, hreads, ?_⟩
  intro hr S hS
  apply hreads (PEqualNP.ReadK.setList S)
  exact hr S (by simpa only [PEqualNP.ReadK.IsPrimeImplicant, hfun] using hS)

end Reorder

namespace DirtyOpposite

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

def blockCircuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [7, 3]⟩,
    ⟨.and, [8, 9]⟩, ⟨.or, [6, 0]⟩, ⟨.and, [5, 11]⟩,
    ⟨.or, [4, 12]⟩, ⟨.and, [10, 13]⟩], 14⟩

abbrev blockGraph : SimpleGraph (Fin 7) :=
  edgeGraph 7 [(0, 4), (0, 5), (1, 4), (1, 6), (2, 4), (3, 5), (3, 6)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma block_ao : PEqualNP.TopForm.IsAO2 7 blockCircuit := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma block_four_cycle_free : PEqualNP.TopForm.NoFourCycle blockGraph := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma block_bipartite : ∀ u v : Fin 7, blockGraph.Adj u v →
    (u.val < 4 ∧ 4 ≤ v.val) ∨ (v.val < 4 ∧ 4 ≤ u.val) := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma block_below : ∀ x : Fin 7 → Bool,
    circuitFun 7 blockCircuit x = true → graphFun blockGraph ∅ x = true := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma source_singletons : ∀ u : Fin 7,
    gateVal 7 blockCircuit 3 (pairInput u u) = true ↔ u = 0 ∨ u = 1 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma opposite_singletons : ∀ u : Fin 7,
    gateVal 7 blockCircuit 6 (pairInput u u) = true ↔ u = 4 := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma first_factor_unsound : ∃ x : Fin 7 → Bool,
    gateVal 7 blockCircuit 1 x = true ∧ gateVal 7 blockCircuit 6 x = true ∧
      graphFun blockGraph ∅ x = false := by
  exact ⟨fun i => decide (i = 2 ∨ i = 5 ∨ i = 6), by decide⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma second_factor_unsound : ∃ x : Fin 7 → Bool,
    gateVal 7 blockCircuit 2 x = true ∧ gateVal 7 blockCircuit 6 x = true ∧
      graphFun blockGraph ∅ x = false := by
  exact ⟨fun i => decide (i = 3 ∨ i = 4), by decide⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma all_gates_productive : ∀ j : Fin 8, ∃ u v : Fin 7,
    blockGraph.Adj u v ∧ gateVal 7 blockCircuit j.val (pairInput u v) = true := by decide

end DirtyOpposite

namespace TopNormalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

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

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_reader (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → ∃ r, r < C.gates.length ∧ i < r ∧ n + i ∈ (gateAt C r).inputs ∧
      (r = j ∨ InCone n C r j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have h' := h
    rw [inCone_iff] at h'
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h'
    · subst h3
      exact ⟨j, h0, hk, hin, Or.inl rfl⟩
    · obtain ⟨r, hr, hir, hrin, h4⟩ := ih k hk h3
      refine ⟨r, hr, hir, hrin, Or.inr ?_⟩
      rw [inCone_iff]
      refine ⟨h0, k, hk, hin, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C C' : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt C' k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma transfer (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool) (R : Bool → Bool → Prop)
    (hRrefl : ∀ a, R a a) (hRtrans : ∀ a b c, R a b → R b c → R a c)
    (hRand : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.and.eval (l.map f)) (GateOp.and.eval (l.map f')))
    (hRor : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.or.eval (l.map f)) (GateOp.or.eval (l.map f')))
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → R (wv n C x (n + r)) (wv n C x b)) →
      R (wv n C x w) (wv n C' x (tau n r b w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hR0
    by_cases h1 : w < n
    · have ht : tau n r b w = w := by unfold tau; rw [if_pos (by omega)]
      rw [ht, wv_input n C x w h1, wv_input n C' x w h1]
      exact hRrefl _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k = r
      · subst hk
        have ht : tau n k b (n + k) = b := by unfold tau; simp
        have htb : tau n k b b = b := by unfold tau; rw [if_pos hb]
        have h2 := ih b (by omega) (by omega) (fun h => absurd h (by omega))
        rw [htb] at h2
        rw [ht]
        exact hRtrans _ _ _ (hR0 le_rfl) h2
      · have hkm : k < C.gates.length := by omega
        obtain ⟨k', hk'1, hk'2, hk'3⟩ : ∃ k', tau n r b (n + k) = n + k' ∧ rho r k' = k ∧
            k' < C.gates.length - 1 := by
          by_cases hkr : k < r
          · refine ⟨k, ?_, ?_, by omega⟩
            · unfold tau; rw [if_pos (by omega)]
            · unfold rho; rw [if_pos hkr]
          · refine ⟨k - 1, ?_, ?_, by omega⟩
            · unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
            · unfold rho; rw [if_neg (by omega)]; omega
        have hg := hred k' hk'3
        rw [hk'2] at hg
        rw [hk'1, wv_rec n C x hC k hkm, wv_rec n C' x hC' k' (by omega), hg]
        simp only [List.map_map]
        have hin : ∀ w ∈ (gateAt C k).inputs,
            R (wv n C x w) ((wv n C' x ∘ tau n r b) w) := by
          intro w hw'
          have hlt := (hC k hkm).2 w hw'
          exact ih w hlt (by omega) (fun h => hR0 (by omega))
        rcases (hC k hkm).1 with hop | hop
        · rw [hop]; exact hRand _ _ _ hin
        · rw [hop]; exact hRor _ _ _ hin

lemma transfer_eq (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → wv n C x (n + r) = wv n C x b) →
      wv n C x w = wv n C' x (tau n r b w) := by
  refine transfer n C C' r b x (fun a b => a = b) (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2)
    ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h
    rw [List.map_congr_left h]
  · intro l f f' h
    rw [List.map_congr_left h]

lemma transfer_le (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length →
      (n + r ≤ w → (wv n C x (n + r) = true → wv n C x b = true)) →
      (wv n C x w = true → wv n C' x (tau n r b w) = true) := by
  refine transfer n C C' r b x (fun a b => a = true → b = true) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h hall
    simp only [GateOp.eval] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw (hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · intro l f f' h hany
    simp only [GateOp.eval] at hany ⊢
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨v, hv, hv2⟩ := hany
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨f' w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩


def gfun (n : ℕ) (C : Circuit) (r b : ℕ) (top : Gate) (k : ℕ) : Gate :=
  if k < C.gates.length - 1 then
    ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ else top

def V1 (n : ℕ) (C : Circuit) (r b : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (gfun n C r b ⟨GateOp.or, []⟩), tau n r b C.output⟩

def V2 (n : ℕ) (C : Circuit) (r b i : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (gfun n C r b ⟨GateOp.or, [tau n r b C.output, n + i]⟩),
    n + C.gates.length - 1⟩

lemma gateAt_range (m : ℕ) (g : ℕ → Gate) (out k : ℕ) (hk : k < m) :
    gateAt ⟨(List.range m).map g, out⟩ k = g k := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma V1_len (n : ℕ) (C : Circuit) (r b : ℕ) :
    (V1 n C r b).gates.length = C.gates.length - 1 := by simp [V1]

lemma V2_len (n : ℕ) (C : Circuit) (r b i : ℕ) :
    (V2 n C r b i).gates.length = C.gates.length := by simp [V2]

lemma V1_gate (n : ℕ) (C : Circuit) (r b k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V1 n C r b) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V1
  rw [gateAt_range _ _ _ _ hk]
  unfold gfun
  rw [if_pos hk]

lemma V2_gate (n : ℕ) (C : Circuit) (r b i k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V2 n C r b i) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_pos hk]

lemma V2_top (n : ℕ) (C : Circuit) (r b i : ℕ) (hm : 0 < C.gates.length) :
    gateAt (V2 n C r b i) (C.gates.length - 1) =
      ⟨GateOp.or, [tau n r b C.output, n + i]⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_neg (by omega)]

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma aob {n : ℕ} {C : Circuit} (h : AO2 n C) : AOB n C :=
  fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho; split_ifs <;> omega

lemma tau_lt (n r b w k : ℕ) (hb : b < n + r) (hw : w < n + rho r k) :
    tau n r b w < n + k := by
  unfold tau; unfold rho at hw; split_ifs at hw ⊢ <;> omega

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  unfold tau; rw [if_pos hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho; split_ifs <;> omega

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma V1_AO2 (n : ℕ) (C : Circuit) (r b : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) : AO2 n (V1 n C r b) := by
  intro k hk
  rw [V1_len] at hk
  rw [V1_gate n C r b k hk]
  obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk)
  refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  exact tau_lt n r b w0 k hb (h3 w0 hw0)

lemma V2_AO2 (n : ℕ) (C : Circuit) (r b i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) (hi : i < r) (hout : C.output < n + C.gates.length) :
    AO2 n (V2 n C r b i) := by
  intro k hk
  rw [V2_len] at hk
  by_cases hk1 : k < C.gates.length - 1
  · rw [V2_gate n C r b i k hk1]
    obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk1)
    refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact tau_lt n r b w0 k hb (h3 w0 hw0)
  · have hk2 : k = C.gates.length - 1 := by omega
    subst hk2
    rw [V2_top n C r b i (by omega)]
    refine ⟨Or.inr rfl, ⟨_, _, rfl⟩, ?_⟩
    intro w hw
    have hw' : w = tau n r b C.output ∨ w = n + i := by simpa using hw
    rcases hw' with rfl | rfl
    · unfold tau; split_ifs <;> omega
    · omega

lemma V1_red (n : ℕ) (C : Circuit) (r b : ℕ) : IsRedirect n C (V1 n C r b) r b :=
  fun k hk => V1_gate n C r b k hk

lemma V2_red (n : ℕ) (C : Circuit) (r b i : ℕ) : IsRedirect n C (V2 n C r b i) r b :=
  fun k hk => V2_gate n C r b i k hk

lemma V1_fun (n : ℕ) (C : Circuit) (r b : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hout : C.output < n + C.gates.length)
    (h1 : wv n C x b = true → wv n C x C.output = true)
    (h2 : wv n C x b = false → wv n C x (n + r) = false) :
    wv n (V1 n C r b) x (V1 n C r b).output = wv n C x C.output := by
  have hC' := V1_AO2 n C r b hC hr hb
  have hlen : C.gates.length - 1 ≤ (V1 n C r b).gates.length := by rw [V1_len]
  show wv n (V1 n C r b) x (tau n r b C.output) = wv n C x C.output
  cases hbv : wv n C x b with
  | true =>
    rw [h1 hbv]
    exact transfer_le n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ _ => hbv) (h1 hbv)
  | false =>
    exact (transfer_eq n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ => by rw [h2 hbv, hbv])).symm

lemma V2_low (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) :
    ∀ w, w < n + r → wv n (V2 n C r b i) x w = wv n C x w := by
  intro w hw
  have h := transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w (by omega) (fun h => absurd h (by omega))
  rw [tau_low n r b w hw] at h
  exact h.symm

lemma V2_same (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x b) :
    ∀ w, w < n + C.gates.length → wv n (V2 n C r b i) x (tau n r b w) = wv n C x w := by
  intro w hw
  exact (transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w hw (fun _ => h0)).symm

lemma V2_out (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbel : wv n C x (n + i) = true → wv n C x C.output = true)
    (h0 : wv n C x (n + i) = false → wv n C x (n + r) = wv n C x b) :
    wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output := by
  have hC' := V2_AO2 n C r b i hC hr hb hi hout
  have hm : 0 < C.gates.length := by omega
  have e : (V2 n C r b i).output = n + (C.gates.length - 1) := by
    show n + C.gates.length - 1 = _
    omega
  rw [e, wv_rec n _ x (aob hC') (C.gates.length - 1) (by rw [V2_len]; omega),
    V2_top n C r b i hm]
  have hi' := V2_low n C r b i x hC hr hb hi hout (n + i) (by omega)
  dsimp only
  rw [eval_or_pair, hi']
  cases hv : wv n C x (n + i) with
  | true => rw [hbel hv]; simp
  | false =>
    rw [V2_same n C r b i x hC hr hb hi hout (h0 hv) C.output hout]; simp

lemma V1_fun_top (n : ℕ) (D : Circuit) (r c i y : ℕ) (x : Fin n → Bool) (hD : AO2 n D)
    (hr : r < D.gates.length - 1) (hc : c < n + r) (hi : i < r)
    (hout : D.output = n + (D.gates.length - 1))
    (htop : gateAt D (D.gates.length - 1) = ⟨GateOp.or, [y, n + i]⟩)
    (h0 : wv n D x (n + i) = false → wv n D x (n + r) = wv n D x c) :
    wv n (V1 n D r c) x (V1 n D r c).output = wv n D x D.output := by
  have hr' : r < D.gates.length := by omega
  have hE := V1_AO2 n D r c hD hr' hc
  have hlen : D.gates.length - 1 ≤ (V1 n D r c).gates.length := by rw [V1_len]
  have hred := V1_red n D r c
  show wv n (V1 n D r c) x (tau n r c D.output) = wv n D x D.output
  cases hv : wv n D x (n + i) with
  | false =>
    exact (transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred D.output (by omega)
      (fun _ => h0 hv)).symm
  | true =>
    have e1 : wv n D x D.output = true := by
      rw [hout, wv_rec n D x (aob hD) _ (by omega), htop]
      dsimp only
      rw [eval_or_pair, hv]; simp
    have e2 : tau n r c D.output = n + (D.gates.length - 2) := by
      rw [hout]; unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
    have e3 : gateAt (V1 n D r c) (D.gates.length - 2) =
        ⟨GateOp.or, [tau n r c y, n + i]⟩ := by
      rw [V1_gate n D r c _ (by omega)]
      have hrho : rho r (D.gates.length - 2) = D.gates.length - 1 := by
        unfold rho; rw [if_neg (by omega)]; omega
      rw [hrho, htop]
      simp [tau_low n r c (n + i) (by omega)]
    have e4 : wv n (V1 n D r c) x (n + i) = true := by
      have h := transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred (n + i) (by omega)
        (fun h => absurd h (by omega))
      rw [tau_low n r c (n + i) (by omega)] at h
      rw [← h, hv]
    rw [e1, e2, wv_rec n _ x (aob hE) _ (by rw [V1_len]; omega), e3]
    dsimp only
    rw [eval_or_pair, e4]; simp

def Least (n : ℕ) (C : Circuit) : Prop :=
  AO2 n C ∧ ∀ D : Circuit, AO2 n D → (∀ x, wv n D x D.output = wv n C x C.output) →
    C.gates.length ≤ D.gates.length

lemma reader_or (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hL.1 r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x => V1_fun n C r (n + i) x hL.1 hr hir hout (hbel x) (key x)
  have hle := hL.2 _ (V1_AO2 n C r (n + i) hL.1 hr hir) hfun
  rw [V1_len] at hle
  omega

lemma reader_unique (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := reader_or n C hL hout i r1 hr1 hbel hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := reader_or n C hL hout i r2 hr2 hbel hin2
  have hir1 : i < r1 := by have := (hL.1 r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hL.1) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hL.1 hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x => V2_out n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (hbel x) (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hL.1 hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x)
  have hle := hL.2 _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
  rw [V1_len, hDlen] at hle
  omega

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma V2_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hc : c < n + r) (hcin : c ∈ (gateAt C r).inputs) (a' : ℕ) :
    ∀ b', b' < C.gates.length - 1 → InCone n (V2 n C r c i) a' b' →
      InCone n C (rho r a') (rho r b') := by
  intro b'
  induction b' using Nat.strong_induction_on with
  | _ b' ih =>
    intro hb' h
    rw [inCone_iff] at h
    obtain ⟨_, k', hk', hin, h3⟩ := h
    rw [V2_gate n C r c i b' hb'] at hin
    simp only [List.mem_map] at hin
    obtain ⟨w, hw, hwk⟩ := hin
    have hbm : rho r b' < C.gates.length := rho_lt r b' _ hr hb'
    have hwlt := (hC (rho r b') hbm).2.2 w hw
    have hrb : rho r b' ≤ b' + 1 := by unfold rho; split_ifs <;> omega
    have hrb2 : b' < r → rho r b' = b' := by intro h; unfold rho; rw [if_pos h]
    have hstep : InCone n C (rho r k') (rho r b') := by
      unfold tau at hwk
      by_cases h1 : w < n + r
      · rw [if_pos h1] at hwk
        have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
        rw [e, inCone_iff]
        refine ⟨hbm, k', by omega, ?_, Or.inl rfl⟩
        rw [← hwk]; exact hw
      · rw [if_neg h1] at hwk
        by_cases h2 : w = n + r
        · rw [if_pos h2] at hwk
          have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
          rw [e]
          have s1 : InCone n C k' r := by
            rw [inCone_iff]
            refine ⟨hr, k', by omega, ?_, Or.inl rfl⟩
            rw [← hwk]; exact hcin
          have s2 : InCone n C r (rho r b') := by
            rw [inCone_iff]
            refine ⟨hbm, r, by omega, ?_, Or.inl rfl⟩
            rw [← h2]; exact hw
          exact inCone_trans n C k' r s1 _ s2
        · rw [if_neg h2] at hwk
          have e : rho r k' = k' + 1 := by unfold rho; rw [if_neg (by omega)]
          rw [e, inCone_iff]
          refine ⟨hbm, k' + 1, by omega, ?_, Or.inl rfl⟩
          have e2 : n + (k' + 1) = w := by omega
          rw [e2]; exact hw
    rcases h3 with h3 | h3
    · rw [h3]; exact hstep
    · exact inCone_trans n C _ _ (ih k' hk' (by omega) h3) _ hstep

lemma V2_no_reader (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ k', k' < C.gates.length - 1 → n + i ∉ (gateAt (V2 n C r c i) k').inputs := by
  intro k' hk' hin
  rw [V2_gate n C r c i k' hk'] at hin
  simp only [List.mem_map] at hin
  obtain ⟨w, hw, hwk⟩ := hin
  have hbm : rho r k' < C.gates.length := rho_lt r k' _ hr hk'
  have hne : rho r k' ≠ r := by unfold rho; split_ifs <;> omega
  unfold tau at hwk
  by_cases h1 : w < n + r
  · rw [if_pos h1] at hwk
    rw [hwk] at hw
    exact hne (huniq _ hbm hw)
  · rw [if_neg h1] at hwk
    by_cases h2 : w = n + r
    · rw [if_pos h2] at hwk
      exact hci hwk
    · rw [if_neg h2] at hwk
      omega

lemma V2_no_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ j', j' < C.gates.length - 1 → ¬ InCone n (V2 n C r c i) i j' := by
  intro j' hj' h
  obtain ⟨r', _, _, hrin, h4⟩ := inCone_reader n _ i j' h
  have hr'j : r' ≤ j' := by
    rcases h4 with h4 | h4
    · omega
    · have := (inCone_lt n _ r' j' h4).1
      omega
  exact V2_no_reader n C r c i hr hi hci huniq r' (by omega) hrin


lemma rho_inj (r : ℕ) : Function.Injective (rho r) := by
  intro a b h
  unfold rho at h
  split_ifs at h <;> omega

lemma rho_ne (r k : ℕ) : rho r k ≠ r := by
  unfold rho; split_ifs <;> omega

lemma rho_surj (r k m : ℕ) (hr : r < m) (hk : k < m) (hne : k ≠ r) : ∃ k', k' < m - 1 ∧ rho r k' = k := by
  by_cases h : k < r
  · exact ⟨k, by omega, by unfold rho; rw [if_pos h]⟩
  · exact ⟨k - 1, by omega, by unfold rho; rw [if_neg (by omega)]; omega⟩

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma out_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : wv n C x C.output = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  unfold wv at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at h
  simp at h

lemma step3_core (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := reader_or n C hL hout i r hr hbel hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (reader_unique n C hL hout i k r h hr hbel hkin hrin).elim
    · exact h
    · exact (reader_unique n C hL hout i r k h hk hbel hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hL.1) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma least_of_same (n : ℕ) (C D : Circuit) (hL : Least n C) (hD : AO2 n D)
    (hfun : ∀ x, wv n D x D.output = wv n C x C.output)
    (hlen : D.gates.length = C.gates.length) : Least n D :=
  ⟨hD, fun E hE hEf => by rw [hlen]; exact hL.2 E hE (fun x => (hEf x).trans (hfun x))⟩

lemma V2_gateval (n : ℕ) (C : Circuit) (r c i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    wv n (V2 n C r c i) x (n + k') = wv n C x (n + rho r k') := by
  have h := V2_same n C r c i x hC hr hb hi hout h0 (n + rho r k')
    (by have := rho_lt r k' _ hr hk'; omega)
  rw [tau_rho] at h
  exact h

lemma V2_below (n : ℕ) (C : Circuit) (r c i : ℕ) (F : (Fin n → Bool) → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : c < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbelF : ∀ x, wv n C x (n + i) = true → F x = true)
    (h0 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c)
    (k' : ℕ) (hk' : k' < C.gates.length - 1) :
    (∀ x, wv n (V2 n C r c i) x (n + k') = true → F x = true) ↔
      (∀ x, wv n C x (n + rho r k') = true → F x = true) := by
  constructor
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv
  · intro h x hv
    cases hx : wv n C x (n + i) with
    | true => exact hbelF x hx
    | false =>
      apply h x
      rw [← V2_gateval n C r c i x hC hr hb hi hout (h0 x hx) k' hk']
      exact hv


lemma card_filter_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) [DecidablePred P]
    [DecidablePred Q]
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    ((Finset.range m).filter Q).card = ((Finset.range m).filter P).card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [Finset.mem_filter, Finset.mem_range] at hk' ⊢
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma card_pairs_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → ℕ → Prop)
    [DecidablePred (fun p : ℕ × ℕ => P p.1 p.2)] [DecidablePred (fun p : ℕ × ℕ => Q p.1 p.2)]
    (hQP : ∀ a' b', a' < m → b' < m → Q a' b' →
      a' < m - 1 ∧ b' < m - 1 ∧ P (rho r a') (rho r b'))
    (i j : ℕ) (hi : i < m) (hj : j < m) (hP : P i j)
    (hne : ∀ a' b', Q a' b' → ¬ (rho r a' = i ∧ rho r b' = j)) :
    ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => Q p.1 p.2)).card <
      ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => P p.1 p.2)).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (rho r p.1, rho r p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (rho_inj r h.1) (rho_inj r h.2)
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hP⟩
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨a', b'⟩, hab, heq⟩ := hmem
      rw [Finset.mem_filter] at hab
      simp only [Prod.mk.injEq] at heq
      exact hne a' b' hab.2 heq
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨h1, h2, h3⟩ := hQP a' b' hab.1.1 hab.1.2 hab.2
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨rho_lt r a' m hr h1, rho_lt r b' m hr h2⟩, h3⟩


lemma step3_struct (n : ℕ) (C : Circuit) (F : (Fin n → Bool) → Bool) (hL : Least n C)
    (hF : ∀ x, wv n C x C.output = F x) (hout : C.output < n + C.gates.length)
    (i j : ℕ) (hbel : ∀ x, wv n C x (n + i) = true → F x = true)
    (hcone : InCone n C i j) :
    ∃ (C' : Circuit) (r : ℕ), r < C.gates.length ∧ i < r ∧ Least n C' ∧
      (∀ x, wv n C' x C'.output = F x) ∧ C'.gates.length = C.gates.length ∧
      (∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op) ∧
      (gateAt C' (C.gates.length - 1)).op = GateOp.or ∧ (gateAt C r).op = GateOp.or ∧
      (∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true))) ∧
      (∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b')) ∧
      (∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j') := by
  have hbel' : ∀ x, wv n C x (n + i) = true → wv n C x C.output = true :=
    fun x h => by rw [hF]; exact hbel x h
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    step3_core n C hL hout i j hbel' hcone
  have hD := V2_AO2 n C r c i hL.1 hr hclt hir hout
  have hfun : ∀ x, wv n (V2 n C r c i) x (V2 n C r c i).output = wv n C x C.output :=
    fun x => V2_out n C r c i x hL.1 hr hclt hir hout (hbel' x) (h0 x)
  refine ⟨V2 n C r c i, r, hr, hir, least_of_same n C _ hL hD hfun (V2_len n C r c i),
    fun x => (hfun x).trans (hF x), V2_len n C r c i, ?_, ?_, hop, ?_, ?_, ?_⟩
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro k' hk'
    exact V2_below n C r c i F hL.1 hr hclt hir hout hbel h0 k' hk'
  · intro a' b' hb' h
    exact V2_cone n C r c i hL.1 hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq

lemma pairs_lt (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
      (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)]
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
      (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)] :
    ((Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)).card <
    ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card := by
  rw [hlen]
  have hjm := (inCone_lt n C i j hij)
  refine card_pairs_rho C.gates.length r hr
    (fun a b => (gateAt C a).op = GateOp.and ∧ (gateAt C b).op = GateOp.and ∧ InCone n C a b)
    (fun a b => (gateAt C' a).op = GateOp.and ∧ (gateAt C' b).op = GateOp.and ∧
      InCone n C' a b) ?_ i j (by omega) hjm.2 ⟨hi, hj, hij⟩ ?_
  · rintro a' b' _ hb' ⟨ha, hb, hab⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have ha' := (inCone_lt n C' a' b' hab).1
    have ha'' : a' < C.gates.length - 1 := by omega
    refine ⟨ha'', hb'', ?_, ?_, hcone a' b' hb'' hab⟩
    · rw [← hops a' ha'']; exact ha
    · rw [← hops b' hb'']; exact hb
  · rintro a' b' ⟨_, hb, hab⟩ ⟨h1, _⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have hb3 := (inCone_lt n C' a' b' hab).2
        have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have e : rho r i = i := by unfold rho; rw [if_pos hir]
    have e2 : a' = i := rho_inj r (h1.trans e.symm)
    rw [e2] at hab
    exact hno b' hb'' hab

lemma card_mem_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → Prop) (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < m ∧ P k) (hS' : ∀ k, k ∈ S' ↔ k < m ∧ Q k)
    (hPQ : ∀ k', k' < m - 1 → (Q k' ↔ P (rho r k'))) (hPr : ¬ P r) (hQ : ¬ Q (m - 1)) :
    S'.card = S.card := by
  apply Finset.card_bij (fun k' _ => rho r k')
  · intro k' hk'
    rw [hS'] at hk'
    rw [hS]
    have hlt : k' < m - 1 := by
      rcases Nat.lt_or_ge k' (m - 1) with h | h
      · exact h
      · have hk'' : k' = m - 1 := by omega
        rw [hk''] at hk'
        exact absurd hk'.2 hQ
    exact ⟨rho_lt r k' m hr hlt, (hPQ k' hlt).mp hk'.2⟩
  · intro a _ b _ h
    exact rho_inj r h
  · intro k hk
    rw [hS] at hk
    have hne : k ≠ r := fun h => hPr (h ▸ hk.2)
    obtain ⟨k', hk'1, hk'2⟩ := rho_surj r k m hr hk.1 hne
    refine ⟨k', ?_, hk'2⟩
    rw [hS']
    exact ⟨by omega, (hPQ k' hk'1).mpr (hk'2 ▸ hk.2)⟩

lemma junk_eq (n : ℕ) (C C' : Circuit) (F : (Fin n → Bool) → Bool) (r : ℕ)
    (hr : r < C.gates.length)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hopr : (gateAt C r).op = GateOp.or)
    (hbelow : ∀ k', k' < C.gates.length - 1 →
        ((∀ x, wv n C' x (n + k') = true → F x = true) ↔
          (∀ x, wv n C x (n + rho r k') = true → F x = true)))
    (S S' : Finset ℕ)
    (hS : ∀ k, k ∈ S ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → F x = true)
    (hS' : ∀ k, k ∈ S' ↔ k < C'.gates.length ∧ (gateAt C' k).op = GateOp.and ∧
      ¬ ∀ x, wv n C' x (n + k) = true → F x = true) :
    S'.card = S.card := by
  rw [hlen] at hS'
  apply card_mem_rho C.gates.length r hr _ _ S S' hS hS'
  · intro k' hk'
    rw [hops k' hk', hbelow k' hk']
  · rintro ⟨h, _⟩
    rw [hopr] at h
    exact absurd h (by simp)
  · rintro ⟨h, _⟩
    rw [htop] at h
    exact absurd h (by simp)


lemma gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj

lemma mem_gateAt (C : Circuit) (g : Gate) (hg : g ∈ C.gates) :
    ∃ j, j < C.gates.length ∧ gateAt C j = g := by
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  exact ⟨j, hj, by unfold gateAt; rw [List.getD_eq_getElem _ _ hj]⟩


lemma ao2_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO2 n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro j hj
  have hm := gateAt_mem C j hj
  exact ⟨h1 _ hm, List.length_eq_two.mp (h3 _ hm), h2 j hj⟩

lemma ao2_to (n : ℕ) (C : Circuit) (h : AO2 n C) : PEqualNP.TopForm.IsAO2 n C := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    exact (h j hj).1
  · intro j hj
    exact (h j hj).2.2
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := mem_gateAt C g hg
    obtain ⟨a, b, hab⟩ := (h j hj).2.1
    rw [hab]
    rfl

lemma least_glue (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : PEqualNP.TopForm.IsLeastAO G C) :
    Least n C ∧ ∀ x, wv n C x C.output = graphFun G ∅ x := by
  obtain ⟨h1, h2, h3⟩ := hL
  have hF : ∀ x, wv n C x C.output = graphFun G ∅ x := fun x => congrFun h2 x
  refine ⟨⟨ao2_of n C h1, ?_⟩, hF⟩
  intro D hD hDf
  exact h3 D (ao2_to n D hD) (funext fun x => (hDf x).trans (hF x))

lemma least_glue' (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : Least n C) (hF : ∀ x, wv n C x C.output = graphFun G ∅ x) :
    PEqualNP.TopForm.IsLeastAO G C := by
  refine ⟨ao2_to n C hL.1, funext hF, ?_⟩
  intro D hD hDf
  exact hL.2 D (ao2_of n D hD) (fun x => (congrFun hDf x).trans (hF x).symm)

lemma exists_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) : ∃ x : Fin n → Bool, graphFun G ∅ x = true := by
  refine ⟨fun _ => true, ?_⟩
  obtain ⟨e, he⟩ := hG
  rw [SimpleGraph.mem_edgeFinset] at he
  revert he
  refine Sym2.inductionOn e ?_
  intro u v he
  have hadj : G.Adj u v := he
  unfold graphFun
  have hd : decide (∃ u v, G.Adj u v ∧ (fun _ : Fin n => true) u = true ∧
      (fun _ : Fin n => true) v = true) = true := decide_eq_true ⟨u, v, hadj, rfl, rfl⟩
  rw [hd]
  simp

lemma mem_junk (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (k : ℕ) :
    k ∈ PEqualNP.TopForm.junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      ¬ ∀ x, wv n C x (n + k) = true → graphFun G ∅ x = true := by
  unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  unfold PEqualNP.CleanedNonEdge.IsDirtyAnd PEqualNP.CleanedNonEdge.IsDirty
  constructor
  · rintro ⟨h1, h2, _, x, hx1, hx2⟩
    refine ⟨h1, h2, fun h => ?_⟩
    have h3 := h x hx1
    rw [hx2] at h3
    exact absurd h3 (by simp)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, h1, ?_⟩
    by_contra hne
    apply h3
    intro x hx
    by_contra hF
    exact hne ⟨x, hx, by simpa using hF⟩

open Classical in
lemma main_ind (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) :
    ∀ k : ℕ, ∀ C : Circuit, PEqualNP.TopForm.IsLeastAO G C →
      ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
        (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
          (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card = k →
      ∃ C' : Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
        (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧
        PEqualNP.TopForm.TopForm G C' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hC hk
    by_cases htop : PEqualNP.TopForm.TopForm G C
    · exact ⟨C, hC, rfl, rfl, htop⟩
    · have hex : ∃ i j, i < C.gates.length ∧ j < C.gates.length ∧
          (gateAt C i).op = GateOp.and ∧ PEqualNP.TopForm.BelowF G C i ∧
          (gateAt C j).op = GateOp.and ∧ InCone n C i j := by
        by_contra hne
        apply htop
        intro i hi j hj h1 h2 h3 h4
        exact hne ⟨i, j, hi, hj, h1, h2, h3, h4⟩
      obtain ⟨i, j, hi, hj, hopi, hbi, hopj, hcone⟩ := hex
      obtain ⟨hL, hF⟩ := least_glue n G C hC
      obtain ⟨x1, hx1⟩ := exists_true n G hG
      have hout : C.output < n + C.gates.length := out_lt n C x1 (by rw [hF]; exact hx1)
      obtain ⟨C', r, hr, hir, hL', hF', hlen, hops, htop', hopr, hbelow, hcn, hno⟩ :=
        step3_struct n C (graphFun G ∅) hL hF hout i j hbi hcone
      have hlt := pairs_lt n C C' r i j hr hir hlen hops htop' hcn hno hopi hopj hcone
      rw [hk] at hlt
      obtain ⟨C'', h1, h2, h3, h4⟩ := ih _ hlt C' (least_glue' n G C' hL' hF') rfl
      refine ⟨C'', h1, h2.trans hlen, h3.trans ?_, h4⟩
      refine junk_eq n C C' (graphFun G ∅) r hr hlen hops htop' hopr hbelow _ _ ?_ ?_
      · intro k
        exact mem_junk n G C k
      · intro k
        exact mem_junk n G C' k

lemma least_to_topForm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
      (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧ PEqualNP.TopForm.TopForm G C' := by
  intro n G _ C hG hC
  exact PEqualNP.Outside.L_meta_2584.TopNormalize.main_ind n G hG _ C hC rfl


lemma exists_least_topForm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hf : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (hne : G.edgeFinset.Nonempty) :
    ∃ D : Circuit, PEqualNP.TopForm.IsLeastAO G D ∧ D.size ≤ C.size ∧
      PEqualNP.TopForm.TopForm G D := by
  obtain ⟨E, hE, hEf, hsize, hmin⟩ :=
    PEqualNP.Outside.L_meta_2584.exists_least_circuit n (graphFun G ∅) C hAO hf
  obtain ⟨D, hD, hDS, hDJ, hDT⟩ := least_to_topForm n G E hne ⟨hE, hEf, hmin⟩
  exact ⟨D, hD, hDS.le.trans hsize, hDT⟩

lemma least_one_dirty_replacement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hne : G.edgeFinset.Nonempty) (hC : PEqualNP.TopForm.IsLeastAO G C)
    (hjunk : (PEqualNP.TopForm.junk G C).card ≤ 1) :
    ∃ D : Circuit, PEqualNP.TopForm.IsLeastAO G D ∧ D.size = C.size ∧
      PEqualNP.ReadK.IsReadK n D 2 := by
  obtain ⟨D, hD, hsize, hcard, htop⟩ := least_to_topForm n G C hne hC
  exact ⟨D, hD, hsize,
    PEqualNP.Outside.L_meta_2584.FlatRead.at_most_one_junk_isReadTwo G hD.1 htop
      (hcard.le.trans hjunk) hD.2.1⟩

end TopNormalize

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

lemma val_true_or_frontier {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (x : Fin n → Bool) (w : ℕ) (hv : val C (List.ofFn x) w = true) :
    (∃ u ∈ orIn n C w, x u = true) ∨
      ∃ g < C.gates.length, (gateAt C g).op = GateOp.and ∧
        OrReaches n C w g ∧ gateVal n C g x = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · left
      refine ⟨⟨w, hn⟩, ?_, ?_⟩
      · exact reach_mem_orIn _ Relation.ReflTransGen.refl
      · simpa only [val_ofFn C x ⟨w, hn⟩] using hv
    by_cases hw : w < n + C.gates.length
    · obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
      have hg : g < C.gates.length := by omega
      rcases hAO.1 _ (gateAt_mem hg) with hand | hor
      · exact Or.inr ⟨g, hg, hand, (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩, hv⟩
      · obtain ⟨v, hvin, hvlt, hvtrue⟩ := (val_or (by simp) hg hor).mp hv
        rcases ih v hvlt hvtrue with ⟨u, hu, hxu⟩ | ⟨k, hk, hkand, hkr, hkval⟩
        · left
          refine ⟨u, ?_, hxu⟩
          exact reach_mem_orIn u (Relation.ReflTransGen.head
            ⟨g, hg, rfl, hor, hvin, hvlt⟩ (mem_orIn_reach u hu))
        · exact Or.inr ⟨k, hk, hkand,
            (orReaches_iff n C g k).mpr ⟨hg, Or.inr ⟨hor, v, hvin, hvlt, hkr⟩⟩, hkval⟩
    · rw [val_ge (n := n) (by simp) (by omega)] at hv
      cases hv

lemma top_pair_through_dirty_centres {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (hfour : NoFourCycle G) (g h : ℕ)
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = h)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hrh : OrReaches n C (opnd C a b) h)
    (u v x y : Fin n) (hv : v ∈ singletonInputs n C (n + h))
    (hxy : G.Adj x y) (huy : G.Adj u y) (huv : G.Adj u v)
    (hyv : ¬ G.Adj y v)
    (hgh : gateVal n C g (pairInput x y) = true → x = u ∨ y = v)
    (hopposite : val C (List.ofFn (pairInput x y)) (opnd C a b.rev) = true) :
    x = u ∨ y = v := by
  have ha' := ha
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha'
  obtain ⟨halen, hand, hab⟩ := ha'
  have hvside := singletonInputs_subset_of_orReaches hrh hv
  rcases val_true_or_frontier hAO (pairInput x y) (opnd C a b.rev) hopposite with
    ⟨z, hz, hxyz⟩ | ⟨k, hk, hkand, hkr, hkval⟩
  · have hzside := orIn_subset_singletonInputs hz
    have hzv : G.Adj z v :=
      (singleton_opposite_adj G C hAO a ha b hvside hzside).symm
    rcases (pairInput_true x y z).mp hxyz with hzx | hzy
    · subst z
      by_cases hxu : x = u
      · exact Or.inl hxu
      · right
        exact Finset.card_le_one.mp (hfour x u hxu) y
          (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hxy, huy⟩)
          v (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hzv, huv⟩)
    · subst z
      exact False.elim (hyv hzv)
  · have hkdirty : ¬ BelowF G C k := by
      intro hkbelow
      exact hTop k hk a halen hkand hkbelow hand (orReaches_operand_inCone hAO halen b.rev hkr)
    rcases honly k hk hkand hkdirty with rfl | rfl
    · exact hgh hkval
    · have hvopp := singletonInputs_subset_of_orReaches hkr hv
      exact False.elim (G.irrefl (singleton_opposite_adj G C hAO a ha b hvside hvopp))

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ}
    (hij : InCone n C i j) (hjk : InCone n C j k) : InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    obtain ⟨hk, a, ha, hain, hja⟩ := (FlatRead.inCone_iff n C j k).mp hjk
    apply (FlatRead.inCone_iff n C i k).mpr
    refine ⟨hk, a, ha, hain, Or.inr ?_⟩
    rcases hja with rfl | hja
    · exact hij
    · exact ih a ha hja

lemma cone_or_frontier_of_no_and_middle {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {i a : ℕ} (hia : InCone n C i a)
    (hmid : ∀ k, InCone n C i k → InCone n C k a → (gateAt C k).op = GateOp.or) :
    ∃ b : Fin 2, OrReaches n C (opnd C a b) i := by
  have haux : ∀ k, InCone n C k a → (i = k ∨ InCone n C i k) →
      OrReaches n C (n + k) i := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hka hik
      have hkl : k < C.gates.length :=
        (inCone_index_lt hka).trans ((FlatRead.inCone_iff n C k a).mp hka).1
      apply (orReaches_iff n C k i).mpr
      refine ⟨hkl, ?_⟩
      rcases hik with he | hik
      · exact Or.inl he
      · right
        have hop := hmid k hik hka
        obtain ⟨_, j, hj, hjin, hij⟩ := (FlatRead.inCone_iff n C i k).mp hik
        have hjk : InCone n C j k :=
          (FlatRead.inCone_iff n C j k).mpr ⟨hkl, j, hj, hjin, Or.inl rfl⟩
        exact ⟨hop, n + j, hjin, by omega, ih j hj (inCone_trans hjk hka) hij⟩
  obtain ⟨ha, k, hka, hkin, hik⟩ := (FlatRead.inCone_iff n C i a).mp hia
  have hkcone : InCone n C k a :=
    (FlatRead.inCone_iff n C k a).mpr ⟨ha, k, hka, hkin, Or.inl rfl⟩
  have hr := haux k hkcone hik
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
  rw [hin] at hkin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hkin
  rcases hkin with he | he
  · exact ⟨0, by simpa [opnd, hin, ← he] using hr⟩
  · exact ⟨1, by simpa [opnd, hin, ← he] using hr⟩

lemma two_dirty_cone_or_frontier {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h : ℕ)
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = h)
    (hhg : ¬ InCone n C h g)
    {a : ℕ} (ha : a < C.gates.length) (haand : (gateAt C a).op = GateOp.and)
    (hha : InCone n C h a) : ∃ b : Fin 2, OrReaches n C (opnd C a b) h := by
  apply cone_or_frontier_of_no_and_middle hAO hha
  intro k hhk hka
  have hk := (inCone_index_lt hka).trans ha
  rcases hAO.1 _ (gateAt_mem hk) with hkand | hkor
  · have hkdirty : ¬ BelowF G C k := by
      intro hkbelow
      exact hTop k hk a ha hkand hkbelow haand hka
    rcases honly k hk hkand hkdirty with he | he
    · subst k
      exact False.elim (hhg hhk)
    · subst k
      have := inCone_index_lt hhk
      omega
  · exact hkor

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

lemma forcedCircuit_val_eq_of_no_ancestor {n : ℕ} (C : Circuit) (j : ℕ)
    (x : Fin n → Bool) (w : ℕ)
    (hnot : ¬(w = n + j ∨ ∃ k < C.gates.length, w = n + k ∧ InCone n C j k)) :
    val (forcedCircuit C j) (List.ofFn x) w = val C (List.ofFn x) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · rw [val_input (n := n) (by simp) hn, val_input (n := n) (by simp) hn]
    by_cases hw : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hk' : k < (forcedCircuit C j).gates.length := by simpa only [forcedCircuit_length] using hk
      have hjk : j ≠ k := by intro he; subst k; exact hnot (Or.inl rfl)
      rw [val_gate (n := n) (by simp) hk', val_gate (n := n) (by simp) hk,
        forcedCircuit_gateAt_other C j k hjk]
      congr 1
      apply List.map_congr_left
      intro i hin
      by_cases hi : i < n + k
      · rw [ite_eq_left hi, ite_eq_left hi]
        apply ih i hi
        intro hic
        apply hnot
        right
        refine ⟨k, hk, rfl, ?_⟩
        apply (FlatRead.inCone_iff n C j k).mpr
        rcases hic with he | ⟨l, hl, he, hjl⟩
        · exact ⟨hk, j, by omega, by simpa only [he] using hin, Or.inl rfl⟩
        · exact ⟨hk, l, by omega, by simpa only [he] using hin, Or.inr hjl⟩
      · rw [ite_eq_right hi, ite_eq_right hi]
    · rw [val_ge (n := n) (by simp) (by rw [forcedCircuit_length]; omega),
        val_ge (n := n) (by simp) (by omega)]

lemma forcedCircuit_orStep_of_and {n : ℕ} (C : Circuit) {j u v : ℕ}
    (hjand : (gateAt C j).op = GateOp.and) (hs : OrStep n C u v) :
    OrStep n (forcedCircuit C j) u v := by
  obtain ⟨k, hk, rfl, hkor, hvin, hvlt⟩ := hs
  have hjk : j ≠ k := by
    intro he
    subst k
    rw [hjand] at hkor
    cases hkor
  refine ⟨k, by simpa only [forcedCircuit_length] using hk, rfl, ?_, ?_, hvlt⟩
  · simpa only [forcedCircuit_gateAt_other C j k hjk] using hkor
  · simpa only [forcedCircuit_gateAt_other C j k hjk] using hvin

lemma forcedCircuit_orReach_of_and {n : ℕ} (C : Circuit) {j u v : ℕ}
    (hjand : (gateAt C j).op = GateOp.and)
    (hr : Relation.ReflTransGen (OrStep n C) u v) :
    Relation.ReflTransGen (OrStep n (forcedCircuit C j)) u v := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hs hr ih => exact Relation.ReflTransGen.head (forcedCircuit_orStep_of_and C hjand hs) ih

lemma forcedCircuit_true_of_top_avoid {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C)
    (hf : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (j : ℕ) (hjand : (gateAt C j).op = GateOp.and) (x : Fin n → Bool)
    (havoid : ∀ a ∈ tops G C, OrReaches n C C.output a → gateVal n C a x = true →
      a ≠ j ∧ ¬ InCone n C j a)
    (hx : PEqualNP.MetaComplexity.circuitFun n C x = true) :
    PEqualNP.MetaComplexity.circuitFun n (forcedCircuit C j) x = true := by
  rcases val_true_or_frontier hAO x C.output hx with ⟨u, hu, _⟩ | ⟨a, ha, haand, har, hav⟩
  · rw [output_orIn_empty G C hf] at hu
    exact False.elim (Finset.notMem_empty u hu)
  · have hatop : a ∈ tops G C := by
      simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
      refine ⟨ha, haand, ?_⟩
      intro z hz
      have hout := orStep_up (by simp) (orReaches_reach a C.output har).1 hz
      change PEqualNP.MetaComplexity.circuitFun n C z = true at hout
      simpa only [hf] using hout
    obtain ⟨haj, hja⟩ := havoid a hatop har hav
    have heq := forcedCircuit_val_eq_of_no_ancestor C j x (n + a) (by
      rintro (he | ⟨k, hk, he, hjk⟩)
      · exact haj (by omega)
      · have hek : k = a := by omega
        subst k
        exact hja hjk)
    have hav' : val (forcedCircuit C j) (List.ofFn x) (n + a) = true := heq.trans hav
    exact orStep_up (by simp)
      (forcedCircuit_orReach_of_and C hjand (orReaches_reach a C.output har).1) hav'

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

lemma and_operand_value {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a : ℕ} (ha : a < C.gates.length) (haand : (gateAt C a).op = GateOp.and)
    (x : Fin n → Bool) (hav : gateVal n C a x = true) (b : Fin 2) :
    val C (List.ofFn x) (opnd C a b) = true := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
  have hmem : opnd C a b ∈ (gateAt C a).inputs := by
    fin_cases b <;> simp [opnd, hin]
  exact ((val_and (by simp) ha haand).mp hav (opnd C a b) hmem).2

lemma two_dirty_forced_pair_away_centres {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (hf : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G) (g h : ℕ) (hhand : (gateAt C h).op = GateOp.and)
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = h)
    (hhg : ¬ InCone n C h g)
    (u v x y : Fin n) (hv : v ∈ singletonInputs n C (n + h))
    (hxy : G.Adj x y) (huy : G.Adj u y) (huv : G.Adj u v)
    (hyv : ¬ G.Adj y v)
    (hgh : gateVal n C g (pairInput x y) = true → x = u ∨ y = v)
    (hxu : x ≠ u) (hyvne : y ≠ v) :
    PEqualNP.MetaComplexity.circuitFun n (forcedCircuit C h) (pairInput x y) = true := by
  apply forcedCircuit_true_of_top_avoid G C hAO hf h hhand (pairInput x y)
  · intro a ha har hav
    have ha' := ha
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha'
    obtain ⟨halen, haand, habelow⟩ := ha'
    constructor
    · intro he
      subst a
      have hvsingle := hv
      simp only [singletonInputs, Finset.mem_filter, Finset.mem_univ, true_and] at hvsingle
      exact G.irrefl ((graphFun_pair G v v).mp (habelow (pairInput v v) hvsingle))
    · intro hha
      obtain ⟨b, hrh⟩ := two_dirty_cone_or_frontier G C hAO hTop g h honly hhg halen haand hha
      have hopposite := and_operand_value hAO halen haand (pairInput x y) hav b.rev
      rcases top_pair_through_dirty_centres G C hAO hTop hfour g h honly ha b hrh
          u v x y hv hxy huy huv hyv hgh hopposite with he | he
      · exact hxu he
      · exact hyvne he
  · rw [hf]
    exact (graphFun_pair G x y).mpr hxy

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

lemma pure_or_star_sound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} {d : ℕ} (u : Fin n)
    (hpure : ∀ g, OrReaches n C d g → (gateAt C g).op = GateOp.or)
    (hneigh : ∀ v ∈ orIn n C d, G.Adj u v)
    (x : Fin n → Bool) (hu : x u = true) (hd : val C (List.ofFn x) d = true) :
    graphFun G ∅ x = true := by
  obtain ⟨v, hv, hxv⟩ := (pure_or_value_iff hpure x).mp hd
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  exact ⟨u, v, hneigh v hv, hu, hxv⟩

lemma pure_or_pair_neighbor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} {d : ℕ} (u x y : Fin n)
    (hpure : ∀ g, OrReaches n C d g → (gateAt C g).op = GateOp.or)
    (hneigh : ∀ v ∈ orIn n C d, G.Adj u v)
    (hxnot : x ∉ orIn n C d)
    (hd : val C (List.ofFn (pairInput x y)) d = true) : G.Adj u y := by
  obtain ⟨v, hv, hxv⟩ := (pure_or_value_iff hpure (pairInput x y)).mp hd
  rcases (pairInput_true x y v).mp hxv with he | he
  · subst v
    exact False.elim (hxnot hv)
  · subst v
    exact hneigh y hv

lemma and_pure_or_pair_neighbor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {h c d : ℕ}
    (hh : h < C.gates.length) (hhand : (gateAt C h).op = GateOp.and)
    (hinputs : (gateAt C h).inputs = [c, d]) (u x y : Fin n)
    (hpure : ∀ g, OrReaches n C d g → (gateAt C g).op = GateOp.or)
    (hneigh : ∀ v ∈ orIn n C d, G.Adj u v)
    (hxnot : x ∉ orIn n C d)
    (hv : gateVal n C h (pairInput x y) = true) : G.Adj u y := by
  apply pure_or_pair_neighbor G u x y hpure hneigh hxnot
  have hd := and_operand_value hAO hh hhand (pairInput x y) hv 1
  simpa [opnd, hinputs] using hd

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

lemma singleton_input_value {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {w : ℕ} {u : Fin n} (hu : u ∈ singletonInputs n C w)
    (x : Fin n → Bool) (hx : x u = true) : val C (List.ofFn x) w = true := by
  simp only [singletonInputs, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  apply val_monotone hAO.1 (pairInput u u) x ?_ w hu
  intro v hv
  have hvu : v = u := by simpa only [pairInput, decide_eq_true_eq, or_self] using hv
  subst v
  exact hx

lemma two_dirty_alias_or_star_pair {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (hf : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (hfour : NoFourCycle G) (g h c d : ℕ) (hh : h < C.gates.length)
    (hhand : (gateAt C h).op = GateOp.and) (hinputs : (gateAt C h).inputs = [c, d])
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = h)
    (hhg : ¬ InCone n C h g)
    (u v x y : Fin n) (hv : v ∈ singletonInputs n C (n + h))
    (hxy : G.Adj x y) (huv : G.Adj u v) (hyv : ¬ G.Adj y v)
    (hpure : ∀ k, OrReaches n C d k → (gateAt C k).op = GateOp.or)
    (hneigh : ∀ z ∈ orIn n C d, G.Adj u z) (hxnot : x ∉ orIn n C d)
    (hgh : gateVal n C h (pairInput x y) = true →
      gateVal n C g (pairInput x y) = true → x = u ∨ y = v)
    (f : (Fin n → Bool) → Bool)
    (heq : ∀ z, gateVal n C h z = z v → f z = PEqualNP.MetaComplexity.circuitFun n C z)
    (hforced : ∀ z, PEqualNP.MetaComplexity.circuitFun n (forcedCircuit C h) z = true → f z = true) :
    f (pairInput x y) = true ∨
      (pairInput x y u = true ∧ val C (List.ofFn (pairInput x y)) d = true) := by
  have hctrue : PEqualNP.MetaComplexity.circuitFun n C (pairInput x y) = true := by
    rw [hf]
    exact (graphFun_pair G x y).mpr hxy
  by_cases hhval : gateVal n C h (pairInput x y) = true
  · have hdval := and_operand_value hAO hh hhand (pairInput x y) hhval 1
    have hd : val C (List.ofFn (pairInput x y)) d = true := by simpa [opnd, hinputs] using hdval
    by_cases hxu : x = u
    · right
      refine ⟨?_, hd⟩
      subst x
      exact pairInput_left u y
    by_cases hyvne : y = v
    · left
      have hveq : gateVal n C h (pairInput x y) = pairInput x y v := by
        rw [hhval]
        subst y
        exact (pairInput_right x v).symm
      exact (heq _ hveq).trans hctrue
    · left
      apply hforced
      exact two_dirty_forced_pair_away_centres G C hAO hTop hf hfour g h hhand honly hhg
        u v x y hv hxy (pure_or_pair_neighbor G u x y hpure hneigh hxnot hd)
        huv hyv (hgh hhval) hxu hyvne
  · left
    have hfalse : gateVal n C h (pairInput x y) = false := Bool.eq_false_iff.mpr hhval
    have hvfalse : pairInput x y v = false := by
      apply Bool.eq_false_iff.mpr
      intro hvtrue
      exact hhval (singleton_input_value hAO hv (pairInput x y) hvtrue)
    exact (heq _ (hfalse.trans hvfalse.symm)).trans hctrue

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

lemma val_all_true {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (w : ℕ) (hw : w < n + C.gates.length) :
    val C (List.ofFn (fun _ : Fin n => true)) w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · exact val_ofFn C _ ⟨w, hn⟩
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    rcases hAO.1 _ (gateAt_mem hj) with hand | hor
    · apply (val_and (by simp) hj hand).mpr
      intro p hp
      have hplt := hAO.2.1 j hj p hp
      exact ⟨hplt, ih p hplt (by omega)⟩
    · obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hj))
      have hpin : p ∈ (gateAt C j).inputs := by rw [hin]; simp
      have hplt := hAO.2.1 j hj p hpin
      exact (val_or (by simp) hj hor).mpr ⟨p, hpin, hplt, ih p hplt (by omega)⟩

lemma empty_top_operand_eq_other_dirty {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h : ℕ)
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = h)
    (hg : (singletonInputs n C (n + g)).Nonempty)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    (hempty : singletonInputs n C (opnd C a b) = ∅) :
    OrReaches n C (opnd C a b) h ∧
      ∀ x : Fin n → Bool, val C (List.ofFn x) (opnd C a b) = gateVal n C h x := by
  have ha' := ha
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha'
  obtain ⟨halen, hand, hab⟩ := ha'
  have hfront (x : Fin n → Bool) (hv : val C (List.ofFn x) (opnd C a b) = true) :
      OrReaches n C (opnd C a b) h ∧ gateVal n C h x = true := by
    rcases val_true_or_frontier hAO x (opnd C a b) hv with
      ⟨u, hu, hxu⟩ | ⟨k, hk, hkand, hkr, hkval⟩
    · have hm := orIn_subset_singletonInputs hu
      rw [hempty] at hm
      exact False.elim (by simpa using hm)
    · have hkdirty : ¬ BelowF G C k := by
        intro hkbelow
        exact hTop k hk a halen hkand hkbelow hand
          (orReaches_operand_inCone hAO halen b hkr)
      rcases honly k hk hkand hkdirty with rfl | rfl
      · obtain ⟨u, hu⟩ := hg
        have hm := singletonInputs_subset_of_orReaches hkr hu
        rw [hempty] at hm
        exact False.elim (by simpa using hm)
      · exact ⟨hkr, hkval⟩
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem halen))
  have hmem : opnd C a b ∈ (gateAt C a).inputs := by
    fin_cases b <;> simp [opnd, hin]
  have hlt := hAO.2.1 a halen (opnd C a b) hmem
  have hr := (hfront (fun _ => true) (val_all_true hAO _ (by omega))).1
  refine ⟨hr, ?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact fun hv => (hfront x hv).2
  · intro hv
    exact orStep_up (by simp) (orReaches_reach h _ hr).1 hv

lemma mixed_region_not_top_of_shared_false_input {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h c : ℕ)
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = h)
    (hg : (singletonInputs n C (n + g)).Nonempty)
    (x : Fin n → Bool) (hhx : gateVal n C h x = true) (hcx : gateVal n C c x = true)
    (hfalse : graphFun G ∅ x = false)
    {u v : Fin n} (hu : u ∈ singletonInputs n C (n + c))
    (hv : v ∈ singletonInputs n C (n + c))
    (hnone : ∀ w, ¬(G.Adj u w ∧ G.Adj v w))
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2) :
    ¬ OrReaches n C (opnd C a b) c := by
  intro hr
  have hempty := shared_region_opposite_empty_of_no_common_neighbor G C hAO ha b hr hu hv hnone
  have heq := (empty_top_operand_eq_other_dirty G C hAO hTop g h honly hg ha b.rev hempty).2
  have ha' := ha
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha'
  obtain ⟨halen, hand, hab⟩ := ha'
  have hvb : val C (List.ofFn x) (opnd C a b) = true :=
    orStep_up (by simp) (orReaches_reach c _ hr).1 hcx
  have hvrev : val C (List.ofFn x) (opnd C a b.rev) = true := by rw [heq]; exact hhx
  have hval (d : Fin 2) : val C (List.ofFn x) (opnd C a d) = true := by
    fin_cases b <;> fin_cases d <;> simp_all
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem halen))
  have htop : gateVal n C a x = true := by
    rw [gateVal_eq_val, val_and (by simp) halen hand]
    intro w hw
    refine ⟨hAO.2.1 a halen w hw, ?_⟩
    rw [hin] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · simpa [opnd, hin] using hval 0
    · simpa [opnd, hin] using hval 1
  have hyes := hab x htop
  rw [hfalse] at hyes
  cases hyes


lemma mixed_dominated_region_not_top_operand {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (g h c : ℕ)
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = h)
    (hg : (singletonInputs n C (n + g)).Nonempty) (hhdirty : ¬ BelowF G C h)
    (hdom : ∀ x : Fin n → Bool, gateVal n C h x = true → gateVal n C c x = true)
    {u v : Fin n} (hu : u ∈ singletonInputs n C (n + c))
    (hv : v ∈ singletonInputs n C (n + c))
    (hnone : ∀ w, ¬(G.Adj u w ∧ G.Adj v w))
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2) :
    ¬ OrReaches n C (opnd C a b) c := by
  intro hr
  apply hhdirty
  intro x hhx
  cases hF : graphFun G ∅ x with
  | true => rfl
  | false =>
    exact False.elim (mixed_region_not_top_of_shared_false_input G C hAO hTop g h c honly hg
      x hhx (hdom x hhx) hF hu hv hnone ha b hr)

end Sharing

namespace AliasSurgery
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_2584.GuardedErase PEqualNP.Outside.L_meta_2584.ChoiceErase
open PEqualNP.Outside.L_meta_2584.AliasErase

def aliasCircuit (n : ℕ) (pre post : List Gate) (a o : ℕ) : Circuit :=
  ⟨pre ++ post.map (Tc (n + pre.length) a), rn (n + pre.length) a o⟩

lemma alias_spec (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate) (a : ℕ)
    (hC : C.gates = pre ++ g :: post)
    (hao : PEqualNP.TopForm.IsAO2 n C) (ha : a < n + pre.length)
    (hle : ∀ x : Fin n → Bool, (wf pre (List.ofFn x)).getD a false = true →
      g.op.eval (g.inputs.map fun i => (wf pre (List.ofFn x)).getD i false) = true) :
    PEqualNP.TopForm.IsAO2 n (aliasCircuit n pre post a C.output) ∧
      (aliasCircuit n pre post a C.output).size + 1 = C.size ∧
      (∀ x, circuitFun n (aliasCircuit n pre post a C.output) x = true → circuitFun n C x = true) ∧
      ∀ x, (wf pre (List.ofFn x)).getD a false =
          g.op.eval (g.inputs.map fun i => (wf pre (List.ofFn x)).getD i false) →
        circuitFun n (aliasCircuit n pre post a C.output) x = circuitFun n C x := by
  let N := n + pre.length
  let T := Tc N a
  let D : Circuit := ⟨pre ++ post.map T, rn N a C.output⟩
  have hmono : Monotone2 C := fun g hg => ⟨hao.1 g hg, (hao.2.2 g hg).le⟩
  have hpost (r : Gate) (hr : r ∈ post) : r ∈ C.gates := by
    rw [hC]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hr)))
  obtain ⟨hm, hrb, hs⟩ := asm n C pre post g hC T (rn N a C.output) hmono hao.2.1
    (Tc_legal N a) (fun r _ M hM hi => Tc_rb N a ha r M hM hi)
  have hAO : PEqualNP.TopForm.IsAO2 n D := by
    refine ⟨fun r hr => (legal_of D hm r hr).1, hrb, ?_⟩
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hao.2.2 r (by rw [hC]; exact List.mem_append.mpr (Or.inl hr))
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      simpa [T, Tc] using hao.2.2 r' (hpost r' hr')
  refine ⟨hAO, ?_, ?_, ?_⟩
  · simp [aliasCircuit, Circuit.size, hC]
    omega
  · intro x hD
    let A := wf pre (List.ofFn x)
    let b := g.op.eval (g.inputs.map fun i => A.getD i false)
    have hN : A.length = N := by simp [A, N, wf_len]
    have haA : a < A.length := by omega
    have hb : A.getD a false = true → b = true := hle x
    have hT : ∀ r ∈ post, ∀ E E' : List Bool,
        List.Forall₂ (fun a b => a = true → b = true) E' E →
        (T r).op.eval ((T r).inputs.map fun i => (A ++ E').getD i false) = true →
          r.op.eval (r.inputs.map fun i => (A ++ b :: E).getD i false) = true := by
      intro r hr E E' hEE htrue
      change r.op.eval ((r.inputs.map (rn N a)).map _) = true at htrue
      rw [List.map_map] at htrue
      apply gate_imp r (hao.1 r (hpost r hr)) _ _ ?_ htrue
      intro i hi hiv
      change (A ++ E').getD (rn N a i) false = true at hiv
      by_cases hiN : i = N
      · subst i
        have hrn : rn N a N = a := by simp [rn]
        rw [hrn, getD_left A E' a haA] at hiv
        rw [getD_mid A E b N hN]
        exact hb hiv
      · rw [rn_eq_sk N a i hiN] at hiv
        have hh := forall₂_getD (forall₂_prefix A hEE) (sk N i) hiv
        exact (getD_sk A E b N hN i hiN).symm.trans hh
    have hh := surg_alias_le T A b a haA hb post hT [] [] .nil C.output
    change (wf (pre ++ post.map T) (List.ofFn x)).getD (rn N a C.output) false = true at hD
    rw [wf_append] at hD
    have hval := hh (by simpa only [List.append_nil, hN] using hD)
    change (wf C.gates (List.ofFn x)).getD C.output false = true
    rw [hC, wf_append, wf_cons]
    exact hval
  · intro x heq
    let A := wf pre (List.ofFn x)
    let b := g.op.eval (g.inputs.map fun i => A.getD i false)
    have hN : A.length = N := by simp [A, N, wf_len]
    have hT : ∀ r ∈ post, ∀ E : List Bool,
        r.op.eval (r.inputs.map fun i => (A ++ b :: E).getD i false) =
          (T r).op.eval ((T r).inputs.map fun i => (A ++ E).getD i false) := by
      intro r _ E
      exact sound_c A E b N hN a ha heq r
    obtain ⟨E, hold, hnew⟩ := ev pre post g T (List.ofFn x) b rfl hT
    change (wf (pre ++ post.map T) (List.ofFn x)).getD (rn N a C.output) false =
      (wf C.gates (List.ofFn x)).getD C.output false
    rw [hC, hold, hnew]
    exact getD_rn A E b N hN a ha heq C.output

lemma alias_false_surg (A : List Bool) (a : ℕ) (ha : a < A.length) (post : List Gate)
    (hAO : ∀ g ∈ post, g.op = .and ∨ g.op = .or) :
    ∀ E E' : List Bool,
      List.Forall₂ (fun a b => a = true → b = true) E E' →
      ∀ o, (wf post (A ++ false :: E)).getD o false = true →
        (wf (post.map (Tc A.length a)) (A ++ E')).getD (rn A.length a o) false = true := by
  induction post with
  | nil =>
    intro E E' h o hv
    change (A ++ false :: E).getD o false = true at hv
    change (A ++ E').getD (rn A.length a o) false = true
    by_cases ho : o = A.length
    · subst o
      rw [getD_mid A E false A.length rfl] at hv
      cases hv
    · rw [rn_eq_sk A.length a o ho]
      apply forall₂_getD (forall₂_prefix A h) (sk A.length o)
      exact (getD_sk A E false A.length rfl o ho).trans hv
  | cons g post ih =>
    intro E E' h o hv
    let v := g.op.eval (g.inputs.map fun i => (A ++ false :: E).getD i false)
    let v' := (Tc A.length a g).op.eval
      ((Tc A.length a g).inputs.map fun i => (A ++ E').getD i false)
    have hvv : v = true → v' = true := by
      change g.op.eval _ = true → g.op.eval ((g.inputs.map (rn A.length a)).map _) = true
      rw [List.map_map]
      apply gate_imp g (hAO g (by simp))
      intro i hi hit
      change (A ++ E').getD (rn A.length a i) false = true
      by_cases hiA : i = A.length
      · subst i
        rw [getD_mid A E false A.length rfl] at hit
        cases hit
      · rw [rn_eq_sk A.length a i hiA]
        apply forall₂_getD (forall₂_prefix A h) (sk A.length i)
        exact (getD_sk A E false A.length rfl i hiA).trans hit
    have hh := forall₂_snoc h hvv
    have htail := ih (fun g' hg' => hAO g' (by simp [hg']))
      (E ++ [v]) (E' ++ [v']) hh o
    change (wf (post.map (Tc A.length a)) ((A ++ E') ++ [v'])).getD
      (rn A.length a o) false = true
    rw [List.append_assoc]
    apply htail
    simpa only [wf_cons, List.append_assoc, List.cons_append] using hv

lemma alias_above_false (n : ℕ) (pre post : List Gate) (a o : ℕ)
    (ha : a < n + pre.length) (hAO : ∀ g ∈ post, g.op = .and ∨ g.op = .or)
    (x : Fin n → Bool) :
    circuitFun n ⟨pre ++ ⟨GateOp.or, []⟩ :: post, o⟩ x = true →
      circuitFun n (aliasCircuit n pre post a o) x = true := by
  let A := wf pre (List.ofFn x)
  have hA : A.length = n + pre.length := by simp [A, wf_len]
  have h := alias_false_surg A a (by omega) post hAO [] [] .nil o
  change (wf (pre ++ ⟨GateOp.or, []⟩ :: post) (List.ofFn x)).getD o false = true →
    (wf (pre ++ post.map (Tc (n + pre.length) a)) (List.ofFn x)).getD
      (rn (n + pre.length) a o) false = true
  rw [wf_append, wf_cons, wf_append]
  simpa only [hA, A, List.append_nil, List.map_nil, GateOp.eval, List.any_nil] using h

lemma forced_alias_lower (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate) (a : ℕ)
    (hC : C.gates = pre ++ g :: post) (ha : a < n + pre.length)
    (hAO : PEqualNP.TopForm.IsAO2 n C) (x : Fin n → Bool) :
    circuitFun n (Sharing.forcedCircuit C pre.length) x = true →
      circuitFun n (aliasCircuit n pre post a C.output) x = true := by
  have he : Sharing.forcedCircuit C pre.length = ⟨pre ++ ⟨GateOp.or, []⟩ :: post, C.output⟩ := by
    simp [Sharing.forcedCircuit, hC]
  rw [he]
  apply alias_above_false n pre post a C.output ha
  intro r hr
  apply hAO.1 r
  rw [hC]
  simp only [List.mem_append, List.mem_cons]
  exact Or.inr (Or.inr hr)

lemma replace_built (n : ℕ) (pre post : List Gate) (g h : Gate)
    (hc : FalsePropagation.built n (pre ++ g :: post))
    (hop : h.op = .and ∨ h.op = .or) (hlen : h.inputs.length = 2)
    (hi : ∀ i ∈ h.inputs, i < n + pre.length) :
    FalsePropagation.built n (pre ++ h :: post) := by
  intro j r hr
  by_cases hj : j < pre.length
  · exact hc j r (by simpa only [List.getElem?_append_left hj] using hr)
  by_cases he : j = pre.length
  · subst j
    have he : h = r := by simpa using hr
    subst r
    exact ⟨hop, hlen, hi⟩
  · have hj' : pre.length ≤ j := by omega
    have hdiff : (pre ++ g :: post)[j]? = (pre ++ h :: post)[j]? := by
      rw [List.getElem?_append_right hj', List.getElem?_append_right hj']
      obtain ⟨k, hk⟩ : ∃ k, j - pre.length = k + 1 := ⟨j - pre.length - 1, by omega⟩
      rw [hk, List.getElem?_cons_succ, List.getElem?_cons_succ]
    exact hc j r (hdiff.trans hr)

lemma replace_ao2 (n : ℕ) (pre post : List Gate) (g h : Gate) (o : ℕ)
    (hc : PEqualNP.TopForm.IsAO2 n ⟨pre ++ g :: post, o⟩)
    (hop : h.op = .and ∨ h.op = .or) (hlen : h.inputs.length = 2)
    (hi : ∀ i ∈ h.inputs, i < n + pre.length) :
    PEqualNP.TopForm.IsAO2 n ⟨pre ++ h :: post, o⟩ :=
  FalsePropagation.built_ao2 n _ (replace_built n pre post g h
    (Reorder.built_of_ao2 n _ hc) hop hlen hi)

lemma replace_unused_semantics (n : ℕ) (pre post : List Gate) (g h : Gate) (o : ℕ)
    (ho : o ≠ n + pre.length)
    (hp : ∀ r ∈ post, ∀ i ∈ r.inputs, i ≠ n + pre.length) :
    circuitFun n ⟨pre ++ g :: post, o⟩ = circuitFun n ⟨pre ++ h :: post, o⟩ := by
  funext x
  let A := Rotation.run pre (List.ofFn x)
  have hA : A.length = n + pre.length := by simp [A, Rotation.run_length]
  have hh : Rotation.AgreeExcept (n + pre.length) (Rotation.step A g) (Rotation.step A h) := by
    refine ⟨by simp [Rotation.step], ?_⟩
    intro i hi
    unfold Rotation.step
    rw [Rotation.snoc_ne _ _ _ (by omega), Rotation.snoc_ne _ _ _ (by omega)]
  have hs := Rotation.agree_run (n + pre.length) _ _ post hh hp
  have hv := hs.2 o ho
  dsimp only [A, Rotation.run] at hv
  unfold Rotation.step at hv
  simpa only [List.foldl_append, List.foldl_cons, circuitFun, Circuit.eval, Circuit.wires] using hv

def appendOr (n : ℕ) (C : Circuit) (u v : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨.or, [u, v]⟩], n + C.size⟩

lemma appendOr_ao2 (n : ℕ) (C : Circuit) (u v : ℕ)
    (hc : PEqualNP.TopForm.IsAO2 n C) (hu : u < n + C.size) (hv : v < n + C.size) :
    PEqualNP.TopForm.IsAO2 n (appendOr n C u v) := by
  apply FalsePropagation.built_ao2
  apply FalsePropagation.built_append n C.gates [⟨.or, [u, v]⟩]
    (Reorder.built_of_ao2 n C hc)
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  subst g
  refine ⟨Or.inr rfl, rfl, ?_⟩
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl <;> assumption

lemma appendOr_value (n : ℕ) (C : Circuit) (u v : ℕ) (x : Fin n → Bool) :
    circuitFun n (appendOr n C u v) x =
      (circuitFun n ⟨C.gates, u⟩ x || circuitFun n ⟨C.gates, v⟩ x) := by
  let A := wf C.gates (List.ofFn x)
  have hA : A.length = n + C.size := by simp [A, wf_len, Circuit.size]
  change (wf (C.gates ++ [⟨.or, [u, v]⟩]) (List.ofFn x)).getD (n + C.size) false = _
  rw [wf_append]
  change (A ++ [GateOp.or.eval ([u, v].map fun i => A.getD i false)]).getD (n + C.size) false = _
  rw [← hA]
  rw [Rotation.snoc_eq]
  simp [GateOp.eval, A, wf, circuitFun, Circuit.eval, Circuit.wires]

def repairCircuit (n : ℕ) (pre post : List Gate) (l p d o : ℕ) : Circuit :=
  let k := n + pre.length
  let B : Circuit := ⟨pre ++ ⟨GateOp.and, [p, d]⟩ :: post.map (Tc (k + 1) l), rn (k + 1) l o⟩
  appendOr n B B.output k

lemma repairCircuit_gates (n : ℕ) (pre post : List Gate) (l p d o : ℕ) :
    (repairCircuit n pre post l p d o).gates =
      (pre ++ ⟨GateOp.and, [p, d]⟩ :: post.map (Tc (n + pre.length + 1) l)) ++
        [⟨GateOp.or, [rn (n + pre.length + 1) l o, n + pre.length]⟩] := rfl

lemma repair_private_pair_spec (n : ℕ) (C : Circuit) (pre post : List Gate)
    (c : Gate) (l p d : ℕ)
    (hC : C.gates = pre ++ [c, ⟨.and, [n + pre.length, d]⟩] ++ post)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hl : l < n + pre.length) (hp : p < n + pre.length) (hd : d < n + pre.length)
    (hout : C.output ≠ n + pre.length) (houtlt : C.output < n + C.size)
    (hprivate : ∀ g ∈ post, ∀ i ∈ g.inputs, i ≠ n + pre.length)
    (hdom : ∀ x : Fin n → Bool, (wf (pre ++ [c]) (List.ofFn x)).getD l false = true →
      GateOp.and.eval ([n + pre.length, d].map fun i =>
        (wf (pre ++ [c]) (List.ofFn x)).getD i false) = true) :
    PEqualNP.TopForm.IsAO2 n (repairCircuit n pre post l p d C.output) ∧
      (repairCircuit n pre post l p d C.output).size = C.size ∧
      ∀ x : Fin n → Bool, circuitFun n (repairCircuit n pre post l p d C.output) x =
        (circuitFun n (aliasCircuit n (pre ++ [c]) post l C.output) x ||
          ((wf pre (List.ofFn x)).getD p false && (wf pre (List.ofFn x)).getD d false)) := by
  let k := n + pre.length
  let tail := post.map (Tc (k + 1) l)
  let o := rn (k + 1) l C.output
  let star : Gate := ⟨.and, [p, d]⟩
  let A := aliasCircuit n (pre ++ [c]) post l C.output
  let B : Circuit := ⟨pre ++ star :: tail, o⟩
  have hc : C.gates = (pre ++ [c]) ++ ⟨GateOp.and, [n + pre.length, d]⟩ :: post := by
    simpa [List.append_assoc] using hC
  obtain ⟨hAAO, hAsize, hAbelow, hAeq⟩ := alias_spec n C (pre ++ [c]) post
    ⟨.and, [n + pre.length, d]⟩ l hc hAO (by simp; omega) hdom
  have ho : o ≠ k := by
    dsimp [o, rn]
    split_ifs <;> dsimp [k] at * <;> omega
  have ht : ∀ g ∈ tail, ∀ i ∈ g.inputs, i ≠ k := by
    intro g hg i hi
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
    have hne := hprivate g' hg' i' hi'
    dsimp [rn]
    split_ifs <;> dsimp [k] at * <;> omega
  have hB : PEqualNP.TopForm.IsAO2 n B := by
    apply replace_ao2 n pre tail c star o
    · simpa [A, aliasCircuit, B, tail, o, k, List.append_assoc, Nat.add_assoc] using hAAO
    · exact Or.inl rfl
    · rfl
    · intro i hi
      simp only [star, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> assumption
  have hBA : circuitFun n B = circuitFun n A := by
    have h := replace_unused_semantics n pre tail c star o ho ht
    simpa [A, B, aliasCircuit, tail, o, k, List.append_assoc, Nat.add_assoc] using h.symm
  have hlen : B.size = pre.length + 1 + post.length := by
    simp [B, tail, Circuit.size]
    omega
  have hoB : o < n + B.size := by
    have hco : C.size = pre.length + 2 + post.length := by
      simp [Circuit.size, hC]
      omega
    rw [hlen]
    dsimp [o, rn]
    split_ifs <;> dsimp [k] at * <;> omega
  have hkB : k < n + B.size := by rw [hlen]; dsimp [k]; omega
  refine ⟨appendOr_ao2 n B o k hB hoB hkB, ?_, ?_⟩
  · change (appendOr n B o k).size = C.size
    have hBs : B.size = A.size := by
      simp [A, B, aliasCircuit, Circuit.size, tail]
    have hdsize : (appendOr n B o k).size = B.size + 1 := by simp [appendOr, Circuit.size]
    rw [hdsize, hBs]
    exact hAsize
  · intro x
    change circuitFun n (appendOr n B o k) x = _
    rw [appendOr_value]
    have hstar : circuitFun n ⟨B.gates, k⟩ x =
        ((wf pre (List.ofFn x)).getD p false && (wf pre (List.ofFn x)).getD d false) := by
      have h := MinimumPure.prefix_gate_value (C := B) (pre := pre) (post := tail) (g := star) rfl x
      change circuitFun n ⟨B.gates, k⟩ x = _ at h
      simpa [star, GateOp.eval] using h
    rw [hstar]
    have hval : circuitFun n ⟨B.gates, o⟩ x = circuitFun n A x := congrFun hBA x
    rw [hval]

lemma repair_private_pair (n : ℕ) (C : Circuit) (pre post : List Gate)
    (c : Gate) (l p d : ℕ)
    (hC : C.gates = pre ++ [c, ⟨.and, [n + pre.length, d]⟩] ++ post)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hl : l < n + pre.length) (hp : p < n + pre.length) (hd : d < n + pre.length)
    (hout : C.output ≠ n + pre.length) (houtlt : C.output < n + C.size)
    (hprivate : ∀ g ∈ post, ∀ i ∈ g.inputs, i ≠ n + pre.length)
    (hdom : ∀ x : Fin n → Bool, (wf (pre ++ [c]) (List.ofFn x)).getD l false = true →
      GateOp.and.eval ([n + pre.length, d].map fun i =>
        (wf (pre ++ [c]) (List.ofFn x)).getD i false) = true) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size = C.size ∧
      ∀ x : Fin n → Bool, circuitFun n D x =
        (circuitFun n (aliasCircuit n (pre ++ [c]) post l C.output) x ||
          ((wf pre (List.ofFn x)).getD p false && (wf pre (List.ofFn x)).getD d false)) := by
  exact ⟨repairCircuit n pre post l p d C.output,
    repair_private_pair_spec n C pre post c l p d hC hAO hl hp hd hout houtlt hprivate hdom⟩

end AliasSurgery

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def overwriteCircuit (C : Circuit) (j : ℕ) (g : Gate) : Circuit :=
  ⟨C.gates.set j g, C.output⟩

def replacementVal (n : ℕ) (C : Circuit) (j : ℕ) (g : Gate)
    (x : Fin n → Bool) : Bool :=
  g.op.eval (g.inputs.map fun i =>
    if i < n + j then val C (List.ofFn x) i else false)

lemma overwriteCircuit_length (C : Circuit) (j : ℕ) (g : Gate) :
    (overwriteCircuit C j g).gates.length = C.gates.length := by
  simp [overwriteCircuit]

lemma overwriteCircuit_size (C : Circuit) (j : ℕ) (g : Gate) :
    (overwriteCircuit C j g).size = C.size := by
  simp [Circuit.size, overwriteCircuit]

lemma overwriteCircuit_gateAt_self (C : Circuit) {j : ℕ}
    (hj : j < C.gates.length) (g : Gate) :
    gateAt (overwriteCircuit C j g) j = g := by
  simp [overwriteCircuit, gateAt, List.getD_eq_getElem?_getD,
    List.getElem?_set_self hj]

lemma overwriteCircuit_gateAt_other (C : Circuit) (j k : ℕ)
    (hne : j ≠ k) (g : Gate) :
    gateAt (overwriteCircuit C j g) k = gateAt C k := by
  simp [overwriteCircuit, gateAt, List.getD_eq_getElem?_getD,
    List.getElem?_set_ne hne]

lemma overwriteCircuit_val_before {n : ℕ} (C : Circuit) (j : ℕ)
    (g : Gate) (x : Fin n → Bool) (w : ℕ) :
    w < n + j →
      val (overwriteCircuit C j g) (List.ofFn x) w = val C (List.ofFn x) w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hwj
    by_cases hn : w < n
    · rw [val_input (n := n) (by simp) hn, val_input (n := n) (by simp) hn]
    by_cases hw : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hk' : k < (overwriteCircuit C j g).gates.length := by
        simpa only [overwriteCircuit_length] using hk
      have hne : j ≠ k := by omega
      rw [val_gate (n := n) (by simp) hk', val_gate (n := n) (by simp) hk,
        overwriteCircuit_gateAt_other C j k hne g]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [ite_eq_left hi, ite_eq_left hi, ih i hi (by omega)]
      · rw [ite_eq_right hi, ite_eq_right hi]
    · rw [val_ge (n := n) (by simp) (by rw [overwriteCircuit_length]; omega),
        val_ge (n := n) (by simp) (by omega)]

lemma overwriteCircuit_val_self {n : ℕ} (C : Circuit) {j : ℕ}
    (hj : j < C.gates.length) (g : Gate) (x : Fin n → Bool) :
    val (overwriteCircuit C j g) (List.ofFn x) (n + j) =
      replacementVal n C j g x := by
  rw [val_gate (n := n) (by simp)
      (by simpa only [overwriteCircuit_length] using hj),
      overwriteCircuit_gateAt_self C hj g]
  unfold replacementVal
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < n + j
  · rw [ite_eq_left hi, ite_eq_left hi, overwriteCircuit_val_before C j g x i hi]
  · rw [ite_eq_right hi, ite_eq_right hi]

lemma replacementVal_of_readsBack {n : ℕ} (C : Circuit) (j : ℕ)
    (g : Gate) (x : Fin n → Bool) (hg : ∀ i ∈ g.inputs, i < n + j) :
    replacementVal n C j g x =
      g.op.eval (g.inputs.map fun i => val C (List.ofFn x) i) := by
  unfold replacementVal
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [ite_eq_left (hg i hi)]

lemma replacementVal_or_inputs {n : ℕ} (C : Circuit) (j : ℕ)
    (u v : Fin n) (x : Fin n → Bool) :
    replacementVal n C j ⟨GateOp.or, [u.val, v.val]⟩ x = (x u || x v) := by
  rw [replacementVal_of_readsBack C j _ x (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega)]
  simp [GateOp.eval, val_ofFn]

lemma overwriteCircuit_val_le {n : ℕ} {C : Circuit}
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (j : ℕ) (g : Gate)
    (x : Fin n → Bool)
    (hrep : replacementVal n C j g x = true → val C (List.ofFn x) (n + j) = true)
    (w : ℕ) :
    val (overwriteCircuit C j g) (List.ofFn x) w = true →
      val C (List.ofFn x) w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input (n := n) (by simp) hn, val_input (n := n) (by simp) hn]
      exact id
    by_cases hw : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hk' : k < (overwriteCircuit C j g).gates.length := by
        simpa only [overwriteCircuit_length] using hk
      by_cases heq : j = k
      · subst k
        rw [overwriteCircuit_val_self C hk g x]
        exact hrep
      have he : gateAt (overwriteCircuit C j g) k = gateAt C k :=
        overwriteCircuit_gateAt_other C j k heq g
      rcases hAO _ (gateAt_mem hk) with hand | hor
      · rw [val_and (n := n) (by simp) hk' (by rw [he]; exact hand),
          val_and (n := n) (by simp) hk hand, he]
        intro h i hi
        exact ⟨(h i hi).1, ih i (h i hi).1 (h i hi).2⟩
      · rw [val_or (n := n) (by simp) hk' (by rw [he]; exact hor),
          val_or (n := n) (by simp) hk hor, he]
        rintro ⟨i, hi, hlt, hv⟩
        exact ⟨i, hi, hlt, ih i hlt hv⟩
    · rw [val_ge (n := n) (by simp) (by rw [overwriteCircuit_length]; omega)]
      simp

lemma overwriteCircuit_val_eq {n : ℕ} (C : Circuit) (j : ℕ) (g : Gate)
    (x : Fin n → Bool)
    (hrep : replacementVal n C j g x = val C (List.ofFn x) (n + j)) (w : ℕ) :
    val (overwriteCircuit C j g) (List.ofFn x) w = val C (List.ofFn x) w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input (n := n) (by simp) hn, val_input (n := n) (by simp) hn]
    by_cases hw : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hk' : k < (overwriteCircuit C j g).gates.length := by
        simpa only [overwriteCircuit_length] using hk
      by_cases heq : j = k
      · subst k
        rw [overwriteCircuit_val_self C hk g x]
        exact hrep
      rw [val_gate (n := n) (by simp) hk', val_gate (n := n) (by simp) hk,
        overwriteCircuit_gateAt_other C j k heq g]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [ite_eq_left hi, ite_eq_left hi, ih i hi]
      · rw [ite_eq_right hi, ite_eq_right hi]
    · rw [val_ge (n := n) (by simp) (by rw [overwriteCircuit_length]; omega),
        val_ge (n := n) (by simp) (by omega)]

lemma overwriteCircuit_fun_le {n : ℕ} {C : Circuit}
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (j : ℕ) (g : Gate)
    (hrep : ∀ x : Fin n → Bool,
      replacementVal n C j g x = true → val C (List.ofFn x) (n + j) = true)
    (x : Fin n → Bool) :
    PEqualNP.MetaComplexity.circuitFun n (overwriteCircuit C j g) x = true →
      PEqualNP.MetaComplexity.circuitFun n C x = true :=
  overwriteCircuit_val_le hAO j g x (hrep x) C.output

lemma overwriteCircuit_fun_eq {n : ℕ} (C : Circuit) (j : ℕ) (g : Gate)
    (x : Fin n → Bool)
    (hrep : replacementVal n C j g x = val C (List.ofFn x) (n + j)) :
    PEqualNP.MetaComplexity.circuitFun n (overwriteCircuit C j g) x =
      PEqualNP.MetaComplexity.circuitFun n C x :=
  overwriteCircuit_val_eq C j g x hrep C.output

lemma overwriteCircuit_andOrOnly {C : Circuit}
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) (j : ℕ) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    PEqualNP.EdgeOwnership.AndOrOnly (overwriteCircuit C j g) := by
  intro g' hg'
  rcases List.mem_or_eq_of_mem_set hg' with hg' | rfl
  · exact hAO g' hg'
  · exact hg

lemma overwriteCircuit_readsBack {n : ℕ} {C : Circuit}
    (hC : ReadsBack n C) (j : ℕ) (g : Gate)
    (hg : ∀ i ∈ g.inputs, i < n + j) :
    ReadsBack n (overwriteCircuit C j g) := by
  intro k hk i hi
  have hkC : k < C.gates.length := by
    simpa only [overwriteCircuit_length] using hk
  by_cases hkj : j = k
  · subst k
    rw [overwriteCircuit_gateAt_self C hkC g] at hi
    exact hg i hi
  · rw [overwriteCircuit_gateAt_other C j k hkj g] at hi
    exact hC k hkC i hi

lemma overwriteCircuit_isAO2 {n : ℕ} {C : Circuit}
    (hC : PEqualNP.TopForm.IsAO2 n C) (j : ℕ) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hback : ∀ i ∈ g.inputs, i < n + j) (hlen : g.inputs.length = 2) :
    PEqualNP.TopForm.IsAO2 n (overwriteCircuit C j g) := by
  refine ⟨overwriteCircuit_andOrOnly hC.1 j g hop,
    overwriteCircuit_readsBack hC.2.1 j g hback, ?_⟩
  intro g' hg'
  rcases List.mem_or_eq_of_mem_set hg' with hg' | rfl
  · exact hC.2.2 g' hg'
  · exact hlen

end Sharing


namespace DoublePoint

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2584.Sharing

def andCount (C : Circuit) : ℕ :=
  C.gates.countP (fun g => match g.op with | .and => true | _ => false)

lemma exists_least_size_and (n : ℕ) (f : (Fin n → Bool) → Bool)
    (C : Circuit) (hC : IsAO2 n C) (hf : circuitFun n C = f) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = f ∧ D.size ≤ C.size ∧
      (∀ E : Circuit, IsAO2 n E → circuitFun n E = f → D.size ≤ E.size) ∧
      ∀ E : Circuit, IsAO2 n E → circuitFun n E = f → E.size = D.size →
        andCount D ≤ andCount E := by
  classical
  obtain ⟨A, hA, hAf, hAs, hmin⟩ := exists_least_circuit n f C hC hf
  let p : ℕ → Prop := fun k => ∃ D : Circuit,
    IsAO2 n D ∧ circuitFun n D = f ∧ D.size = A.size ∧ andCount D = k
  have hp : ∃ k, p k := ⟨andCount A, A, hA, hAf, rfl, rfl⟩
  obtain ⟨D, hD, hDf, hDs, hDk⟩ := Nat.find_spec hp
  refine ⟨D, hD, hDf, hDs ▸ hAs, ?_, ?_⟩
  · intro E hE hEf
    rw [hDs]
    exact hmin E hE hEf
  · intro E hE hEf hEs
    rw [hDk]
    exact Nat.find_min' hp ⟨E, hE, hEf, hEs.trans hDs, rfl⟩

lemma pure_point_and_double_pair_value {P L : ℕ} {C : Circuit}
    (hRB : ReadsBack (P + L) C) {a p q : ℕ}
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (hin : (gateAt C a).inputs = [p, q])
    (hpure : ∀ g, OrReaches (P + L) C p g → (gateAt C g).op = GateOp.or)
    (qpure : ∀ g, OrReaches (P + L) C q g → (gateAt C g).op = GateOp.or)
    (hsidep : ∀ t ∈ orIn (P + L) C p, t.val < P)
    (hsideq : ∀ t ∈ orIn (P + L) C q, t.val < P)
    (u v : Fin (P + L))
    (hmeet : orIn (P + L) C p ∩ orIn (P + L) C q = {u, v})
    (x : Fin P) (y : Fin L) :
    gateVal (P + L) C a (pairInput (Fin.castAdd L x) (Fin.natAdd P y)) =
      (pairInput (Fin.castAdd L x) (Fin.natAdd P y) u ||
       pairInput (Fin.castAdd L x) (Fin.natAdd P y) v) := by
  have hu : u ∈ orIn (P + L) C p ∩ orIn (P + L) C q := by rw [hmeet]; simp
  have hv : v ∈ orIn (P + L) C p ∩ orIn (P + L) C q := by rw [hmeet]; simp
  have hup := hsidep u (Finset.mem_inter.mp hu).1
  have hvp := hsidep v (Finset.mem_inter.mp hv).1
  have hun : u ≠ Fin.natAdd P y := by
    intro he
    have heval := congrArg Fin.val he
    simp only [Fin.val_natAdd] at heval
    omega
  have hvn : v ≠ Fin.natAdd P y := by
    intro he
    have heval := congrArg Fin.val he
    simp only [Fin.val_natAdd] at heval
    omega
  apply Bool.eq_iff_iff.mpr
  rw [pure_point_and_pair_iff hRB ha hand hin hpure qpure hsidep hsideq, hmeet]
  simp only [Finset.mem_insert, Finset.mem_singleton, Bool.or_eq_true, pairInput_true,
    hun, hvn, or_false]
  exact or_congr eq_comm eq_comm

lemma list_and_count_set_or (gs : List Gate) (a : ℕ) (ha : a < gs.length)
    (hand : gs[a].op = GateOp.and) (r : Gate) (hor : r.op = GateOp.or) :
    (gs.set a r).countP (fun g => match g.op with | .and => true | _ => false) + 1 =
      gs.countP (fun g => match g.op with | .and => true | _ => false) := by
  induction gs generalizing a with
  | nil => simp at ha
  | cons g gs ih =>
    cases a with
    | zero =>
      have hg : g.op = GateOp.and := by simpa using hand
      simp [hg, hor]
    | succ a =>
      have ha' : a < gs.length := by simpa using ha
      have hand' : gs[a].op = GateOp.and := by simpa using hand
      have h := ih a ha' hand'
      simp only [List.set_cons_succ, List.countP_cons]
      omega

lemma andCount_set_or {C : Circuit} {a : ℕ} (ha : a < C.gates.length)
    (hand : (gateAt C a).op = GateOp.and) (r : Gate) (hor : r.op = GateOp.or) :
    andCount ⟨C.gates.set a r, C.output⟩ + 1 = andCount C := by
  apply list_and_count_set_or C.gates a ha
  · simpa only [Sharing.gateAt_eq ha] using hand
  · exact hor

end DoublePoint

namespace DoublePoint

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2584.Sharing

lemma replacementVal_point_or {n : ℕ} (C : Circuit) (a : ℕ)
    (u v : Fin n) (x : Fin n → Bool) :
    replacementVal n C a ⟨GateOp.or, [u.val, v.val]⟩ x = (x u || x v) := by
  rw [replacementVal_of_readsBack C a _ x (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega)]
  simp [GateOp.eval, val_ofFn]

lemma replace_pure_point_and_double {P L : ℕ}
    (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hAO : IsAO2 (P + L) C)
    (hf : circuitFun (P + L) C = fun x =>
      decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    {a p q : ℕ} (ha : a < C.gates.length)
    (hand : (gateAt C a).op = GateOp.and) (hin : (gateAt C a).inputs = [p, q])
    (hpure : ∀ g, OrReaches (P + L) C p g → (gateAt C g).op = GateOp.or)
    (qpure : ∀ g, OrReaches (P + L) C q g → (gateAt C g).op = GateOp.or)
    (hsidep : ∀ t ∈ orIn (P + L) C p, t.val < P)
    (hsideq : ∀ t ∈ orIn (P + L) C q, t.val < P)
    (u v : Fin (P + L))
    (hmeet : orIn (P + L) C p ∩ orIn (P + L) C q = {u, v}) :
    ∃ D : Circuit, IsAO2 (P + L) D ∧ D.size = C.size ∧
      andCount D + 1 = andCount C ∧
      circuitFun (P + L) D = fun x =>
        decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) := by
  let r : Gate := ⟨GateOp.or, [u.val, v.val]⟩
  let D := overwriteCircuit C a r
  have hD : IsAO2 (P + L) D := overwriteCircuit_isAO2 hAO a r (Or.inr rfl) (by
    intro i hi
    change i ∈ [u.val, v.val] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega) rfl
  have hu : u ∈ orIn (P + L) C p ∩ orIn (P + L) C q := by rw [hmeet]; simp
  have hv : v ∈ orIn (P + L) C p ∩ orIn (P + L) C q := by rw [hmeet]; simp
  have hrep (x : Fin (P + L) → Bool) :
      replacementVal (P + L) C a r x = true → val C (List.ofFn x) (P + L + a) = true := by
    rw [replacementVal_point_or, Bool.or_eq_true]
    intro hx
    rcases hx with hx | hx
    · exact common_or_input_implies_and hAO.2.1 ha hand hin hu x hx
    · exact common_or_input_implies_and hAO.2.1 ha hand hin hv x hx
  refine ⟨D, hD, overwriteCircuit_size C a r, ?_, ?_⟩
  · exact andCount_set_or ha hand r rfl
  · apply incidence_eq_of_pair_cover I (circuitFun (P + L) D)
    · intro x y hxy
      exact val_monotone hD.1 x y hxy D.output
    · intro x hx
      have h := overwriteCircuit_fun_le hAO.1 a r hrep x hx
      simpa only [hf] using h
    · intro x y hxy
      have hval := pure_point_and_double_pair_value hAO.2.1 ha hand hin hpure qpure
        hsidep hsideq u v hmeet x y
      have heq := overwriteCircuit_fun_eq C a r (pairInput (Fin.castAdd L x) (Fin.natAdd P y))
        (by rw [replacementVal_point_or]; exact hval.symm)
      change circuitFun (P + L) (overwriteCircuit C a r) _ = true
      rw [heq, hf]
      exact decide_eq_true ⟨x, y, hxy, pairInput_left _ _, pairInput_right _ _⟩

lemma least_and_pure_point_intersection_card {P L : ℕ}
    (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hAO : IsAO2 (P + L) C)
    (hf : circuitFun (P + L) C = fun x =>
      decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (hmin : ∀ D : Circuit, IsAO2 (P + L) D →
      circuitFun (P + L) D = (fun x =>
        decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) →
      C.size ≤ D.size)
    (hminAnd : ∀ D : Circuit, IsAO2 (P + L) D →
      circuitFun (P + L) D = (fun x =>
        decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) →
      D.size = C.size → andCount C ≤ andCount D)
    {a p q : ℕ} (ha : a < C.gates.length)
    (hand : (gateAt C a).op = GateOp.and) (hin : (gateAt C a).inputs = [p, q])
    (hpure : ∀ g, OrReaches (P + L) C p g → (gateAt C g).op = GateOp.or)
    (qpure : ∀ g, OrReaches (P + L) C q g → (gateAt C g).op = GateOp.or)
    (hsidep : ∀ t ∈ orIn (P + L) C p, t.val < P)
    (hsideq : ∀ t ∈ orIn (P + L) C q, t.val < P) :
    3 ≤ (orIn (P + L) C p ∩ orIn (P + L) C q).card := by
  have htwo := MinimumPure.least_pure_point_and_intersection_card I C hAO hf hmin ha hand hin
    hpure qpure hsidep hsideq
  by_contra hnot
  have hcard : (orIn (P + L) C p ∩ orIn (P + L) C q).card = 2 := by omega
  obtain ⟨u, v, huv, hmeet⟩ := Finset.card_eq_two.mp hcard
  obtain ⟨D, hD, hsize, hcount, hfun⟩ := replace_pure_point_and_double I C hAO hf ha hand hin
    hpure qpure hsidep hsideq u v hmeet
  have h := hminAnd D hD hfun hsize
  omega

end DoublePoint

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2584.TwoJunkStructure

lemma pure_or_pair_iff {n : ℕ} {C : Circuit} {w : ℕ}
    (hpure : ∀ g, OrReaches n C w g → (gateAt C g).op = GateOp.or)
    (x y : Fin n) :
    val C (List.ofFn (pairInput x y)) w = true ↔ x ∈ orIn n C w ∨ y ∈ orIn n C w := by
  rw [pure_or_value_iff hpure]
  constructor
  · rintro ⟨u, hu, hv⟩
    rcases (pairInput_true x y u).mp hv with rfl | rfl
    · exact Or.inl hu
    · exact Or.inr hu
  · rintro (hx | hy)
    · exact ⟨x, hx, pairInput_left x y⟩
    · exact ⟨y, hy, pairInput_right x y⟩

lemma four_or_block_double_star {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (a b c d : ℕ)
    (hfour : ∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (hapure : ∀ g, OrReaches (P + L) C a g → (gateAt C g).op = GateOp.or)
    (hbpure : ∀ g, OrReaches (P + L) C b g → (gateAt C g).op = GateOp.or)
    (hcpure : ∀ g, OrReaches (P + L) C c g → (gateAt C g).op = GateOp.or)
    (hdpure : ∀ g, OrReaches (P + L) C d g → (gateAt C g).op = GateOp.or)
    (hapoint : ∀ u ∈ orIn (P + L) C a, u.val < P)
    (hdline : ∀ u ∈ orIn (P + L) C d, P ≤ u.val)
    (hsound : ∀ z : Fin (P + L) → Bool,
      val C (List.ofFn z) a = true → val C (List.ofFn z) b = true →
      val C (List.ofFn z) c = true → val C (List.ofFn z) d = true →
      decide (∃ p l, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true) = true)
    (p0 : Fin P) (l0 : Fin L)
    (hp0 : Fin.castAdd L p0 ∈ orIn (P + L) C a ∧
      Fin.castAdd L p0 ∈ orIn (P + L) C b ∧ Fin.castAdd L p0 ∈ orIn (P + L) C c)
    (hl0 : Fin.natAdd P l0 ∈ orIn (P + L) C d ∧
      Fin.natAdd P l0 ∉ orIn (P + L) C b ∧ Fin.natAdd P l0 ∉ orIn (P + L) C c) :
    ∃ l1 : Fin L, ∀ p l,
      val C (List.ofFn (pairInput (Fin.castAdd L p) (Fin.natAdd P l))) a = true →
      val C (List.ofFn (pairInput (Fin.castAdd L p) (Fin.natAdd P l))) b = true →
      val C (List.ofFn (pairInput (Fin.castAdd L p) (Fin.natAdd P l))) c = true →
      val C (List.ofFn (pairInput (Fin.castAdd L p) (Fin.natAdd P l))) d = true →
      p = p0 ∨ l = l1 := by
  let A := fun p : Fin P => Fin.castAdd L p ∈ orIn (P + L) C a
  let B := fun p : Fin P => Fin.castAdd L p ∈ orIn (P + L) C b
  let E := fun l : Fin L => Fin.natAdd P l ∈ orIn (P + L) C b
  let K := fun p : Fin P => Fin.castAdd L p ∈ orIn (P + L) C c
  let F := fun l : Fin L => Fin.natAdd P l ∈ orIn (P + L) C c
  let D := fun l : Fin L => Fin.natAdd P l ∈ orIn (P + L) C d
  have hpair : ∀ p l, fourClauseEdge A B K D E F p l → I p l := by
    intro p l hh
    obtain ⟨hA, hD, hB, hK⟩ := hh
    have ht := hsound (pairInput (Fin.castAdd L p) (Fin.natAdd P l))
      (orIn_value hA _ (pairInput_left _ _))
      ((pure_or_pair_iff hbpure _ _).mpr hB)
      ((pure_or_pair_iff hcpure _ _).mpr hK)
      (orIn_value hD _ (pairInput_right _ _))
    have heq := incidenceGraph_function I (pairInput (Fin.castAdd L p) (Fin.natAdd P l))
    rw [← heq] at ht
    have hadj := (graphFun_pair (incidenceGraph I) _ _).mp ht
    simpa [incidenceBit] using hadj
  have htriple : ∀ p q l, A p → A q → D l →
      (B p ∨ B q ∨ E l) → (K p ∨ K q ∨ F l) → I p l ∨ I q l := by
    intro p q l hAp hAq hD hB hK
    let z : Fin (P + L) → Bool :=
      Fin.addCases (fun r => decide (r = p ∨ r = q)) (fun m => decide (m = l))
    have hzp : z (Fin.castAdd L p) = true := by simp [z]
    have hzq : z (Fin.castAdd L q) = true := by simp [z]
    have hzl : z (Fin.natAdd P l) = true := by simp [z]
    have hbval : val C (List.ofFn z) b = true := by
      rcases hB with hp | hq | hl
      · exact orIn_value hp z hzp
      · exact orIn_value hq z hzq
      · exact orIn_value hl z hzl
    have hcval : val C (List.ofFn z) c = true := by
      rcases hK with hp | hq | hl
      · exact orIn_value hp z hzp
      · exact orIn_value hq z hzq
      · exact orIn_value hl z hzl
    have ht := decide_eq_true_iff.mp (hsound z (orIn_value hAp z hzp) hbval hcval (orIn_value hD z hzl))
    obtain ⟨r, m, hrm, hzr, hzm⟩ := ht
    have hr : r = p ∨ r = q := by simpa [z] using hzr
    have hm : m = l := by simpa [z] using hzm
    subst m
    rcases hr with rfl | rfl
    · exact Or.inl hrm
    · exact Or.inr hrm
  obtain ⟨l1, hcover⟩ := four_clause_double_star I A B K D E F hfour hpair htriple p0 l0 hp0 hl0
  refine ⟨l1, ?_⟩
  intro p l hav hbv hcv hdv
  have hA : A p := by
    rcases (pure_or_pair_iff hapure _ _).mp hav with hp | hl
    · exact hp
    · have := hapoint _ hl
      simp only [Fin.val_natAdd] at this
      omega
  have hD : D l := by
    rcases (pure_or_pair_iff hdpure _ _).mp hdv with hp | hl
    · have := hdline _ hp
      simp only [Fin.val_castAdd] at this
      omega
    · exact hl
  exact hcover p l ⟨hA, hD, (pure_or_pair_iff hbpure _ _).mp hbv,
    (pure_or_pair_iff hcpure _ _).mp hcv⟩

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

lemma overwrite_or_junk_subset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : AndOrOnly C) (g : ℕ) (r : Gate) (hror : r.op = GateOp.or)
    (hrep : ∀ x : Fin n → Bool,
      replacementVal n C g r x = true → val C (List.ofFn x) (n + g) = true) :
    PEqualNP.TopForm.junk G (overwriteCircuit C g r) ⊆ (PEqualNP.TopForm.junk G C).erase g := by
  intro j hj
  have hj' := hj
  simp only [PEqualNP.TopForm.junk, PEqualNP.TopForm.gatesWhere, Finset.mem_filter, Finset.mem_range] at hj'
  obtain ⟨hjlen, hjand, _, x, hjval, hxfalse⟩ := hj'
  have hjC : j < C.gates.length := by simpa only [overwriteCircuit_length] using hjlen
  have hjg : j ≠ g := by
    intro he
    subst j
    rw [overwriteCircuit_gateAt_self C hjC r, hror] at hjand
    cases hjand
  have hjandC : (gateAt C j).op = GateOp.and := by
    simpa only [overwriteCircuit_gateAt_other C g j hjg.symm r] using hjand
  have hjvalC : gateVal n C j x = true :=
    overwriteCircuit_val_le hAO g r x (hrep x) (n + j) hjval
  apply Finset.mem_erase.mpr
  refine ⟨hjg, ?_⟩
  simp only [PEqualNP.TopForm.junk, PEqualNP.TopForm.gatesWhere, Finset.mem_filter, Finset.mem_range]
  exact ⟨hjC, hjandC, hjC, x, hjvalC, hxfalse⟩

lemma overwrite_or_junk_card_le_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : AndOrOnly C) (g h : ℕ) (r : Gate) (hror : r.op = GateOp.or)
    (hrep : ∀ x : Fin n → Bool,
      replacementVal n C g r x = true → val C (List.ofFn x) (n + g) = true)
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = h) :
    (PEqualNP.TopForm.junk G (overwriteCircuit C g r)).card ≤ 1 := by
  have hsub : PEqualNP.TopForm.junk G (overwriteCircuit C g r) ⊆ {h} := by
    intro j hj
    obtain ⟨hjg, hjold⟩ := Finset.mem_erase.mp (overwrite_or_junk_subset G C hAO g r hror hrep hj)
    simp only [PEqualNP.TopForm.junk, PEqualNP.TopForm.gatesWhere, Finset.mem_filter, Finset.mem_range] at hjold
    obtain ⟨hjlen, hjand, _, x, hjval, hxfalse⟩ := hjold
    have hjdirty : ¬ BelowF G C j := by
      intro hjbelow
      have hF := hjbelow x hjval
      rw [hxfalse] at hF
      cases hF
    rcases honly j hjlen hjand hjdirty with he | he
    · exact False.elim (hjg he)
    · exact Finset.mem_singleton.mpr he
  exact (Finset.card_le_card hsub).trans (by simp)

end Sharing

namespace TopAndCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2584.TopNormalize
open PEqualNP.Outside.L_meta_2584.DoublePoint

lemma andCount_eq_card (C : Circuit) :
    andCount C = ((Finset.range C.gates.length).filter
      (fun i => (match (gateAt C i).op with | .and => true | _ => false) = true)).card := by
  let p : Gate → Bool := fun g => match g.op with | .and => true | _ => false
  have hmap : (List.range C.gates.length).map
      (fun i => C.gates.getD i ⟨GateOp.or, []⟩) = C.gates := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      rw [List.getElem_map, List.getElem_range]
      exact List.getD_eq_getElem _ _ hj
  have hc := congrArg (List.countP p) hmap
  simp only [List.countP_map, Function.comp_def] at hc
  have hcard := (show (List.range C.gates.length).Nodup from List.nodup_range).card_eq_countP
    (P := fun i => p (C.gates.getD i ⟨GateOp.or, []⟩) = true)
  calc
    andCount C = ((List.range C.gates.length).toFinset.filter
        (fun i => p (C.gates.getD i ⟨GateOp.or, []⟩) = true)).card := hc.symm.trans hcard.symm
    _ = _ := by
      congr 1
      ext i
      simp [gateAt, p]

lemma andCount_eq_of_rho (C C' : Circuit) (r : ℕ) (hr : r < C.gates.length)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 →
      (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hopr : (gateAt C r).op = GateOp.or) : andCount C' = andCount C := by
  classical
  rw [andCount_eq_card, andCount_eq_card, hlen]
  apply card_filter_rho C.gates.length r hr
    (fun k => (match (gateAt C k).op with | .and => true | _ => false) = true)
    (fun k => (match (gateAt C' k).op with | .and => true | _ => false) = true)
  · intro k hk
    rw [hops k hk]
  · simp [hopr]
  · simp [htop]

open Classical in
lemma main_ind_andCount (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : G.edgeFinset.Nonempty) :
    ∀ k : ℕ, ∀ C : Circuit, PEqualNP.TopForm.IsLeastAO G C →
      ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
        (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
          (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card = k →
      ∃ C' : Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
        (PEqualNP.TopForm.junk G C').card = (PEqualNP.TopForm.junk G C).card ∧
        andCount C' = andCount C ∧ PEqualNP.TopForm.TopForm G C' := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hC hk
    by_cases htop : PEqualNP.TopForm.TopForm G C
    · exact ⟨C, hC, rfl, rfl, rfl, htop⟩
    · have hex : ∃ i j, i < C.gates.length ∧ j < C.gates.length ∧
          (gateAt C i).op = GateOp.and ∧ PEqualNP.TopForm.BelowF G C i ∧
          (gateAt C j).op = GateOp.and ∧ InCone n C i j := by
        by_contra hne
        apply htop
        intro i hi j hj h1 h2 h3 h4
        exact hne ⟨i, j, hi, hj, h1, h2, h3, h4⟩
      obtain ⟨i, j, hi, hj, hopi, hbi, hopj, hcone⟩ := hex
      obtain ⟨hL, hF⟩ := least_glue n G C hC
      obtain ⟨x1, hx1⟩ := exists_true n G hG
      have hout : C.output < n + C.gates.length := out_lt n C x1 (by rw [hF]; exact hx1)
      obtain ⟨C', r, hr, hir, hL', hF', hlen, hops, htop', hopr, hbelow, hcn, hno⟩ :=
        step3_struct n C (graphFun G ∅) hL hF hout i j hbi hcone
      have hlt := pairs_lt n C C' r i j hr hir hlen hops htop' hcn hno hopi hopj hcone
      rw [hk] at hlt
      obtain ⟨C'', h1, h2, h3, h4, h5⟩ := ih _ hlt C' (least_glue' n G C' hL' hF') rfl
      refine ⟨C'', h1, h2.trans hlen, h3.trans ?_,
        h4.trans (andCount_eq_of_rho C C' r hr hlen hops htop' hopr), h5⟩
      refine junk_eq n C C' (graphFun G ∅) r hr hlen hops htop' hopr hbelow _ _ ?_ ?_
      · intro k
        exact mem_junk n G C k
      · intro k
        exact mem_junk n G C' k


lemma least_to_topForm_andCount {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hne : G.edgeFinset.Nonempty) (hC : IsLeastAO G C) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size = C.size ∧
      (junk G D).card = (junk G C).card ∧ andCount D = andCount C ∧ TopForm G D :=
  main_ind_andCount n G hne _ C hC rfl

lemma exists_least_and_topForm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hf : circuitFun n C = graphFun G ∅)
    (hne : G.edgeFinset.Nonempty) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size ≤ C.size ∧ TopForm G D ∧
      ∀ E : Circuit, IsAO2 n E → circuitFun n E = graphFun G ∅ → E.size = D.size →
        andCount D ≤ andCount E := by
  obtain ⟨A, hA, hAf, hAs, hmin, hminAnd⟩ := exists_least_size_and n (graphFun G ∅) C hAO hf
  obtain ⟨D, hD, hDS, hDJ, hDA, hDT⟩ := least_to_topForm_andCount G A hne ⟨hA, hAf, hmin⟩
  refine ⟨D, hD, hDS.le.trans hAs, hDT, ?_⟩
  intro E hE hEf hES
  rw [hDA]
  exact hminAnd E hE hEf (hES.trans hDS)

end TopAndCount

namespace Reorder
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

lemma sw_add (n k i : ℕ) : sw (n + k) (n + i) = n + sw k i := by
  unfold sw
  split_ifs <;> omega

lemma rename_getD_op (post : List Gate) (k j : ℕ) :
    ((post.map (rename k)).getD j ⟨.or, []⟩).op = (post.getD j ⟨.or, []⟩).op := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases post[j]? <;> rfl

lemma adjacent_gateOp (n : ℕ) (pre post : List Gate) (a b : Gate) (o j : ℕ) :
    (gateAt (⟨pre ++ [b, a] ++ post.map (rename (n + pre.length)), sw (n + pre.length) o⟩ : Circuit)
      (sw pre.length j)).op =
      (gateAt (⟨pre ++ [a, b] ++ post, o⟩ : Circuit) j).op := by
  by_cases hj : j = pre.length
  · subst j
    simp [gateAt, sw, List.append_assoc, List.getD_eq_getElem?_getD]
  by_cases hj1 : j = pre.length + 1
  · subst j
    simp [gateAt, sw, List.append_assoc, List.getD_eq_getElem?_getD]
  have hs : sw pre.length j = j := by simp [sw, hj, hj1]
  rw [hs]
  by_cases hlt : j < pre.length
  · simp only [gateAt, List.append_assoc, List.getD_append _ _ _ _ hlt]
  · have he (a b : Gate) (post : List Gate) :
        (pre ++ [a, b] ++ post).getD j ⟨.or, []⟩ = post.getD (j - pre.length - 2) ⟨.or, []⟩ := by
      rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by simp; omega)]
      rfl
    simp only [gateAt]
    rw [he, he]
    exact rename_getD_op post _ _

lemma adjacent_gateVal (n : ℕ) (pre post : List Gate) (a b : Gate) (o j : ℕ)
    (ha : ∀ i ∈ a.inputs, i < n + pre.length)
    (hb : ∀ i ∈ b.inputs, i < n + pre.length) (x : Fin n → Bool) :
    gateVal n (⟨pre ++ [b, a] ++ post.map (rename (n + pre.length)), sw (n + pre.length) o⟩ : Circuit)
      (sw pre.length j) x =
      gateVal n (⟨pre ++ [a, b] ++ post, o⟩ : Circuit) j x := by
  have h := adjacent_semantics n pre post a b (n + j) ha hb
  have hv := congrFun h x
  rw [sw_add] at hv
  exact hv

lemma adjacent_junk_mem (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (a b : Gate) (o j : ℕ)
    (ha : ∀ i ∈ a.inputs, i < n + pre.length)
    (hb : ∀ i ∈ b.inputs, i < n + pre.length) :
    sw pre.length j ∈ junk G
      ⟨pre ++ [b, a] ++ post.map (rename (n + pre.length)), sw (n + pre.length) o⟩ ↔
      j ∈ junk G ⟨pre ++ [a, b] ++ post, o⟩ := by
  have hlt : sw pre.length j < pre.length + 2 + post.length ↔ j < pre.length + 2 + post.length := by
    constructor
    · intro h
      have hh := sw_lt pre.length (pre.length + 2 + post.length) (sw pre.length j) (by omega) h
      simpa only [sw_involutive] using hh
    · exact sw_lt pre.length _ j (by omega)
  let C : Circuit := ⟨pre ++ [a, b] ++ post, o⟩
  let D : Circuit := ⟨pre ++ [b, a] ++ post.map (rename (n + pre.length)), sw (n + pre.length) o⟩
  have hlenC : C.gates.length = pre.length + 2 + post.length := by simp [C]; omega
  have hlenD : D.gates.length = pre.length + 2 + post.length := by simp [D]; omega
  have hop : (gateAt D (sw pre.length j)).op = (gateAt C j).op := adjacent_gateOp n pre post a b o j
  have hv (x : Fin n → Bool) : gateVal n D (sw pre.length j) x = gateVal n C j x :=
    adjacent_gateVal n pre post a b o j ha hb x
  change sw pre.length j ∈ junk G D ↔ j ∈ junk G C
  unfold junk gatesWhere
  simp only [Finset.mem_filter, Finset.mem_range]
  unfold IsDirtyAnd IsDirty
  rw [hop, hlenD, hlenC, hlt]
  simp only [hv]

lemma adjacent_junk_card (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (a b : Gate) (o : ℕ)
    (ha : ∀ i ∈ a.inputs, i < n + pre.length)
    (hb : ∀ i ∈ b.inputs, i < n + pre.length) :
    (junk G ⟨pre ++ [b, a] ++ post.map (rename (n + pre.length)), sw (n + pre.length) o⟩).card =
      (junk G ⟨pre ++ [a, b] ++ post, o⟩).card := by
  symm
  apply Finset.card_bij (fun j _ => sw pre.length j)
  · intro j hj
    exact (adjacent_junk_mem n G pre post a b o j ha hb).mpr hj
  · intro i hi j hj he
    have h := congrArg (sw pre.length) he
    simpa only [sw_involutive] using h
  · intro j hj
    refine ⟨sw pre.length j, ?_, sw_involutive pre.length j⟩
    apply (adjacent_junk_mem n G pre post a b o (sw pre.length j) ha hb).mp
    simpa only [sw_involutive] using hj

lemma bubble_private_junk (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (pre : List Gate) (a : Gate) (mid : List Gate) (b : ℕ)
    (post : List Gate) (o : ℕ)
    (ha : ∀ i ∈ a.inputs, i < n + pre.length)
    (hb : b < n + pre.length + 1 + mid.length) (hbne : b ≠ n + pre.length)
    (ho : o ≠ n + pre.length)
    (hprivate : ∀ g ∈ mid ++ post, ∀ i ∈ g.inputs, i ≠ n + pre.length)
    (hC : PEqualNP.TopForm.IsAO2 n (shape n pre a mid b post o)) :
    ∃ pre' post' b' o',
      pre'.length = pre.length + mid.length ∧
      PEqualNP.TopForm.IsAO2 n (shape n pre' a [] b' post' o') ∧
      Same n (shape n pre a mid b post o) (shape n pre' a [] b' post' o') ∧
      b' < n + pre'.length ∧ o' ≠ n + pre'.length ∧
      (∀ g ∈ post', ∀ i ∈ g.inputs, i ≠ n + pre'.length) ∧
      (∀ i, i < n + pre.length →
        circuitFun n ⟨(shape n pre' a [] b' post' o').gates, i⟩ =
          circuitFun n ⟨(shape n pre a mid b post o).gates, i⟩) ∧
      circuitFun n ⟨(shape n pre' a [] b' post' o').gates, b'⟩ =
        circuitFun n ⟨(shape n pre a mid b post o).gates, b⟩ ∧
      (junk G (shape n pre' a [] b' post' o')).card =
        (junk G (shape n pre a mid b post o)).card := by
  generalize hm : mid.length = m
  induction m using Nat.strong_induction_on generalizing pre mid b post o with
  | _ m ih =>
    cases mid with
    | nil =>
      refine ⟨pre, post, b, o, by simp at hm; omega, hC, same_refl _ _, ?_, ho, ?_,
        fun _ _ => rfl, rfl, rfl⟩
      · simp only [List.length_nil] at hb
        omega
      · simpa only [List.nil_append] using hprivate
    | cons g mid =>
      let k := n + pre.length
      have hg : ∀ i ∈ g.inputs, i < k := by
        intro i hi
        have hidx : pre.length + 1 < (shape n pre a (g :: mid) b post o).gates.length := by
          simp [shape]
        have he : NestedCover.gateAt (shape n pre a (g :: mid) b post o) (pre.length + 1) = g := by
          simp [shape, NestedCover.gateAt, List.append_assoc, List.getD_eq_getElem?_getD]
        have hlt := hC.2.1 (pre.length + 1) hidx i (by simpa only [he] using hi)
        have hne := hprivate g (by simp) i hi
        dsimp [k]
        omega
      let tail := mid ++ [⟨.and, [k, b]⟩] ++ post
      let pre1 := pre ++ [g]
      let mid1 := mid.map (rename k)
      let post1 := post.map (rename k)
      let b1 := sw k b
      let o1 := sw k o
      have hsource : shape n pre a (g :: mid) b post o = ⟨pre ++ [a, g] ++ tail, o⟩ := by
        simp [shape, tail, k, List.append_assoc]
      have hdest : (⟨pre ++ [g, a] ++ tail.map (rename k), o1⟩ : Circuit) =
          shape n pre1 a mid1 b1 post1 o1 := by
        simp [shape, tail, pre1, mid1, post1, b1, rename, sw_self, k, List.map_append,
          List.append_assoc, Nat.add_assoc]
      have hao1 : PEqualNP.TopForm.IsAO2 n (shape n pre1 a mid1 b1 post1 o1) := by
        rw [← hdest]
        exact adjacent_ao2 n pre tail a g o ha hg (by rw [← hsource]; exact hC)
      have hs1 : Same n (shape n pre a (g :: mid) b post o)
          (shape n pre1 a mid1 b1 post1 o1) := by
        rw [hsource, ← hdest]
        exact adjacent_same n pre tail a g o ha hg
      have ha1 : ∀ i ∈ a.inputs, i < n + pre1.length := by
        intro i hi
        have := ha i hi
        simp [pre1]
        omega
      have hb1 : b1 < n + pre1.length + 1 + mid1.length := by
        have h := sw_lt k (n + pre.length + 2 + mid.length) b (by dsimp [k]; omega)
          (by simp only [List.length_cons] at hb; omega)
        simpa [b1, pre1, mid1, Nat.add_assoc] using h
      have hbne1 : b1 ≠ n + pre1.length := by
        simpa [b1, pre1, k, Nat.add_assoc] using sw_ne_succ k b hbne
      have ho1 : o1 ≠ n + pre1.length := by
        simpa [o1, pre1, k, Nat.add_assoc] using sw_ne_succ k o ho
      have hp1 : ∀ h ∈ mid1 ++ post1, ∀ i ∈ h.inputs, i ≠ n + pre1.length := by
        have hp : ∀ h ∈ mid ++ post, ∀ i ∈ h.inputs, i ≠ k := by
          intro h hh i hi
          apply hprivate h _ i hi
          simp only [List.mem_append, List.mem_cons] at hh ⊢
          tauto
        simpa [mid1, post1, pre1, k, List.map_append, Nat.add_assoc] using rename_avoids k (mid ++ post) hp
      have hvs (i : ℕ) :
          circuitFun n ⟨(shape n pre1 a mid1 b1 post1 o1).gates, sw k i⟩ =
            circuitFun n ⟨(shape n pre a (g :: mid) b post o).gates, i⟩ := by
        rw [congrArg Circuit.gates hsource, ← congrArg Circuit.gates hdest]
        exact adjacent_semantics n pre tail a g i ha hg
      have hJ1 : (junk G (shape n pre1 a mid1 b1 post1 o1)).card =
          (junk G (shape n pre a (g :: mid) b post o)).card := by
        rw [hsource, ← hdest]
        exact adjacent_junk_card n G pre tail a g o ha hg
      obtain ⟨pre', post', b', o', hlen, hAO, hs, hb', ho', hp', hvals, hvalb, hJ⟩ :=
        ih mid.length (by simp only [List.length_cons] at hm; omega)
          pre1 mid1 b1 post1 o1 ha1 hb1 hbne1 ho1 hp1 hao1 (by simp [mid1])
      refine ⟨pre', post', b', o', ?_, hAO, same_trans hs1 hs, hb', ho', hp', ?_, ?_, hJ.trans hJ1⟩
      · simp only [pre1, List.length_append, List.length_cons, List.length_nil] at hlen
        simp only [List.length_cons] at hm
        omega
      · intro i hi
        have hi1 : i < n + pre1.length := by simp [pre1]; omega
        exact (hvals i hi1).trans (by simpa only [sw_below k i hi] using hvs i)
      · exact hvalb.trans (hvs b)

end Reorder

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

lemma pure_or_and_singleton_inputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {h a b : ℕ} (hh : h < C.gates.length) (hhand : (gateAt C h).op = GateOp.and)
    (hinputs : (gateAt C h).inputs = [a, b])
    (hapure : ∀ g, OrReaches n C a g → (gateAt C g).op = GateOp.or)
    (hbpure : ∀ g, OrReaches n C b g → (gateAt C g).op = GateOp.or) :
    singletonInputs n C (n + h) = orIn n C a ∩ orIn n C b := by
  apply Finset.ext
  intro u
  constructor
  · intro hu
    simp only [singletonInputs, Finset.mem_filter, Finset.mem_univ, true_and] at hu
    have hav := and_operand_value hAO hh hhand (pairInput u u) hu 0
    have hbv := and_operand_value hAO hh hhand (pairInput u u) hu 1
    simp only [opnd, hinputs, List.getD_cons_zero] at hav
    have hbval : val C (List.ofFn (pairInput u u)) b = true := by simpa [opnd, hinputs] using hbv
    have ha := (pure_or_pair_iff hapure u u).mp hav
    have hb := (pure_or_pair_iff hbpure u u).mp hbval
    exact Finset.mem_inter.mpr ⟨ha.elim id id, hb.elim id id⟩
  · intro hu
    simp only [singletonInputs, Finset.mem_filter, Finset.mem_univ, true_and]
    exact common_or_input_implies_and hAO.2.1 hh hhand hinputs hu _ (pairInput_left u u)

lemma pure_opposite_and_singletons_empty {P L : ℕ} {C : Circuit} (hAO : IsAO2 (P + L) C)
    {h a b : ℕ} (hh : h < C.gates.length) (hhand : (gateAt C h).op = GateOp.and)
    (hinputs : (gateAt C h).inputs = [a, b])
    (hapure : ∀ g, OrReaches (P + L) C a g → (gateAt C g).op = GateOp.or)
    (hbpure : ∀ g, OrReaches (P + L) C b g → (gateAt C g).op = GateOp.or)
    (hapoint : ∀ u ∈ orIn (P + L) C a, u.val < P)
    (hbline : ∀ u ∈ orIn (P + L) C b, P ≤ u.val) :
    singletonInputs (P + L) C (P + L + h) = ∅ := by
  rw [pure_or_and_singleton_inputs hAO hh hhand hinputs hapure hbpure]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  have hp := hapoint u (Finset.mem_inter.mp hu).1
  have hl := hbline u (Finset.mem_inter.mp hu).2
  omega

end Sharing

namespace Sharing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

lemma sound_or_factors_have_pure_sides {P L : ℕ}
    (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit) (W : List ℕ)
    (hsound : ∀ z : Fin (P + L) → Bool,
      (∀ w ∈ W, val C (List.ofFn z) w = true) →
      decide (∃ p l, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true) = true) :
    (∃ w ∈ W, ∀ u ∈ orIn (P + L) C w, u.val < P) ∧
    (∃ w ∈ W, ∀ u ∈ orIn (P + L) C w, P ≤ u.val) := by
  classical
  constructor
  · by_contra hn
    let z : Fin (P + L) → Bool := fun u => decide (P ≤ u.val)
    have hval : ∀ w ∈ W, val C (List.ofFn z) w = true := by
      intro w hw
      have hex : ∃ u ∈ orIn (P + L) C w, P ≤ u.val := by
        by_contra hno
        apply hn
        refine ⟨w, hw, ?_⟩
        intro u hu
        by_contra hlt
        exact hno ⟨u, hu, by omega⟩
      obtain ⟨u, hu, hpu⟩ := hex
      exact orIn_value hu z (decide_eq_true hpu)
    obtain ⟨p, l, hpl, hp, hl⟩ := of_decide_eq_true (hsound z hval)
    have hge : P ≤ p.val := by simpa [z] using hp
    omega
  · by_contra hn
    let z : Fin (P + L) → Bool := fun u => decide (u.val < P)
    have hval : ∀ w ∈ W, val C (List.ofFn z) w = true := by
      intro w hw
      have hex : ∃ u ∈ orIn (P + L) C w, u.val < P := by
        by_contra hno
        apply hn
        refine ⟨w, hw, ?_⟩
        intro u hu
        by_contra hge
        exact hno ⟨u, hu, by omega⟩
      obtain ⟨u, hu, hpu⟩ := hex
      exact orIn_value hu z (decide_eq_true hpu)
    obtain ⟨p, l, hpl, hp, hl⟩ := of_decide_eq_true (hsound z hval)
    have hlt : P + l.val < P := by simpa [z] using hl
    omega

end Sharing

namespace CommonLine

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2584.Sharing

lemma centres_forced_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (hf : circuitFun n C = graphFun G ∅) (g h : ℕ)
    (hgand : (gateAt C g).op = GateOp.and)
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = h)
    (hgh : ¬ InCone n C g h) (u v : Fin n)
    (hu : u ∈ singletonInputs n C (n + g))
    (hv : v ∈ singletonInputs n C (n + g))
    (hnone : ∀ w, ¬(G.Adj u w ∧ G.Adj v w))
    (x y : Fin n) (hxy : G.Adj x y)
    (hcover : gateVal n C h (pairInput x y) = true →
      (pairInput x y u || pairInput x y v) = true)
    (haway : (pairInput x y u || pairInput x y v) = false) :
    circuitFun n (forcedCircuit C g) (pairInput x y) = true := by
  apply forcedCircuit_true_of_top_avoid G C hAO hf g hgand (pairInput x y)
  · intro a ha har hav
    have ha' := ha
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha'
    obtain ⟨halen, haand, hbelow⟩ := ha'
    constructor
    · intro he
      subst a
      have husingle := hu
      simp only [singletonInputs, Finset.mem_filter, Finset.mem_univ, true_and] at husingle
      exact G.irrefl ((graphFun_pair G u u).mp (hbelow (pairInput u u) husingle))
    · intro hga
      have honly' : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
          ¬ BelowF G C j → j = h ∨ j = g := by
        intro j hj hjand hjdirty
        exact (honly j hj hjand hjdirty).symm
      obtain ⟨b, hr⟩ := two_dirty_cone_or_frontier G C hAO hTop h g honly' hgh halen haand hga
      have hempty := shared_region_opposite_empty_of_no_common_neighbor G C hAO ha b hr hu hv hnone
      have heq := (empty_top_operand_eq_other_dirty G C hAO hTop g h honly ⟨u, hu⟩
        ha b.rev hempty).2
      have hopposite := and_operand_value hAO halen haand (pairInput x y) hav b.rev
      rw [heq] at hopposite
      have hyes := hcover hopposite
      rw [haway] at hyes
      cases hyes
  · rw [hf]
    exact (graphFun_pair G x y).mpr hxy

lemma overwrite_centres_properties {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C)
    (hf : circuitFun n C = graphFun G ∅) (g h : ℕ)
    (hgand : (gateAt C g).op = GateOp.and)
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = h)
    (hgh : ¬ InCone n C g h) (u v : Fin n)
    (hu : u ∈ singletonInputs n C (n + g))
    (hv : v ∈ singletonInputs n C (n + g))
    (hnone : ∀ w, ¬(G.Adj u w ∧ G.Adj v w))
    (hcover : ∀ x y : Fin n, G.Adj x y → gateVal n C h (pairInput x y) = true →
      (pairInput x y u || pairInput x y v) = true) :
    let D := overwriteCircuit C g ⟨GateOp.or, [u.val, v.val]⟩
    IsAO2 n D ∧ D.size = C.size ∧ circuitFun n D = graphFun G ∅ := by
  let r : Gate := ⟨GateOp.or, [u.val, v.val]⟩
  let D := overwriteCircuit C g r
  have hD : IsAO2 n D := overwriteCircuit_isAO2 hAO g r (Or.inr rfl) (by
    intro i hi
    change i ∈ [u.val, v.val] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega) rfl
  have hrep (x : Fin n → Bool) : replacementVal n C g r x = true →
      val C (List.ofFn x) (n + g) = true := by
    rw [replacementVal_or_inputs, Bool.or_eq_true]
    rintro (hx | hx)
    · exact singleton_input_value hAO hu x hx
    · exact singleton_input_value hAO hv x hx
  refine ⟨hD, overwriteCircuit_size C g r, ?_⟩
  apply circuit_graphFun_eq_of_pair_cover G D hD.1
  · intro x hx
    have hold := overwriteCircuit_fun_le hAO.1 g r hrep x hx
    simpa only [hf] using hold
  · intro x y hxy
    by_cases hc : (pairInput x y u || pairInput x y v) = true
    · have hnew : replacementVal n C g r (pairInput x y) = true := by
        rw [replacementVal_or_inputs]; exact hc
      have hold := hrep (pairInput x y) hnew
      have heq := overwriteCircuit_fun_eq C g r (pairInput x y) (hnew.trans hold.symm)
      change circuitFun n (overwriteCircuit C g r) _ = true
      rw [heq, hf]
      exact (graphFun_pair G x y).mpr hxy
    · have haway := Bool.eq_false_iff.mpr hc
      have hforced := centres_forced_pair G C hAO hTop hf g h hgand honly hgh u v hu hv
        hnone x y hxy (hcover x y hxy) haway
      have hsame : forcedCircuit D g = forcedCircuit C g := by
        simp [D, overwriteCircuit, forcedCircuit, List.set_set]
      apply forcedCircuit_fun_le hD.1 g (pairInput x y)
      rw [hsame]
      exact hforced

lemma pure_operands_cover_by_centres {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hAO : IsAO2 n C) (hfour : NoFourCycle G)
    (h c d : ℕ) (hh : h < C.gates.length) (hhand : (gateAt C h).op = GateOp.and)
    (hinputs : (gateAt C h).inputs = [c, d])
    (hcpure : ∀ k, OrReaches n C c k → (gateAt C k).op = GateOp.or)
    (hdpure : ∀ k, OrReaches n C d k → (gateAt C k).op = GateOp.or)
    (u v : Fin n) (huv : G.Adj u v)
    (hcneigh : ∀ z ∈ orIn n C c, G.Adj v z)
    (hdneigh : ∀ z ∈ orIn n C d, G.Adj u z)
    (hnone : ∀ w, ¬(G.Adj u w ∧ G.Adj v w))
    (x y : Fin n) (hxy : G.Adj x y) (hhval : gateVal n C h (pairInput x y) = true) :
    (pairInput x y u || pairInput x y v) = true := by
  have hcval := and_operand_value hAO hh hhand (pairInput x y) hhval 0
  have hdval := and_operand_value hAO hh hhand (pairInput x y) hhval 1
  simp only [opnd, hinputs] at hcval hdval
  obtain ⟨a, ha, hav⟩ := (pure_or_value_iff hcpure (pairInput x y)).mp hcval
  obtain ⟨b, hb, hbv⟩ := (pure_or_value_iff hdpure (pairInput x y)).mp hdval
  have habne : a ≠ b := by
    intro he
    subst b
    exact hnone a ⟨hdneigh a hb, hcneigh a ha⟩
  have hab : G.Adj a b := by
    rcases (pairInput_true x y a).mp hav with hax | hay
    · rcases (pairInput_true x y b).mp hbv with hbx | hby
      · exact False.elim (habne (hax.trans hbx.symm))
      · rw [hax, hby]; exact hxy
    · rcases (pairInput_true x y b).mp hbv with hbx | hby
      · rw [hay, hbx]; exact hxy.symm
      · exact False.elim (habne (hay.trans hby.symm))
  have hcentres : a = u ∨ b = v := by
    by_cases hau : a = u
    · exact Or.inl hau
    · right
      exact Finset.card_le_one.mp (hfour a u hau) b
        (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hab, hdneigh b hb⟩)
        v (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨(hcneigh a ha).symm, huv⟩)
  rw [Bool.or_eq_true]
  rcases hcentres with rfl | rfl
  · exact Or.inl hav
  · exact Or.inr hbv

lemma common_line_neighborhoods {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (g h c d : ℕ)
    (hh : h < C.gates.length) (hhand : (gateAt C h).op = GateOp.and)
    (hinputs : (gateAt C h).inputs = [c, d])
    (u v : Fin n) (hu : u ∈ singletonInputs n C (n + g))
    (hv : v ∈ singletonInputs n C (n + g))
    (huc : u ∈ orIn n C c) (hvd : v ∈ orIn n C d)
    (hsound : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateVal n C h x = true → graphFun G ∅ x = true) :
    G.Adj u v ∧ (∀ z ∈ orIn n C c, G.Adj v z) ∧ (∀ z ∈ orIn n C d, G.Adj u z) := by
  have hblock (a b : Fin n) (ha : a ∈ orIn n C c) (hb : b ∈ orIn n C d)
      (hgv : gateVal n C g (pairInput a b) = true) : G.Adj a b := by
    apply (graphFun_pair G a b).mp
    apply hsound (pairInput a b) hgv
    apply (val_and (by simp) hh hhand).mpr
    intro w hw
    refine ⟨hAO.2.1 h hh w hw, ?_⟩
    rw [hinputs] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact orIn_value ha _ (pairInput_left a b)
    · exact orIn_value hb _ (pairInput_right a b)
  refine ⟨hblock u v huc hvd (singleton_input_pair_value hAO.1 hu v), ?_, ?_⟩
  · intro z hz
    apply SimpleGraph.Adj.symm
    apply hblock z v hz hvd
    exact singleton_input_value hAO hv _ (pairInput_right z v)
  · intro z hz
    exact hblock u z huc hz (singleton_input_pair_value hAO.1 hu z)


lemma least_common_line_replacement {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hne : G.edgeFinset.Nonempty)
    (hL : IsLeastAO G C) (hTop : TopForm G C) (hfour : NoFourCycle G)
    (g h c d : ℕ) (hgand : (gateAt C g).op = GateOp.and)
    (hh : h < C.gates.length) (hhand : (gateAt C h).op = GateOp.and)
    (hinputs : (gateAt C h).inputs = [c, d])
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = h)
    (hgh : ¬ InCone n C g h)
    (hcpure : ∀ k, OrReaches n C c k → (gateAt C k).op = GateOp.or)
    (hdpure : ∀ k, OrReaches n C d k → (gateAt C k).op = GateOp.or)
    (u v : Fin n) (hu : u ∈ singletonInputs n C (n + g))
    (hv : v ∈ singletonInputs n C (n + g))
    (huc : u ∈ orIn n C c) (hvd : v ∈ orIn n C d)
    (hnone : ∀ w, ¬(G.Adj u w ∧ G.Adj v w))
    (hsound : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateVal n C h x = true → graphFun G ∅ x = true) :
    ∃ E : Circuit, IsLeastAO G E ∧ E.size = C.size ∧ PEqualNP.ReadK.IsReadK n E 2 := by
  obtain ⟨huv, hcneigh, hdneigh⟩ := common_line_neighborhoods G C hL.1 g h c d hh hhand
    hinputs u v hu hv huc hvd hsound
  have hcover := pure_operands_cover_by_centres G C hL.1 hfour h c d hh hhand hinputs
    hcpure hdpure u v huv hcneigh hdneigh hnone
  let r : Gate := ⟨GateOp.or, [u.val, v.val]⟩
  let D := overwriteCircuit C g r
  obtain ⟨hD, hsize, hfun⟩ := overwrite_centres_properties G C hL.1 hTop hL.2.1 g h hgand
    honly hgh u v hu hv hnone hcover
  have hleast : IsLeastAO G D := by
    refine ⟨hD, hfun, ?_⟩
    intro E hE hEF
    have hh := hL.2.2 E hE hEF
    change D.size ≤ E.size
    exact (overwriteCircuit_size C g r).le.trans hh
  have hrep (x : Fin n → Bool) : replacementVal n C g r x = true →
      val C (List.ofFn x) (n + g) = true := by
    rw [replacementVal_or_inputs, Bool.or_eq_true]
    rintro (hx | hx)
    · exact singleton_input_value hL.1 hu x hx
    · exact singleton_input_value hL.1 hv x hx
  have hjunk := overwrite_or_junk_card_le_one G C hL.1.1 g h r rfl hrep honly
  obtain ⟨E, hE, hES, hread⟩ := TopNormalize.least_one_dirty_replacement G D hne hleast hjunk
  exact ⟨E, hE, hES.trans hsize, hread⟩

end CommonLine

namespace RestrictedMin

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2584.Sharing
open PEqualNP.Outside.L_meta_2584.DoublePoint
open PEqualNP.Outside.L_meta_2584.TopAndCount

lemma least_topForm_min_and_bounded_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (hne : G.edgeFinset.Nonempty)
    (r : ℕ) (hJ : (junk G C).card ≤ r) :
    ∃ D : Circuit, IsLeastAO G D ∧ D.size = C.size ∧ TopForm G D ∧ (junk G D).card ≤ r ∧
      ∀ E : Circuit, IsAO2 n E → circuitFun n E = graphFun G ∅ → E.size = D.size →
        (junk G E).card ≤ r → andCount D ≤ andCount E := by
  classical
  let p : ℕ → Prop := fun k => ∃ D : Circuit,
    IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧
      (junk G D).card ≤ r ∧ andCount D = k
  have hp : ∃ k, p k := ⟨andCount C, C, hC.1, hC.2.1, rfl, hJ, rfl⟩
  obtain ⟨A, hA, hAf, hAs, hAJ, hAk⟩ := Nat.find_spec hp
  have hAL : IsLeastAO G A := by
    refine ⟨hA, hAf, ?_⟩
    intro E hE hEf
    rw [hAs]
    exact hC.2.2 E hE hEf
  obtain ⟨D, hD, hDS, hDJ, hDA, hDT⟩ := least_to_topForm_andCount G A hne hAL
  refine ⟨D, hD, hDS.trans hAs, hDT, hDJ.le.trans hAJ, ?_⟩
  intro E hE hEf hES hEJ
  rw [hDA, hAk]
  exact Nat.find_min' hp ⟨E, hE, hEf, hES.trans (hDS.trans hAs), hEJ, rfl⟩

lemma replace_pure_point_and_double_junk {P L : ℕ}
    (G : SimpleGraph (Fin (P + L))) [DecidableRel G.Adj]
    (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hAO : IsAO2 (P + L) C)
    (hf : circuitFun (P + L) C = fun x =>
      decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    {a p q : ℕ} (ha : a < C.gates.length)
    (hand : (gateAt C a).op = GateOp.and) (hin : (gateAt C a).inputs = [p, q])
    (hpure : ∀ g, OrReaches (P + L) C p g → (gateAt C g).op = GateOp.or)
    (qpure : ∀ g, OrReaches (P + L) C q g → (gateAt C g).op = GateOp.or)
    (hsidep : ∀ t ∈ orIn (P + L) C p, t.val < P)
    (hsideq : ∀ t ∈ orIn (P + L) C q, t.val < P)
    (u v : Fin (P + L))
    (hmeet : orIn (P + L) C p ∩ orIn (P + L) C q = {u, v}) :
    ∃ D : Circuit, IsAO2 (P + L) D ∧ D.size = C.size ∧
      andCount D + 1 = andCount C ∧ (junk G D).card ≤ (junk G C).card ∧
      circuitFun (P + L) D = fun x =>
        decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true) := by
  let r : Gate := ⟨GateOp.or, [u.val, v.val]⟩
  let D := overwriteCircuit C a r
  have hD : IsAO2 (P + L) D := overwriteCircuit_isAO2 hAO a r (Or.inr rfl) (by
    intro i hi
    change i ∈ [u.val, v.val] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega) rfl
  have hu : u ∈ orIn (P + L) C p ∩ orIn (P + L) C q := by rw [hmeet]; simp
  have hv : v ∈ orIn (P + L) C p ∩ orIn (P + L) C q := by rw [hmeet]; simp
  have hrep (x : Fin (P + L) → Bool) :
      replacementVal (P + L) C a r x = true → val C (List.ofFn x) (P + L + a) = true := by
    rw [replacementVal_point_or, Bool.or_eq_true]
    intro hx
    rcases hx with hx | hx
    · exact common_or_input_implies_and hAO.2.1 ha hand hin hu x hx
    · exact common_or_input_implies_and hAO.2.1 ha hand hin hv x hx
  refine ⟨D, hD, overwriteCircuit_size C a r, ?_, ?_, ?_⟩
  · exact andCount_set_or ha hand r rfl
  · exact (Finset.card_le_card (overwrite_or_junk_subset G C hAO.1 a r rfl hrep)).trans
      (Finset.card_le_card (Finset.erase_subset a (junk G C)))
  · apply incidence_eq_of_pair_cover I (circuitFun (P + L) D)
    · intro x y hxy
      exact val_monotone hD.1 x y hxy D.output
    · intro x hx
      have h := overwriteCircuit_fun_le hAO.1 a r hrep x hx
      simpa only [hf] using h
    · intro x y hxy
      have hval := pure_point_and_double_pair_value hAO.2.1 ha hand hin hpure qpure
        hsidep hsideq u v hmeet x y
      have heq := overwriteCircuit_fun_eq C a r (pairInput (Fin.castAdd L x) (Fin.natAdd P y))
        (by rw [replacementVal_point_or]; exact hval.symm)
      change circuitFun (P + L) (overwriteCircuit C a r) _ = true
      rw [heq, hf]
      exact decide_eq_true ⟨x, y, hxy, pairInput_left _ _, pairInput_right _ _⟩

lemma least_and_pure_point_intersection_card_bounded_junk {P L : ℕ}
    (G : SimpleGraph (Fin (P + L))) [DecidableRel G.Adj] (r : ℕ)
    (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hAO : IsAO2 (P + L) C)
    (hf : circuitFun (P + L) C = fun x =>
      decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true))
    (hJ : (junk G C).card ≤ r)
    (hmin : ∀ D : Circuit, IsAO2 (P + L) D →
      circuitFun (P + L) D = (fun x =>
        decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) →
      C.size ≤ D.size)
    (hminAnd : ∀ D : Circuit, IsAO2 (P + L) D →
      circuitFun (P + L) D = (fun x =>
        decide (∃ p l, I p l ∧ x (Fin.castAdd L p) = true ∧ x (Fin.natAdd P l) = true)) →
      D.size = C.size → (junk G D).card ≤ r → andCount C ≤ andCount D)
    {a p q : ℕ} (ha : a < C.gates.length)
    (hand : (gateAt C a).op = GateOp.and) (hin : (gateAt C a).inputs = [p, q])
    (hpure : ∀ g, OrReaches (P + L) C p g → (gateAt C g).op = GateOp.or)
    (qpure : ∀ g, OrReaches (P + L) C q g → (gateAt C g).op = GateOp.or)
    (hsidep : ∀ t ∈ orIn (P + L) C p, t.val < P)
    (hsideq : ∀ t ∈ orIn (P + L) C q, t.val < P) :
    3 ≤ (orIn (P + L) C p ∩ orIn (P + L) C q).card := by
  have htwo := MinimumPure.least_pure_point_and_intersection_card I C hAO hf hmin ha hand hin
    hpure qpure hsidep hsideq
  by_contra hnot
  have hcard : (orIn (P + L) C p ∩ orIn (P + L) C q).card = 2 := by omega
  obtain ⟨u, v, huv, hmeet⟩ := Finset.card_eq_two.mp hcard
  obtain ⟨D, hD, hsize, hcount, hJD, hfun⟩ := replace_pure_point_and_double_junk G I C hAO hf ha hand hin
    hpure qpure hsidep hsideq u v hmeet
  have h := hminAnd D hD hfun hsize (hJD.trans hJ)
  omega


end RestrictedMin

namespace TwoJunkStructure

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma four_clause_unbalanced_signature (A B : Fin 4 → Bool)
    (hpair : ∀ i, A i = true ∨ B i = true)
    (hnopoint : ∃ i, A i = false) (hnoline : ∃ i, B i = false)
    (hnobalanced : ¬∃ S : Finset (Fin 4), S.card = 2 ∧
      (∀ i ∈ S, A i = true) ∧ ∀ i ∉ S, B i = true) :
    (∀ i, A i = !B i) ∧
      ((Finset.univ.filter fun i => A i = true).card = 1 ∨
       (Finset.univ.filter fun i => A i = true).card = 3) := by
  revert A B
  decide

end TwoJunkStructure

namespace FlatRead

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership PEqualNP.ReadK
open PEqualNP.Outside.L_meta_2584.Sharing

lemma words_gate_pair {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    words n C (n + j) = wordOp (gateAt C j).op
      [words n C (opnd C j 0), words n C (opnd C j 1)] := by
  let k : Fin C.size := ⟨j, hj⟩
  have hrow : gateAt C j = row C k := List.getD_eq_getElem _ _ hj
  simpa only [outWire, operand, ← hrow, opnd] using words_gate hAO k

lemma word_and_inputs {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j a b : ℕ} (hj : j < C.gates.length) (hjand : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [a, b]) {s t : List ℕ}
    (hs : s ∈ words n C a) (ht : t ∈ words n C b) : s ++ t ∈ words n C (n + j) := by
  rw [words_gate_pair hAO hj, hjand]
  have he : wordOp GateOp.and [words n C (opnd C j 0), words n C (opnd C j 1)] =
      {w | ∃ s ∈ words n C a, ∃ t ∈ words n C b, w = s ++ t} := by
    simp [wordOp, opnd, hin]
  rw [he]
  exact ⟨s, hs, t, ht, rfl⟩

lemma word_or_step {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {u v : ℕ} (hst : OrStep n C u v) {t : List ℕ}
    (ht : t ∈ words n C v) : t ∈ words n C u := by
  obtain ⟨j, hj, rfl, hjor, hvin, hvlt⟩ := hst
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hj))
  rw [words_gate_pair hAO hj, hjor]
  have he : wordOp GateOp.or [words n C (opnd C j 0), words n C (opnd C j 1)] =
      words n C a ∪ words n C b := by simp [wordOp, opnd, hin]
  rw [he]
  rw [hin] at hvin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hvin
  rcases hvin with rfl | rfl
  · exact Or.inl ht
  · exact Or.inr ht

lemma word_or_path {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {u v : ℕ} (hr : Relation.ReflTransGen (OrStep n C) u v) {t : List ℕ}
    (ht : t ∈ words n C v) : t ∈ words n C u := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact ht
  | head hs hr ih => exact word_or_step hAO hs ih

lemma singleton_word_of_orIn {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {w : ℕ} {u : Fin n} (hu : u ∈ orIn n C w) : [u.val] ∈ words n C w := by
  apply word_or_path hAO (mem_orIn_reach u hu)
  rw [words_input C u.isLt]
  rfl

lemma explicit_four_clause_word {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (g h t a b c d s r : ℕ)
    (hg : g < C.gates.length) (hh : h < C.gates.length) (ht : t < C.gates.length)
    (hgand : (gateAt C g).op = GateOp.and) (hhand : (gateAt C h).op = GateOp.and)
    (htand : (gateAt C t).op = GateOp.and)
    (hginputs : (gateAt C g).inputs = [a, b])
    (hhinputs : (gateAt C h).inputs = [c, d])
    (htinputs : (gateAt C t).inputs = [s, r])
    (hsg : OrReaches n C s g) (hrh : OrReaches n C r h)
    (hout : OrReaches n C C.output t)
    (u0 u1 u2 u3 : Fin n)
    (hu0 : u0 ∈ orIn n C a) (hu1 : u1 ∈ orIn n C b)
    (hu2 : u2 ∈ orIn n C c) (hu3 : u3 ∈ orIn n C d) :
    [u0.val, u1.val, u2.val, u3.val] ∈ words n C C.output := by
  have hgw := word_and_inputs hAO hg hgand hginputs
    (singleton_word_of_orIn hAO hu0) (singleton_word_of_orIn hAO hu1)
  have hhw := word_and_inputs hAO hh hhand hhinputs
    (singleton_word_of_orIn hAO hu2) (singleton_word_of_orIn hAO hu3)
  have hsw := word_or_path hAO (orReaches_reach g s hsg).1 hgw
  have hrw := word_or_path hAO (orReaches_reach h r hrh).1 hhw
  have htw := word_and_inputs hAO ht htand htinputs hsw hrw
  exact word_or_path hAO (orReaches_reach t C.output hout).1 htw

end FlatRead

namespace FlatRead

lemma fin_four_card_select (S : Finset (Fin 4)) :
    S.card = (if 0 ∈ S then 1 else 0) + (if 1 ∈ S then 1 else 0) +
      (if 2 ∈ S then 1 else 0) + (if 3 ∈ S then 1 else 0) := by
  revert S
  decide

lemma balanced_four_choice_counts (S : Finset (Fin 4)) (hS : S.card = 2)
    (x y : ℕ) (hxy : x ≠ y) :
    let t := [if 0 ∈ S then x else y, if 1 ∈ S then x else y,
      if 2 ∈ S then x else y, if 3 ∈ S then x else y]
    t.count x ≤ 2 ∧ t.count y ≤ 2 := by
  have hc := fin_four_card_select S
  by_cases h0 : (0 : Fin 4) ∈ S <;>
    by_cases h1 : (1 : Fin 4) ∈ S <;>
    by_cases h2 : (2 : Fin 4) ∈ S <;>
    by_cases h3 : (3 : Fin 4) ∈ S <;>
    simp_all [List.count_cons, Ne.symm hxy]

end FlatRead

namespace FlatRead

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership PEqualNP.ReadK
open PEqualNP.Outside.L_meta_2584.Sharing
open PEqualNP.Outside.L_meta_2584.TwoJunkStructure

lemma explicit_four_clause_balanced_read {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (g h t s r : ℕ) (w : Fin 4 → ℕ)
    (hg : g < C.gates.length) (hh : h < C.gates.length) (ht : t < C.gates.length)
    (hgand : (gateAt C g).op = GateOp.and) (hhand : (gateAt C h).op = GateOp.and)
    (htand : (gateAt C t).op = GateOp.and)
    (hginputs : (gateAt C g).inputs = [w 0, w 1])
    (hhinputs : (gateAt C h).inputs = [w 2, w 3])
    (htinputs : (gateAt C t).inputs = [s, r])
    (hsg : OrReaches n C s g) (hrh : OrReaches n C r h)
    (hout : OrReaches n C C.output t)
    (x y : Fin n) (hxy : x ≠ y) (S : Finset (Fin 4)) (hS : S.card = 2)
    (hx : ∀ i ∈ S, x ∈ orIn n C (w i))
    (hy : ∀ i ∉ S, y ∈ orIn n C (w i)) : readsAtMost C n [x.val, y.val] 2 = true := by
  let u : Fin 4 → Fin n := fun i => if i ∈ S then x else y
  have hu : ∀ i, u i ∈ orIn n C (w i) := by
    intro i
    by_cases hi : i ∈ S
    · simpa [u, hi] using hx i hi
    · simpa [u, hi] using hy i hi
  have huv (i : Fin 4) : (u i).val = if i ∈ S then x.val else y.val := by
    by_cases hi : i ∈ S <;> simp [u, hi]
  let word : List ℕ := [if 0 ∈ S then x.val else y.val, if 1 ∈ S then x.val else y.val,
    if 2 ∈ S then x.val else y.val, if 3 ∈ S then x.val else y.val]
  have hword : word ∈ words n C C.output := by
    have hw := explicit_four_clause_word hAO g h t (w 0) (w 1) (w 2) (w 3) s r
      hg hh ht hgand hhand htand hginputs hhinputs htinputs hsg hrh hout
      (u 0) (u 1) (u 2) (u 3) (hu 0) (hu 1) (hu 2) (hu 3)
    simpa only [huv] using hw
  have hxyval : x.val ≠ y.val := fun he => hxy (Fin.ext he)
  have hcounts : word.count x.val ≤ 2 ∧ word.count y.val ≤ 2 :=
    balanced_four_choice_counts S hS x.val y.val hxyval
  apply (reads_two_iff_word hAO [x.val, y.val]).mpr
  refine ⟨word, hword, ?_, ?_⟩
  · intro i hi
    have hchoice (j : Fin 4) : (if j ∈ S then x.val else y.val) ∈ [x.val, y.val] := by
      split_ifs <;> simp
    simp only [word, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hchoice 0
    · exact hchoice 1
    · exact hchoice 2
    · exact hchoice 3
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hcounts.1
    · exact hcounts.2

lemma explicit_four_clause_signature {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (g h t s r : ℕ) (w : Fin 4 → ℕ)
    (hg : g < C.gates.length) (hh : h < C.gates.length) (ht : t < C.gates.length)
    (hgand : (gateAt C g).op = GateOp.and) (hhand : (gateAt C h).op = GateOp.and)
    (htand : (gateAt C t).op = GateOp.and)
    (hginputs : (gateAt C g).inputs = [w 0, w 1])
    (hhinputs : (gateAt C h).inputs = [w 2, w 3])
    (htinputs : (gateAt C t).inputs = [s, r])
    (hsg : OrReaches n C s g) (hrh : OrReaches n C r h)
    (hout : OrReaches n C C.output t)
    (x y : Fin n) (hxy : x ≠ y)
    (hpair : ∀ i, x ∈ orIn n C (w i) ∨ y ∈ orIn n C (w i))
    (hxfalse : circuitFun n C (pairInput x x) = false)
    (hyfalse : circuitFun n C (pairInput y y) = false)
    (hnoread : readsAtMost C n [x.val, y.val] 2 = false) :
    (∀ i, (x ∈ orIn n C (w i)) ↔ y ∉ orIn n C (w i)) ∧
      ((Finset.univ.filter fun i => x ∈ orIn n C (w i)).card = 1 ∨
       (Finset.univ.filter fun i => x ∈ orIn n C (w i)).card = 3) := by
  classical
  let A : Fin 4 → Bool := fun i => decide (x ∈ orIn n C (w i))
  let B : Fin 4 → Bool := fun i => decide (y ∈ orIn n C (w i))
  have hmissing (u : Fin n) (hufalse : circuitFun n C (pairInput u u) = false) :
      ∃ i, u ∉ orIn n C (w i) := by
    by_contra hn
    have hall : ∀ i, u ∈ orIn n C (w i) := by simpa only [not_exists, not_not] using hn
    have hw := explicit_four_clause_word hAO g h t (w 0) (w 1) (w 2) (w 3) s r
      hg hh ht hgand hhand htand hginputs hhinputs htinputs hsg hrh hout
      u u u u (hall 0) (hall 1) (hall 2) (hall 3)
    have hval : circuitValue C (pairInput u u) C.output = true := by
      apply (value_eq_terms hAO (pairInput u u) C.output).mpr
      refine ⟨[u.val, u.val, u.val, u.val], hw, ?_⟩
      intro j hj
      have hju : j = u.val := by simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using hj
      exact ⟨u, hju.symm, pairInput_left u u⟩
    have htrue : circuitFun n C (pairInput u u) = true := hval
    rw [hufalse] at htrue
    cases htrue
  have hA : ∃ i, A i = false := by
    obtain ⟨i, hi⟩ := hmissing x hxfalse
    exact ⟨i, by simp [A, hi]⟩
  have hB : ∃ i, B i = false := by
    obtain ⟨i, hi⟩ := hmissing y hyfalse
    exact ⟨i, by simp [B, hi]⟩
  have hAB : ∀ i, A i = true ∨ B i = true := by
    intro i
    simpa only [A, B, decide_eq_true_eq] using hpair i
  have hnobalanced : ¬∃ S : Finset (Fin 4), S.card = 2 ∧
      (∀ i ∈ S, A i = true) ∧ ∀ i ∉ S, B i = true := by
    rintro ⟨S, hS, hx, hy⟩
    have hread := explicit_four_clause_balanced_read hAO g h t s r w hg hh ht hgand hhand htand
      hginputs hhinputs htinputs hsg hrh hout x y hxy S hS
      (fun i hi => of_decide_eq_true (hx i hi)) (fun i hi => of_decide_eq_true (hy i hi))
    rw [hnoread] at hread
    cases hread
  obtain ⟨hcompl, hcard⟩ := four_clause_unbalanced_signature A B hAB hA hB hnobalanced
  refine ⟨?_, ?_⟩
  · intro i
    have hc := hcompl i
    by_cases hx : x ∈ orIn n C (w i) <;>
      by_cases hy : y ∈ orIn n C (w i) <;> simpa [A, B, hx, hy] using hc
  · simpa only [A, decide_eq_true_eq] using hcard

end FlatRead

namespace FlatRead

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership PEqualNP.ReadK
open PEqualNP.Outside.L_meta_2584.Sharing

lemma explicit_four_pure_clause_signature {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C)
    (hf : circuitFun n C = graphFun G ∅)
    (g h t s r : ℕ) (w : Fin 4 → ℕ)
    (hg : g < C.gates.length) (hh : h < C.gates.length) (ht : t < C.gates.length)
    (hgand : (gateAt C g).op = GateOp.and) (hhand : (gateAt C h).op = GateOp.and)
    (htand : (gateAt C t).op = GateOp.and)
    (hginputs : (gateAt C g).inputs = [w 0, w 1])
    (hhinputs : (gateAt C h).inputs = [w 2, w 3])
    (htinputs : (gateAt C t).inputs = [s, r])
    (hsg : OrReaches n C s g) (hrh : OrReaches n C r h)
    (hout : OrReaches n C C.output t)
    (hpure : ∀ i k, OrReaches n C (w i) k → (gateAt C k).op = GateOp.or)
    (x y : Fin n) (hxy : G.Adj x y)
    (hgv : gateVal n C g (pairInput x y) = true)
    (hhv : gateVal n C h (pairInput x y) = true)
    (hnoread : readsAtMost C n [x.val, y.val] 2 = false) :
    (∀ i, (x ∈ orIn n C (w i)) ↔ y ∉ orIn n C (w i)) ∧
      ((Finset.univ.filter fun i => x ∈ orIn n C (w i)).card = 1 ∨
       (Finset.univ.filter fun i => x ∈ orIn n C (w i)).card = 3) := by
  have hclause (i : Fin 4) : val C (List.ofFn (pairInput x y)) (w i) = true := by
    fin_cases i
    · simpa [opnd, hginputs] using and_operand_value hAO hg hgand (pairInput x y) hgv 0
    · simpa [opnd, hginputs] using and_operand_value hAO hg hgand (pairInput x y) hgv 1
    · simpa [opnd, hhinputs] using and_operand_value hAO hh hhand (pairInput x y) hhv 0
    · simpa [opnd, hhinputs] using and_operand_value hAO hh hhand (pairInput x y) hhv 1
  have hpair : ∀ i, x ∈ orIn n C (w i) ∨ y ∈ orIn n C (w i) := by
    intro i
    obtain ⟨u, hu, huv⟩ := (pure_or_value_iff (hpure i) (pairInput x y)).mp (hclause i)
    rcases (pairInput_true x y u).mp huv with rfl | rfl
    · exact Or.inl hu
    · exact Or.inr hu
  have hsingle (u : Fin n) : circuitFun n C (pairInput u u) = false := by
    rw [hf]
    cases hval : graphFun G ∅ (pairInput u u) with
    | false => rfl
    | true => exact False.elim (G.irrefl ((graphFun_pair G u u).mp hval))
  exact explicit_four_clause_signature hAO g h t s r w hg hh ht hgand hhand htand
    hginputs hhinputs htinputs hsg hrh hout x y hxy.ne hpair (hsingle x) (hsingle y) hnoread

end FlatRead

namespace AliasSurgery
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2584.GuardedErase PEqualNP.Outside.L_meta_2584.TopNormalize
open PEqualNP.Outside.L_meta_2584.Sharing

def repairBody (n : ℕ) (pre post : List Gate) (l p d o : ℕ) : Circuit :=
  ⟨pre ++ ⟨GateOp.and, [p, d]⟩ :: post.map (Tc (n + pre.length + 1) l),
    rn (n + pre.length + 1) l o⟩

lemma repairBody_size (n : ℕ) (pre post : List Gate) (l p d o : ℕ) :
    (repairBody n pre post l p d o).size = pre.length + 1 + post.length := by
  simp [repairBody, Circuit.size]
  omega

lemma repair_eq_append (n : ℕ) (pre post : List Gate) (l p d o : ℕ) :
    repairCircuit n pre post l p d o =
      appendOr n (repairBody n pre post l p d o)
        (rn (n + pre.length + 1) l o) (n + pre.length) := rfl

lemma rn_rho_wire (n r l j : ℕ) (hl : l < n + r) :
    rn (n + r) l (n + rho r j) = n + j := by
  unfold rn rho
  split_ifs <;> omega

lemma Tc_getD_op (post : List Gate) (k l j : ℕ) :
    ((post.map (Tc k l)).getD j ⟨.or, []⟩).op = (post.getD j ⟨.or, []⟩).op := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases post[j]? <;> rfl

lemma repair_gateOp (n : ℕ) (C : Circuit) (pre post : List Gate) (c : Gate)
    (l p d : ℕ) (hC : C.gates = pre ++ [c, ⟨.and, [n + pre.length, d]⟩] ++ post)
    (j : ℕ) (hj : j < pre.length + 1 + post.length) (hne : j ≠ pre.length) :
    (gateAt (repairCircuit n pre post l p d C.output) j).op =
      (gateAt C (rho (pre.length + 1) j)).op := by
  rw [repair_eq_append]
  have hB : j < (repairBody n pre post l p d C.output).gates.length := by
    change j < (repairBody n pre post l p d C.output).size
    rw [repairBody_size]
    exact hj
  simp only [gateAt, appendOr, List.getD_append _ _ _ _ hB]
  by_cases hlt : j < pre.length
  · have hr : rho (pre.length + 1) j = j := by simp [rho]; omega
    rw [hr, hC]
    simp only [repairBody, List.append_assoc, List.getD_append _ _ _ _ hlt]
  · have hr : rho (pre.length + 1) j = j + 1 := by simp [rho]; omega
    rw [hr, hC]
    change ((pre ++ ⟨GateOp.and, [p, d]⟩ :: post.map (Tc (n + pre.length + 1) l)).getD j ⟨.or, []⟩).op = _
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hj1 : j - pre.length = (j - pre.length - 1) + 1 := by omega
    rw [hj1]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
    have hold : (pre ++ [c, ⟨GateOp.and, [n + pre.length, d]⟩] ++ post).getD (j + 1) ⟨.or, []⟩ =
        post.getD (j - pre.length - 1) ⟨.or, []⟩ := by
      rw [List.append_assoc, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by simp; omega)]
      congr 1
      simp only [List.length_cons, List.length_nil]
      omega
    change ((post.map (Tc (n + pre.length + 1) l)).getD (j - pre.length - 1) ⟨.or, []⟩).op =
      ((pre ++ [c, ⟨GateOp.and, [n + pre.length, d]⟩] ++ post).getD (j + 1) ⟨.or, []⟩).op
    rw [hold]
    exact Tc_getD_op post _ _ _

lemma repair_last_op (n : ℕ) (pre post : List Gate) (l p d o : ℕ) :
    (gateAt (repairCircuit n pre post l p d o) (pre.length + 1 + post.length)).op = GateOp.or := by
  rw [repair_eq_append, ← repairBody_size n pre post l p d o]
  simp [gateAt, appendOr, Circuit.size]

lemma repair_gate_before_append (n : ℕ) (pre post : List Gate) (l p d o j : ℕ)
    (hj : j < pre.length + 1 + post.length) (x : Fin n → Bool) :
    gateVal n (repairCircuit n pre post l p d o) j x =
      gateVal n (repairBody n pre post l p d o) j x := by
  rw [repair_eq_append]
  let B := repairBody n pre post l p d o
  change val (appendOr n B _ _) (List.ofFn x) (n + j) = val B (List.ofFn x) (n + j)
  exact MinimumPure.prefix_wire_value (C := appendOr n B _ _) (pre := B.gates)
    (post := [⟨.or, [rn (n + pre.length + 1) l o, n + pre.length]⟩]) rfl x
    (by change n + j < n + B.size; dsimp [B]; rw [repairBody_size]; omega)


lemma repair_renamed_private (n : ℕ) (pre post : List Gate) (l : ℕ)
    (hl : l < n + pre.length)
    (hprivate : ∀ g ∈ post, ∀ i ∈ g.inputs, i ≠ n + pre.length) :
    ∀ g ∈ post.map (Tc (n + pre.length + 1) l), ∀ i ∈ g.inputs,
      i ≠ n + pre.length := by
  intro g hg i hi
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hi
  have hne := hprivate g' hg' i' hi'
  unfold rn
  split_ifs <;> omega

lemma repairBody_gate_le (n : ℕ) (C : Circuit) (pre post : List Gate) (c : Gate)
    (l p d : ℕ) (hC : C.gates = pre ++ [c, ⟨.and, [n + pre.length, d]⟩] ++ post)
    (hAO : IsAO2 n C) (hl : l < n + pre.length)
    (hprivate : ∀ g ∈ post, ∀ i ∈ g.inputs, i ≠ n + pre.length)
    (hdom : ∀ x : Fin n → Bool, (wf (pre ++ [c]) (List.ofFn x)).getD l false = true →
      GateOp.and.eval ([n + pre.length, d].map fun i =>
        (wf (pre ++ [c]) (List.ofFn x)).getD i false) = true)
    (j : ℕ) (hne : j ≠ pre.length) (x : Fin n → Bool) :
    gateVal n (repairBody n pre post l p d C.output) j x = true →
      gateVal n C (rho (pre.length + 1) j) x = true := by
  let tail := post.map (Tc (n + pre.length + 1) l)
  have hp := repair_renamed_private n pre post l hl hprivate
  have hBA : circuitFun n ⟨pre ++ ⟨.and, [p, d]⟩ :: tail, n + j⟩ =
      circuitFun n ⟨pre ++ c :: tail, n + j⟩ :=
    (replace_unused_semantics n pre tail c ⟨.and, [p, d]⟩ (n + j) (by omega) hp).symm
  let Cj : Circuit := ⟨C.gates, n + rho (pre.length + 1) j⟩
  have hCj : Cj.gates = (pre ++ [c]) ++ ⟨.and, [n + pre.length, d]⟩ :: post := by
    simpa [Cj, List.append_assoc] using hC
  have hAOj : IsAO2 n Cj := hAO
  have hle := (alias_spec n Cj (pre ++ [c]) post ⟨.and, [n + pre.length, d]⟩ l
    hCj hAOj (by simp; omega) hdom).2.2.1
  intro hv
  have hval : circuitFun n ⟨pre ++ c :: tail, n + j⟩ x = true := by
    rw [← hBA]
    exact hv
  apply hle x
  have he := rn_rho_wire n (pre.length + 1) l j (by omega)
  simpa [aliasCircuit, Cj, tail, List.append_assoc, he, Nat.add_assoc] using hval

lemma repair_star_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pre post : List Gate) (l p d o : ℕ)
    (hstar : ∀ x : Fin n → Bool,
      (wf pre (List.ofFn x)).getD p false = true →
      (wf pre (List.ofFn x)).getD d false = true → graphFun G ∅ x = true) :
    BelowF G (repairCircuit n pre post l p d o) pre.length := by
  intro x hv
  rw [repair_gate_before_append n pre post l p d o pre.length (by omega)] at hv
  have he := MinimumPure.prefix_gate_value
    (C := repairBody n pre post l p d o)
    (pre := pre) (post := post.map (Tc (n + pre.length + 1) l))
    (g := ⟨.and, [p, d]⟩) rfl x
  rw [he] at hv
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true] at hv
  exact hstar x hv.1 hv.2


lemma repair_junk_card_le_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (pre post : List Gate) (c : Gate) (l p d g : ℕ)
    (hC : C.gates = pre ++ [c, ⟨.and, [n + pre.length, d]⟩] ++ post)
    (hAO : IsAO2 n C) (hl : l < n + pre.length)
    (hprivate : ∀ r ∈ post, ∀ i ∈ r.inputs, i ≠ n + pre.length)
    (hdom : ∀ x : Fin n → Bool, (wf (pre ++ [c]) (List.ofFn x)).getD l false = true →
      GateOp.and.eval ([n + pre.length, d].map fun i =>
        (wf (pre ++ [c]) (List.ofFn x)).getD i false) = true)
    (hstar : ∀ x : Fin n → Bool,
      (wf pre (List.ofFn x)).getD p false = true →
      (wf pre (List.ofFn x)).getD d false = true → graphFun G ∅ x = true)
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = pre.length + 1) :
    (junk G (repairCircuit n pre post l p d C.output)).card ≤ 1 := by
  let D := repairCircuit n pre post l p d C.output
  have hlen : D.gates.length = pre.length + 1 + post.length + 1 := by
    simp [D, repairCircuit_gates]
    omega
  have hstar' := repair_star_below G pre post l p d C.output hstar
  have hmap : ∀ j ∈ junk G D, rho (pre.length + 1) j = g := by
    intro j hj
    have hj' := hj
    simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hj'
    obtain ⟨hjlen, hjand, _, x, hjval, hxfalse⟩ := hj'
    have hjlast : j ≠ pre.length + 1 + post.length := by
      intro he
      subst j
      rw [repair_last_op] at hjand
      cases hjand
    have hjsmall : j < pre.length + 1 + post.length := by omega
    have hjne : j ≠ pre.length := by
      intro he
      subst j
      have hv := hstar' x hjval
      rw [hxfalse] at hv
      cases hv
    have hidx : rho (pre.length + 1) j < C.gates.length := by
      apply rho_lt (pre.length + 1) j C.gates.length
      · rw [hC]
        simp
      · rw [hC]
        simp
        omega
    have hand : (gateAt C (rho (pre.length + 1) j)).op = GateOp.and := by
      rw [← repair_gateOp n C pre post c l p d hC j hjsmall hjne]
      exact hjand
    have hvalue : gateVal n C (rho (pre.length + 1) j) x = true := by
      apply repairBody_gate_le n C pre post c l p d hC hAO hl hprivate hdom j hjne x
      rw [← repair_gate_before_append n pre post l p d C.output j hjsmall]
      exact hjval
    have hdirty : ¬ BelowF G C (rho (pre.length + 1) j) := by
      intro hb
      have hf := hb x hvalue
      rw [hxfalse] at hf
      cases hf
    exact (honly _ hidx hand hdirty).resolve_right (rho_ne (pre.length + 1) j)
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact rho_inj (pre.length + 1) ((hmap a ha).trans (hmap b hb).symm)

lemma least_repair_read_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (pre post : List Gate) (c : Gate) (l p d g : ℕ)
    (hC : C.gates = pre ++ [c, ⟨.and, [n + pre.length, d]⟩] ++ post)
    (hLeast : IsLeastAO G C) (hne : G.edgeFinset.Nonempty)
    (hl : l < n + pre.length) (hp : p < n + pre.length) (hd : d < n + pre.length)
    (hout : C.output ≠ n + pre.length) (houtlt : C.output < n + C.size)
    (hprivate : ∀ r ∈ post, ∀ i ∈ r.inputs, i ≠ n + pre.length)
    (hdom : ∀ x : Fin n → Bool, (wf (pre ++ [c]) (List.ofFn x)).getD l false = true →
      GateOp.and.eval ([n + pre.length, d].map fun i =>
        (wf (pre ++ [c]) (List.ofFn x)).getD i false) = true)
    (hstar : ∀ x : Fin n → Bool,
      (wf pre (List.ofFn x)).getD p false = true →
      (wf pre (List.ofFn x)).getD d false = true → graphFun G ∅ x = true)
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = pre.length + 1)
    (hfun : circuitFun n (repairCircuit n pre post l p d C.output) = graphFun G ∅) :
    ∃ E : Circuit, IsLeastAO G E ∧ E.size = C.size ∧ PEqualNP.ReadK.IsReadK n E 2 := by
  let D := repairCircuit n pre post l p d C.output
  obtain ⟨hD, hsize, hval⟩ := repair_private_pair_spec n C pre post c l p d hC hLeast.1
    hl hp hd hout houtlt hprivate hdom
  have hLeastD : IsLeastAO G D := by
    refine ⟨hD, hfun, ?_⟩
    intro E hE hEf
    exact hsize.le.trans (hLeast.2.2 E hE hEf)
  have hJ := repair_junk_card_le_one G C pre post c l p d g hC hLeast.1 hl hprivate hdom hstar honly
  obtain ⟨E, hE, hES, hER⟩ := TopNormalize.least_one_dirty_replacement G D hne hLeastD hJ
  exact ⟨E, hE, hES.trans hsize, hER⟩


lemma least_repair_read_two_of_pair_cover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (pre post : List Gate) (c : Gate) (l p d g : ℕ)
    (hC : C.gates = pre ++ [c, ⟨.and, [n + pre.length, d]⟩] ++ post)
    (hLeast : IsLeastAO G C) (hne : G.edgeFinset.Nonempty)
    (hl : l < n + pre.length) (hp : p < n + pre.length) (hd : d < n + pre.length)
    (hout : C.output ≠ n + pre.length) (houtlt : C.output < n + C.size)
    (hprivate : ∀ r ∈ post, ∀ i ∈ r.inputs, i ≠ n + pre.length)
    (hdom : ∀ x : Fin n → Bool, (wf (pre ++ [c]) (List.ofFn x)).getD l false = true →
      GateOp.and.eval ([n + pre.length, d].map fun i =>
        (wf (pre ++ [c]) (List.ofFn x)).getD i false) = true)
    (hstar : ∀ x : Fin n → Bool,
      (wf pre (List.ofFn x)).getD p false = true →
      (wf pre (List.ofFn x)).getD d false = true → graphFun G ∅ x = true)
    (honly : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ BelowF G C j → j = g ∨ j = pre.length + 1)
    (hcover : ∀ u v : Fin n, G.Adj u v →
      circuitFun n (aliasCircuit n (pre ++ [c]) post l C.output) (pairInput u v) = true ∨
        (wf pre (List.ofFn (pairInput u v))).getD p false = true ∧
        (wf pre (List.ofFn (pairInput u v))).getD d false = true) :
    ∃ E : Circuit, IsLeastAO G E ∧ E.size = C.size ∧ PEqualNP.ReadK.IsReadK n E 2 := by
  let D := repairCircuit n pre post l p d C.output
  obtain ⟨hD, hsize, hval⟩ := repair_private_pair_spec n C pre post c l p d hC hLeast.1
    hl hp hd hout houtlt hprivate hdom
  have hshape : C.gates = (pre ++ [c]) ++ ⟨.and, [n + pre.length, d]⟩ :: post := by
    simpa [List.append_assoc] using hC
  have hAfun := (alias_spec n C (pre ++ [c]) post ⟨.and, [n + pre.length, d]⟩ l
    hshape hLeast.1 (by simp; omega) hdom).2.2.1
  have hfun : circuitFun n D = graphFun G ∅ := by
    apply circuit_graphFun_eq_of_pair_cover G D hD.1
    · intro x hx
      rw [hval, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · simpa only [hLeast.2.1] using hAfun x hx
      · simp only [Bool.and_eq_true] at hx
        exact hstar x hx.1 hx.2
    · intro u v huv
      rw [hval, Bool.or_eq_true, Bool.and_eq_true]
      exact hcover u v huv
  exact least_repair_read_two G C pre post c l p d g hC hLeast hne hl hp hd hout houtlt
    hprivate hdom hstar honly hfun

end AliasSurgery

namespace ColorErase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2584.Sharing

lemma overwrite_eq_of_or_frontiers {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (c : ℕ) (r : Gate) (x : Fin n → Bool)
    (hfront : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      (∃ w ∈ (gateAt C j).inputs, OrReaches n C w c) →
      gateVal n (overwriteCircuit C c r) j x = gateVal n C j x)
    (w : ℕ) (hnot : ¬ OrReaches n C w c) :
    val (overwriteCircuit C c r) (List.ofFn x) w = val C (List.ofFn x) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · rw [val_input (n := n) (by simp) hn, val_input (n := n) (by simp) hn]
    by_cases hw : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hk' : k < (overwriteCircuit C c r).gates.length := by
        simpa only [overwriteCircuit_length] using hk
      have hck : c ≠ k := by
        intro he
        subst k
        exact hnot ((orReaches_iff n C c c).mpr ⟨hk, Or.inl rfl⟩)
      rcases hAO.1 _ (gateAt_mem hk) with hand | hor
      · by_cases hhit : ∃ i ∈ (gateAt C k).inputs, OrReaches n C i c
        · exact hfront k hk hand hhit
        · rw [val_gate (n := n) (by simp) hk', val_gate (n := n) (by simp) hk,
            overwriteCircuit_gateAt_other C c k hck r]
          congr 1
          apply List.map_congr_left
          intro i hi
          have hilt := hAO.2.1 k hk i hi
          rw [ite_eq_left hilt, ite_eq_left hilt]
          exact ih i hilt (fun hic => hhit ⟨i, hi, hic⟩)
      · rw [val_gate (n := n) (by simp) hk', val_gate (n := n) (by simp) hk,
          overwriteCircuit_gateAt_other C c k hck r]
        congr 1
        apply List.map_congr_left
        intro i hi
        have hilt := hAO.2.1 k hk i hi
        rw [ite_eq_left hilt, ite_eq_left hilt]
        apply ih i hilt
        intro hic
        apply hnot
        exact (orReaches_iff n C k c).mpr ⟨hk, Or.inr ⟨hor, i, hi, hilt, hic⟩⟩
    · rw [val_ge (n := n) (by simp) (by rw [overwriteCircuit_length]; omega),
        val_ge (n := n) (by simp) (by omega)]

lemma overwrite_eq_of_false_unique_frontier {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (c h : ℕ) (r : Gate) (x : Fin n → Bool)
    (hrep : replacementVal n C c r x = true → val C (List.ofFn x) (n + c) = true)
    (hunique : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ w ∈ (gateAt C j).inputs, OrReaches n C w c → j = h)
    (hhfalse : gateVal n C h x = false)
    (hout : ¬ OrReaches n C C.output c) :
    circuitFun n (overwriteCircuit C c r) x = circuitFun n C x := by
  apply overwrite_eq_of_or_frontiers C hAO c r x _ C.output hout
  intro j hj hjand hhit
  obtain ⟨w, hw, hreach⟩ := hhit
  have hjh := hunique j hj hjand w hw hreach
  subst j
  rw [hhfalse]
  cases he : gateVal n (overwriteCircuit C c r) h x with
  | false => rfl
  | true =>
    have hy := overwriteCircuit_val_le hAO.1 c r x hrep (n + h) he
    change gateVal n C h x = true at hy
    rw [hhfalse] at hy
    cases hy


lemma erase_or_with_false_frontier {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hf : circuitFun n C = graphFun G ∅)
    (c h a b : ℕ) (hc : c < C.gates.length) (hcor : (gateAt C c).op = GateOp.or)
    (hcin : (gateAt C c).inputs = [a, b])
    (hunique : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ w ∈ (gateAt C j).inputs, OrReaches n C w c → j = h)
    (hout : ¬ OrReaches n C C.output c)
    (hpair : ∀ u v : Fin n, G.Adj u v →
      val C (List.ofFn (pairInput u v)) b = false ∨ gateVal n C h (pairInput u v) = false) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  let r : Gate := ⟨GateOp.or, [a, a]⟩
  let E := overwriteCircuit C c r
  have ha : a < n + c := hAO.2.1 c hc a (by rw [hcin]; simp)
  have hb : b < n + c := hAO.2.1 c hc b (by rw [hcin]; simp)
  have hrback : ∀ i ∈ r.inputs, i < n + c := by
    intro i hi
    simp only [r, List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
    simpa [hi] using ha
  have hrval (x : Fin n → Bool) : replacementVal n C c r x = val C (List.ofFn x) a := by
    rw [replacementVal_of_readsBack C c r x hrback]
    simp [r, GateOp.eval]
  have hcval (x : Fin n → Bool) : val C (List.ofFn x) (n + c) =
      (val C (List.ofFn x) a || val C (List.ofFn x) b) := by
    rw [val_gate (n := n) (by simp) hc, hcor, hcin]
    simp [GateOp.eval, ha, hb]
  have hrep (x : Fin n → Bool) : replacementVal n C c r x = true →
      val C (List.ofFn x) (n + c) = true := by
    rw [hrval, hcval]
    intro hx
    simp [hx]
  have hE : IsAO2 n E := overwriteCircuit_isAO2 hAO c r (Or.inr rfl) hrback rfl
  have hEf : circuitFun n E = graphFun G ∅ := by
    apply circuit_graphFun_eq_of_pair_cover G E hE.1
    · intro x hx
      simpa only [hf] using overwriteCircuit_fun_le hAO.1 c r hrep x hx
    · intro u v huv
      have heq : circuitFun n E (pairInput u v) = circuitFun n C (pairInput u v) := by
        rcases hpair u v huv with hbfalse | hhfalse
        · apply overwriteCircuit_fun_eq C c r
          rw [hrval, hcval, hbfalse, Bool.or_false]
        · exact overwrite_eq_of_false_unique_frontier C hAO c h r _
            (hrep _) hunique hhfalse hout
      rw [heq, hf]
      exact (graphFun_pair G u v).mpr huv
  have hgate (x : Fin n → Bool) : gateVal n E c x = val E (List.ofFn x) a := by
    change val (overwriteCircuit C c r) (List.ofFn x) (n + c) = _
    rw [overwriteCircuit_val_self C hc r x, hrval,
      overwriteCircuit_val_before C c r x a ha]
  obtain ⟨D, hD, hsize, hDf⟩ := MinimumPure.erase_equivalent_wire E hE
    (by simpa only [E, overwriteCircuit_length] using hc) ha hgate
  refine ⟨D, hD, ?_, hDf.trans hEf⟩
  simpa only [E, overwriteCircuit_size] using hsize

lemma disjoint_or_false_on_independent_pair {n : ℕ} (C : Circuit) (b d : ℕ)
    (bpure : ∀ k, OrReaches n C b k → (gateAt C k).op = GateOp.or)
    (dpure : ∀ k, OrReaches n C d k → (gateAt C k).op = GateOp.or)
    (S : Fin n → Prop) (bside : ∀ u ∈ orIn n C b, S u)
    (dside : ∀ u ∈ orIn n C d, S u)
    (hdisj : Disjoint (orIn n C b) (orIn n C d))
    (x y : Fin n) (hxy : ¬ (S x ∧ S y)) :
    val C (List.ofFn (pairInput x y)) b = false ∨
      val C (List.ofFn (pairInput x y)) d = false := by
  cases hb : val C (List.ofFn (pairInput x y)) b with
  | false => exact Or.inl rfl
  | true =>
    right
    cases hd : val C (List.ofFn (pairInput x y)) d with
    | false => rfl
    | true =>
      obtain ⟨u, hu, hx_u⟩ := (pure_or_value_iff bpure _).mp hb
      obtain ⟨v, hv, hx_v⟩ := (pure_or_value_iff dpure _).mp hd
      have he : u = v := by
        rcases (pairInput_true x y u).mp hx_u with hux | huy <;>
          rcases (pairInput_true x y v).mp hx_v with hvx | hvy
        · exact hux.trans hvx.symm
        · exact False.elim (hxy ⟨hux ▸ bside _ hu, hvy ▸ dside _ hv⟩)
        · exact False.elim (hxy ⟨hvx ▸ dside _ hv, huy ▸ bside _ hu⟩)
        · exact huy.trans hvy.symm
      subst v
      exact False.elim (Finset.disjoint_left.mp hdisj hu hv)

lemma erase_or_disjoint_guard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hf : circuitFun n C = graphFun G ∅)
    (c h a b d : ℕ) (hc : c < C.gates.length) (hcor : (gateAt C c).op = GateOp.or)
    (hcin : (gateAt C c).inputs = [a, b])
    (hh : h < C.gates.length) (hhand : (gateAt C h).op = GateOp.and)
    (hdin : d ∈ (gateAt C h).inputs)
    (hunique : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ w ∈ (gateAt C j).inputs, OrReaches n C w c → j = h)
    (hout : ¬ OrReaches n C C.output c)
    (bpure : ∀ k, OrReaches n C b k → (gateAt C k).op = GateOp.or)
    (dpure : ∀ k, OrReaches n C d k → (gateAt C k).op = GateOp.or)
    (S : Fin n → Prop) (bside : ∀ u ∈ orIn n C b, S u)
    (dside : ∀ u ∈ orIn n C d, S u)
    (hdisj : Disjoint (orIn n C b) (orIn n C d))
    (hind : ∀ x y, G.Adj x y → ¬ (S x ∧ S y)) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  apply erase_or_with_false_frontier G C hAO hf c h a b hc hcor hcin hunique hout
  intro x y hxy
  rcases disjoint_or_false_on_independent_pair C b d bpure dpure S bside dside hdisj
    x y (hind x y hxy) with hb | hd
  · exact Or.inl hb
  · right
    apply Bool.eq_false_iff.mpr
    intro hv
    have hdt := ((val_and (n := n) (by simp) hh hhand).mp hv d hdin).2
    rw [hd] at hdt
    cases hdt

end ColorErase

namespace EdgePurification

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2584.Sharing

lemma overwrite_clean_junk_subset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : AndOrOnly C) (g : ℕ) (r : Gate)
    (hrep : ∀ x : Fin n → Bool,
      replacementVal n C g r x = true → val C (List.ofFn x) (n + g) = true)
    (hclean : BelowF G (overwriteCircuit C g r) g) :
    junk G (overwriteCircuit C g r) ⊆ (junk G C).erase g := by
  intro j hj
  have hj' := hj
  simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range] at hj'
  obtain ⟨hjlen, hjand, _, x, hjval, hxfalse⟩ := hj'
  have hjC : j < C.gates.length := by simpa only [overwriteCircuit_length] using hjlen
  have hjg : j ≠ g := by
    intro he
    subst j
    have hF := hclean x hjval
    rw [hxfalse] at hF
    cases hF
  have hjandC : (gateAt C j).op = GateOp.and := by
    simpa only [overwriteCircuit_gateAt_other C g j hjg.symm r] using hjand
  have hjvalC : gateVal n C j x = true :=
    overwriteCircuit_val_le hAO g r x (hrep x) (n + j) hjval
  apply Finset.mem_erase.mpr
  refine ⟨hjg, ?_⟩
  simp only [junk, gatesWhere, Finset.mem_filter, Finset.mem_range]
  exact ⟨hjC, hjandC, hjC, x, hjvalC, hxfalse⟩

lemma replacementVal_and_inputs {n : ℕ} (C : Circuit) (j : ℕ)
    (u v : Fin n) (x : Fin n → Bool) :
    replacementVal n C j ⟨GateOp.and, [u.val, v.val]⟩ x = (x u && x v) := by
  rw [replacementVal_of_readsBack C j _ x (by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega)]
  simp [GateOp.eval, val_ofFn]

lemma list_and_count_set_and (gs : List Gate) (a : ℕ) (ha : a < gs.length)
    (hand : gs[a].op = GateOp.and) (r : Gate) (hr : r.op = GateOp.and) :
    (gs.set a r).countP (fun g => match g.op with | .and => true | _ => false) =
      gs.countP (fun g => match g.op with | .and => true | _ => false) := by
  induction gs generalizing a with
  | nil => simp at ha
  | cons g gs ih =>
    cases a with
    | zero =>
      have hg : g.op = GateOp.and := by simpa using hand
      simp [hg, hr]
    | succ a =>
      have ha' : a < gs.length := by simpa using ha
      have hand' : gs[a].op = GateOp.and := by simpa using hand
      simp only [List.set_cons_succ, List.countP_cons]
      rw [ih a ha' hand']

lemma unique_edge_purification {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hf : circuitFun n C = graphFun G ∅)
    (g : ℕ) (hg : g < C.gates.length) (hand : (gateAt C g).op = GateOp.and)
    (u v : Fin n) (huv : G.Adj u v)
    (hgate : gateVal n C g (pairInput u v) = true)
    (hunique : ∀ x y : Fin n, G.Adj x y → gateVal n C g (pairInput x y) = true →
      (x = u ∧ y = v) ∨ (x = v ∧ y = u)) :
    let D := overwriteCircuit C g ⟨GateOp.and, [u.val, v.val]⟩
    IsAO2 n D ∧ D.size = C.size ∧
      DoublePoint.andCount D = DoublePoint.andCount C ∧
      circuitFun n D = graphFun G ∅ ∧ junk G D ⊆ (junk G C).erase g := by
  let r : Gate := ⟨GateOp.and, [u.val, v.val]⟩
  let D := overwriteCircuit C g r
  have hD : IsAO2 n D := overwriteCircuit_isAO2 hAO g r (Or.inl rfl) (by
    intro i hi
    change i ∈ [u.val, v.val] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega) rfl
  have hrep (x : Fin n → Bool) :
      replacementVal n C g r x = true → val C (List.ofFn x) (n + g) = true := by
    rw [replacementVal_and_inputs]
    intro hx
    have ⟨hu, hv⟩ : x u = true ∧ x v = true := by simpa using hx
    apply val_monotone hAO.1 (pairInput u v) x _ (n + g) hgate
    intro w hw
    rcases (pairInput_true u v w).mp hw with rfl | rfl
    · exact hu
    · exact hv
  have hpair (x y : Fin n) (hxy : G.Adj x y) :
      replacementVal n C g r (pairInput x y) =
        val C (List.ofFn (pairInput x y)) (n + g) := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · exact hrep _
    · intro hv
      rcases hunique x y hxy hv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [r, replacementVal_and_inputs, pairInput_left, pairInput_right]
  have hfun : circuitFun n D = graphFun G ∅ := by
    apply circuit_graphFun_eq_of_pair_cover G D hD.1
    · intro x hx
      rw [← hf]
      exact overwriteCircuit_fun_le hAO.1 g r hrep x hx
    · intro x y hxy
      change circuitFun n (overwriteCircuit C g r) (pairInput x y) = true
      rw [overwriteCircuit_fun_eq C g r _ (hpair x y hxy), hf]
      exact (graphFun_pair G x y).mpr hxy
  have hclean : BelowF G D g := by
    intro x hx
    change val D (List.ofFn x) (n + g) = true at hx
    rw [overwriteCircuit_val_self C hg r x, replacementVal_and_inputs] at hx
    have ⟨hu, hv⟩ : x u = true ∧ x v = true := by simpa using hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨u, v, huv, hu, hv⟩
  refine ⟨hD, overwriteCircuit_size C g r, ?_, hfun,
    overwrite_clean_junk_subset G C hAO.1 g r hrep hclean⟩
  apply list_and_count_set_and C.gates g hg
  · simpa only [Sharing.gateAt_eq hg] using hand
  · rfl

end EdgePurification

end PEqualNP.Outside.L_meta_2584
