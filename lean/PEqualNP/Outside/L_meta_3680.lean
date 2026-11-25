import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_3680


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

section Circuit

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

private lemma words_nonempty {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {w : ℕ} {t : List ℕ} (ht : t ∈ words n C w) : t ≠ [] := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      simp [ht']
    · rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht
        obtain ⟨u, hu, v, _, rfl⟩ := ht
        exact fun hh => ih _ (earlier h k 0) hu (List.append_eq_nil_iff.mp hh).1
      · rw [ho] at ht
        exact ht.elim (ih _ (earlier h k 0)) (ih _ (earlier h k 1))
    · simp [words_missing n C hb] at ht

end Circuit


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def run (gs : List Gate) (xs : List Bool) : List Bool :=
  evalFrom false GateOp.eval gs xs

private lemma run_snoc (gs : List Gate) (g : Gate) (xs : List Bool) :
    run (gs ++ [g]) xs = run gs xs ++ [g.op.eval (g.inputs.map fun i => (run gs xs).getD i false)] := by
  simp [run, evalFrom, List.foldl_append]

private lemma run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length :=
  evalFrom_length false GateOp.eval gs xs

private lemma supports (n : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (F : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ F.card + gs.length ∧
      ∀ (x y : List Bool), x.length = n → y.length = n →
        (∀ i ∈ S, x.getD i false = y.getD i false) →
        ∀ i ∈ F, (run gs x).getD i false = (run gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing F with
  | nil => exact ⟨F, by simp, fun _ _ _ _ ha => ha⟩
  | append_singleton gs g ih =>
    let j := n + gs.length
    let B := if j ∈ F then F.erase j ∪ g.inputs.toFinset else F
    have hb : B.card ≤ F.card + 1 := by
      by_cases hj : j ∈ F
      · have hu := Finset.card_union_le (F.erase j) g.inputs.toFinset
        have he := Finset.card_erase_add_one hj
        have hd := (List.toFinset_card_le g.inputs).trans (hg g (by simp))
        simp only [B, ite_eq_left hj]
        omega
      · simp [B, hj]
    obtain ⟨S, hS, hs⟩ := ih (fun a ha => hg a (List.mem_append_left _ ha)) B
    refine ⟨S, by simp only [List.length_append, List.length_singleton]; omega, ?_⟩
    intro x y hx hy ha i hi
    have ex : (run gs x).length = j := by simp [run_length, hx, j]
    have ey : (run gs y).length = j := by simp [run_length, hy, j]
    rw [run_snoc, run_snoc]
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      apply hs x y hx hy ha i
      by_cases hj : j ∈ F
      · simpa [B, hj] using Finset.mem_union_left g.inputs.toFinset (Finset.mem_erase.mpr ⟨hij.ne, hi⟩)
      · simpa [B, hj] using hi
    · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp only [ex, ey, Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro k hk
      apply hs x y hx hy ha k
      simpa [B, hi] using Finset.mem_union_right (F.erase j) (List.mem_toFinset.mpr hk)
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

private lemma essential_bound {n : ℕ} (C : Circuit)
    (hg : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (he : ∀ i : Fin n, ∃ x y : Fin n → Bool, (∀ j, j ≠ i → x j = y j) ∧
      circuitFun n C x ≠ circuitFun n C y) :
    n ≤ C.size + 1 := by
  obtain ⟨S, hS, hs⟩ := supports n C.gates hg {C.output}
  suffices hh : Finset.range n ⊆ S by
    have := Finset.card_le_card hh
    simp only [Finset.card_range] at this
    simp only [Finset.card_singleton] at hS
    unfold Circuit.size
    omega
  intro i hi
  by_contra hni
  let a : Fin n := ⟨i, Finset.mem_range.mp hi⟩
  obtain ⟨x, y, hxy, hne⟩ := he a
  apply hne
  apply hs (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
  intro j hj
  by_cases hjn : j < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hjn),
      List.getD_eq_getElem _ _ (by simpa using hjn)]
    simp only [List.getElem_ofFn]
    apply hxy
    intro e
    have he : j = i := congrArg Fin.val e
    exact hni (he ▸ hj)
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hjn)]

private lemma cast_ne_nat {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have he := congrArg Fin.val h
  change p.val = N + l.val at he
  omega

private def pair {N : ℕ} (p l : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)

private def point {N : ℕ} (p : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.castAdd N p)

private def line {N : ℕ} (l : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i = Fin.natAdd N l)

private def Thin {N : ℕ} (z : Fin (N+N) → Bool) : Prop :=
  ∀ l l' : Fin N, z (Fin.natAdd N l) = true → z (Fin.natAdd N l') = true → l = l'

private lemma thin_pair {N : ℕ} (p l : Fin N) : Thin (pair p l) := by
  intro i j hi hj
  simp only [pair,decide_eq_true_eq] at hi hj
  exact Fin.natAdd_injective _ _ ((hi.resolve_left (Ne.symm (cast_ne_nat p i))).trans (hj.resolve_left (Ne.symm (cast_ne_nat p j))).symm)

private lemma thin_point {N : ℕ} (p : Fin N) : Thin (point p) := by
  intro i j hi
  exact ((cast_ne_nat p i) (of_decide_eq_true hi).symm).elim

private lemma thin_line {N : ℕ} (l : Fin N) : Thin (line l) := by
  intro i j hi hj
  simp [line] at hi hj
  exact hi.trans hj.symm

private lemma plane_support (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hp : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hC : ∀ z : Fin (N + N) → Bool, Thin z → circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (hq2 : 2 ≤ q) : N + N ≤ C.size + 1 := by
  have htwo : 2 ≤ N := by nlinarith
  have hpair (p l : Fin N) (h : I p l) : circuitFun (N + N) C (pair p l) = true := by
    rw [hC _ (thin_pair p l), decide_eq_true_eq]
    exact ⟨p, l, h, by simp [pair], by simp [pair]⟩
  have hpoint (p : Fin N) : circuitFun (N + N) C (point p) = false := by
    rw [hC _ (thin_point p), decide_eq_false_iff_not]
    rintro ⟨_, l, _, _, h⟩
    exact cast_ne_nat p l (of_decide_eq_true h).symm
  have hline (l : Fin N) : circuitFun (N + N) C (line l) = false := by
    rw [hC _ (thin_line l), decide_eq_false_iff_not]
    rintro ⟨p, _, _, h, _⟩
    exact cast_ne_nat p l (of_decide_eq_true h)
  apply essential_bound C (fun g hg => (hAO.2.2 g hg).le)
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p
    have hex : ∃ p' : Fin N, p ≠ p' := by
      by_cases hz : p.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by have hh := congrArg Fin.val h; simp at hh; omega⟩
      · exact ⟨⟨0, by omega⟩, fun h => hz (congrArg Fin.val h)⟩
    obtain ⟨p', hn⟩ := hex
    obtain ⟨l, hi, _⟩ := hp p p' hn
    refine ⟨pair p l, line l, fun j hj => ?_, by rw [hpair p l hi.1, hline]; decide⟩
    simp [pair, line, hj]
  · intro l
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (Finset.univ.filter (fun p => I p l)).card by
      rw [hl]; omega)
    refine ⟨pair p l, point p, fun j hj => ?_,
      by rw [hpair p l (Finset.mem_filter.mp hp).2, hpoint]; decide⟩
    simp only [pair, point, hj, or_false]


section ReadWitness


open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

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

private lemma encode_witness {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (w : ℕ) (v : List ℕ) (hv : v ∈ vecs n C S w) :
    ∃ t ∈ words n C w, v = encode S t ∧ ∀ i ∈ t, i ∈ S := by
  induction w using Nat.strong_induction_on generalizing v with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · have hi : w < ((List.range n).map (leafVectors S 2)).length := by simpa using hb
      rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi] at hv
      simp only [List.getElem_map, List.getElem_range] at hv
      rw [words_input C hb]
      by_cases hs : w ∈ S
      · refine ⟨[w], rfl, ?_, by simpa using hs⟩
        have hvec : v = S.map (fun j => if j = w then min 1 (2 + 1) else 0) := by
          simpa only [leafVectors, hs, ite_true, List.mem_singleton] using hv
        rw [hvec]
        unfold encode
        apply List.map_congr_left
        intro a _
        by_cases hea : a = w
        · simp [hea]
        · simp [hea, Ne.symm hea]
      · simp [leafVectors, hs] at hv
    · have hlen : ((List.range n).map (leafVectors S 2)).length = n := by simp
      have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
      rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
      rw [hvec] at hv
      rw [words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho] at hv ⊢
        change v ∈ andStep 2 (andStep 2 [S.map (fun _ => 0)] (vecs n C S (operand C k 0)))
          (vecs n C S (operand C k 1)) at hv
        obtain ⟨x, hx, y, hy, rfl⟩ := (mem_andStep_two _ _ _).mp hv
        obtain ⟨z, hz, x', hx', rfl⟩ := (mem_andStep_two _ _ _).mp hx
        obtain ⟨t, ht, rfl, hts⟩ := ih _ (earlier h k 0) _ hx'
        obtain ⟨u, hu, rfl, hus⟩ := ih _ (earlier h k 1) _ hy
        refine ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, ?_, fun i hi =>
          (List.mem_append.mp hi).elim (hts i) (hus i)⟩
        have hz' : z = encode S [] := by simpa [encode_nil] using hz
        rw [hz', encode_append, List.nil_append, encode_append]
      · rw [ho] at hv ⊢
        change v ∈ (vecs n C S (operand C k 1)).foldl insertNew
          ((vecs n C S (operand C k 0)).foldl insertNew []) at hv
        rw [mem_fold_insertNew, mem_fold_insertNew] at hv
        simp only [List.not_mem_nil, false_or] at hv
        rcases hv with hp | hp
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 0) _ hp
          exact ⟨t, Or.inl ht, he, hs⟩
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 1) _ hp
          exact ⟨t, Or.inr ht, he, hs⟩
    · rw [vec_eval, List.getD_eq_default _ _ (by
        simpa [evalFrom_length, Circuit.size] using hb)] at hv
      simp at hv

private lemma read_to_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (r : readsAtMost C n S 2 = true) :
    ∃ t ∈ words n C C.output, (∀ i ∈ t, i ∈ S) ∧ ∀ i ∈ S, t.count i ≤ 2 := by
  obtain ⟨v, hv, ha⟩ := List.any_eq_true.mp r
  obtain ⟨t, ht, rfl, hts⟩ := encode_witness h S C.output v hv
  refine ⟨t, ht, hts, fun i hi => ?_⟩
  have hv : min (t.count i) 3 ∈ encode S t := List.mem_map.mpr ⟨i, hi, rfl⟩
  have hb := of_decide_eq_true ((List.all_eq_true.mp ha) _ hv)
  omega

end ReadWitness


section Degrees

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

private def on (N : ℕ) (X Y : Set (Fin N)) (w : ℕ) : Prop :=
  (∃ p ∈ X, (p : ℕ) = w) ∨ ∃ l ∈ Y, N + (l : ℕ) = w

private lemma on_point {N : ℕ} (X Y : Set (Fin N)) (p : Fin N) :
    on N X Y p.val ↔ p ∈ X := by
  constructor
  · rintro (⟨q, hq, hv⟩ | ⟨l, _, hv⟩)
    · exact (Fin.ext hv : q = p) ▸ hq
    · omega
  · exact fun hp => Or.inl ⟨p, hp, rfl⟩

private lemma on_line {N : ℕ} (X Y : Set (Fin N)) (l : Fin N) :
    on N X Y (N + l.val) ↔ l ∈ Y := by
  constructor
  · rintro (⟨p, _, hv⟩ | ⟨l', hl', hv⟩)
    · omega
    · exact (Fin.ext (Nat.add_left_cancel hv) : l' = l) ▸ hl'
  · exact fun hl => Or.inr ⟨l, hl, rfl⟩

private noncomputable def bits {N : ℕ} (X Y : Set (Fin N)) (i : Fin (N + N)) : Bool := by
  classical
  exact decide (on N X Y i.val)

private lemma bits_true {N : ℕ} (X Y : Set (Fin N)) (i : Fin (N + N)) :
    bits X Y i = true ↔ on N X Y i.val := by
  classical
  simp [bits]

private def pcount (N : ℕ) (t : List ℕ) : ℕ := (t.filter fun w => decide (w < N)).length
private def lcount (N : ℕ) (t : List ℕ) : ℕ := (t.filter fun w => decide (N ≤ w)).length

private lemma sum_counts (N : ℕ) (t : List ℕ) : pcount N t + lcount N t = t.length := by
  induction t with
  | nil => rfl
  | cons a t ih =>
    by_cases h : a < N
    · have hn : ¬ N ≤ a := by omega
      simp [pcount, lcount, h, hn] at ih ⊢
      omega
    · have hn : N ≤ a := by omega
      simp [pcount, lcount, h, hn] at ih ⊢
      omega

private def Hom (N : ℕ) (C : Circuit) (w a b : ℕ) (X Y : Set (Fin N)) : Prop :=
  ∃ t ∈ words (N + N) C w, pcount N t = a ∧ lcount N t = b ∧ ∀ j ∈ t, on N X Y j

private lemma hom_mono {N : ℕ} {C : Circuit} {w a b : ℕ} {X X' Y Y' : Set (Fin N)}
    (hx : X ⊆ X') (hy : Y ⊆ Y') (h : Hom N C w a b X Y) : Hom N C w a b X' Y' := by
  obtain ⟨t, ht, ha, hb, hxy⟩ := h
  exact ⟨t, ht, ha, hb, fun j hj => (hxy j hj).imp
    (fun ⟨p, hp, he⟩ => ⟨p, hx hp, he⟩) (fun ⟨l, hl, he⟩ => ⟨l, hy hl, he⟩)⟩

private lemma hom_pure_x {N : ℕ} {C : Circuit} {w a : ℕ} {X Y : Set (Fin N)} :
    Hom N C w a 0 X Y ↔ Hom N C w a 0 X ∅ := by
  refine ⟨?_, hom_mono (fun _ h => h) (Set.empty_subset _)⟩
  rintro ⟨t, ht, ha, hb, hxy⟩
  refine ⟨t, ht, ha, hb, fun j hj => ?_⟩
  rcases hxy j hj with hp | ⟨l, _, hl⟩
  · exact Or.inl hp
  · have hn : N ≤ j := by omega
    have hmem : j ∈ t.filter (fun w => decide (N ≤ w)) := List.mem_filter.mpr ⟨hj, by simp [hn]⟩
    unfold lcount at hb
    rw [List.length_eq_zero_iff.mp hb] at hmem
    simp at hmem

private lemma hom_pure_y {N : ℕ} {C : Circuit} {w b : ℕ} {X Y : Set (Fin N)} :
    Hom N C w 0 b X Y ↔ Hom N C w 0 b ∅ Y := by
  refine ⟨?_, hom_mono (Set.empty_subset _) (fun _ h => h)⟩
  rintro ⟨t, ht, ha, hb, hxy⟩
  refine ⟨t, ht, ha, hb, fun j hj => ?_⟩
  rcases hxy j hj with ⟨p, _, hp⟩ | hl
  · have hn : j < N := hp ▸ p.isLt
    have hmem : j ∈ t.filter (fun w => decide (w < N)) := List.mem_filter.mpr ⟨hj, by simp [hn]⟩
    unfold pcount at ha
    rw [List.length_eq_zero_iff.mp ha] at hmem
    simp at hmem
  · exact Or.inr hl

private lemma hom_invalid {N : ℕ} {C : Circuit} {w a b : ℕ} {X Y : Set (Fin N)}
    (hw : N + N + C.size ≤ w) : ¬ Hom N C w a b X Y := by
  simp [Hom, words_missing _ _ hw]

private lemma hom_pos {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w a b : ℕ} {X Y : Set (Fin N)} (hh : Hom N C w a b X Y) : 0 < a + b := by
  obtain ⟨t, ht, ha, hb, _⟩ := hh
  rw [← ha, ← hb, sum_counts]
  exact List.length_pos_iff.mpr (words_nonempty h ht)

private lemma hom_input {N : ℕ} {C : Circuit} {w a b : ℕ} {X Y : Set (Fin N)} (hw : w < N + N) :
    Hom N C w a b X Y ↔ on N X Y w ∧
      ((w < N ∧ a = 1 ∧ b = 0) ∨ (N ≤ w ∧ a = 0 ∧ b = 1)) := by
  unfold Hom
  rw [words_input C hw]
  by_cases h : w < N
  · have h' : ¬ N ≤ w := by omega
    simp [pcount, lcount, h, h', eq_comm, and_comm, and_left_comm, and_assoc]
  · have h' : N ≤ w := by omega
    simp [pcount, lcount, h, h', eq_comm, and_comm, and_left_comm, and_assoc]

private lemma hom_or {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.or) {a b : ℕ} {X Y : Set (Fin N)} :
    Hom N C (outWire (N + N) k) a b X Y ↔
      ∃ i : Fin 2, Hom N C (operand C k i) a b X Y := by
  rw [Fin.exists_fin_two]
  unfold Hom
  rw [words_gate h k, ho]
  simp only [wordOp, Set.mem_union]
  exact ⟨fun ⟨t, hr, he⟩ => hr.imp (fun ht => ⟨t, ht, he⟩) (fun ht => ⟨t, ht, he⟩),
    fun h => h.elim (fun ⟨t, ht, he⟩ => ⟨t, Or.inl ht, he⟩) (fun ⟨t, ht, he⟩ => ⟨t, Or.inr ht, he⟩)⟩

private lemma hom_and {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.and) {a b : ℕ} {X Y : Set (Fin N)} :
    Hom N C (outWire (N + N) k) a b X Y ↔
      ∃ a₀ b₀ a₁ b₁ : ℕ, a₀ + a₁ = a ∧ b₀ + b₁ = b ∧
        Hom N C (operand C k 0) a₀ b₀ X Y ∧ Hom N C (operand C k 1) a₁ b₁ X Y := by
  unfold Hom
  rw [words_gate h k, ho]
  constructor
  · rintro ⟨_, ⟨t, ht, u, hu, rfl⟩, ha, hb, hxy⟩
    exact ⟨pcount N t, lcount N t, pcount N u, lcount N u, by simpa [pcount] using ha,
      by simpa [lcount] using hb, ⟨t, ht, rfl, rfl, fun j hj => hxy j (List.mem_append_left _ hj)⟩,
      ⟨u, hu, rfl, rfl, fun j hj => hxy j (List.mem_append_right _ hj)⟩⟩
  · rintro ⟨a₀, b₀, a₁, b₁, ha, hb, ⟨t, ht, rfl, rfl, hxy⟩, ⟨u, hu, rfl, rfl, hxy'⟩⟩
    exact ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, by simpa [pcount] using ha,
      by simpa [lcount] using hb, fun j hj => (List.mem_append.mp hj).elim (hxy j) (hxy' j)⟩

private lemma hom_and_add {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.and) (i : Fin 2)
    {a b c d : ℕ} {X Y : Set (Fin N)}
    (h₁ : Hom N C (operand C k i) a b X Y)
    (h₂ : Hom N C (operand C k (1 - i)) c d X Y) :
    Hom N C (outWire (N + N) k) (a + c) (b + d) X Y := by
  apply (hom_and h ho).mpr
  fin_cases i
  · exact ⟨a, b, c, d, rfl, rfl, h₁, h₂⟩
  · exact ⟨c, d, a, b, Nat.add_comm _ _, Nat.add_comm _ _, h₂, h₁⟩

private lemma hom_sound {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w a b : ℕ} {X Y : Set (Fin N)} (hh : Hom N C w a b X Y) :
    circuitValue C (bits X Y) w = true := by
  obtain ⟨t, ht, _, _, hxy⟩ := hh
  apply (value_eq_terms h _ _).mpr
  refine ⟨t, ht, fun j hj => ?_⟩
  rcases hxy j hj with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
  · exact ⟨Fin.castAdd N p, rfl, (bits_true _ _ _).mpr ((on_point X Y p).mpr hp)⟩
  · exact ⟨Fin.natAdd N l, rfl, (bits_true _ _ _).mpr ((on_line X Y l).mpr hl)⟩

end Degrees


open Finset

section Charging


variable {A B W E : Type*} [Fintype A] [Fintype B]
variable (I : A → B → Prop) [DecidableRel I]

private def fourFree : Prop :=
  ∀ ⦃c d : B⦄, c ≠ d → ∀ ⦃a b : A⦄, I a c → I a d → I b c → I b d → a = b

private noncomputable def single (f : Set A → Prop) : Finset A := by
  classical
  exact univ.filter (fun a => f {a})

private lemma mem_single (f : Set A → Prop) (a : A) : a ∈ single f ↔ f {a} := by
  classical
  simp [single]

private def clean (f : Set A → Prop) (c : B) : Prop :=
  ¬ f {a | ¬ I a c}

private lemma clean_single {f : Set A → Prop} (hm : Monotone f) {a : A} {c : B}
    (hc : clean I f c) (ha : a ∈ single f) : I a c := by
  by_contra hn
  exact hc (hm (Set.singleton_subset_iff.mpr hn) ((mem_single f a).mp ha))

private def almost (s : Finset A) (c : B) : Prop :=
  (s.filter fun a => ¬ I a c).card ≤ 1

private def approved (simple : Prop) (f : Set A → Prop) (c : B) : Prop :=
  (2 ≤ (single f).card ∧ clean I f c) ∨
    (simple ∧ 4 ≤ (single f).card ∧ almost I (single f) c)

private lemma almost_of_clean {f : Set A → Prop} (hm : Monotone f) {c : B}
    (hc : clean I f c) : almost I (single f) c := by
  classical
  have hzero : (single f).filter (fun a => ¬ I a c) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact (Finset.mem_filter.mp ha).2 (clean_single I hm hc (Finset.mem_filter.mp ha).1)
  simp [almost, hzero]

private lemma almost_mono {s t : Finset A} (hst : s ⊆ t) {c : B}
    (h : almost I t c) : almost I s c :=
  (Finset.card_le_card (Finset.filter_subset_filter _ hst)).trans h

private lemma almost_unique (hf : fourFree I) (s : Finset A) (hs : 4 ≤ s.card)
    {c d : B} (hc : almost I s c) (hd : almost I s d) : c = d := by
  classical
  by_contra hcd
  let good := s.filter (fun a => I a c ∧ I a d)
  have hgood : good.card ≤ 1 := by
    refine Finset.card_le_one_iff.mpr ?_
    intro a b ha hb
    exact hf hcd (Finset.mem_filter.mp ha).2.1 (Finset.mem_filter.mp ha).2.2
      (Finset.mem_filter.mp hb).2.1 (Finset.mem_filter.mp hb).2.2
  let badC := s.filter (fun a => ¬ I a c)
  let badD := s.filter (fun a => ¬ I a d)
  have hcover : s ⊆ good ∪ (badC ∪ badD) := by
    intro a ha
    by_cases h1 : I a c <;> by_cases h2 : I a d <;> simp [good, badC, badD, ha, h1, h2]
  have hcard := (Finset.card_le_card hcover).trans (Finset.card_union_le good (badC ∪ badD))
  have hbad := Finset.card_union_le badC badD
  change badC.card ≤ 1 at hc
  change badD.card ≤ 1 at hd
  omega

private lemma exact_unique (hf : fourFree I) {f : Set A → Prop} (hm : Monotone f)
    (hs : 2 ≤ (single f).card) {c d : B} (hc : clean I f c) (hd : clean I f d) : c = d := by
  classical
  by_contra hcd
  have hcard : (single f).card ≤ 1 := by
    refine Finset.card_le_one_iff.mpr ?_
    intro a b ha hb
    exact hf hcd (clean_single I hm hc ha) (clean_single I hm hd ha)
      (clean_single I hm hc hb) (clean_single I hm hd hb)
  omega

private lemma approved_unique (hf : fourFree I) {simple : Prop} {f : Set A → Prop}
    (hm : Monotone f) {c d : B} (hc : approved I simple f c) (hd : approved I simple f d) :
    c = d := by
  rcases hc with ⟨hs, hc⟩ | ⟨_, hs, hc⟩ <;> rcases hd with ⟨_, hd⟩ | ⟨_, hsd, hd⟩
  · exact exact_unique I hf hm hs hc hd
  · exact almost_unique I hf _ hsd (almost_of_clean I hm hc) hd
  · exact almost_unique I hf _ hs hc (almost_of_clean I hm hd)
  · exact almost_unique I hf _ hs hc hd

private lemma small_unapproved (simple : Prop) (f : Set A → Prop) (c : B)
    (simple_spec : simple → ∀ U, f U ↔ ∃ a ∈ single f, a ∈ U)
    (h : ¬ approved I simple f c)
    (ha : clean I f c ∨ simple ∧ almost I (single f) c) :
    ((single f).filter fun a => I a c).card ≤ 2 := by
  classical
  by_contra hbad
  have hs : 3 ≤ (single f).card := by
    have hcard := Finset.card_filter_le (single f) (fun a => I a c)
    omega
  rcases ha with hc | ⟨hsim, halm⟩
  · exact h (Or.inl ⟨by omega, hc⟩)
  by_cases h4 : 4 ≤ (single f).card
  · exact h (Or.inr ⟨hsim, h4, halm⟩)
  have hcard := Finset.card_filter_add_card_filter_not
    (s := single f) (p := fun a => I a c)
  have he : ((single f).filter fun a => ¬ I a c).card = 0 := by omega
  have hempty := Finset.card_eq_zero.mp he
  have hclean : clean I f c := by
    intro ht
    obtain ⟨a, ha, hni⟩ := (simple_spec hsim _).mp ht
    have hm' : a ∈ (single f).filter (fun a => ¬ I a c) := Finset.mem_filter.mpr ⟨ha, hni⟩
    simp [hempty] at hm'
  exact h (Or.inl ⟨by omega, hclean⟩)

private noncomputable def edgeCover (f : W → Set A → Prop) (simple : W → Prop) : Finset (A × B) := by
  classical
  exact univ.filter (fun p => I p.1 p.2 ∧ ∃ w, approved I (simple w) (f w) p.2 ∧
    p.1 ∈ single (f w))

private lemma cover_bound (hf : fourFree I) (f : W → Set A → Prop) (simple : W → Prop)
    (rank : W → ℕ) (arcs : Finset E) (src dst : E → W)
    (hm : ∀ w, Monotone (f w))
    (hs : ∀ w, simple w → ∀ U, f w U ↔ ∃ a ∈ single (f w), a ∈ U)
    (hr : ∀ w,
      (∀ c, ¬ approved I (simple w) (f w) c) ∨
      (∃ u v, rank u < rank w ∧ rank v < rank w ∧ ¬ simple w ∧
        ∀ U, f w U ↔ f u U ∧ f v U) ∨
      ((∀ e ∈ arcs, src e = w → rank (dst e) < rank w ∧ (simple w → simple (dst e))) ∧
        ∀ U, f w U ↔ ∃ e ∈ arcs, src e = w ∧ f (dst e) U)) :
    (edgeCover I f simple).card ≤ 2 * arcs.card := by
  classical
  let Pay (e : E) : Finset (A × B) := univ.filter fun p => I p.1 p.2 ∧
    approved I (simple (src e)) (f (src e)) p.2 ∧
    ¬ approved I (simple (dst e)) (f (dst e)) p.2 ∧
    (clean I (f (dst e)) p.2 ∨ simple (dst e) ∧ almost I (single (f (dst e))) p.2) ∧
    p.1 ∈ single (f (dst e))
  have pay_card (e : E) : (Pay e).card ≤ 2 := by
    by_cases hn : (Pay e).Nonempty
    · obtain ⟨p, hp⟩ := hn
      have hpv := (Finset.mem_filter.mp hp).2
      refine le_trans (Finset.card_le_card_of_injOn (t := (single (f (dst e))).filter (fun a => I a p.2)) Prod.fst ?_ ?_) ?_
      · intro q hq
        have hqv := (Finset.mem_filter.mp hq).2
        have he := approved_unique I hf (hm (src e)) hqv.2.1 hpv.2.1
        exact Finset.mem_filter.mpr ⟨hqv.2.2.2.2, he ▸ hqv.1⟩
      · intro q hq r hrr he
        exact Prod.ext he (approved_unique I hf (hm (src e))
          (Finset.mem_filter.mp hq).2.2.1 (Finset.mem_filter.mp hrr).2.2.1)
      · exact small_unapproved I _ _ _ (hs (dst e)) hpv.2.2.1 hpv.2.2.2.1
    · simp [Finset.not_nonempty_iff_eq_empty.mp hn]
  have descend (w : W) (p : A × B) (hi : I p.1 p.2)
      (ha : approved I (simple w) (f w) p.2) (hsp : p.1 ∈ single (f w)) :
      ∃ e ∈ arcs, p ∈ Pay e := by
    induction ht : rank w using Nat.strong_induction_on generalizing w with
    | ind k ih =>
      rcases hr w with hl | ⟨u, v, hu, hv, hn, hmeet⟩ | ⟨hsub, hunion⟩
      · exact (hl _ ha).elim
      · have hw := (mem_single _ _).mp hsp
        obtain ⟨hpu, hpv⟩ := (hmeet _).mp hw
        obtain ⟨_, hc⟩ := ha.resolve_right (fun h => hn h.1)
        have hcu : clean I (f u) p.2 ∨ clean I (f v) p.2 := by
          by_cases hu : f u {a | ¬ I a p.2}
          · exact Or.inr (fun hv => hc ((hmeet _).mpr ⟨hu, hv⟩))
          · exact Or.inl hu
        have hSu : single (f w) ⊆ single (f u) := by
          intro a h
          exact (mem_single _ _).mpr ((hmeet _).mp ((mem_single _ _).mp h)).1
        have hSv : single (f w) ⊆ single (f v) := by
          intro a h
          exact (mem_single _ _).mpr ((hmeet _).mp ((mem_single _ _).mp h)).2
        have hs2 : 2 ≤ (single (f w)).card := (ha.resolve_right (fun h => hn h.1)).1
        rcases hcu with hcu | hcv
        · exact ih (rank u) (ht ▸ hu) u (Or.inl ⟨hs2.trans (Finset.card_le_card hSu), hcu⟩)
            ((mem_single _ _).mpr hpu) rfl
        · exact ih (rank v) (ht ▸ hv) v (Or.inl ⟨hs2.trans (Finset.card_le_card hSv), hcv⟩)
            ((mem_single _ _).mpr hpv) rfl
      · obtain ⟨e, he, hew, hep⟩ := (hunion _).mp ((mem_single _ _).mp hsp)
        have hsub' : single (f (dst e)) ⊆ single (f w) := by
          intro a ha'
          exact (mem_single _ _).mpr ((hunion _).mpr ⟨e, he, hew, (mem_single _ _).mp ha'⟩)
        have hnext : clean I (f (dst e)) p.2 ∨
            simple (dst e) ∧ almost I (single (f (dst e))) p.2 := by
          rcases ha with ⟨_, hc⟩ | ⟨hsw, _, hd⟩
          · exact Or.inl (fun hb => hc ((hunion _).mpr ⟨e, he, hew, hb⟩))
          · exact Or.inr ⟨(hsub e he hew).2 hsw, almost_mono I hsub' hd⟩
        by_cases hnext' : approved I (simple (dst e)) (f (dst e)) p.2
        · exact ih (rank (dst e)) (ht ▸ (hsub e he hew).1) _ hnext'
            ((mem_single _ _).mpr hep) rfl
        · refine ⟨e, he, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, ?_, hnext', hnext,
            (mem_single _ _).mpr hep⟩⟩
          simpa only [hew] using ha
  have hcover : edgeCover I f simple ⊆ arcs.biUnion Pay := by
    intro p hp
    obtain ⟨hi, w, ha, hsp⟩ := (Finset.mem_filter.mp hp).2
    exact Finset.mem_biUnion.mpr (descend w p hi ha hsp)
  calc
    _ ≤ (arcs.biUnion Pay).card := Finset.card_le_card hcover
    _ ≤ ∑ e ∈ arcs, (Pay e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ arcs, 2 := Finset.sum_le_sum (fun e _ => pay_card e)
    _ = _ := by simp [Nat.mul_comm]

end Charging


section Plane

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

variable {N : ℕ} {C : Circuit}
variable (I : Fin N → Fin N → Prop) [DecidableRel I]

private lemma plane_four_free
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) : fourFree I := by
  intro l l' hll p p' hp hpl' hp' hp'l'
  by_contra hpp
  obtain ⟨_, _, hunique⟩ := hu p p' hpp
  exact hll ((hunique l ⟨hp, hp'⟩).trans (hunique l' ⟨hpl', hp'l'⟩).symm)

private lemma pair_prime
    (hC : ∀ z : Fin (N + N) → Bool, Thin z → circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {p l : Fin N} (hi : I p l) :
    IsPrimeImplicant (N + N) C {Fin.castAdd N p, Fin.natAdd N l} := by
  classical
  have small (T : Finset (Fin (N+N))) (hT : T ⊆ {Fin.castAdd N p, Fin.natAdd N l}) :
      Thin (setInput T) := by
    intro i j hi hj
    have eqv (k : Fin N) (hk : setInput T (Fin.natAdd N k) = true) : k = l := by
      have hv := hT (of_decide_eq_true hk)
      exact Fin.natAdd_injective _ _ (Finset.mem_singleton.mp ((Finset.mem_insert.mp hv).resolve_left (Ne.symm (cast_ne_nat p k))))
    exact (eqv i hi).trans (eqv j hj).symm
  constructor
  · rw [hC _ (small _ (fun _ h => h)), decide_eq_true_eq]
    exact ⟨p, l, hi, by simp [setInput], by simp [setInput]⟩
  · intro T hT
    have hT' := Finset.mem_ssubsets.mp hT
    rw [hC _ (small _ hT'.subset), decide_eq_false_iff_not]
    rintro ⟨p', l', _, hp, hl⟩
    have hp' : Fin.castAdd N p' ∈ T := of_decide_eq_true hp
    have hl' : Fin.natAdd N l' ∈ T := of_decide_eq_true hl
    have pe : Fin.castAdd N p' = Fin.castAdd N p := by
      have := Finset.mem_insert.mp (hT'.subset hp')
      exact this.resolve_right (fun hm => cast_ne_nat p' l (Finset.mem_singleton.mp hm))
    have le : Fin.natAdd N l' = Fin.natAdd N l := by
      have := Finset.mem_insert.mp (hT'.subset hl')
      exact Finset.mem_singleton.mp (this.resolve_left (fun e => cast_ne_nat p l' e.symm))
    exact hT'.not_ge (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · simpa only [pe] using hp'
      · rw [Finset.mem_singleton.mp hw, ← le]
        exact hl')

private lemma setList_pair {p l : Fin N} (j : ℕ) :
    j ∈ setList ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ↔
      j = p.val ∨ j = N + l.val := by
  simp only [setList, List.mem_map, List.mem_filter, decide_eq_true_eq, List.mem_finRange,
    true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨Fin.castAdd N p, Or.inl rfl, rfl⟩
    · exact ⟨Fin.natAdd N l, Or.inr rfl, rfl⟩

private lemma pair_counts {p l : Fin N} (t : List ℕ)
    (ht : ∀ a ∈ t, a = p.val ∨ a = N + l.val) :
    pcount N t = t.count p.val ∧ lcount N t = t.count (N + l.val) := by
  have hp : p.val < N := p.isLt
  have hne : p.val ≠ N + l.val := by omega
  have hl : ¬ N + l.val < N := by omega
  induction t with
  | nil => simp [pcount, lcount]
  | cons j t ih =>
    obtain ⟨h1, h2⟩ := ih (fun a ha => ht a (List.mem_cons_of_mem _ ha))
    change (t.filter _).length = _ at h1 h2
    rcases ht j (by simp) with rfl | rfl
    · have hpn : ¬ N ≤ p.val := by omega
      simp [pcount, lcount, hp, hpn, hne, Ne.symm hne, h1, h2, List.count_cons]
    · simp [pcount, lcount, hl, hne, Ne.symm hne, h1, h2, List.count_cons]

private lemma singleton_sound {N : ℕ} {C : Circuit} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (h : PEqualNP.TopForm.IsAO2 (N+N) C)
    (hC : ∀ z : Fin (N+N) → Bool, Thin z → circuitFun (N+N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    {X Y : Set (Fin N)} {a b : ℕ} (hy : ∀ i ∈ Y, ∀ j ∈ Y, i = j)
    (hh : Hom N C C.output a b X Y) : ∃ p ∈ X, ∃ l ∈ Y, I p l := by
  have hv := hom_sound h hh
  change circuitFun (N+N) C (bits X Y) = true at hv
  have ly (i : Fin N) (hi : bits X Y (Fin.natAdd N i) = true) : i ∈ Y :=
    (on_line X Y i).mp ((bits_true _ _ _).mp hi)
  rw [hC _ (fun i j hi hj => hy i (ly i hi) j (ly j hj)), decide_eq_true_eq] at hv
  obtain ⟨p,l,hi,hp,hl⟩ := hv
  exact ⟨p,(on_point X Y p).mp ((bits_true _ _ _).mp hp),l,ly l hl,hi⟩

private lemma plane_read_cover
    (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hC : ∀ z : Fin (N + N) → Bool, Thin z → circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (hr : IsReadK (N + N) C 2) {p l : Fin N} (hi : I p l) :
    ∃ a b : ℕ, 1 ≤ a ∧ a ≤ 2 ∧ 1 ≤ b ∧ b ≤ 2 ∧ Hom N C C.output a b {p} {l} := by
  obtain ⟨t, ht, hs, hu⟩ := read_to_terms h _
    (hr {Fin.castAdd N p, Fin.natAdd N l} (pair_prime I hC hi))
  obtain ⟨hp, hl⟩ := pair_counts (p := p) (l := l) t
    (fun j hj => (setList_pair j).mp (hs j hj))
  have hh : Hom N C C.output (pcount N t) (lcount N t) {p} {l} := by
    refine ⟨t, ht, rfl, rfl, fun j hj => ?_⟩
    rcases (setList_pair j).mp (hs j hj) with rfl | rfl
    · exact (on_point _ _ p).mpr (by simp)
    · exact (on_line _ _ l).mpr (by simp)
  have hp1 : 1 ≤ pcount N t := by
    by_contra! hn
    have he : pcount N t = 0 := by omega
    rw [he] at hh
    obtain ⟨a, ha, _⟩ := singleton_sound I h hC (by simp) (hom_pure_y.mp hh)
    exact ha
  have hl1 : 1 ≤ lcount N t := by
    by_contra! hn
    have he : lcount N t = 0 := by omega
    rw [he] at hh
    obtain ⟨_, _, b, hb, _⟩ := singleton_sound I h hC (by simp) (hom_pure_x.mp hh)
    exact hb
  exact ⟨_, _, hp1, hp ▸ hu _ ((setList_pair _).mpr (Or.inl rfl)),
    hl1, hl ▸ hu _ ((setList_pair _).mpr (Or.inr rfl)), hh⟩

private noncomputable def allEdges : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2)

private lemma allEdges_card (q : ℕ)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    (allEdges I).card = N * (q + 1) := by
  classical
  let F (l : Fin N) : Finset (Fin N × Fin N) :=
    (Finset.univ.filter (fun p => I p l)).map ⟨fun p => (p, l), fun _ _ h => congrArg Prod.fst h⟩
  have hF (l : Fin N) (e : Fin N × Fin N) : e ∈ F l ↔ I e.1 l ∧ e.2 = l := by
    constructor
    · intro he
      obtain ⟨p, hp, ht⟩ := Finset.mem_map.mp he
      change (p, l) = e at ht
      rw [← ht]
      exact ⟨(Finset.mem_filter.mp hp).2, rfl⟩
    · rintro ⟨hi, hh⟩
      refine Finset.mem_map.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
      exact Prod.ext rfl hh.symm
  have heq : allEdges I = Finset.univ.biUnion F := by
    ext e
    simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, hF]
    exact ⟨fun h => ⟨e.2, h, rfl⟩, fun ⟨l, hi, he⟩ => he ▸ hi⟩
  rw [heq, Finset.card_biUnion]
  · simp [F, hL]
  · intro l _ l' _ hne
    refine Finset.disjoint_left.mpr ?_
    intro e he he'
    exact hne (((hF l e).mp he).2.symm.trans ((hF l' e).mp he').2)

end Plane


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Relation

private abbrev Occ (C : Circuit) := Fin C.size × Fin 2
private def atWire (N : ℕ) {C : Circuit} (e : Occ C) : ℕ := outWire (N + N) e.1
private def fromWire {C : Circuit} (e : Occ C) : ℕ := operand C e.1 e.2
private def otherWire {C : Circuit} (e : Occ C) : ℕ := operand C e.1 (1 - e.2)
private def flip {C : Circuit} (e : Occ C) : Occ C := (e.1, 1 - e.2)

private lemma earlier_occ {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (e : Occ C) : fromWire e < atWire N e := earlier h e.1 e.2

private lemma earlier_other {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (e : Occ C) : otherWire e < atWire N e := earlier h e.1 (1 - e.2)

private lemma at_bound (N : ℕ) {C : Circuit} (e : Occ C) :
    atWire N e < N + N + C.size := Nat.add_lt_add_left e.1.isLt _

private lemma at_eq {C : Circuit} {N : ℕ} {e : Occ C} {k : Fin C.size}
    (hh : atWire N e = outWire (N + N) k) : e.1 = k := by
  apply Fin.ext
  exact Nat.add_left_cancel hh

private def andAt {C : Circuit} (e : Occ C) : Prop := (row C e.1).op = GateOp.and
private def orAt {C : Circuit} (e : Occ C) : Prop := (row C e.1).op = GateOp.or

private def orLink (N : ℕ) (C : Circuit) (w t : ℕ) : Prop :=
  ∃ e : Occ C, orAt e ∧ fromWire e = w ∧ atWire N e = t

private def orPath (N : ℕ) (C : Circuit) := ReflTransGen (orLink N C)

private lemma orPath_head {N : ℕ} {C : Circuit} {w t : ℕ} :
    orPath N C w t ↔ w = t ∨
      ∃ e : Occ C, orAt e ∧ fromWire e = w ∧ orPath N C (atWire N e) t := by
  unfold orPath
  rw [ReflTransGen.cases_head_iff]
  constructor
  · rintro (he | ⟨u, ⟨e, ho, hf, rfl⟩, ht⟩)
    · exact Or.inl he
    · exact Or.inr ⟨e, ho, hf, ht⟩
  · rintro (he | ⟨e, ho, hf, ht⟩)
    · exact Or.inl he
    · exact Or.inr ⟨_, ⟨e, ho, hf, rfl⟩, ht⟩

private lemma or_reaches {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w t a b : ℕ} {X Y : Set (Fin N)} (hp : orPath N C w t)
    (hw : Hom N C w a b X Y) : Hom N C t a b X Y := by
  induction hp with
  | refl => exact hw
  | tail _ hy ih =>
    obtain ⟨e, ho, rfl, rfl⟩ := hy
    exact (hom_or h ho).mpr ⟨e.2, ih⟩

private def tag (s : Bool) {N : ℕ} (p : Fin N) : ℕ :=
  if s then N + p.val else p.val

private lemma tag_inj {s : Bool} {N : ℕ} {p q : Fin N} (h : tag s p = tag s q) : p = q := by
  cases s
  · exact Fin.ext h
  · exact Fin.ext (Nat.add_left_cancel h)

private def OHom (N : ℕ) (C : Circuit) (s : Bool) (w a b : ℕ) (X Y : Set (Fin N)) :=
  if s then Hom N C w b a Y X else Hom N C w a b X Y

private def oneSide (N : ℕ) (C : Circuit) (s : Bool) (w a : ℕ) (X : Set (Fin N)) :=
  OHom N C s w a 0 X ∅

private lemma ohom_mono {N : ℕ} {C : Circuit} {s : Bool} {w a b : ℕ} {X X' Y Y' : Set (Fin N)}
    (hx : X ⊆ X') (hy : Y ⊆ Y') :
    OHom N C s w a b X Y → OHom N C s w a b X' Y' := by
  cases s
  · exact hom_mono hx hy
  · exact hom_mono hy hx

private lemma ohom_pure {N : ℕ} {C : Circuit} {s : Bool} {w a : ℕ} {X Y : Set (Fin N)} :
    OHom N C s w a 0 X Y ↔ oneSide N C s w a X := by
  cases s
  · exact hom_pure_x
  · exact hom_pure_y

private lemma ohom_void {N : ℕ} {C : Circuit} {s : Bool} {w a b : ℕ} {X Y : Set (Fin N)}
    (hw : N + N + C.size ≤ w) : ¬ OHom N C s w a b X Y := by
  cases s <;> exact hom_invalid hw

private lemma ohom_pos {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {w a b : ℕ} {X Y : Set (Fin N)} (hh : OHom N C s w a b X Y) : 0 < a + b := by
  cases s
  · exact hom_pos h hh
  · rw [Nat.add_comm]
    exact hom_pos h hh

private lemma ohom_input {N : ℕ} {C : Circuit} {s : Bool} {w a b : ℕ} {X Y : Set (Fin N)}
    (hw : w < N + N) :
    OHom N C s w a b X Y ↔
      (a = 1 ∧ b = 0 ∧ ∃ x ∈ X, tag s x = w) ∨ (a = 0 ∧ b = 1 ∧ ∃ y ∈ Y, tag (!s) y = w) := by
  cases s
  · simp only [OHom, Bool.false_eq_true, ite_false, Bool.not_false, tag, ite_true, hom_input hw, on]
    constructor
    · rintro ⟨(⟨i, hi, he⟩ | ⟨i, hi, he⟩), (⟨hn, ha, hb⟩ | ⟨hn, ha, hb⟩)⟩
      · exact Or.inl ⟨ha, hb, i, hi, he⟩
      · omega
      · omega
      · exact Or.inr ⟨ha, hb, i, hi, he⟩
    · rintro (⟨ha, hb, i, hi, he⟩ | ⟨ha, hb, i, hi, he⟩)
      · exact ⟨Or.inl ⟨i, hi, he⟩, Or.inl ⟨by omega, ha, hb⟩⟩
      · exact ⟨Or.inr ⟨i, hi, he⟩, Or.inr ⟨by omega, ha, hb⟩⟩
  · simp only [OHom, ite_true, Bool.not_true, tag, Bool.false_eq_true, ite_false, hom_input hw, on]
    constructor
    · rintro ⟨(⟨i, hi, he⟩ | ⟨i, hi, he⟩), (⟨hn, ha, hb⟩ | ⟨hn, ha, hb⟩)⟩
      · exact Or.inr ⟨hb, ha, i, hi, he⟩
      · omega
      · omega
      · exact Or.inl ⟨hb, ha, i, hi, he⟩
    · rintro (⟨ha, hb, i, hi, he⟩ | ⟨ha, hb, i, hi, he⟩)
      · exact ⟨Or.inr ⟨i, hi, he⟩, Or.inr ⟨by omega, hb, ha⟩⟩
      · exact ⟨Or.inl ⟨i, hi, he⟩, Or.inl ⟨by omega, hb, ha⟩⟩

private lemma ohom_or {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.or) {s : Bool} {a b : ℕ} {X Y : Set (Fin N)} :
    OHom N C s (outWire (N + N) k) a b X Y ↔
      ∃ i : Fin 2, OHom N C s (operand C k i) a b X Y := by
  cases s <;> exact hom_or h ho

private lemma ohom_and {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.and) {s : Bool} {a b : ℕ} {X Y : Set (Fin N)} :
    OHom N C s (outWire (N + N) k) a b X Y ↔
      ∃ a₀ b₀ a₁ b₁ : ℕ, a₀ + a₁ = a ∧ b₀ + b₁ = b ∧
        OHom N C s (operand C k 0) a₀ b₀ X Y ∧ OHom N C s (operand C k 1) a₁ b₁ X Y := by
  cases s
  · exact hom_and h ho
  · exact (hom_and h ho).trans ⟨
      fun ⟨a₀, b₀, a₁, b₁, h₁, h₂, hh, hh'⟩ => ⟨b₀, a₀, b₁, a₁, h₂, h₁, hh, hh'⟩,
      fun ⟨a₀, b₀, a₁, b₁, h₁, h₂, hh, hh'⟩ => ⟨b₀, a₀, b₁, a₁, h₂, h₁, hh, hh'⟩⟩

private lemma ohom_add {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {e : Occ C} (ho : andAt e) {s : Bool} {a b c d : ℕ} {X Y : Set (Fin N)}
    (h₁ : OHom N C s (fromWire e) a b X Y) (h₂ : OHom N C s (otherWire e) c d X Y) :
    OHom N C s (atWire N e) (a + c) (b + d) X Y := by
  cases s <;> exact hom_and_add h ho e.2 h₁ h₂

private lemma one_mono (N : ℕ) (C : Circuit) (s : Bool) (w a : ℕ) :
    Monotone (oneSide N C s w a) := fun _ _ h hx => ohom_mono h (fun _ he => he) hx

private lemma one_input {N : ℕ} {C : Circuit} {s : Bool} {w a : ℕ} {X : Set (Fin N)}
    (hw : w < N + N) : oneSide N C s w a X ↔ a = 1 ∧ ∃ x ∈ X, tag s x = w := by
  unfold oneSide
  rw [ohom_input hw]
  simp

private lemma one_or {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.or) {s : Bool} {a : ℕ} {X : Set (Fin N)} :
    oneSide N C s (outWire (N + N) k) a X ↔ ∃ i : Fin 2, oneSide N C s (operand C k i) a X :=
  ohom_or h ho

private lemma one_and_small {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {k : Fin C.size} (ho : (row C k).op = GateOp.and) {s : Bool} {a : ℕ} {X : Set (Fin N)}
    (ha : a ≤ 2) :
    oneSide N C s (outWire (N + N) k) a X ↔
      a = 2 ∧ oneSide N C s (operand C k 0) 1 X ∧ oneSide N C s (operand C k 1) 1 X := by
  unfold oneSide
  rw [ohom_and h ho]
  constructor
  · rintro ⟨a₀, b₀, a₁, b₁, h₁, h₂, h₀, h₁'⟩
    have := ohom_pos h h₀
    have := ohom_pos h h₁'
    obtain rfl : a₀ = 1 := by omega
    obtain rfl : a₁ = 1 := by omega
    obtain rfl : b₀ = 0 := by omega
    obtain rfl : b₁ = 0 := by omega
    exact ⟨by omega, h₀, h₁'⟩
  · rintro ⟨rfl, hl, hr⟩
    exact ⟨1, 0, 1, 0, rfl, rfl, hl, hr⟩

section OneOccurrence


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Relation Finset

private lemma no_approved_small {A B : Type*} [Fintype A] (I : A → B → Prop) [DecidableRel I]
    {f : Set A → Prop} {s : Prop} (hc : (single f).card ≤ 1) (l : B) :
    ¬ approved I s f l := by
  rintro (⟨h, _⟩ | ⟨_, h, _⟩) <;> omega

end OneOccurrence


section Shapes


open PEqualNP.CircuitLowerBounds Relation

private lemma ohom_pure_other {N : ℕ} {C : Circuit} {s : Bool}
    {w b : ℕ} {X Y : Set (Fin N)} :
    OHom N C s w 0 b X Y ↔ oneSide N C (!s) w b Y := by
  cases s
  · exact hom_pure_y
  · exact hom_pure_x

private lemma ohom_or_reach {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {w t a b : ℕ} {X Y : Set (Fin N)} (hp : orPath N C w t)
    (hw : OHom N C s w a b X Y) : OHom N C s t a b X Y := by
  cases s <;> exact or_reaches h hp hw

private lemma and_origin {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (s : Bool) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (X Y : Set (Fin N)) (w : ℕ) :
    OHom N C s w a b X Y ↔ ∃ k : Fin C.size, (row C k).op = GateOp.and ∧
      orPath N C (outWire (N + N) k) w ∧ OHom N C s (outWire (N + N) k) a b X Y := by
  refine ⟨?_, fun ⟨_, _, hp, hh⟩ => ohom_or_reach h hp hh⟩
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hh
    rcases wire_cases (N + N) C.size w with hi | ⟨k, rfl⟩ | hm
    · have hf := (ohom_input hi).mp hh
      rcases hf with hf | hf <;> omega
    · rcases op_kind h k with ho | ho
      · exact ⟨k, ho, .refl, hh⟩
      · obtain ⟨i, hsub⟩ := (ohom_or h ho).mp hh
        obtain ⟨k', ho', hp, ht⟩ := ih _ (earlier h k i) hsub
        exact ⟨k', ho', hp.tail ⟨(k, i), ho, rfl, rfl⟩, ht⟩
    · exact (ohom_void hm hh).elim

private lemma mixed11 {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w : ℕ} {X Y : Set (Fin N)} :
    Hom N C w 1 1 X Y ↔ ∃ e : Occ C, andAt e ∧ orPath N C (atWire N e) w ∧
      oneSide N C false (fromWire e) 1 X ∧ oneSide N C true (otherWire e) 1 Y := by
  refine ⟨?_, ?_⟩
  · intro hw
    obtain ⟨k, ho, hp, hk⟩ := (and_origin h false (by decide : 0 < 1) (by decide : 0 < 1) X Y w).mp hw
    obtain ⟨a, b, c, d, ha, hb, h₁, h₂⟩ := (hom_and h ho).mp hk
    have hpos₁ := hom_pos h h₁
    have hpos₂ := hom_pos h h₂
    have hs : (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 1 ∧ d = 0) := by omega
    rcases hs with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨(k, 0), ho, hp, hom_pure_x.mp h₁, hom_pure_y.mp h₂⟩
    · exact ⟨(k, 1), ho, hp, hom_pure_x.mp h₂, hom_pure_y.mp h₁⟩
  · rintro ⟨e, ho, hp, h₁, h₂⟩
    exact or_reaches h hp (hom_and_add h ho e.2 (hom_pure_x.mpr h₁) (hom_pure_y.mpr h₂))

private lemma mixed21 {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {w : ℕ} {X Y : Set (Fin N)} (hw : OHom N C s w 2 1 X Y) :
    ∃ e : Occ C, andAt e ∧ orPath N C (atWire N e) w ∧
      ((oneSide N C s (fromWire e) 2 X ∧ oneSide N C (!s) (otherWire e) 1 Y) ∨
       (OHom N C s (fromWire e) 1 1 X Y ∧ oneSide N C s (otherWire e) 1 X)) := by
  obtain ⟨k, ho, hp, hk⟩ := (and_origin h s (by decide : 0 < 2) (by decide : 0 < 1) X Y w).mp hw
  obtain ⟨a, b, c, d, ha, hb, h₁, h₂⟩ := (ohom_and h ho).mp hk
  have hpos₁ := ohom_pos h h₁
  have hpos₂ := ohom_pos h h₂
  have hs : (a = 2 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 0) ∨
      (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 0) ∨ (a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 1) := by omega
  rcases hs with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨(k, 0), ho, hp, Or.inl ⟨ohom_pure.mp h₁, ohom_pure_other.mp h₂⟩⟩
  · exact ⟨(k, 1), ho, hp, Or.inl ⟨ohom_pure.mp h₂, ohom_pure_other.mp h₁⟩⟩
  · exact ⟨(k, 0), ho, hp, Or.inr ⟨h₁, ohom_pure.mp h₂⟩⟩
  · exact ⟨(k, 1), ho, hp, Or.inr ⟨h₂, ohom_pure.mp h₁⟩⟩

private lemma mixed22 {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w : ℕ} {X Y : Set (Fin N)} (hw : Hom N C w 2 2 X Y) :
    (∃ k : Fin C.size, (row C k).op = GateOp.and ∧ orPath N C (outWire (N + N) k) w ∧
      Hom N C (operand C k 0) 1 1 X Y ∧ Hom N C (operand C k 1) 1 1 X Y) ∨
    ∃ e : Occ C, andAt e ∧ orPath N C (atWire N e) w ∧
      ((oneSide N C false (fromWire e) 2 X ∧ oneSide N C true (otherWire e) 2 Y) ∨
       (Hom N C (fromWire e) 2 1 X Y ∧ oneSide N C true (otherWire e) 1 Y) ∨
       (Hom N C (fromWire e) 1 2 X Y ∧ oneSide N C false (otherWire e) 1 X)) := by
  obtain ⟨k, ho, hp, hk⟩ := (and_origin h false (by decide : 0 < 2) (by decide : 0 < 2) X Y w).mp hw
  obtain ⟨a, b, c, d, ha, hb, h₁, h₂⟩ := (hom_and h ho).mp hk
  have hpos₁ := hom_pos h h₁
  have hpos₂ := hom_pos h h₂
  have hs : (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1) ∨
      (a = 2 ∧ b = 0 ∧ c = 0 ∧ d = 2) ∨ (a = 0 ∧ b = 2 ∧ c = 2 ∧ d = 0) ∨
      (a = 2 ∧ b = 1 ∧ c = 0 ∧ d = 1) ∨ (a = 0 ∧ b = 1 ∧ c = 2 ∧ d = 1) ∨
      (a = 1 ∧ b = 2 ∧ c = 1 ∧ d = 0) ∨ (a = 1 ∧ b = 0 ∧ c = 1 ∧ d = 2) := by omega
  rcases hs with ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact Or.inl ⟨k, ho, hp, h₁, h₂⟩
  · exact Or.inr ⟨(k, 0), ho, hp, Or.inl ⟨hom_pure_x.mp h₁, hom_pure_y.mp h₂⟩⟩
  · exact Or.inr ⟨(k, 1), ho, hp, Or.inl ⟨hom_pure_x.mp h₂, hom_pure_y.mp h₁⟩⟩
  · exact Or.inr ⟨(k, 0), ho, hp, Or.inr (Or.inl ⟨h₁, hom_pure_y.mp h₂⟩)⟩
  · exact Or.inr ⟨(k, 1), ho, hp, Or.inr (Or.inl ⟨h₂, hom_pure_y.mp h₁⟩)⟩
  · exact Or.inr ⟨(k, 0), ho, hp, Or.inr (Or.inr ⟨h₁, hom_pure_x.mp h₂⟩)⟩
  · exact Or.inr ⟨(k, 1), ho, hp, Or.inr (Or.inr ⟨h₂, hom_pure_x.mp h₁⟩)⟩

private def backOne (N : ℕ) (C : Circuit) (s : Bool) (w : ℕ) (X : Set (Fin N)) : Prop :=
  ∃ e : Occ C, andAt e ∧ orPath N C w (fromWire e) ∧ orPath N C (atWire N e) C.output ∧
    oneSide N C s (otherWire e) 1 X

private lemma backOne_mono (N : ℕ) (C : Circuit) (s : Bool) (w : ℕ) :
    Monotone (backOne N C s w) :=
  fun _ _ hx ⟨e, ha, hp, ht, hh⟩ => ⟨e, ha, hp, ht, one_mono N C s _ _ hx hh⟩

private lemma backOne_head {N : ℕ} {C : Circuit} {s : Bool} {w : ℕ} {X : Set (Fin N)} :
    backOne N C s w X ↔ ∃ e : Occ C, fromWire e = w ∧
      ((orAt e ∧ backOne N C s (atWire N e) X) ∨
       (andAt e ∧ orPath N C (atWire N e) C.output ∧ oneSide N C s (otherWire e) 1 X)) := by
  constructor
  · rintro ⟨e, ha, hp, ht, hh⟩
    rcases orPath_head.mp hp with he | ⟨e', ho, he, hp'⟩
    · exact ⟨e, he.symm, Or.inr ⟨ha, ht, hh⟩⟩
    · exact ⟨e', he, Or.inl ⟨ho, e, ha, hp', ht, hh⟩⟩
  · rintro ⟨e, rfl, ⟨ho, e', ha, hp, ht, hh⟩ | ⟨ha, ht, hh⟩⟩
    · exact ⟨e', ha, orPath_head.mpr (Or.inr ⟨e, ho, rfl, hp⟩), ht, hh⟩
    · exact ⟨e, ha, .refl, ht, hh⟩

private lemma backOne_apply {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {s : Bool} {a b w : ℕ} {X Y : Set (Fin N)}
    (hb : backOne N C s w X) (hh : OHom N C s w a b X Y) :
    OHom N C s C.output (a + 1) b X Y := by
  obtain ⟨e, ho, hp, ht, hx⟩ := hb
  exact ohom_or_reach h ht (ohom_add h ho (ohom_or_reach h hp hh) (ohom_pure.mpr hx))

end Shapes


section PureNetwork


open Finset PEqualNP.CircuitLowerBounds

private lemma one_linear {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (s : Bool) (w : ℕ) (X : Set (Fin N)) :
    oneSide N C s w 1 X ↔ ∃ p ∈ single (oneSide N C s w 1), p ∈ X := by
  simp only [mem_single]
  refine ⟨?_, fun ⟨p, hp, hx⟩ => one_mono N C s w 1 (Set.singleton_subset_iff.mpr hx) hp⟩
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rcases wire_cases (N + N) C.size w with hh | ⟨k, rfl⟩ | hm
    · obtain ⟨_, p, hp, hv⟩ := (one_input hh).mp hw
      exact ⟨p, (one_input hh).mpr ⟨rfl, p, by simp, hv⟩, hp⟩
    · rcases op_kind h k with ha | ho
      · have hbad := (one_and_small h ha (by decide)).mp hw
        omega
      · obtain ⟨i, hi⟩ := (one_or h ho).mp hw
        obtain ⟨p, hp, hx⟩ := ih _ (earlier h k i) hi
        exact ⟨p, (one_or h ho).mpr ⟨i, hp⟩, hx⟩
    · exact (ohom_void hm hw).elim

private lemma back_linear {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (s : Bool) (w : ℕ) (X : Set (Fin N)) :
    backOne N C s w X ↔ ∃ p ∈ single (backOne N C s w), p ∈ X := by
  simp only [mem_single]
  refine ⟨?_, fun ⟨p, hp, hx⟩ => backOne_mono N C s w (Set.singleton_subset_iff.mpr hx) hp⟩
  rintro ⟨e, ha, hp, ht, h1⟩
  obtain ⟨p, hm, hx⟩ := (one_linear h s (otherWire e) X).mp h1
  exact ⟨p, ⟨e, ha, hp, ht, (mem_single _ _).mp hm⟩, hx⟩

private abbrev PureNode (C : Circuit) := ((Fin 2 × ℕ) ⊕ ℕ) ⊕ Occ C
private abbrev PureArc (C : Circuit) := (Fin 2 × Occ C) ⊕ Occ C
private def pfwd {C : Circuit} (d : Fin 2) (w : ℕ) : PureNode C := .inl (.inl (d, w))
private def pbck {C : Circuit} (w : ℕ) : PureNode C := .inl (.inr w)
private def pjoin {C : Circuit} (e : Occ C) : PureNode C := .inr e

private def pureNode (N : ℕ) {C : Circuit} (s : Bool) : PureNode C → Set (Fin N) → Prop
  | .inl (.inl (d, w)) => oneSide N C s w (1 + d.val)
  | .inl (.inr w) => backOne N C s w
  | .inr e => fun X => oneSide N C s (fromWire e) 1 X ∧ backOne N C s (atWire N e) X

private def pureSimple {C : Circuit} : PureNode C → Prop
  | .inl (.inl (d, _)) => d = 0
  | .inl (.inr _) => True
  | .inr _ => False

private lemma pureNode_mono (N : ℕ) {C : Circuit} (s : Bool) (w : PureNode C) :
    Monotone (pureNode N s w) := by
  rcases w with (⟨d, w⟩ | w) | e
  · exact one_mono N C s w _
  · exact backOne_mono N C s w
  · exact fun X Y h hx => ⟨one_mono N C s _ _ h hx.1, backOne_mono N C s _ h hx.2⟩

private lemma pureNode_linear {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (s : Bool) (w : PureNode C) (hs : pureSimple w) (X : Set (Fin N)) :
    pureNode N s w X ↔ ∃ p ∈ single (pureNode N s w), p ∈ X := by
  rcases w with (⟨d, w⟩ | w) | e
  · obtain rfl : d = 0 := hs
    exact one_linear h s w X
  · exact back_linear h s w X
  · exact hs.elim

private def pureRank (N : ℕ) {C : Circuit} (w : PureNode C) : ℕ :=
  let m := N + N + C.size + 1
  match w with
  | .inl (.inl (_, w)) => w
  | .inl (.inr w) => m + (m - w)
  | .inr _ => 2 * m + 1

private def endAnd (N : ℕ) {C : Circuit} (e : Occ C) : Prop :=
  andAt e ∧ orPath N C (atWire N e) C.output

private noncomputable def pureArcs (N : ℕ) (C : Circuit) : Finset (PureArc C) := by
  classical
  exact univ.filter fun a => a.elim (fun e => orAt e.2) (fun e => orAt e ∨ endAnd N e)

private def pureSrc (N : ℕ) {C : Circuit} : PureArc C → PureNode C
  | .inl (d, e) => pfwd d (atWire N e)
  | .inr e => pbck (fromWire e)

private noncomputable def pureDst (N : ℕ) {C : Circuit} : PureArc C → PureNode C
  | .inl (d, e) => pfwd d (fromWire e)
  | .inr e => by
    classical
    exact if orAt e then pbck (atWire N e) else pfwd 0 (otherWire e)

private lemma pure_rule {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (J : Fin N → Fin N → Prop) [DecidableRel J] (s : Bool) (w : PureNode C) :
    (∀ c, ¬ approved J (pureSimple w) (pureNode N s w) c) ∨
    (∃ u v : PureNode C, pureRank N u < pureRank N w ∧ pureRank N v < pureRank N w ∧
      ¬ pureSimple w ∧ ∀ X, pureNode N s w X ↔ pureNode N s u X ∧ pureNode N s v X) ∨
    ((∀ e ∈ pureArcs N C, pureSrc N e = w → pureRank N (pureDst N e) < pureRank N w ∧
      (pureSimple w → pureSimple (pureDst N e))) ∧
      ∀ X, pureNode N s w X ↔
        ∃ e ∈ pureArcs N C, pureSrc N e = w ∧ pureNode N s (pureDst N e) X) := by
  classical
  rcases w with (⟨d, w⟩ | w) | e
  · rcases wire_cases (N + N) C.size w with hin | ⟨k, rfl⟩ | hmiss
    · left
      apply no_approved_small
      apply Finset.card_le_one_iff.mpr
      intro p q hp hq
      obtain ⟨_, p', hp', hpt⟩ := (one_input hin).mp ((mem_single _ _).mp hp)
      obtain ⟨_, q', hq', hqt⟩ := (one_input hin).mp ((mem_single _ _).mp hq)
      obtain rfl : p' = p := hp'
      obtain rfl : q' = q := hq'
      exact tag_inj (hpt.trans hqt.symm)
    · rcases op_kind h k with ho | ho
      · fin_cases d
        · left
          apply no_approved_small
          apply Finset.card_le_one_iff.mpr
          intro p q hp _
          have hh := (one_and_small h ho (by decide)).mp ((mem_single _ _).mp hp)
          exact (by decide : (1 : ℕ) ≠ 2) hh.1 |>.elim
        · right; left
          exact ⟨pfwd 0 (operand C k 0), pfwd 0 (operand C k 1), earlier h k 0, earlier h k 1,
            by change (1 : Fin 2) ≠ 0; decide, fun X => by
              change oneSide N C s (outWire (N + N) k) 2 X ↔
                oneSide N C s (operand C k 0) 1 X ∧ oneSide N C s (operand C k 1) 1 X
              simpa using (one_and_small h ho (by decide : (2 : ℕ) ≤ 2) (s := s) (X := X))⟩
      · right; right
        constructor
        · rintro (⟨i, e⟩ | e) _ he
          · change Sum.inl (Sum.inl (i, atWire N e)) = Sum.inl (Sum.inl (d, outWire (N + N) k)) at he
            obtain ⟨rfl, hw⟩ := Prod.mk.inj (Sum.inl.inj (Sum.inl.inj he))
            exact ⟨by simpa [pureDst, pureRank, pfwd, hw] using earlier_occ h e, id⟩
          · simp [pureSrc, pbck] at he
        · intro X
          change oneSide N C s (outWire (N + N) k) (1 + d.val) X ↔ _
          rw [one_or h ho]
          constructor
          · rintro ⟨i, hi⟩
            exact ⟨.inl (d, (k, i)), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho⟩, rfl, hi⟩
          · rintro ⟨(⟨j, e⟩ | e), _, hi, ht⟩
            · change Sum.inl (Sum.inl (j, atWire N e)) = Sum.inl (Sum.inl (d, outWire (N + N) k)) at hi
              obtain ⟨rfl, hh⟩ := Prod.mk.inj (Sum.inl.inj (Sum.inl.inj hi))
              have heq := at_eq hh
              exact ⟨e.2, by simpa [pureNode, pureDst, pfwd, fromWire, heq] using ht⟩
            · simp [pureSrc, pbck] at hi
    · left
      apply no_approved_small
      apply Finset.card_le_one_iff.mpr
      intro p q hp _
      have hh : oneSide N C s w (1 + d.val) {p} := (mem_single _ _).mp hp
      exact (ohom_void hmiss hh).elim
  · right; right
    constructor
    · rintro (⟨d, e⟩ | e) _ he
      · simp [pureSrc, pfwd] at he
      · have heq : fromWire e = w := by simpa [pureSrc, pbck] using he
        have hh := earlier_occ h e
        have hb := at_bound N e
        have hb' := earlier_other h e
        by_cases ho : orAt e
        · refine ⟨?_, fun _ => by simp [pureDst, ho, pbck, pureSimple]⟩
          simp [pureDst, ho, pureRank, pbck]
          omega
        · refine ⟨?_, fun _ => by simp [pureDst, ho, pfwd, pureSimple]⟩
          simp [pureDst, ho, pureRank, pbck, pfwd]
          omega
    · intro X
      change backOne N C s w X ↔ _
      rw [backOne_head]
      constructor
      · rintro ⟨e, he, ⟨ho, ht⟩ | ⟨ha, hp, ht⟩⟩
        · exact ⟨.inr e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ho⟩, by simpa [pureSrc, pbck] using he,
            by simpa [pureNode, pureDst, ho, pbck] using ht⟩
        · have hn : ¬ orAt e := fun ho => GateOp.noConfusion (ha.symm.trans ho)
          exact ⟨.inr e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨ha, hp⟩⟩, by simpa [pureSrc, pbck] using he,
            by simpa [pureNode, pureDst, hn, pfwd] using ht⟩
      · rintro ⟨(e | e), he, hp, ht⟩
        · obtain ⟨d, e⟩ := e
          simp [pureSrc, pfwd] at hp
        · have heq : fromWire e = w := by simpa [pureSrc, pbck] using hp
          by_cases ho : orAt e
          · exact ⟨e, heq, Or.inl ⟨ho, by simpa [pureNode, pureDst, ho, pbck] using ht⟩⟩
          · have hAnd : endAnd N e := ((Finset.mem_filter.mp he).2 : orAt e ∨ endAnd N e).resolve_left ho
            exact ⟨e, heq, Or.inr ⟨hAnd.1, hAnd.2, by simpa [pureNode, pureDst, ho, pfwd] using ht⟩⟩
  · right; left
    refine ⟨pfwd 0 (fromWire e), pbck (atWire N e), ?_, ?_, not_false, fun _ => Iff.rfl⟩
    · have := earlier_occ h e
      have := at_bound N e
      simp [pureRank, pfwd]
      omega
    · simp [pureRank, pbck]
      omega

end PureNetwork


section Rectangles


variable {A B R : Type*} [Fintype A] [Fintype B]
variable (I : A → B → Prop) [DecidableRel I]
variable (f : R → Set A → Prop) (g : R → Set B → Prop)

private def mixHit (S : Set R) (X : Set A) (Y : Set B) : Prop :=
  ∃ r ∈ S, f r X ∧ g r Y

private def safe (U : Set A → Set B → Prop) : Prop :=
  ∀ X Y, U X Y → ∃ p ∈ X, ∃ l ∈ Y, I p l

private def little (r : R) : Prop :=
  ((single (f r)).card ≤ 1 ∧ (single (g r)).card ≤ 3) ∨
    ((single (f r)).card ≤ 3 ∧ (single (g r)).card ≤ 1)

private def badL (S : Set R) (l : B) : Prop :=
  ∃ r ∈ S, single (g r) = {l} ∧ ¬ almost I (single (f r)) l

private def badP (S : Set R) (p : A) : Prop :=
  ∃ r ∈ S, single (f r) = {p} ∧ ¬ almost (fun l p => I p l) (single (g r)) p

private lemma swapped_free (hf : fourFree I) : fourFree (fun l p => I p l) := by
  intro p q hp a b hap haq hbp hbq
  by_contra hne
  exact hp (hf hne hap hbp haq hbq)

private lemma opposite_bad_adj (hf : fourFree I)
    (Sf : ∀ r X, f r X ↔ ∃ a ∈ single (f r), a ∈ X)
    (Sg : ∀ r Y, g r Y ↔ ∃ b ∈ single (g r), b ∈ Y)
    {U V : Set R} (hUV : safe I (fun X Y => mixHit f g U X Y ∧ mixHit f g V X Y))
    {p : A} {l : B} (hl : badL I f g U l) (hp : badP I f g V p) : I p l := by
  classical
  obtain ⟨r, hr, hrl, hA⟩ := hl
  obtain ⟨s, hs, hsp, hB⟩ := hp
  let Ar := (single (f r)).filter (fun p' => ¬ I p' l)
  let Bs := (single (g s)).filter (fun l' => ¬ I p l')
  have hAr : 1 < Ar.card := Nat.lt_of_not_ge hA
  have hBs : 1 < Bs.card := Nat.lt_of_not_ge hB
  by_contra hpl
  have hfind : ∃ p' ∈ Ar, ∃ l' ∈ Bs, ¬ I p' l' := by
    by_contra! hall
    obtain ⟨p₁, p₂, ha₁, ha₂, hpp⟩ := Finset.one_lt_card_iff.mp hAr
    obtain ⟨l₁, l₂, hb₁, hb₂, hll⟩ := Finset.one_lt_card_iff.mp hBs
    exact hpp (hf hll (hall p₁ ha₁ l₁ hb₁) (hall p₁ ha₁ l₂ hb₂)
      (hall p₂ ha₂ l₁ hb₁) (hall p₂ ha₂ l₂ hb₂))
  obtain ⟨p', hpr, l', hls, hcross⟩ := hfind
  have hp' := Finset.mem_filter.mp hpr
  have hl' := Finset.mem_filter.mp hls
  have hr' : mixHit f g U ({p, p'} : Set A) ({l, l'} : Set B) :=
    ⟨r, hr, (Sf _ _).mpr ⟨p', hp'.1, by simp⟩, (Sg _ _).mpr ⟨l, by simp [hrl], by simp⟩⟩
  have hs' : mixHit f g V ({p, p'} : Set A) ({l, l'} : Set B) :=
    ⟨s, hs, (Sf _ _).mpr ⟨p, by simp [hsp], by simp⟩, (Sg _ _).mpr ⟨l', hl'.1, by simp⟩⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hUV _ _ ⟨hr', hs'⟩
  rcases Set.mem_insert_iff.mp ha with rfl | ha
  · rcases Set.mem_insert_iff.mp hb with rfl | hb
    · exact hpl hab
    · obtain rfl : b = l' := hb
      exact hl'.2 hab
  · obtain rfl : a = p' := ha
    rcases Set.mem_insert_iff.mp hb with rfl | hb
    · exact hp'.2 hab
    · obtain rfl : b = l' := hb
      exact hcross hab

private def pureGood (p : A) (l : B) : Prop :=
  (∃ r, p ∈ single (f r) ∧ approved I True (f r) l) ∨
    ∃ r, l ∈ single (g r) ∧ approved (fun l p => I p l) True (g r) p

private def smallGood (p : A) (l : B) : Prop :=
  ∃ r, little f g r ∧ p ∈ single (f r) ∧ l ∈ single (g r)

private lemma classify_same (p : A) (l : B) (r : R)
    (hp : p ∈ single (f r)) (hl : l ∈ single (g r))
    (hx : clean I (f r) l) (hy : clean (fun l p => I p l) (g r) p) :
    pureGood I f g p l ∨ smallGood f g p l := by
  by_cases h2 : 2 ≤ (single (f r)).card
  · exact Or.inl (Or.inl ⟨r, hp, Or.inl ⟨h2, hx⟩⟩)
  by_cases hg2 : 2 ≤ (single (g r)).card
  · exact Or.inl (Or.inr ⟨r, hl, Or.inl ⟨hg2, hy⟩⟩)
  exact Or.inr ⟨r, Or.inl ⟨by omega, by omega⟩, hp, hl⟩

private lemma singleton_of_small {T : Type*} [DecidableEq T] {s : Finset T}
    {a : T} (h : a ∈ s) (hc : s.card ≤ 1) : s = {a} := by
  ext b
  simp only [Finset.mem_singleton]
  exact ⟨fun hb => Finset.card_le_one_iff.mp hc hb h, fun e => e ▸ h⟩

private lemma classify_opposite {U V : Set R} {p : A} {l : B} {r s : R}
    (hr : r ∈ U) (hs : s ∈ V) (hpr : p ∈ single (f r)) (hlr : l ∈ single (g r))
    (hps : p ∈ single (f s)) (hls : l ∈ single (g s))
    (hY : clean (fun l p => I p l) (g r) p) (hX : clean I (f s) l) :
    (pureGood I f g p l ∨ smallGood f g p l) ∨ (badL I f g U l ∧ badP I f g V p) := by
  classical
  by_cases hy2 : 2 ≤ (single (g r)).card
  · exact Or.inl (Or.inl (Or.inr ⟨r, hlr, Or.inl ⟨hy2, hY⟩⟩))
  by_cases hx2 : 2 ≤ (single (f s)).card
  · exact Or.inl (Or.inl (Or.inl ⟨s, hps, Or.inl ⟨hx2, hX⟩⟩))
  by_cases hRa : almost I (single (f r)) l
  · by_cases hR4 : 4 ≤ (single (f r)).card
    · exact Or.inl (Or.inl (Or.inl ⟨r, hpr, Or.inr ⟨trivial, hR4, hRa⟩⟩))
    · exact Or.inl (Or.inr ⟨r, Or.inr ⟨by omega, by omega⟩, hpr, hlr⟩)
  by_cases hSa : almost (fun l p => I p l) (single (g s)) p
  · by_cases hS4 : 4 ≤ (single (g s)).card
    · exact Or.inl (Or.inl (Or.inr ⟨s, hls, Or.inr ⟨trivial, hS4, hSa⟩⟩))
    · exact Or.inl (Or.inr ⟨s, Or.inl ⟨by omega, by omega⟩, hps, hls⟩)
  exact Or.inr ⟨⟨r, hr, singleton_of_small hlr (by omega), hRa⟩,
    ⟨s, hs, singleton_of_small hps (by omega), hSa⟩⟩

private lemma classify_product {U V : Set R}
    (hUV : safe I (fun X Y => mixHit f g U X Y ∧ mixHit f g V X Y))
    {p : A} {l : B} (hU : mixHit f g U {p} {l}) (hV : mixHit f g V {p} {l}) :
    (pureGood I f g p l ∨ smallGood f g p l) ∨
      (badL I f g U l ∧ badP I f g V p) ∨ (badL I f g V l ∧ badP I f g U p) := by
  classical
  obtain ⟨r, hr, hpr, hlr⟩ := hU
  obtain ⟨s, hs, hps, hls⟩ := hV
  let X := {a | ¬ I a l}
  let Y := {b | ¬ I p b}
  have hX : ¬ (mixHit f g U X {l} ∧ mixHit f g V X {l}) := by
    intro h
    obtain ⟨a, ha, b, hb, hi⟩ := hUV _ _ h
    obtain rfl : b = l := hb
    exact ha hi
  have hY : ¬ (mixHit f g U {p} Y ∧ mixHit f g V {p} Y) := by
    intro h
    obtain ⟨a, ha, b, hb, hi⟩ := hUV _ _ h
    obtain rfl : a = p := ha
    exact hb hi
  have hx : clean I (f r) l ∨ clean I (f s) l := by
    by_cases ha : f r X
    · exact Or.inr (fun hb => hX ⟨⟨r, hr, ha, hlr⟩, ⟨s, hs, hb, hls⟩⟩)
    · exact Or.inl ha
  have hy : clean (fun l p => I p l) (g r) p ∨ clean (fun l p => I p l) (g s) p := by
    by_cases ha : g r Y
    · exact Or.inr (fun hb => hY ⟨⟨r, hr, hpr, ha⟩, ⟨s, hs, hps, hb⟩⟩)
    · exact Or.inl ha
  have hpr' := (mem_single _ _).mpr hpr
  have hlr' := (mem_single _ _).mpr hlr
  have hps' := (mem_single _ _).mpr hps
  have hls' := (mem_single _ _).mpr hls
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Or.inl (classify_same I f g p l r hpr' hlr' hx hy)
  · exact (classify_opposite I f g hs hr hps' hls' hpr' hlr' hy hx).imp id Or.inr
  · exact (classify_opposite I f g hr hs hpr' hlr' hps' hls' hy hx).imp id Or.inl
  · exact Or.inl (classify_same I f g p l s hps' hls' hx hy)

private lemma classify_direct
    (U : Set A → Prop) (V : Set B → Prop)
    (hUV : safe I (fun X Y => U X ∧ V Y))
    (p : A) (l : B) (hp : U {p}) (hl : V {l}) :
    (approved I False U l ∨ approved (fun l p => I p l) False V p) ∨
      ((single U).card ≤ 1 ∧ (single V).card ≤ 1) := by
  have hx : clean I U l := by
    intro hm
    obtain ⟨a, ha, b, hb, hi⟩ := hUV _ _ ⟨hm, hl⟩
    obtain rfl : b = l := hb
    exact ha hi
  have hy : clean (fun l p => I p l) V p := by
    intro hm
    obtain ⟨a, ha, b, hb, hi⟩ := hUV _ _ ⟨hp, hm⟩
    obtain rfl : a = p := ha
    exact hb hi
  by_cases ha : 2 ≤ (single U).card
  · exact Or.inl (Or.inl (Or.inl ⟨ha, hx⟩))
  by_cases hb : 2 ≤ (single V).card
  · exact Or.inl (Or.inr (Or.inl ⟨hb, hy⟩))
  exact Or.inr ⟨by omega, by omega⟩

end Rectangles


section MixedNetwork

open Finset Relation PEqualNP.CircuitLowerBounds

private abbrev Rect (C : Circuit) := Occ C ⊕ (Occ C × Fin 2)
private abbrev MixNode (C : Circuit) := (ℕ ⊕ ℕ) ⊕ Rect C

private def mfwd {C : Circuit} (w : ℕ) : MixNode C := .inl (.inl w)
private def mbck {C : Circuit} (w : ℕ) : MixNode C := .inl (.inr w)
private def mleaf {C : Circuit} (r : Rect C) : MixNode C := .inr r

private def rectPoint (N : ℕ) {C : Circuit} : Rect C → PureNode C
  | .inl e => pfwd 0 (fromWire e)
  | .inr (e, i) => if i = 0 then pfwd 0 (otherWire e) else pbck (atWire N e)

private def rectLine (N : ℕ) {C : Circuit} : Rect C → PureNode C
  | .inl e => pfwd 0 (otherWire e)
  | .inr (e, i) => if i = 0 then pbck (atWire N e) else pfwd 0 (otherWire e)

private def rpoint (N : ℕ) {C : Circuit} (r : Rect C) : Set (Fin N) → Prop :=
  pureNode N false (rectPoint N r)

private def rline (N : ℕ) {C : Circuit} (r : Rect C) : Set (Fin N) → Prop :=
  pureNode N true (rectLine N r)

private lemma rectPoint_simple (N : ℕ) {C : Circuit} (r : Rect C) :
    pureSimple (rectPoint N r) := by
  rcases r with e | ⟨e, i⟩
  · rfl
  · fin_cases i <;> simp [rectPoint, pfwd, pbck, pureSimple]

private lemma rectLine_simple (N : ℕ) {C : Circuit} (r : Rect C) :
    pureSimple (rectLine N r) := by
  rcases r with e | ⟨e, i⟩
  · rfl
  · fin_cases i <;> simp [rectLine, pfwd, pbck, pureSimple]

private def mixFamily (N : ℕ) {C : Circuit} : MixNode C → Set (Rect C)
  | .inl (.inl w) => {r | ∃ e : Occ C, r = .inl e ∧ andAt e ∧ orPath N C (atWire N e) w}
  | .inl (.inr w) => {r | ∃ e : Occ C, ∃ i : Fin 2, r = .inr (e, i) ∧ andAt e ∧
      orPath N C w (fromWire e)}
  | .inr r => {r}

private lemma mixFwd_spec {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (w : ℕ) (X Y : Set (Fin N)) :
    mixHit (rpoint N) (rline N) (mixFamily N (mfwd (C := C) w)) X Y ↔ Hom N C w 1 1 X Y := by
  rw [mixed11 h]
  constructor
  · rintro ⟨_, ⟨e, rfl, he, hp⟩, hX, hY⟩
    exact ⟨e, he, hp, hX, hY⟩
  · rintro ⟨e, he, hp, hX, hY⟩
    exact ⟨.inl e, ⟨e, rfl, he, hp⟩, hX, hY⟩

private lemma mixBack_apply {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    {w a b : ℕ} {X Y : Set (Fin N)}
    (hb : mixHit (rpoint N) (rline N) (mixFamily N (mbck (C := C) w)) X Y)
    (hh : Hom N C w a b X Y) : Hom N C C.output (a + 1) (b + 1) X Y := by
  obtain ⟨_, ⟨e, i, rfl, he, hp⟩, hx, hy⟩ := hb
  fin_cases i
  · have hx' : oneSide N C false (otherWire e) 1 X := by
      simpa [rpoint, rectPoint, pureNode, pfwd] using hx
    have hy' : backOne N C true (atWire N e) Y := by
      simpa [rline, rectLine, pureNode, pbck] using hy
    have hj : Hom N C (atWire N e) (a + 1) b X Y :=
      hom_and_add h he e.2 (or_reaches h hp hh) (hom_pure_x.mpr hx')
    exact backOne_apply (s := true) h hy' hj
  · have hx' : backOne N C false (atWire N e) X := by
      simpa [rpoint, rectPoint, pureNode, pbck] using hx
    have hy' : oneSide N C true (otherWire e) 1 Y := by
      simpa [rline, rectLine, pureNode, pfwd] using hy
    have hj : Hom N C (atWire N e) a (b + 1) X Y :=
      hom_and_add h he e.2 (or_reaches h hp hh) (hom_pure_y.mpr hy')
    exact backOne_apply (s := false) h hx' hj

private lemma mixLeaf_spec (N : ℕ) {C : Circuit} (r : Rect C) (X Y : Set (Fin N)) :
    mixHit (rpoint N) (rline N) (mixFamily N (mleaf r)) X Y ↔ rpoint N r X ∧ rline N r Y := by
  simp [mixHit, mixFamily, mleaf]

private def mixRank (N : ℕ) {C : Circuit} : MixNode C → ℕ
  | .inl (.inl w) => w + 1
  | .inl (.inr w) => (N + N + C.size + 1 - w) + 1
  | .inr _ => 0

private def mixSrc (N : ℕ) {C : Circuit} : Rect C → MixNode C
  | .inl e => mfwd (atWire N e)
  | .inr (e, _) => mbck (fromWire e)

private noncomputable def mixDst (N : ℕ) {C : Circuit} (a : Rect C) : MixNode C := by
  classical
  exact match a with
  | .inl e => if orAt e then mfwd (fromWire e) else mleaf a
  | .inr (e, _) => if orAt e then mbck (atWire N e) else mleaf a

private lemma mixArc_rank {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (a : Rect C) : mixRank N (mixDst N a) < mixRank N (mixSrc N a) := by
  classical
  rcases a with e | ⟨e, i⟩
  · have := earlier_occ h e
    by_cases ho : orAt e <;> simp [mixDst, ho, mixRank, mixSrc, mfwd, mleaf] <;> omega
  · have := earlier_occ h e
    have := at_bound N e
    by_cases ho : orAt e <;> simp [mixDst, ho, mixRank, mixSrc, mbck, mleaf] <;> omega

private lemma mixFwd_next {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (w : ℕ) (r : Rect C) :
    r ∈ mixFamily N (mfwd w) ↔
      ∃ a : Rect C, mixSrc N a = mfwd w ∧ r ∈ mixFamily N (mixDst N a) := by
  classical
  constructor
  · rintro ⟨e, rfl, he, hp⟩
    rcases hp.cases_tail with heq | ⟨_, hp', ⟨a, ha, hf, hw⟩⟩
    · have hn : ¬ orAt e := fun ho => GateOp.noConfusion (he.symm.trans ho)
      exact ⟨.inl e, by simp [mixSrc, heq], by simp [mixDst, hn, mleaf, mixFamily]⟩
    · refine ⟨.inl a, by simp [mixSrc, hw], ?_⟩
      simp only [mixDst, ha, ite_true]
      exact ⟨e, rfl, he, hf ▸ hp'⟩
  · rintro ⟨(a | a), hs, ht⟩
    · have hw : atWire N a = w := by simpa [mixSrc, mfwd] using hs
      by_cases ha : orAt a
      · simp only [mixDst, ha, ite_true] at ht
        obtain ⟨e, rfl, he, hp⟩ := ht
        exact ⟨e, rfl, he, hp.tail ⟨a, ha, rfl, hw⟩⟩
      · have hn : andAt a := (op_kind h a.1).resolve_right ha
        have heq : r = .inl a := by simpa [mixDst, ha, mleaf, mixFamily] using ht
        exact ⟨a, heq, hn, hw ▸ ReflTransGen.refl⟩
    · obtain ⟨a, i⟩ := a
      simp [mixSrc, mbck, mfwd] at hs

private lemma mixBack_next {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (w : ℕ) (r : Rect C) :
    r ∈ mixFamily N (mbck w) ↔
      ∃ a : Rect C, mixSrc N a = mbck w ∧ r ∈ mixFamily N (mixDst N a) := by
  classical
  constructor
  · rintro ⟨e, i, rfl, he, hp⟩
    rcases orPath_head.mp hp with heq | ⟨a, ha, hf, ht⟩
    · have hn : ¬ orAt e := fun ho => GateOp.noConfusion (he.symm.trans ho)
      exact ⟨.inr (e, i), by simp [mixSrc, heq], by simp [mixDst, hn, mleaf, mixFamily]⟩
    · refine ⟨.inr (a, 0), by simp [mixSrc, hf], ?_⟩
      simp only [mixDst, ha, ite_true]
      exact ⟨e, i, rfl, he, ht⟩
  · rintro ⟨(a | ⟨a, i⟩), hs, ht⟩
    · simp [mixSrc, mfwd, mbck] at hs
    · have hw : fromWire a = w := by simpa [mixSrc, mbck] using hs
      by_cases ha : orAt a
      · simp only [mixDst, ha, ite_true] at ht
        obtain ⟨e, j, rfl, he, hp⟩ := ht
        exact ⟨e, j, rfl, he, orPath_head.mpr (Or.inr ⟨a, ha, hw, hp⟩)⟩
      · have hn : andAt a := (op_kind h a.1).resolve_right ha
        have heq : r = .inr (a, i) := by simpa [mixDst, ha, mleaf, mixFamily] using ht
        exact ⟨a, i, heq, hn, hw ▸ ReflTransGen.refl⟩

variable {N : ℕ} {C : Circuit}

private def centerLabel (I : Fin N → Fin N → Prop) [DecidableRel I]
    (s : Bool) (r : Rect C) (v : Fin N) : Prop := by
  classical
  exact if s then single (rline N r) = {v} ∧ ¬ almost I (single (rpoint N r)) v
    else single (rpoint N r) = {v} ∧ ¬ almost (fun l p => I p l) (single (rline N r)) v

private def centerNode (I : Fin N → Fin N → Prop) [DecidableRel I]
    (s : Bool) (w : MixNode C) (X : Set (Fin N)) : Prop :=
  ∃ r ∈ mixFamily N w, ∃ v ∈ X, centerLabel I s r v

private lemma center_mono (I : Fin N → Fin N → Prop) [DecidableRel I]
    (s : Bool) (w : MixNode C) : Monotone (centerNode I s w) :=
  fun _ _ h ⟨r, hr, v, hv, hl⟩ => ⟨r, hr, v, h hv, hl⟩

private lemma center_member (I : Fin N → Fin N → Prop) [DecidableRel I]
    (s : Bool) (w : MixNode C) (v : Fin N) :
    v ∈ single (centerNode I s w) ↔ ∃ r ∈ mixFamily N w, centerLabel I s r v := by
  simp [centerNode, mem_single]

private lemma center_linear (I : Fin N → Fin N → Prop) [DecidableRel I]
    (s : Bool) (w : MixNode C) (X : Set (Fin N)) :
    centerNode I s w X ↔ ∃ v ∈ single (centerNode I s w), v ∈ X := by
  simp only [center_member, centerNode]
  exact ⟨fun ⟨r, hr, v, hv, hl⟩ => ⟨v, ⟨r, hr, hl⟩, hv⟩,
    fun ⟨v, ⟨r, hr, hl⟩, hv⟩ => ⟨r, hr, v, hv, hl⟩⟩

private lemma center_rule (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (I : Fin N → Fin N → Prop) [DecidableRel I] (s : Bool)
    (J : Fin N → Fin N → Prop) [DecidableRel J] (w : MixNode C) :
    (∀ c, ¬ approved J True (centerNode I s w) c) ∨
    (∃ u v : MixNode C, mixRank N u < mixRank N w ∧ mixRank N v < mixRank N w ∧
      ¬ True ∧ ∀ X, centerNode I s w X ↔ centerNode I s u X ∧ centerNode I s v X) ∨
    ((∀ a ∈ (univ : Finset (Rect C)), mixSrc N a = w →
      mixRank N (mixDst N a) < mixRank N w ∧ (True → True)) ∧
      ∀ X, centerNode I s w X ↔
        ∃ a ∈ (univ : Finset (Rect C)), mixSrc N a = w ∧ centerNode I s (mixDst N a) X) := by
  classical
  have go (w : MixNode C) (hw : ∀ r, r ∈ mixFamily N w ↔
      ∃ a : Rect C, mixSrc N a = w ∧ r ∈ mixFamily N (mixDst N a)) :
      (∀ a ∈ (univ : Finset (Rect C)), mixSrc N a = w →
        mixRank N (mixDst N a) < mixRank N w ∧ (True → True)) ∧
      ∀ X, centerNode I s w X ↔
        ∃ a ∈ (univ : Finset (Rect C)), mixSrc N a = w ∧ centerNode I s (mixDst N a) X := by
    refine ⟨fun a _ he => ⟨he ▸ mixArc_rank h a, id⟩, ?_⟩
    intro X
    constructor
    · rintro ⟨r, hr, v, hv, ht⟩
      obtain ⟨a, he, ha⟩ := (hw r).mp hr
      exact ⟨a, Finset.mem_univ _, he, r, ha, v, hv, ht⟩
    · rintro ⟨a, _, he, r, ha, v, hv, ht⟩
      exact ⟨r, (hw r).mpr ⟨a, he, ha⟩, v, hv, ht⟩
  rcases w with (w | w) | r
  · exact Or.inr (Or.inr (go (mfwd w) (mixFwd_next h w)))
  · exact Or.inr (Or.inr (go (mbck w) (mixBack_next h w)))
  · left
    apply no_approved_small
    apply Finset.card_le_one_iff.mpr
    intro p q hp hq
    obtain ⟨r', hr, hpl⟩ := (center_member I s _ _).mp hp
    obtain ⟨r'', ht, hql⟩ := (center_member I s _ _).mp hq
    have he' : r' = r := hr
    have he'' : r'' = r := ht
    subst r'
    subst r''
    cases s
    · exact Finset.singleton_injective (hpl.1.symm.trans hql.1)
    · exact Finset.singleton_injective (hpl.1.symm.trans hql.1)

end MixedNetwork


section Products


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ} {C : Circuit}

private abbrev MixProduct (C : Circuit) := Fin C.size ⊕ Occ C
private abbrev PureProduct (C : Circuit) := Fin 3 × Occ C

private def validMixed (N : ℕ) {C : Circuit} : MixProduct C → Prop
  | .inl k => (row C k).op = GateOp.and ∧ orPath N C (outWire (N + N) k) C.output
  | .inr e => andAt e

private def leftMix {C : Circuit} : MixProduct C → MixNode C
  | .inl k => mfwd (operand C k 0)
  | .inr e => mleaf (.inl e)

private def rightMix (N : ℕ) {C : Circuit} : MixProduct C → MixNode C
  | .inl k => mfwd (operand C k 1)
  | .inr e => mbck (atWire N e)

private def validPure (N : ℕ) {C : Circuit} (d : PureProduct C) : Prop :=
  andAt d.2 ∧ (d.1 = 0 → orPath N C (atWire N d.2) C.output)

private def purePoint {C : Circuit} (d : PureProduct C) : PureNode C :=
  if d.1 = 2 then pjoin (flip d.2) else pfwd 1 (fromWire d.2)

private def pureLine {C : Circuit} (d : PureProduct C) : PureNode C :=
  if d.1 = 0 then pfwd 1 (otherWire d.2) else
    if d.1 = 1 then pjoin (flip d.2) else pfwd 1 (fromWire d.2)

private lemma pjoin_spec (N : ℕ) {C : Circuit} (s : Bool) (e : Occ C) (X : Set (Fin N)) :
    pureNode N s (pjoin (flip e)) X ↔
      oneSide N C s (otherWire e) 1 X ∧ backOne N C s (atWire N e) X := Iff.rfl

private lemma mixed_sound (h : PEqualNP.TopForm.IsAO2 (N + N) C) {t : MixProduct C}
    (ht : validMixed N t) {X Y : Set (Fin N)}
    (hl : mixHit (rpoint N) (rline N) (mixFamily N (leftMix t)) X Y)
    (hr : mixHit (rpoint N) (rline N) (mixFamily N (rightMix N t)) X Y) :
    Hom N C C.output 2 2 X Y := by
  rcases t with k | e
  · have ha := (mixFwd_spec h _ _ _).mp hl
    have hb := (mixFwd_spec h _ _ _).mp hr
    exact or_reaches h ht.2 (hom_and_add h ht.1 0 ha hb)
  · have hs := (mixLeaf_spec N (.inl e) X Y).mp hl
    have hm := hom_and_add h ht e.2 (hom_pure_x.mpr hs.1) (hom_pure_y.mpr hs.2)
    exact mixBack_apply h hr hm

private lemma pure_sound (h : PEqualNP.TopForm.IsAO2 (N + N) C) {d : PureProduct C}
    (hd : validPure N d) {X Y : Set (Fin N)}
    (hp : pureNode N false (purePoint d) X) (hl : pureNode N true (pureLine d) Y) :
    Hom N C C.output 2 2 X Y := by
  obtain ⟨t, e⟩ := d
  fin_cases t
  · have hp' : oneSide N C false (fromWire e) 2 X := hp
    have hl' : oneSide N C true (otherWire e) 2 Y := hl
    exact or_reaches h (hd.2 rfl) (hom_and_add h hd.1 e.2 (hom_pure_x.mpr hp') (hom_pure_y.mpr hl'))
  · have hp' : oneSide N C false (fromWire e) 2 X := hp
    have hl' := (pjoin_spec N true e Y).mp hl
    have hh : Hom N C (atWire N e) 2 1 X Y :=
      hom_and_add h hd.1 e.2 (hom_pure_x.mpr hp') (hom_pure_y.mpr hl'.1)
    exact backOne_apply (s := true) h hl'.2 hh
  · have hp' := (pjoin_spec N false e X).mp hp
    have hl' : oneSide N C true (fromWire e) 2 Y := hl
    have hh : Hom N C (atWire N e) 1 2 X Y :=
      hom_and_add h hd.1 e.2 (hom_pure_y.mpr hl') (hom_pure_x.mpr hp'.1)
    exact backOne_apply (s := false) h hp'.2 hh

private def mixedTerm (N : ℕ) {C : Circuit} (t : MixProduct C) (X Y : Set (Fin N)) : Prop :=
  mixHit (rpoint N) (rline N) (mixFamily N (leftMix t)) X Y ∧
    mixHit (rpoint N) (rline N) (mixFamily N (rightMix N t)) X Y

private def pureTerm (N : ℕ) {C : Circuit} (d : PureProduct C) (X Y : Set (Fin N)) : Prop :=
  pureNode N false (purePoint d) X ∧ pureNode N true (pureLine d) Y

private lemma product_normal (h : PEqualNP.TopForm.IsAO2 (N + N) C) {X Y : Set (Fin N)}
    (hw : Hom N C C.output 2 2 X Y) :
    (∃ t : MixProduct C, validMixed N t ∧ mixedTerm N t X Y) ∨
    (∃ d : PureProduct C, validPure N d ∧ pureTerm N d X Y) := by
  rcases mixed22 h hw with ⟨k, ha, ht, h₁, h₂⟩ | ⟨e, ha, ht, (⟨hp, hl⟩ | ⟨hh, hl⟩ | ⟨hh, hp⟩)⟩
  · exact Or.inl ⟨.inl k, ⟨ha, ht⟩, (mixFwd_spec h _ _ _).mpr h₁, (mixFwd_spec h _ _ _).mpr h₂⟩
  · exact Or.inr ⟨(0, e), ⟨ha, fun _ => ht⟩, hp, hl⟩
  · obtain ⟨e', he', hp', (⟨hy, hx⟩ | ⟨hm, hz⟩)⟩ := mixed21 (s := false) h hh
    · have hb : backOne N C true (atWire N e') Y := ⟨e, ha, hp', ht, hl⟩
      exact Or.inr ⟨(1, e'), ⟨he', fun hf => ((by decide : (1 : Fin 3) ≠ 0) hf).elim⟩,
        hy, (pjoin_spec N true e' Y).mpr ⟨hx, hb⟩⟩
    · have hb : backOne N C true (atWire N e') Y := ⟨e, ha, hp', ht, hl⟩
      obtain ⟨r, hra, hpath, hP, hL⟩ := (mixed11 h).mp hm
      exact Or.inl ⟨.inr r, hra, (mixLeaf_spec N (.inl r) X Y).mpr ⟨hP, hL⟩,
        ⟨.inr (e', 0), ⟨e', 0, rfl, he', hpath⟩, hz, hb⟩⟩
  · obtain ⟨e', he', hp', (⟨hy, hx⟩ | ⟨hm, hz⟩)⟩ := mixed21 (s := true) h hh
    · have hb : backOne N C false (atWire N e') X := ⟨e, ha, hp', ht, hp⟩
      exact Or.inr ⟨(2, e'), ⟨he', fun hf => ((by decide : (2 : Fin 3) ≠ 0) hf).elim⟩,
        (pjoin_spec N false e' X).mpr ⟨hx, hb⟩, hy⟩
    · have hb : backOne N C false (atWire N e') X := ⟨e, ha, hp', ht, hp⟩
      obtain ⟨r, hra, hpath, hP, hL⟩ := (mixed11 h).mp hm
      exact Or.inl ⟨.inr r, hra, (mixLeaf_spec N (.inl r) X Y).mpr ⟨hP, hL⟩,
        ⟨.inr (e', 1), ⟨e', 1, rfl, he', hpath⟩, hb, hz⟩⟩

end Products


section Accounting


open Finset PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def exchange {N : ℕ} (S : Finset (Fin N × Fin N)) : Finset (Fin N × Fin N) :=
  S.map (Equiv.prodComm (Fin N) (Fin N)).toEmbedding

private lemma exchange_card {N : ℕ} (S : Finset (Fin N × Fin N)) :
    (exchange S).card = S.card := Finset.card_map _

private lemma exchange_mem {N : ℕ} {S : Finset (Fin N × Fin N)} {p l : Fin N}
    (h : (l, p) ∈ S) : (p, l) ∈ exchange S :=
  Finset.mem_map.mpr ⟨(l, p), h, rfl⟩

private lemma in_cover {A B W : Type*} [Fintype A] [Fintype B]
    (I : A → B → Prop) [DecidableRel I] {f : W → Set A → Prop} {s : W → Prop}
    {p : A} {l : B} (hi : I p l) (w : W) (ha : approved I (s w) (f w) l)
    (hp : p ∈ single (f w)) : (p, l) ∈ edgeCover I f s := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, w, ha, hp⟩

private noncomputable def singletonPay {N : ℕ} (f g : Set (Fin N) → Prop) :
    Finset (Fin N × Fin N) := by
  classical
  exact if (single f).card ≤ 1 ∧ (single g).card ≤ 1 then (single f) ×ˢ (single g) else ∅

private lemma singletonPay_mem {N : ℕ} {f g : Set (Fin N) → Prop} {p l : Fin N}
    (hp : p ∈ single f) (hl : l ∈ single g) (hs : (single f).card ≤ 1 ∧ (single g).card ≤ 1) :
    (p, l) ∈ singletonPay f g := by
  classical
  simp [singletonPay, hs, hp, hl]

variable {N : ℕ} {C : Circuit}
variable (I : Fin N → Fin N → Prop) [DecidableRel I]

private noncomputable def rectPay (N : ℕ) {C : Circuit} (r : Rect C) : Finset (Fin N × Fin N) := by
  classical
  exact if little (rpoint N) (rline N) r then
    single (rpoint N r) ×ˢ single (rline N r) else ∅

private def centerPoint (N : ℕ) {C : Circuit} (t : MixProduct C) (rev : Bool) : MixNode C :=
  if rev then leftMix t else rightMix N t

private def centerLine (N : ℕ) {C : Circuit} (t : MixProduct C) (rev : Bool) : MixNode C :=
  if rev then rightMix N t else leftMix t

private noncomputable def mixedPay (t : MixProduct C × Bool) : Finset (Fin N × Fin N) :=
  singletonPay (centerNode I false (centerPoint N t.1 t.2)) (centerNode I true (centerLine N t.1 t.2))

private noncomputable def purePay (d : PureProduct C) : Finset (Fin N × Fin N) :=
  singletonPay (pureNode N false (purePoint d)) (pureNode N true (pureLine d))

private noncomputable def pureCover (N : ℕ) (C : Circuit) (I : Fin N → Fin N → Prop)
    [DecidableRel I] : Finset (Fin N × Fin N) :=
  edgeCover I (pureNode N (C := C) false) pureSimple ∪
  exchange (edgeCover (fun l p => I p l) (pureNode N (C := C) true) pureSimple)

private lemma covered_by_pure {p l : Fin N} (hi : I p l)
    (h : pureGood I (rpoint N (C := C)) (rline N) p l) : (p, l) ∈ pureCover N C I := by
  rcases h with ⟨r, hp, ha⟩ | ⟨r, hl, ha⟩
  · apply Finset.mem_union_left
    apply in_cover I hi (rectPoint N r) _ hp
    change approved I (pureSimple (rectPoint N r)) (rpoint N r) l
    simpa only [rectPoint_simple] using ha
  · apply Finset.mem_union_right
    apply exchange_mem
    apply in_cover (fun l p => I p l) hi (rectLine N r) _ hl
    change approved (fun l p => I p l) (pureSimple (rectLine N r)) (rline N r) p
    simpa only [rectLine_simple] using ha

private lemma pure_charges (d : PureProduct C) (hs : safe I (pureTerm N d))
    (p l : Fin N) (hi : I p l) (hTerm : pureTerm N d {p} {l}) :
    (p, l) ∈ pureCover N C I ∨ (p, l) ∈ purePay d := by
  have hp := (mem_single _ _).mpr hTerm.1
  have hl := (mem_single _ _).mpr hTerm.2
  rcases classify_direct I _ _ hs p l hTerm.1 hTerm.2 with (ha | ha) | ha
  · exact Or.inl (Finset.mem_union_left _ (in_cover I hi _ (Or.inl (ha.resolve_right (fun hx => hx.1))) hp))
  · exact Or.inl (Finset.mem_union_right _ (exchange_mem
      (in_cover (fun l p => I p l) hi _ (Or.inl (ha.resolve_right (fun hx => hx.1))) hl)))
  · exact Or.inr (singletonPay_mem hp hl ha)

private noncomputable def twiceEdges (N : ℕ) (C : Circuit) (I : Fin N → Fin N → Prop)
    [DecidableRel I] : Finset (Fin N × Fin N) := by
  classical
  exact univ.filter fun e => I e.1 e.2 ∧ Hom N C C.output 2 2 {e.1} {e.2}

end Accounting


section GateAccounting

open Finset PEqualNP.CircuitLowerBounds

private noncomputable def andRows (C : Circuit) : Finset (Fin C.size) := by
  classical
  exact univ.filter fun k => (row C k).op = GateOp.and

private noncomputable def orRows (C : Circuit) : Finset (Fin C.size) := by
  classical
  exact univ.filter fun k => (row C k).op = GateOp.or

private lemma orRows_mem {C : Circuit} (k : Fin C.size) :
    k ∈ orRows C ↔ (row C k).op = GateOp.or := by
  classical
  simp [orRows]

private lemma andRows_mem {C : Circuit} (k : Fin C.size) :
    k ∈ andRows C ↔ (row C k).op = GateOp.and := by
  classical
  simp [andRows]

private lemma gate_card_sum {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C) :
    (orRows C).card + (andRows C).card = C.size := by
  classical
  have heq : andRows C = univ.filter fun k => ¬ (row C k).op = GateOp.or := by
    ext k
    simp only [andRows_mem, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ha ho
      exact GateOp.noConfusion (ha.symm.trans ho)
    · exact (op_kind h k).resolve_right
  rw [heq, orRows, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]

private lemma pure_bound_by_ops {N : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 (N + N) C)
    (J : Fin N → Fin N → Prop) [DecidableRel J] (hf : fourFree J) (s : Bool) :
    (edgeCover J (pureNode N (C := C) s) pureSimple).card ≤
      12 * (orRows C).card + 4 * (andRows C).card := by
  classical
  have hCover := cover_bound J hf (pureNode N (C := C) s) pureSimple (pureRank N)
    (pureArcs N C) (pureSrc N) (pureDst N) (pureNode_mono N s) (pureNode_linear h s) (pure_rule h J s)
  let O : Finset (Occ C) := (orRows C) ×ˢ univ
  let A : Finset (Occ C) := (andRows C) ×ˢ univ
  let S : Finset (PureArc C) := (univ ×ˢ O).disjSum (O ∪ A)
  have hsub : pureArcs N C ⊆ S := by
    intro e he
    have hp := (mem_filter.mp he).2
    rcases e with ⟨d, e⟩ | e
    · have he : e ∈ O := by simpa [O, orRows_mem, orAt] using hp
      exact mem_disjSum.mpr (Or.inl ⟨(d,e), mem_product.mpr ⟨mem_univ _, he⟩, rfl⟩)
    · refine mem_disjSum.mpr (Or.inr ⟨e, ?_, rfl⟩)
      rcases hp with hp | hp
      · exact mem_union_left _ (by simpa [O, orRows_mem, orAt] using hp)
      · exact mem_union_right _ (by simpa [A, andRows_mem, andAt] using hp.1)
  have hS : S.card ≤ 6 * (orRows C).card + 2 * (andRows C).card := by
    have hu := card_union_le O A
    have ho : O.card = 2 * (orRows C).card := by simp [O, Nat.mul_comm]
    have ha : A.card = 2 * (andRows C).card := by simp [A, Nat.mul_comm]
    simp only [S, card_disjSum, card_product, card_univ, Fintype.card_fin]
    omega
  have hA := (card_le_card hsub).trans hS
  omega

end GateAccounting


section CleanCenterAccounting

open Finset PEqualNP.CircuitLowerBounds

private noncomputable def cleanEdgeCover {A B W : Type*} [Fintype A] [Fintype B]
    (J : A → B → Prop) [DecidableRel J] (f : W → Set A → Prop) : Finset (A × B) := by
  classical
  exact univ.filter fun e => J e.1 e.2 ∧
    ∃ w, 2 ≤ (single (f w)).card ∧ clean J (f w) e.2 ∧ e.1 ∈ single (f w)

private noncomputable def cleanPay {A B W : Type*} [Fintype A] [Fintype B]
    (J : A → B → Prop) [DecidableRel J] (f : W → Set A → Prop) (u v : W) : Finset (A × B) := by
  classical
  exact univ.filter fun e => J e.1 e.2 ∧ 2 ≤ (single (f u)).card ∧
    clean J (f u) e.2 ∧ (single (f v)).card ≤ 1 ∧ e.1 ∈ single (f v)

private lemma cleanEdgeCover_mem {A B W : Type*} [Fintype A] [Fintype B]
    (J : A → B → Prop) [DecidableRel J] (f : W → Set A → Prop) (e : A × B) :
    e ∈ cleanEdgeCover J f ↔ J e.1 e.2 ∧
      ∃ w, 2 ≤ (single (f w)).card ∧ clean J (f w) e.2 ∧ e.1 ∈ single (f w) := by
  classical
  simp [cleanEdgeCover]

private lemma cleanPay_mem {A B W : Type*} [Fintype A] [Fintype B]
    (J : A → B → Prop) [DecidableRel J] (f : W → Set A → Prop) (u v : W) (e : A × B) :
    e ∈ cleanPay J f u v ↔ J e.1 e.2 ∧ 2 ≤ (single (f u)).card ∧
      clean J (f u) e.2 ∧ (single (f v)).card ≤ 1 ∧ e.1 ∈ single (f v) := by
  classical
  simp [cleanPay]

private lemma cleanPay_card {A B W : Type*} [Fintype A] [Fintype B]
    (J : A → B → Prop) [DecidableRel J] (hf : fourFree J)
    (f : W → Set A → Prop) (u v : W) (hm : Monotone (f u)) :
    (cleanPay J f u v).card ≤ 1 := by
  classical
  apply Finset.card_le_one_iff.mpr
  intro a b ha hb
  obtain ⟨_, hsize, hac, hsmall, ham⟩ := (cleanPay_mem J f u v a).mp ha
  obtain ⟨_, _, hbc, _, hbm⟩ := (cleanPay_mem J f u v b).mp hb
  exact Prod.ext (Finset.card_le_one_iff.mp hsmall ham hbm)
    (exact_unique J hf hm hsize hac hbc)

private lemma center_descend {N : ℕ} {C : Circuit}
    (h : PEqualNP.TopForm.IsAO2 (N+N) C)
    (I : Fin N → Fin N → Prop) [DecidableRel I] (s : Bool)
    (J : Fin N → Fin N → Prop) [DecidableRel J] (a b : Fin N) (hi : J a b)
    (w : MixNode C) (hbig : 2 ≤ (single (centerNode I s w)).card)
    (hclean : clean J (centerNode I s w) b) (hm : a ∈ single (centerNode I s w)) :
    ∃ r : Rect C, (a,b) ∈ cleanPay J (centerNode I s) (mixSrc N r) (mixDst N r) := by
  classical
  induction heq : mixRank N w using Nat.strong_induction_on generalizing w with
  | ind k ih =>
    rcases center_rule h I s J w with hno | ⟨_, _, _, _, bad, _⟩ | ⟨hdown, hor⟩
    · exact (hno b (Or.inl ⟨hbig,hclean⟩)).elim
    · exact (bad trivial).elim
    · obtain ⟨r, hr, hs, ht⟩ := (hor _).mp ((mem_single _ _).mp hm)
      have ht' := (mem_single _ _).mpr ht
      have hcd : clean J (centerNode I s (mixDst N r)) b := by
        intro bad
        exact hclean ((hor _).mpr ⟨r,hr,hs,bad⟩)
      by_cases hd : 2 ≤ (single (centerNode I s (mixDst N r))).card
      · exact ih _ (heq ▸ (hdown r hr hs).1) _ hd hcd ht' rfl
      · refine ⟨r, (cleanPay_mem _ _ _ _ _).mpr ⟨hi, ?_, ?_, by omega, ht'⟩⟩
        · simpa only [hs] using hbig
        · simpa only [hs] using hclean

private noncomputable def centerPayBoth {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (r : Rect C) : Finset (Fin N × Fin N) :=
  cleanPay I (centerNode I false) (mixSrc N r) (mixDst N r) ∪
    exchange (cleanPay (fun l p => I p l) (centerNode I true) (mixSrc N r) (mixDst N r))

private lemma centerPayBoth_card {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (hf : fourFree I) (r : Rect C) :
    (centerPayBoth I r).card ≤ 2 := by
  have hp := cleanPay_card I hf (centerNode I false) (mixSrc N r) (mixDst N r)
    (center_mono I false _)
  have hl := cleanPay_card (fun l p => I p l) (swapped_free I hf)
    (centerNode I true) (mixSrc N r) (mixDst N r) (center_mono I true _)
  unfold centerPayBoth
  refine (Finset.card_union_le _ _).trans ?_
  rw [exchange_card]
  omega

private lemma center_labels_disjoint {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (r : Rect C) (p l : Fin N)
    (hp : centerLabel I false r p) (hl : centerLabel I true r l) : False := by
  change single (rpoint N r) = {p} ∧ _ at hp
  change _ ∧ ¬ almost I (single (rpoint N r)) l at hl
  apply hl.2
  unfold almost
  exact (Finset.card_filter_le _ _).trans (by rw [hp.1, Finset.card_singleton])

private lemma centerPayBoth_leaf {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (hf : fourFree I) (r : Rect C)
    (hleaf : mixDst N r = mleaf r) : (centerPayBoth I r).card ≤ 1 := by
  classical
  let P := cleanPay I (centerNode I false) (mixSrc N r) (mixDst N r)
  let L := cleanPay (fun l p => I p l) (centerNode I true) (mixSrc N r) (mixDst N r)
  have hp := cleanPay_card I hf (centerNode I false) (mixSrc N r) (mixDst N r)
    (center_mono I false _)
  have hl := cleanPay_card (fun l p => I p l) (swapped_free I hf)
    (centerNode I true) (mixSrc N r) (mixDst N r) (center_mono I true _)
  have hdis : P.Nonempty → ¬ L.Nonempty := by
    rintro ⟨e, he⟩ ⟨f, hf'⟩
    have hep := ((cleanPay_mem _ _ _ _ _).mp he).2.2.2.2
    have hfl := ((cleanPay_mem _ _ _ _ _).mp hf').2.2.2.2
    rw [hleaf] at hep hfl
    obtain ⟨r₁, hr₁, hp'⟩ := (center_member I false (mleaf r) e.1).mp hep
    obtain ⟨r₂, hr₂, hl'⟩ := (center_member I true (mleaf r) f.1).mp hfl
    have eq₁ : r₁ = r := hr₁
    have eq₂ : r₂ = r := hr₂
    exact center_labels_disjoint I r e.1 f.1 (eq₁ ▸ hp') (eq₂ ▸ hl')
  change (P ∪ exchange L).card ≤ 1
  by_cases hP : P.Nonempty
  · have hz := Finset.not_nonempty_iff_eq_empty.mp (hdis hP)
    rw [hz, show exchange (∅ : Finset (Fin N × Fin N)) = ∅ by simp [exchange], Finset.union_empty]
    exact hp
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hP
    rw [hz, Finset.empty_union, exchange_card]
    exact hl

private noncomputable def centerSlotPay {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (e : Occ C) : Finset (Fin N × Fin N) := by
  classical
  exact centerPayBoth I (.inl e) ∪
    if orAt e then centerPayBoth I (.inr (e,0)) else
      centerPayBoth I (.inr (e,0)) ∪ centerPayBoth I (.inr (e,1))

private lemma every_center_slot {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (r : Rect C) (p l : Fin N)
    (he : (p,l) ∈ centerPayBoth I r) : ∃ e : Occ C, (p,l) ∈ centerSlotPay I e := by
  classical
  rcases r with e | ⟨e,i⟩
  · exact ⟨e, Finset.mem_union_left _ he⟩
  · refine ⟨e, Finset.mem_union_right _ ?_⟩
    by_cases ho : orAt e
    · simp only [ho, ite_true]
      simpa [centerPayBoth, mixSrc, mixDst, ho] using he
    · simp only [ho, ite_false]
      fin_cases i
      · exact Finset.mem_union_left _ he
      · exact Finset.mem_union_right _ he

private lemma centerSlotPay_or {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (hf : fourFree I) (e : Occ C)
    (ho : orAt e) : (centerSlotPay I e).card ≤ 4 := by
  classical
  have h0 := centerPayBoth_card I hf (.inl e)
  have h1 := centerPayBoth_card I hf (.inr (e,0))
  rw [centerSlotPay, ite_eq_left ho]
  exact (Finset.card_union_le _ _).trans (by omega)

private lemma centerSlotPay_and {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I] (hf : fourFree I) (e : Occ C)
    (ha : andAt e) : (centerSlotPay I e).card ≤ 3 := by
  classical
  have ho : ¬ orAt e := fun ho => GateOp.noConfusion (ha.symm.trans ho)
  have h0 := centerPayBoth_leaf I hf (.inl e) (by simp [mixDst, ho])
  have h1 := centerPayBoth_leaf I hf (.inr (e,0)) (by simp [mixDst, ho])
  have h2 := centerPayBoth_leaf I hf (.inr (e,1)) (by simp [mixDst, ho])
  rw [centerSlotPay, ite_eq_right ho]
  have hU := Finset.card_union_le (centerPayBoth I (.inl e))
    (centerPayBoth I (.inr (e,0)) ∪ centerPayBoth I (.inr (e,1)))
  have hV := Finset.card_union_le (centerPayBoth I (.inr (e,0))) (centerPayBoth I (.inr (e,1)))
  omega

private lemma center_bound_by_ops {N : ℕ} {C : Circuit}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (h : PEqualNP.TopForm.IsAO2 (N+N) C) (hf : fourFree I) :
    (cleanEdgeCover I (centerNode I (C := C) false) ∪
      exchange (cleanEdgeCover (fun l p => I p l) (centerNode I (C := C) true))).card ≤
      8 * (orRows C).card + 6 * (andRows C).card := by
  classical
  let O : Finset (Occ C) := (orRows C) ×ˢ univ
  let A : Finset (Occ C) := (andRows C) ×ˢ univ
  have hcO : (O.biUnion (centerSlotPay I)).card ≤ 4 * O.card := by
    calc
      _ ≤ ∑ e ∈ O, (centerSlotPay I e).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ O, 4 := Finset.sum_le_sum (fun e he =>
        centerSlotPay_or I hf e (by simpa [O, orAt, orRows_mem] using he))
      _ = _ := by simp [Nat.mul_comm]
  have hcA : (A.biUnion (centerSlotPay I)).card ≤ 3 * A.card := by
    calc
      _ ≤ ∑ e ∈ A, (centerSlotPay I e).card := Finset.card_biUnion_le
      _ ≤ ∑ _ ∈ A, 3 := Finset.sum_le_sum (fun e he =>
        centerSlotPay_and I hf e (by simpa [A, andAt, andRows_mem] using he))
      _ = _ := by simp [Nat.mul_comm]
  have hsub :
      cleanEdgeCover I (centerNode I (C := C) false) ∪
        exchange (cleanEdgeCover (fun l p => I p l) (centerNode I (C := C) true)) ⊆
      O.biUnion (centerSlotPay I) ∪ A.biUnion (centerSlotPay I) := by
    rintro ⟨p,l⟩ hm
    have he : ∃ e : Occ C, (p,l) ∈ centerSlotPay I e := by
      rcases Finset.mem_union.mp hm with hp | hl
      · obtain ⟨hi, w, hb, hc, hm⟩ := (cleanEdgeCover_mem _ _ _).mp hp
        obtain ⟨r,hr⟩ := center_descend h I false I p l hi w hb hc hm
        exact every_center_slot I r p l (Finset.mem_union_left _ hr)
      · obtain ⟨⟨l',p'⟩, hpair, heq⟩ := Finset.mem_map.mp hl
        change (p',l') = (p,l) at heq
        cases heq
        obtain ⟨hi, w, hb, hc, hm⟩ := (cleanEdgeCover_mem _ _ _).mp hpair
        obtain ⟨r,hr⟩ := center_descend h I true (fun l p => I p l) l p hi w hb hc hm
        exact every_center_slot I r p l (Finset.mem_union_right _ (exchange_mem hr))
    obtain ⟨e, he⟩ := he
    rcases op_kind h e.1 with ha | ho
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨e, by simp [A, andRows_mem, ha], he⟩)
    · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨e, by simp [O, orRows_mem, ho], he⟩)
  have hA : A.card = 2 * (andRows C).card := by simp [A, Nat.mul_comm]
  have hO : O.card = 2 * (orRows C).card := by simp [O, Nat.mul_comm]
  have hsum := (Finset.card_le_card hsub).trans (Finset.card_union_le
    (O.biUnion (centerSlotPay I)) (A.biUnion (centerSlotPay I)))
  omega

end CleanCenterAccounting

section RefinedPayments

open Finset Relation PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ} {C : Circuit}
variable (I : Fin N → Fin N → Prop) [DecidableRel I]

private theorem exchange_iff (S : Finset (Fin N × Fin N)) (p l : Fin N) :
    (p,l) ∈ exchange S ↔ (l,p) ∈ S := by
  constructor
  · intro h
    obtain ⟨⟨a,b⟩, ha, he⟩ := Finset.mem_map.mp h
    change (b,a) = (p,l) at he
    cases he
    exact ha
  · exact exchange_mem

private theorem columnPayment
    (F G : Finset (Fin N)) (S : Finset (Fin N × Fin N))
    (hF : F.card ≤ 3) (hG : G.card ≤ 1) (hsub : S ⊆ F ×ˢ G)
    (hinc : ∀ p l : Fin N, (p,l) ∈ S → I p l)
    (absorb : ∀ l ∈ G, (∀ p ∈ F, I p l) → 2 ≤ F.card → ∀ p ∈ F, (p,l) ∉ S) :
    S.card ≤ 2 := by
  classical
  by_contra! high
  have upper := Finset.card_le_card hsub
  rw [Finset.card_product] at upper
  have noZero : G.card ≠ 0 := by
    intro hz
    rw [hz, Nat.mul_zero] at upper
    omega
  have cardG : G.card = 1 := by omega
  have eq : S = F ×ˢ G := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_product, cardG, Nat.mul_one]
    omega
  obtain ⟨l, hl⟩ := Finset.card_eq_one.mp cardG
  have hGl : l ∈ G := by simp [hl]
  have hF3 : F.card = 3 := by simp [cardG] at upper; omega
  have all : ∀ p ∈ F, I p l := by
    intro p hp
    exact hinc p l (eq ▸ Finset.mem_product.mpr ⟨hp,hGl⟩)
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < F.card by omega)
  exact absorb l hGl all (by omega) p hp (eq ▸ Finset.mem_product.mpr ⟨hp,hGl⟩)

private theorem badColumnPayment
    (F : Finset (Fin N)) (l : Fin N) (S : Finset (Fin N × Fin N))
    (hF : F.card ≤ 3) (hsub : S ⊆ F ×ˢ {l})
    (hinc : ∀ p l : Fin N, (p,l) ∈ S → I p l)
    (bad : ¬ almost I F l) : S.card ≤ 1 := by
  classical
  let hit := F.filter fun p => I p l
  let miss := F.filter fun p => ¬ I p l
  have ge : 2 ≤ miss.card := by
    change ¬ miss.card ≤ 1 at bad
    omega
  have bound : S ⊆ hit ×ˢ {l} := by
    intro e he
    have b := Finset.mem_product.mp (hsub he)
    have eq : e.2 = l := Finset.mem_singleton.mp b.2
    exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨b.1, eq ▸ hinc e.1 e.2 he⟩,b.2⟩
  have both : hit ∪ miss = F := by
    ext p
    simp only [hit, miss, Finset.mem_union, Finset.mem_filter]
    by_cases h : I p l <;> simp [h]
  have sep : Disjoint hit miss := by
    rw [Finset.disjoint_left]
    intro p hp hnp
    exact (Finset.mem_filter.mp hnp).2 (Finset.mem_filter.mp hp).2
  have added := Finset.card_union_of_disjoint sep
  rw [both] at added
  have smaller := Finset.card_le_card bound
  simp only [Finset.card_product, Finset.card_singleton, Nat.mul_one] at smaller
  omega

private noncomputable def rectPayment (r : Rect C) : Finset (Fin N × Fin N) := by
  classical
  exact (rectPay N r).filter fun e => I e.1 e.2 ∧ e ∉ pureCover N C I

private theorem rectPayment_sub (r : Rect C) :
    rectPayment I r ⊆ single (rpoint N r) ×ˢ single (rline N r) := by
  classical
  intro e he
  have hr := (Finset.mem_filter.mp he).1
  by_cases h : little (rpoint N) (rline N) r
  · simpa [rectPay,h] using hr
  · simp [rectPay,h] at hr

private theorem rectPayment_inc (r : Rect C) {p l : Fin N} (h : (p,l) ∈ rectPayment I r) :
    I p l := (Finset.mem_filter.mp h).2.1

private theorem rectPayment_little (r : Rect C) (h : ¬ little (rpoint N) (rline N) r) :
    rectPayment I r = ∅ := by
  classical
  simp [rectPayment, rectPay, h]

private theorem swapPayment_sub (r : Rect C) :
    exchange (rectPayment I r) ⊆ single (rline N r) ×ˢ single (rpoint N r) := by
  intro ⟨l,p⟩ h
  have orig := (exchange_iff _ l p).mp h
  obtain ⟨hp,hl⟩ := Finset.mem_product.mp (rectPayment_sub I r orig)
  exact Finset.mem_product.mpr ⟨hl,hp⟩

private theorem rectPayment_card (hAO : PEqualNP.TopForm.IsAO2 (N+N) C) (r : Rect C) :
    (rectPayment I r).card ≤ 2 := by
  classical
  by_cases h : little (rpoint N) (rline N) r
  · rcases h with ⟨hp,hl⟩ | ⟨hp,hl⟩
    · rw [← exchange_card (rectPayment I r)]
      refine columnPayment (fun l p => I p l) _ _ _ hl hp (swapPayment_sub I r)
        (fun l p he => rectPayment_inc I r ((exchange_iff _ l p).mp he)) ?_
      intro p _ all large l hl he
      have hc : clean (fun l p => I p l) (rline N r) p := by
        intro hn
        obtain ⟨k,hk,hnk⟩ := (pureNode_linear hAO true (rectLine N r) (rectLine_simple N r) _).mp hn
        exact hnk (all k hk)
      have used : (p,l) ∈ pureCover N C I :=
        covered_by_pure I (all l hl) (Or.inr ⟨r,hl,Or.inl ⟨large,hc⟩⟩)
      exact (Finset.mem_filter.mp ((exchange_iff _ l p).mp he)).2.2 used
    · refine columnPayment I _ _ _ hp hl (rectPayment_sub I r) (fun _ _ he => rectPayment_inc I r he) ?_
      intro l _ all large p hp he
      have hc : clean I (rpoint N r) l := by
        intro hn
        obtain ⟨k,hk,hnk⟩ := (pureNode_linear hAO false (rectPoint N r) (rectPoint_simple N r) _).mp hn
        exact hnk (all k hk)
      have used : (p,l) ∈ pureCover N C I :=
        covered_by_pure I (all p hp) (Or.inl ⟨r,hp,Or.inl ⟨large,hc⟩⟩)
      exact (Finset.mem_filter.mp he).2.2 used
  · simp [rectPayment_little I r h]

end RefinedPayments

section SharedRectPayments

open Finset Relation PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ} {C : Circuit}
variable (I : Fin N → Fin N → Prop) [DecidableRel I]

private def rectLabel (e : Occ C) (rev : Bool) : Prop :=
  if rev then
    ∃ p : Fin N, single (rpoint N (.inl e)) = {p} ∧
      ¬ almost (fun l p => I p l) (single (rline N (.inl e))) p
  else
    ∃ l : Fin N, single (rline N (.inl e)) = {l} ∧
      ¬ almost I (single (rpoint N (.inl e))) l

private theorem rectLabel_separate (e : Occ C) :
    rectLabel I e true → rectLabel I e false → False := by
  classical
  intro a b
  obtain ⟨p,hp,_⟩ := a
  obtain ⟨l,_,hl⟩ := b
  apply hl
  unfold almost
  exact (Finset.card_filter_le _ _).trans (by simp [hp])

private noncomputable def mixedChoices (e : Occ C) : Finset Bool := by
  classical
  exact Finset.univ.filter fun rev => rectLabel I e rev

private theorem mixedChoices_card (e : Occ C) : (mixedChoices I e).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have ha' : rectLabel I e a := (Finset.mem_filter.mp ha).2
  have hb' : rectLabel I e b := (Finset.mem_filter.mp hb).2
  cases a <;> cases b
  · rfl
  · exact (rectLabel_separate I e hb' ha').elim
  · exact (rectLabel_separate I e ha' hb').elim
  · rfl

private noncomputable def rectSupplement : Rect C → Finset (Fin N × Fin N)
  | .inl e => (mixedChoices I e).biUnion fun rev => mixedPay I (.inr e,rev)
  | .inr _ => ∅

private lemma mixedPay_le_one (t : MixProduct C × Bool) : (mixedPay I t).card ≤ 1 := by
  classical
  unfold mixedPay singletonPay
  split <;> simp_all only [Finset.card_empty, Finset.card_product]
  · exact (Nat.mul_le_mul ‹_ ∧ _›.1 ‹_ ∧ _›.2)
  · omega

private theorem rectSupplement_card (r : Rect C) : (rectSupplement I r).card ≤ 1 := by
  rcases r with e | e
  · calc
      _ ≤ ∑ rev ∈ mixedChoices I e, (mixedPay I (.inr e, rev)).card := Finset.card_biUnion_le
      _ ≤ ∑ _rev ∈ mixedChoices I e, 1 := Finset.sum_le_sum (fun rev _ => mixedPay_le_one I (.inr e,rev))
      _ ≤ 1 := by simpa only [Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_one] using mixedChoices_card I e
  · simp [rectSupplement]

private theorem rectPayment_label (e : Occ C) (rev : Bool) (label : rectLabel I e rev) :
    (rectPayment I (.inl e)).card ≤ 1 := by
  classical
  let r : Rect C := .inl e
  change (rectPayment I r).card ≤ 1
  by_cases littleCase : little (rpoint N) (rline N) r
  · cases rev
    · obtain ⟨l, hl, bad⟩ := label
      change single (rline N r) = {l} at hl
      have big : 2 ≤ (single (rpoint N r)).card := by
        have h := Finset.card_filter_le (single (rpoint N r)) (fun p => ¬ I p l)
        change ¬ (Finset.filter (fun p => ¬ I p l) (single (rpoint N r))).card ≤ 1 at bad
        omega
      have h3 : (single (rpoint N r)).card ≤ 3 := by rcases littleCase with h | h <;> omega
      have hsub := rectPayment_sub I r
      rw [hl] at hsub
      exact badColumnPayment I _ l _ h3 hsub (fun _ _ h => rectPayment_inc I r h) bad
    · obtain ⟨p, hp, bad⟩ := label
      change single (rpoint N r) = {p} at hp
      have big : 2 ≤ (single (rline N r)).card := by
        have h := Finset.card_filter_le (single (rline N r)) (fun l => ¬ I p l)
        change ¬ (Finset.filter (fun l => ¬ I p l) (single (rline N r))).card ≤ 1 at bad
        omega
      have h3 : (single (rline N r)).card ≤ 3 := by rcases littleCase with h | h <;> omega
      rw [← exchange_card (rectPayment I r)]
      have hsub := swapPayment_sub I r
      rw [hp] at hsub
      exact badColumnPayment (fun l p => I p l) _ p _ h3 hsub
        (fun l p h => rectPayment_inc I r ((exchange_iff _ l p).mp h)) bad
  · rw [rectPayment_little I r littleCase]
    simp

private noncomputable def joinedRectPayment (r : Rect C) : Finset (Fin N × Fin N) :=
  rectPayment I r ∪ rectSupplement I r

private theorem joinedRectPayment_card (hAO : PEqualNP.TopForm.IsAO2 (N+N) C) (r : Rect C) :
    (joinedRectPayment I r).card ≤ 2 := by
  classical
  rcases r with e | e
  · by_cases chosen : (mixedChoices I e).Nonempty
    · obtain ⟨rev,hrev⟩ := chosen
      have h1 := rectPayment_label I e rev (Finset.mem_filter.mp hrev).2
      have h2 := rectSupplement_card I (.inl e)
      have h3 := Finset.card_union_le (rectPayment I (.inl e)) (rectSupplement I (.inl e))
      unfold joinedRectPayment
      omega
    · have empty : mixedChoices I e = ∅ := Finset.not_nonempty_iff_eq_empty.mp chosen
      simpa [joinedRectPayment, rectSupplement, empty] using rectPayment_card I hAO (.inl e)
  · simpa [joinedRectPayment, rectSupplement] using rectPayment_card I hAO (.inr e)

end SharedRectPayments

section CoverByPayments

open Finset Relation PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {N : ℕ} {C : Circuit}
variable (I : Fin N → Fin N → Prop) [DecidableRel I]

private def rectActive : Rect C → Prop
  | .inl e => andAt e
  | .inr (e,_) => andAt e

private theorem mixFamily_active (t : MixProduct C) (valid : validMixed N t) :
    (∀ r ∈ mixFamily N (leftMix t), rectActive r) ∧
      ∀ r ∈ mixFamily N (rightMix N t), rectActive r := by
  rcases t with j | e
  · constructor <;> intro r hr
    · obtain ⟨o,rfl,h,_⟩ := hr
      exact h
    · obtain ⟨o,rfl,h,_⟩ := hr
      exact h
  · constructor
    · intro r hr
      change r = Sum.inl e at hr
      subst r
      exact valid
    · intro r hr
      obtain ⟨o,b,rfl,h,_⟩ := hr
      exact h

private theorem classify_active (t : MixProduct C) (valid : validMixed N t)
    (safeTerm : safe I (mixedTerm N t)) (p l : Fin N) (hit : mixedTerm N t {p} {l}) :
    (pureGood I (rpoint N (C := C)) (rline N) p l ∨
      ∃ r : Rect C, rectActive r ∧ little (rpoint N) (rline N) r ∧
        p ∈ single (rpoint N r) ∧ l ∈ single (rline N r)) ∨
    (badL I (rpoint N) (rline N) (mixFamily N (leftMix t)) l ∧
      badP I (rpoint N) (rline N) (mixFamily N (rightMix N t)) p) ∨
    (badL I (rpoint N) (rline N) (mixFamily N (rightMix N t)) l ∧
      badP I (rpoint N) (rline N) (mixFamily N (leftMix t)) p) := by
  let T := {r : Rect C // rectActive r}
  let F (r : T) := rpoint N r.val
  let G (r : T) := rline N r.val
  let U : Set T := {r : T | r.val ∈ mixFamily N (leftMix t)}
  let V : Set T := {r : T | r.val ∈ mixFamily N (rightMix N t)}
  have active := mixFamily_active t valid
  have derive (W : Set (Rect C)) (X Y : Set (Fin N)) :
      mixHit F G {r : T | r.val ∈ W} X Y → mixHit (rpoint N) (rline N) W X Y := by
    rintro ⟨r, h, hp, hl⟩
    exact ⟨r.val,h,hp,hl⟩
  have cleanAll : safe I (fun X Y => mixHit F G U X Y ∧ mixHit F G V X Y) :=
    fun _ _ h => safeTerm _ _ ⟨derive _ _ _ h.1,derive _ _ _ h.2⟩
  have hitU : mixHit F G U {p} {l} := by
    obtain ⟨r,hr,hp,hl⟩ := hit.1
    exact ⟨⟨r,active.1 r hr⟩,hr,hp,hl⟩
  have hitV : mixHit F G V {p} {l} := by
    obtain ⟨r,hr,hp,hl⟩ := hit.2
    exact ⟨⟨r,active.2 r hr⟩,hr,hp,hl⟩
  have liftP (W : Set (Rect C)) :
      badP I F G {r : T | r.val ∈ W} p → badP I (rpoint N) (rline N) W p := by
    rintro ⟨r,hr,hp,hl⟩
    exact ⟨r.val,hr,hp,hl⟩
  have liftL (W : Set (Rect C)) :
      badL I F G {r : T | r.val ∈ W} l → badL I (rpoint N) (rline N) W l := by
    rintro ⟨r,hr,hp,hl⟩
    exact ⟨r.val,hr,hp,hl⟩
  rcases classify_product I F G cleanAll hitU hitV with ((pg | sg) | left | right)
  · rcases pg with ⟨r,hr,h⟩ | ⟨r,hr,h⟩
    · exact Or.inl (Or.inl (Or.inl ⟨r.val,hr,h⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨r.val,hr,h⟩))
  · obtain ⟨r,hr,hp,hl⟩ := sg
    exact Or.inl (Or.inr ⟨r.val,r.prop,hr,hp,hl⟩)
  · exact Or.inr (Or.inl ⟨liftL _ left.1,liftP _ left.2⟩)
  · exact Or.inr (Or.inr ⟨liftL _ right.1,liftP _ right.2⟩)

private noncomputable def andOccs (C : Circuit) : Finset (Occ C) :=
  andRows C ×ˢ Finset.univ

private theorem andOccs_mem {e : Occ C} :
    e ∈ andOccs C ↔ andAt e := by
  simp [andOccs, andRows_mem, andAt]

private noncomputable def andRectangles (C : Circuit) : Finset (Rect C) :=
  (andOccs C).map ⟨Sum.inl, Sum.inl_injective⟩ ∪
  (andOccs C ×ˢ (Finset.univ : Finset (Fin 2))).map ⟨Sum.inr, Sum.inr_injective⟩

private theorem andRectangles_mem {r : Rect C} : r ∈ andRectangles C ↔ rectActive r := by
  classical
  cases r <;> simp [andRectangles, rectActive, andOccs_mem]

private theorem andRectangles_card (C : Circuit) :
    (andRectangles C).card ≤ 6 * (andRows C).card := by
  simpa [andRectangles, andOccs, Finset.card_product] using
    Finset.card_union_le
      ((andOccs C).map (⟨Sum.inl, Sum.inl_injective⟩ : Occ C ↪ Rect C))
      ((andOccs C ×ˢ (Finset.univ : Finset (Fin 2))).map
        (⟨Sum.inr, Sum.inr_injective⟩ : Occ C × Fin 2 ↪ Rect C))
    |>.trans (by simp [andOccs, Finset.card_product]; omega)

private noncomputable def sharpCenter (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit) :
    Finset (Fin N × Fin N) :=
  cleanEdgeCover I (centerNode I (C := C) false) ∪
    exchange (cleanEdgeCover (fun l p => I p l) (centerNode I (C := C) true))

private theorem enters_clean_center (t : MixProduct C) (rev : Bool)
    (p l : Fin N)
    (hp : p ∈ single (centerNode I false (centerPoint N t rev)))
    (hl : l ∈ single (centerNode I true (centerLine N t rev)))
    (hcross : ∀ a ∈ single (centerNode I false (centerPoint N t rev)),
      ∀ b ∈ single (centerNode I true (centerLine N t rev)), I a b) :
    (p,l) ∈ sharpCenter I C ∨ (p,l) ∈ mixedPay I (t,rev) := by
  classical
  have hi := hcross p hp l hl
  by_cases hP : 2 ≤ (single (centerNode I false (centerPoint N t rev))).card
  · left
    apply Finset.mem_union_left
    refine (cleanEdgeCover_mem _ _ _).mpr ⟨hi, centerPoint N t rev, hP, ?_, hp⟩
    intro hc
    obtain ⟨a,ha,hn⟩ := (center_linear I false _ _).mp hc
    exact hn (hcross a ha l hl)
  by_cases hL : 2 ≤ (single (centerNode I true (centerLine N t rev))).card
  · left
    apply Finset.mem_union_right
    apply exchange_mem
    refine (cleanEdgeCover_mem _ _ _).mpr ⟨hi, centerLine N t rev, hL, ?_, hl⟩
    intro hc
    obtain ⟨b,hb,hn⟩ := (center_linear I true _ _).mp hc
    exact hn (hcross p hp b hb)
  · right
    have hp' : (single (centerNode I false (centerPoint N t rev))).card ≤ 1 := by omega
    have hl' : (single (centerNode I true (centerLine N t rev))).card ≤ 1 := by omega
    exact singletonPay_mem hp hl ⟨hp',hl'⟩

private noncomputable def smallAtRoot : Finset (Fin N × Fin N) :=
  (andRows C ×ˢ (Finset.univ : Finset Bool)).biUnion fun j => mixedPay I (.inl j.1,j.2)

private noncomputable def smallPure : Finset (Fin N × Fin N) :=
  ((Finset.univ : Finset (Fin 3)) ×ˢ andOccs C).biUnion fun d => purePay (N := N) d

private noncomputable def sharpRects : Finset (Fin N × Fin N) :=
  (andRectangles C).biUnion fun r => joinedRectPayment I r

private theorem payCardOn {S T : Type*} [DecidableEq T] (F : Finset S) (pay : S → Finset T) (b : ℕ)
    (hpay : ∀ s ∈ F, (pay s).card ≤ b) : (F.biUnion pay).card ≤ F.card * b := calc
  _ ≤ ∑ s ∈ F, (pay s).card := Finset.card_biUnion_le
  _ ≤ ∑ _s ∈ F, b := Finset.sum_le_sum hpay
  _ = _ := by simp

private theorem smallAtRoot_card :
    (smallAtRoot (C := C) I).card ≤ 2 * (andRows C).card := by
  have b := payCardOn (andRows C ×ˢ (Finset.univ : Finset Bool))
    (fun j => mixedPay I (.inl j.1,j.2)) 1 (fun j _ => mixedPay_le_one I (.inl j.1,j.2))
  simpa [smallAtRoot, Finset.card_product, Nat.mul_comm] using b

private theorem smallPure_card : (smallPure (N := N) (C := C)).card ≤ 6 * (andRows C).card := by
  classical
  have b := payCardOn ((Finset.univ : Finset (Fin 3)) ×ˢ andOccs C) (purePay (N := N)) 1 (by
    intro d _
    unfold purePay singletonPay
    split
    · rw [Finset.card_product]
      exact Nat.mul_le_mul ‹_ ∧ _›.1 ‹_ ∧ _›.2
    · simp)
  simp [smallPure, andOccs, Finset.card_product] at b ⊢
  omega

private theorem sharpRects_card (hAO : PEqualNP.TopForm.IsAO2 (N+N) C) :
    (sharpRects (C := C) I).card ≤ 12 * (andRows C).card := by
  have a := andRectangles_card C
  have b := payCardOn (andRectangles C) (joinedRectPayment I) 2 (fun r _ => joinedRectPayment_card I hAO r)
  change (sharpRects (C := C) I).card ≤ _ at b
  omega

end CoverByPayments

section SharpCounting

open Finset Relation PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

variable {N : ℕ} {C : Circuit}
variable (I : Fin N → Fin N → Prop) [DecidableRel I]

private theorem mixed_sharp_cover (hAO : PEqualNP.TopForm.IsAO2 (N+N) C)
    (hf : fourFree I) (t : MixProduct C) (valid : validMixed N t)
    (safeTerm : safe I (mixedTerm N t)) (p l : Fin N) (hi : I p l)
    (hit : mixedTerm N t {p} {l}) :
    (p,l) ∈ pureCover N C I ∨ (p,l) ∈ sharpCenter I C ∨
      (p,l) ∈ sharpRects (C := C) I ∨ (p,l) ∈ smallAtRoot (C := C) I := by
  classical
  have sf (r : Rect C) (X : Set (Fin N)) := pureNode_linear hAO false (rectPoint N r) (rectPoint_simple N r) X
  have sg (r : Rect C) (Y : Set (Fin N)) := pureNode_linear hAO true (rectLine N r) (rectLine_simple N r) Y
  have coverBad (rev : Bool)
      (bp : badP I (rpoint N) (rline N) (mixFamily N (centerPoint N t rev)) p)
      (bl : badL I (rpoint N) (rline N) (mixFamily N (centerLine N t rev)) l) :
      (p,l) ∈ sharpCenter I C ∨ (p,l) ∈ sharpRects (C := C) I ∨ (p,l) ∈ smallAtRoot (C := C) I := by
    have hp : p ∈ single (centerNode I false (centerPoint N t rev)) :=
      (center_member I false _ _).mpr bp
    have hl : l ∈ single (centerNode I true (centerLine N t rev)) :=
      (center_member I true _ _).mpr bl
    have cross (a : Fin N) (ha : a ∈ single (centerNode I false (centerPoint N t rev)))
        (b : Fin N) (hb : b ∈ single (centerNode I true (centerLine N t rev))) : I a b := by
      have ap := (center_member I false _ _).mp ha
      have bl' := (center_member I true _ _).mp hb
      cases rev
      · exact opposite_bad_adj I (rpoint N) (rline N) hf sf sg safeTerm bl' ap
      · exact opposite_bad_adj I (rpoint N) (rline N) hf sf sg (fun X Y hs => safeTerm X Y hs.symm) bl' ap
    rcases enters_clean_center I t rev p l hp hl cross with h | paid
    · exact Or.inl h
    · rcases t with j | e
      · apply Or.inr; apply Or.inr
        exact Finset.mem_biUnion.mpr
          ⟨(j,rev), Finset.mem_product.mpr ⟨(andRows_mem j).mpr valid.1, Finset.mem_univ _⟩, paid⟩
      · have active : Sum.inl e ∈ andRectangles C := andRectangles_mem.mpr valid
        have label : rectLabel I e rev := by
          cases rev
          · obtain ⟨r, hr, h1, h2⟩ := bl
            change r = Sum.inl e at hr
            subst r
            exact ⟨l,h1,h2⟩
          · obtain ⟨r, hr, h1, h2⟩ := bp
            change r = Sum.inl e at hr
            subst r
            exact ⟨p,h1,h2⟩
        apply Or.inr; apply Or.inl
        apply Finset.mem_biUnion.mpr
        refine ⟨Sum.inl e,active,Finset.mem_union_right _ ?_⟩
        exact Finset.mem_biUnion.mpr
          ⟨rev,Finset.mem_filter.mpr ⟨Finset.mem_univ _,label⟩,paid⟩
  rcases classify_active I t valid safeTerm p l hit with ((h | h) | h | h)
  · exact Or.inl (covered_by_pure I hi h)
  · obtain ⟨r, act, littleCase, hp, hl⟩ := h
    by_cases used : (p,l) ∈ pureCover N C I
    · exact Or.inl used
    · refine Or.inr (Or.inr (Or.inl (Finset.mem_biUnion.mpr
        ⟨r,andRectangles_mem.mpr act,Finset.mem_union_left _ ?_⟩)))
      exact Finset.mem_filter.mpr ⟨by simp [rectPay,littleCase,hp,hl],hi,used⟩
  · exact Or.inr (coverBad false h.2 h.1)
  · exact Or.inr (coverBad true h.2 h.1)

private theorem twice_sharp_bound (hAO : PEqualNP.TopForm.IsAO2 (N + N) C) (hf : fourFree I)
    (hFun : ∀ {X Y : Set (Fin N)}, Hom N C C.output 2 2 X Y → ∃ p ∈ X, ∃ l ∈ Y, I p l) :
    (twiceEdges N C I).card ≤ 34 * C.size := by
  classical
  let U := pureCover N C I
  let V := sharpCenter I C
  let R := sharpRects (C := C) I
  let M := smallAtRoot (C := C) I
  let P := smallPure (N := N) (C := C)
  have fund : U.card ≤ 24 * (orRows C).card + 8 * (andRows C).card := by
    have full := Finset.card_union_le
      (edgeCover I (pureNode N (C := C) false) pureSimple)
      (exchange (edgeCover (fun l p => I p l) (pureNode N (C := C) true) pureSimple))
    rw [exchange_card] at full
    have h1 := pure_bound_by_ops hAO I hf false
    have h2 := pure_bound_by_ops hAO (fun l p => I p l) (swapped_free I hf) true
    change (pureCover N C I).card ≤ _
    unfold pureCover
    omega
  have cen : V.card ≤ 8 * (orRows C).card + 6 * (andRows C).card :=
    center_bound_by_ops I hAO hf
  have rectBound : R.card ≤ 12 * (andRows C).card := sharpRects_card I hAO
  have mix : M.card ≤ 2 * (andRows C).card := smallAtRoot_card I
  have one : P.card ≤ 6 * (andRows C).card := smallPure_card
  have all : twiceEdges N C I ⊆ U ∪ (V ∪ (R ∪ (M ∪ P))) := by
    rintro ⟨p,l⟩ he
    obtain ⟨hi, hh⟩ := (Finset.mem_filter.mp he).2
    rcases product_normal hAO hh with ⟨t,valid,hit⟩ | ⟨d,valid,hit⟩
    · have safeTerm : safe I (mixedTerm N t) := fun x y h =>
        hFun (mixed_sound hAO valid h.1 h.2)
      rcases mixed_sharp_cover I hAO hf t valid safeTerm p l hi hit with hu | hv | hr | hm
      · exact Finset.mem_union_left _ hu
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ hv)
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_union_left _ hr))
      · exact Finset.mem_union_right _ (Finset.mem_union_right _
          (Finset.mem_union_right _ (Finset.mem_union_left _ hm)))
    · have safeTerm : safe I (pureTerm N d) := fun x y h =>
        hFun (pure_sound hAO valid h.1 h.2)
      rcases pure_charges I d safeTerm p l hi hit with hu | hp
      · exact Finset.mem_union_left _ hu
      · apply Finset.mem_union_right
        apply Finset.mem_union_right
        apply Finset.mem_union_right
        apply Finset.mem_union_right
        exact Finset.mem_biUnion.mpr
          ⟨d,Finset.mem_product.mpr ⟨Finset.mem_univ _,andOccs_mem.mpr valid.1⟩,hp⟩
  have h0 := Finset.card_le_card all
  have h1 := Finset.card_union_le U (V ∪ (R ∪ (M ∪ P)))
  have h2 := Finset.card_union_le V (R ∪ (M ∪ P))
  have h3 := Finset.card_union_le R (M ∪ P)
  have h4 := Finset.card_union_le M P
  have count := gate_card_sum hAO
  omega

end SharpCounting
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity


private def addGate (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op,[a,b]⟩], n + C.size⟩

private lemma addSize (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (addGate n C op a b).size = C.size + 1 := by simp [Circuit.size, addGate]

private lemma addAO {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {op : GateOp} (hop : op = .and ∨ op = .or) {a b : ℕ} (ha : a < n+C.size) (hb : b < n+C.size) :
    PEqualNP.TopForm.IsAO2 n (addGate n C op a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h.1 g hg
    · obtain rfl := List.mem_singleton.mp hg
      exact hop
  · intro j hj i hi
    change j < (C.gates ++ [_]).length at hj
    change i ∈ ((C.gates ++ [_]).getD j _).inputs at hi
    by_cases hj' : j < C.gates.length
    · rw [List.getD_append _ _ _ _ hj'] at hi
      exact h.2.1 j hj' i hi
    · simp only [List.length_append, List.length_singleton] at hj
      obtain rfl : j = C.gates.length := by omega
      rw [List.getD_append_right _ _ _ _ (le_refl _)] at hi
      simp at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h.2.2 g hg
    · obtain rfl := List.mem_singleton.mp hg
      rfl

private lemma evalLast {α : Type} (d : α) (f : GateOp → List α → α) (xs : List α)
    {n : ℕ} (hx : xs.length = n) (C : Circuit) (op : GateOp) (a b i : ℕ) :
    (evalFrom d f (addGate n C op a b).gates xs).getD i d =
    if i = n+C.size then f op [(evalFrom d f C.gates xs).getD a d,(evalFrom d f C.gates xs).getD b d]
    else (evalFrom d f C.gates xs).getD i d := by
  let w := evalFrom d f C.gates xs
  have hl : w.length = n+C.size := by simp [w,evalFrom_length,hx,Circuit.size]
  change (evalFrom d f (C.gates ++ [_]) xs).getD i d = _
  simp only [evalFrom,List.foldl_append,List.foldl_cons,List.foldl_nil,List.map_cons,List.map_nil]
  change (w ++ [f op [w.getD a d,w.getD b d]]).getD i d = if i = n+C.size then _ else w.getD i d
  rcases lt_trichotomy i (n+C.size) with hi | rfl | hi
  · rw [if_neg hi.ne,List.getD_append _ _ _ _ (by omega)]
  · rw [if_pos rfl,List.getD_append_right _ _ _ _ (by omega)]
    simp [hl] <;> rfl
  · rw [if_neg hi.ne',List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by omega)]

private lemma wordLast (n : ℕ) (C : Circuit) (op : GateOp) (a b i : ℕ) :
    words n (addGate n C op a b) i = if i = n+C.size then
      wordOp op [words n C a,words n C b] else words n C i :=
  evalLast _ _ _ List.length_ofFn _ _ _ _ _

private lemma boolLast {n : ℕ} (C : Circuit) (z : Fin n → Bool) (op : GateOp) (a b i : ℕ) :
    circuitValue (addGate n C op a b) z i = if i = n+C.size then
      op.eval [circuitValue C z a,circuitValue C z b] else circuitValue C z i :=
  evalLast _ _ _ List.length_ofFn _ _ _ _ _

private lemma bank {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (ho : C.output < n+C.size) (k : ℕ) (hk : k ≤ n) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size = C.size+k ∧ D.output < n+D.size ∧
      (∀ i < k, [i] ∈ words n D D.output) ∧
      words n D C.output = words n C C.output ∧
      ∀ z : Fin n → Bool, circuitValue D z C.output = circuitValue C z C.output := by
  induction k with
  | zero => exact ⟨C,h,by simp,ho,by simp,rfl,fun _ => rfl⟩
  | succ k ih =>
    obtain ⟨D,hd,hs,hot,hall,hw,hv⟩ := ih (by omega)
    let E := addGate n D .or D.output k
    have hk' : k < n := by omega
    have hout : C.output ≠ n+D.size := by omega
    refine ⟨E,addAO hd (Or.inr rfl) hot (by omega),by simp [E,addSize,hs,Nat.add_assoc],
      ?_,?_,?_,?_⟩
    · change n+D.size < n+E.size
      simp [E,addSize,Nat.add_assoc]
    · intro i hi
      change [i] ∈ words n E (n+D.size)
      unfold E
      rw [wordLast, if_pos rfl]
      by_cases hh : i = k
      · subst i
        exact Or.inr (by rw [words_input D hk']; rfl)
      · exact Or.inl (hall i (by omega))
    · simpa [E,wordLast,hout] using hw
    · intro z
      simpa [E,boolLast,hout] using hv z

private def augment (n : ℕ) (D : Circuit) (w r : ℕ) : Circuit :=
  addGate n (addGate n D .and w r) .or w (n+D.size)

private lemma augSize (n : ℕ) (D : Circuit) (w r : ℕ) :
    (augment n D w r).size = D.size+2 := by simp [augment,addSize,Nat.add_assoc]

private lemma augAO {n : ℕ} {D : Circuit} (h : PEqualNP.TopForm.IsAO2 n D)
    {w r : ℕ} (hw : w < n+D.size) (hr : r < n+D.size) :
    PEqualNP.TopForm.IsAO2 n (augment n D w r) :=
  addAO (addAO h (Or.inl rfl) hw hr) (Or.inr rfl)
    (by rw [addSize]; omega) (by rw [addSize]; omega)

private lemma augWords {n : ℕ} {D : Circuit} {w r : ℕ} (hw : w < n+D.size) :
    words n (augment n D w r) (augment n D w r).output =
      words n D w ∪ {t | ∃ u ∈ words n D w, ∃ v ∈ words n D r, t = u ++ v} := by
  change words n (addGate n (addGate n D .and w r) .or w (n+D.size))
    (n+(addGate n D .and w r).size) = _
  simp [wordLast,hw.ne,wordOp]

private lemma augValue {n : ℕ} {D : Circuit} {w r : ℕ} (hw : w < n+D.size) (z : Fin n → Bool) :
    circuitValue (augment n D w r) z (augment n D w r).output = circuitValue D z w := by
  change circuitValue (addGate n (addGate n D .and w r) .or w (n+D.size)) z
    (n+(addGate n D .and w r).size) = _
  simp [boolLast,hw.ne,GateOp.eval] <;> tauto

private lemma augOld {n : ℕ} {D : Circuit} {w r i : ℕ} (hi : i < n+D.size) :
    words n (augment n D w r) i = words n D i := by
  have hh : i ≠ n+(D.size+1) := by omega
  simp [augment,wordLast,hi.ne,addSize,hh]

open PEqualNP.GenericRejection

private def activeP {N : ℕ} (z : Fin (N+N) → Bool) : Finset (Fin N) :=
  Finset.univ.filter fun p => z (Fin.castAdd N p) = true

private def activeL {N : ℕ} (z : Fin (N+N) → Bool) : Finset (Fin N) :=
  Finset.univ.filter fun l => z (Fin.natAdd N l) = true

private lemma inputRep {N : ℕ} (z : Fin (N+N) → Bool) :
    incidenceInput (activeP z) (activeL z) = List.ofFn z := by
  unfold incidenceInput
  rw [← List.ofFn_fin_append]
  congr 1
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro p
    simp [activeP]
  · intro l
    rw [Fin.append_right]
    simp [activeL]

private lemma thinCorrect {N q : ℕ} {S : Fin N → Finset (Fin N)} {C : Circuit}
    (hq : 1 ≤ q) (h : PEqualNP.TopForm.IsAO2 (N+N) C) (hr : RightOnIncidentPairs S C)
    (hf : ∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false)
    (z : Fin (N+N) → Bool) (hz : Thin z) :
    circuitFun (N+N) C z = decide (∃ p l : Fin N, p ∈ S l ∧
      z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
  classical
  by_cases he : ∃ p l : Fin N, p ∈ S l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true
  · rw [decide_eq_true he]
    obtain ⟨p,l,hi,hp,hl⟩ := he
    have hinput : List.ofFn (pair p l) = incidenceInput ({p} : Finset (Fin N)) ({l} : Finset (Fin N)) := by
      unfold incidenceInput
      rw [← List.ofFn_fin_append]
      congr 1
      funext k
      refine Fin.addCases ?_ ?_ k
      · intro i
        simp only [pair,Fin.append_left,Finset.mem_singleton,cast_ne_nat i l,or_false,
          EmbeddingLike.apply_eq_iff_eq]
        simp
      · intro i
        simp only [pair,Fin.append_right,Finset.mem_singleton,Ne.symm (cast_ne_nat p i),false_or]
        simp
    have hv : circuitValue C (pair p l) C.output = true := by
      change C.eval (List.ofFn (pair p l)) = true
      rw [hinput]
      exact hr l p hi
    obtain ⟨t,ht,ha⟩ := (value_eq_terms h _ _).mp hv
    apply (value_eq_terms h _ _).mpr
    refine ⟨t,ht,?_⟩
    intro j hj
    obtain ⟨i,hi,hb⟩ := ha j hj
    refine ⟨i,hi,?_⟩
    rcases (of_decide_eq_true hb : i = Fin.castAdd N p ∨ i = Fin.natAdd N l) with rfl | rfl
    · exact hp
    · exact hl
  · rw [decide_eq_false he]
    change C.eval (List.ofFn z) = false
    rw [← inputRep z]
    apply hf
    · apply le_trans _ hq
      exact Finset.card_le_one_iff.mpr (fun {i} {j} hi hj =>
        hz i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2)
    · intro l hl
      apply Finset.disjoint_left.mpr
      intro p hp hz
      exact he ⟨p,l,hp,(Finset.mem_filter.mp hz).2,(Finset.mem_filter.mp hl).2⟩

private lemma boundSound {N q : ℕ} {S : Fin N → Finset (Fin N)} {C D : Circuit}
    (hq : 2 ≤ q) (h : PEqualNP.TopForm.IsAO2 (N+N) D)
    (hv : ∀ z : Fin (N+N) → Bool, circuitValue D z D.output = circuitValue C z C.output)
    (hf : ∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false)
    {X Y : Set (Fin N)} (hh : Hom N D D.output 2 2 X Y) :
    ∃ p ∈ X, ∃ l ∈ Y, p ∈ S l := by
  classical
  obtain ⟨t,ht,ha,hb,hw⟩ := hh
  let L : Finset (Fin N) := Finset.univ.filter (fun l : Fin N => N+l.val ∈ t)
  have hsub : L.map ⟨fun l => N+l.val, fun _ _ he => Fin.ext (Nat.add_left_cancel he)⟩ ⊆
      (t.filter fun w => decide (N ≤ w)).toFinset := by
    intro w hw
    obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hw
    exact List.mem_toFinset.mpr (List.mem_filter.mpr ⟨(Finset.mem_filter.mp hl).2, by change decide (N ≤ N+l.val) = true; simp⟩)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_map] at hcard
  have hlen := List.toFinset_card_le (t.filter fun w => decide (N ≤ w))
  change (t.filter fun w => decide (N ≤ w)).length = 2 at hb
  have hly (l : Fin N) (hl : l ∈ L) : l ∈ Y :=
    (on_line X Y l).mp (hw _ (Finset.mem_filter.mp hl).2)
  have hh' : Hom N D D.output 2 2 X (↑L) := by
    refine ⟨t,ht,ha,hb,?_⟩
    intro j hj
    rcases hw j hj with hh | ⟨l,_,rfl⟩
    · exact Or.inl hh
    · exact Or.inr ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩,rfl⟩
  have hok := hom_sound h hh'
  rw [hv] at hok
  let z := bits X (↑L)
  have hp (p : Fin N) : p ∈ activeP z ↔ p ∈ X := by
    simp only [activeP,Finset.mem_filter,Finset.mem_univ,true_and,z,bits_true]
    exact on_point _ _ _
  have hl (l : Fin N) : l ∈ activeL z ↔ l ∈ L := by
    simp only [activeL,Finset.mem_filter,Finset.mem_univ,true_and,z,bits_true]
    exact on_line _ _ _
  have he : activeL z = L := Finset.ext hl
  by_contra hn
  have hfalse := hf (activeP z) (activeL z) (by rw [he]; omega) (by
    intro l hll
    apply Finset.disjoint_left.mpr
    intro p hpi hpp
    exact hn ⟨p,(hp p).mp hpp,l,hly l ((hl l).mp hll),hpi⟩)
  rw [inputRep] at hfalse
  change C.eval (List.ofFn z) = true at hok
  rw [hfalse] at hok
  contradiction

private lemma fillPoint {N : ℕ} {D : Circuit} {w r a b : ℕ} {p l : Fin N}
    (hw : w < N+N+D.size) (ha : 1 ≤ a) (ha' : a ≤ 2)
    (hr : [p.val] ∈ words (N+N) D r) (hh : Hom N D w a b {p} {l}) :
    Hom N (augment (N+N) D w r) (augment (N+N) D w r).output 2 b {p} {l} := by
  obtain ⟨t,ht,hp,hl,hs⟩ := hh
  by_cases he : a = 2
  · exact ⟨t, (augWords hw).symm ▸ Or.inl ht, hp.trans he,hl,hs⟩
  · refine ⟨t ++ [p.val], ?_, ?_, ?_, ?_⟩
    · rw [augWords hw]
      exact Or.inr ⟨t,ht,_,hr,rfl⟩
    · have he' : pcount N t = 1 := by omega
      simpa [pcount,p.isLt] using he'
    · have hnp : ¬ N ≤ p.val := by omega
      simpa [lcount,hnp] using hl
    · intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · exact hs j hj
      · rw [List.mem_singleton.mp hj]
        exact (on_point _ _ p).mpr rfl

private lemma fillLine {N : ℕ} {D : Circuit} {w r b : ℕ} {p l : Fin N}
    (hw : w < N+N+D.size) (hb : 1 ≤ b) (hb' : b ≤ 2)
    (hr : [N+l.val] ∈ words (N+N) D r) (hh : Hom N D w 2 b {p} {l}) :
    Hom N (augment (N+N) D w r) (augment (N+N) D w r).output 2 2 {p} {l} := by
  obtain ⟨t,ht,hp,hl,hs⟩ := hh
  by_cases he : b = 2
  · exact ⟨t, (augWords hw).symm ▸ Or.inl ht,hp,hl.trans he,hs⟩
  · refine ⟨t ++ [N+l.val], ?_, ?_, ?_, ?_⟩
    · rw [augWords hw]
      exact Or.inr ⟨t,ht,_,hr,rfl⟩
    · have hn : ¬ N+l.val < N := by omega
      simpa [pcount,hn] using hp
    · have he' : lcount N t = 1 := by omega
      simpa [lcount] using he'
    · intro j hj
      rcases List.mem_append.mp hj with hj | hj
      · exact hs j hj
      · rw [List.mem_singleton.mp hj]
        exact (on_line _ _ l).mpr rfl

private lemma assembled (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit)
    (hq : 200 ≤ q) (hN : N = q^2+q+1) (hc : ∀ l, (S l).card = q+1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l, p ∈ S l ∧ p' ∈ S l)
    (h : PEqualNP.TopForm.IsAO2 (N+N) C) (hk : PEqualNP.ReadK.IsReadK (N+N) C 2)
    (ho : C.output < N+N+C.size) (hr : RightOnIncidentPairs S C)
    (hf : ∀ X Y : Finset (Fin N), Y.card ≤ q → IsFalseInput S X Y → C.eval (incidenceInput X Y) = false) :
    N*q ≤ 100*C.size := by
  classical
  let I : Fin N → Fin N → Prop := fun p l => p ∈ S l
  letI : DecidableRel I := fun p l => inferInstanceAs (Decidable (p ∈ S l))
  have hL (l : Fin N) : (Finset.univ.filter (fun p => I p l)).card = q+1 := by
    simpa [I] using hc l
  have hthin := thinCorrect (by omega : 1 ≤ q) h hr hf
  have hbase := plane_support q N I C hN hL hu h hthin (by omega)
  obtain ⟨B,hB,hBs,hBo,hterms,hwords,hval⟩ := bank h ho (N+N) (le_refl _)
  let E := augment (N+N) B C.output B.output
  let F := augment (N+N) E E.output B.output
  have hco : C.output < N+N+B.size := by omega
  have he : PEqualNP.TopForm.IsAO2 (N+N) E := augAO hB hco hBo
  have hes : E.size = B.size+2 := augSize _ _ _ _
  have heo : E.output < N+N+E.size := by
    change N+N+(addGate (N+N) B .and C.output B.output).size < _
    rw [addSize,hes]
    omega
  have hF : PEqualNP.TopForm.IsAO2 (N+N) F := augAO he heo (by omega)
  have hFs : F.size = E.size+2 := augSize _ _ _ _
  have hv (z : Fin (N+N) → Bool) : circuitValue F z F.output = circuitValue C z C.output :=
    (augValue heo z).trans ((augValue hco z).trans (hval z))
  have hcnt := twice_sharp_bound I hF (plane_four_free I hu)
    (fun hh => boundSound (by omega : 2 ≤ q) hF hv hf hh)
  have hsub : allEdges I ⊆ twiceEdges N F I := by
    rintro ⟨p,l⟩ hi
    have hpl : I p l := (Finset.mem_filter.mp hi).2
    obtain ⟨a,b,ha,ha',hb,hb',hh⟩ := plane_read_cover I h hthin hk hpl
    have hhB : Hom N B C.output a b {p} {l} := by
      unfold Hom at hh ⊢
      rw [hwords]
      exact hh
    have hE : Hom N E E.output 2 b {p} {l} :=
      fillPoint hco ha ha' (hterms p.val (by omega)) hhB
    have hw : [N+l.val] ∈ words (N+N) E B.output := by
      rw [show words (N+N) E B.output = words (N+N) B B.output from augOld hBo]
      exact hterms _ (by omega)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpl,fillLine heo hb hb' hw hE⟩
  have hc' := Finset.card_le_card hsub
  rw [allEdges_card I q hL,Nat.mul_add,Nat.mul_one] at hc'
  have hN' : 200 ≤ N := by omega
  omega

end PEqualNP.Outside.L_meta_3680
theorem PEqualNP.Outside.L_meta_3680 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Finset (Fin x2)) (x4 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x7 : Fin x2), (x3 x7).card = x1 + (1 : ℕ)) → (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x8 ∈ x3 x11 ∧ x9 ∈ x3 x11) → PEqualNP.TopForm.IsAO2 (x2 + x2) x4 → PEqualNP.ReadK.IsReadK (x2 + x2) x4 (2 : ℕ) → x4.output < x2 + x2 + x4.size → PEqualNP.GenericRejection.RightOnIncidentPairs x3 x4 → (∀ (x13 x14 : Finset (Fin x2)), x14.card ≤ x1 → PEqualNP.GenericRejection.IsFalseInput x3 x13 x14 → x4.eval (PEqualNP.GenericRejection.incidenceInput x13 x14) = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x4.size := by
  exact PEqualNP.Outside.L_meta_3680.assembled
