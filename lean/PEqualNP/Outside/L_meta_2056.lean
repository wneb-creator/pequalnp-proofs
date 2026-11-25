import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2056

def reviewAdjacent (u v : Fin 26) : Prop :=
  (u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ [0, 1, 3, 9]) ∨
  (v.val < 13 ∧ 13 ≤ u.val ∧ (u.val + v.val) % 13 ∈ [0, 1, 3, 9])

lemma reviewAdjacent_irrefl : ∀ u : Fin 26, ¬ reviewAdjacent u u := by
  unfold reviewAdjacent
  decide +kernel

lemma reviewAdjacent_symm : ∀ u v : Fin 26,
    reviewAdjacent u v ↔ reviewAdjacent v u := by
  unfold reviewAdjacent
  decide +kernel

set_option synthInstance.maxSize 1000 in
lemma reviewPrivateNeighbor : ∀ u v : Fin 26, u ≠ v →
    ∃ w : Fin 26, w ≠ v ∧ reviewAdjacent u w ∧ ¬ reviewAdjacent v w := by
  unfold reviewAdjacent
  decide +kernel


def pairAssignment (p q z : Fin 26) : Bool :=
  decide (z = p ∨ z = q)

lemma pairAssignment_nonedge (p q v w : Fin 26)
    (hpq : reviewAdjacent p q) (hvw : v ≠ w)
    (hnot : ¬ reviewAdjacent v w) :
    (pairAssignment p q v && pairAssignment p q w) = false := by
  have hboth : ¬ ((v = p ∨ v = q) ∧ (w = p ∨ w = q)) := by
    rintro ⟨hvp | hvq, hwp | hwq⟩
    · exact hvw (hvp.trans hwp.symm)
    · exact hnot (by simpa only [hvp, hwq] using hpq)
    · exact hnot (by
        simpa only [hvq, hwp] using (reviewAdjacent_symm p q).mp hpq)
    · exact hvw (hvq.trans hwq.symm)
  by_cases hv : v = p ∨ v = q
  · have hw : ¬ (w = p ∨ w = q) := fun hw => hboth ⟨hv, hw⟩
    simp [pairAssignment, hw]
  · simp [pairAssignment, hv]

lemma productiveBranch_positive (p q u v w : Fin 26)
    (hpq : reviewAdjacent p q) (hvw : v ≠ w)
    (hnot : ¬ reviewAdjacent v w) :
    (pairAssignment p q w && (pairAssignment p q u || pairAssignment p q v)) =
      (pairAssignment p q w && pairAssignment p q u) := by
  have h := pairAssignment_nonedge p q v w hpq hvw hnot
  cases hv : pairAssignment p q v <;>
    cases hw : pairAssignment p q w <;> simp_all

lemma productiveBranch_le (x : Fin 26 → Bool) (u v w : Fin 26) :
    (x w && x u) ≤ (x w && (x u || x v)) := by
  cases hw : x w <;> cases hu : x u <;> cases hv : x v <;> decide


namespace PrefixPrune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma prefix_fold_mono (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (hab : ∀ i, a.getD i false = true → b.getD i false = true)
    (hlen : a.length = b.length) :
    ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) a).getD i false = true →
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) b).getD i false = true := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hg : g.op.eval (g.inputs.map fun j => a.getD j false) = true →
        g.op.eval (g.inputs.map fun j => b.getD j false) = true := by
      rcases hm g (by simp) with h | h
      · simp only [h, GateOp.eval, List.all_map]
        rw [List.all_eq_true, List.all_eq_true]
        exact fun he j hj => hab j (he j hj)
      · simp only [h, GateOp.eval, List.any_map]
        rw [List.any_eq_true, List.any_eq_true]
        rintro ⟨j, hj, he⟩
        exact ⟨j, hj, hab j he⟩
    apply ih (fun g' hg' => hm g' (List.mem_cons_of_mem _ hg')) _ _ _ (by simp [hlen])
    intro i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, ← hlen] at hi ⊢
    split at hi <;> rename_i hlt
    · simp only [ite_eq_left hlt]
      exact hab _ hi
    · simp only [ite_eq_right hlt]
      by_cases he : i = a.length
      · subst i
        simpa using hg (by simpa using hi)
      · cases hs : i - a.length with
        | zero =>
          exact (he (Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hs) (Nat.le_of_not_gt hlt))).elim
        | succ k => simp [hs] at hi

def original (u v w : Fin 26) (D : Circuit) : Circuit :=
  ⟨⟨GateOp.or, [u.val, v.val]⟩ :: ⟨GateOp.and, [w.val, 26]⟩ :: D.gates,
    D.output⟩

def pruned (u v w : Fin 26) (D : Circuit) : Circuit :=
  ⟨⟨GateOp.or, [u.val, v.val]⟩ :: ⟨GateOp.and, [w.val, u.val]⟩ :: D.gates,
    D.output⟩

lemma input_get (x : Fin 26 → Bool) (i : Fin 26) :
    (List.ofFn x).getD i.val false = x i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left i.isLt,
    Option.getD_some, Fin.eta]

lemma input_append_get (x : Fin 26 → Bool) (l : List Bool) (i : Fin 26) :
    (List.ofFn x ++ l).getD i.val false = x i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    ite_eq_left i.isLt, List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some, Fin.eta]

lemma input_append_last (x : Fin 26 → Bool) (b : Bool) :
    (List.ofFn x ++ [b]).getD 26 false = b := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    Nat.lt_irrefl, ite_false, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

lemma original_eval (u v w : Fin 26) (D : Circuit) (x : Fin 26 → Bool) :
    (original u v w D).eval (List.ofFn x) =
      D.eval ((List.ofFn x ++ [x u || x v]) ++ [x w && (x u || x v)]) := by
  simp only [original, Circuit.eval, Circuit.wires, List.foldl_cons, List.map_cons,
    List.map_nil, GateOp.eval, List.any_cons, List.any_nil, List.all_cons,
    List.all_nil, id_eq, Bool.or_false, Bool.and_true,
    input_get, input_append_get, input_append_last]

lemma pruned_eval (u v w : Fin 26) (D : Circuit) (x : Fin 26 → Bool) :
    (pruned u v w D).eval (List.ofFn x) =
      D.eval ((List.ofFn x ++ [x u || x v]) ++ [x w && x u]) := by
  simp only [pruned, Circuit.eval, Circuit.wires, List.foldl_cons, List.map_cons,
    List.map_nil, GateOp.eval, List.any_cons, List.any_nil, List.all_cons,
    List.all_nil, id_eq, Bool.or_false, Bool.and_true,
    input_get, input_append_get]

lemma prefix_size (u v w : Fin 26) (D : Circuit) :
    (pruned u v w D).size = (original u v w D).size := rfl

lemma prefix_monotone (u v w : Fin 26) (D : Circuit)
    (hC : Monotone2 (original u v w D)) : Monotone2 (pruned u v w D) := by
  intro g hg
  simp only [pruned, List.mem_cons] at hg
  rcases hg with rfl | rfl | hg
  · simp
  · simp
  · exact hC g (by simp [original, hg])

lemma prefix_positive (p q u v w : Fin 26) (D : Circuit)
    (hpq : reviewAdjacent p q) (hvw : v ≠ w) (hnot : ¬ reviewAdjacent v w) :
    (pruned u v w D).eval (List.ofFn (pairAssignment p q)) =
      (original u v w D).eval (List.ofFn (pairAssignment p q)) := by
  rw [original_eval, pruned_eval,
    productiveBranch_positive p q u v w hpq hvw hnot]

lemma append_signal_mono (a : List Bool) (b c : Bool)
    (hbc : b = true → c = true) :
    ∀ i, (a ++ [b]).getD i false = true → (a ++ [c]).getD i false = true := by
  intro i hi
  by_cases hlt : i < a.length
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_append, hlt] using hi
  · cases hs : i - a.length with
    | zero =>
      have hb : b = true := by
        simpa [List.getD_eq_getElem?_getD, List.getElem?_append, hlt, hs] using hi
      simpa [List.getD_eq_getElem?_getD, List.getElem?_append, hlt, hs] using hbc hb
    | succ k =>
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, hlt, hs] at hi

lemma prefix_le (u v w : Fin 26) (D : Circuit)
    (hC : Monotone2 (original u v w D)) (x : Fin 26 → Bool) :
    (pruned u v w D).eval (List.ofFn x) = true →
      (original u v w D).eval (List.ofFn x) = true := by
  rw [original_eval, pruned_eval]
  apply prefix_fold_mono _
    (fun g hg => by simpa using (hC g (by simp [original, hg])).1) _ _ _ (by simp)
  apply append_signal_mono
  intro hnew
  have hle := productiveBranch_le x u v w
  rw [hnew] at hle
  exact Bool.eq_true_of_true_le hle

abbrev incidence (p l : Fin 13) : Prop :=
  (p.val + l.val) % 13 ∈ [0, 1, 3, 9]

def testInput (S T : Finset (Fin 13)) (i : Fin 26) : Bool :=
  if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ S)
  else decide (Fin.ofNat 13 i.val ∈ T)

def nonneighbors (S : Finset (Fin 13)) : Finset (Fin 13) :=
  {l | ∀ p ∈ S, ¬ incidence p l}

def postedTests (C : Circuit) : Prop :=
  (∀ p l : Fin 13, incidence p l →
    C.eval (List.ofFn (testInput {p} {l})) = true) ∧
  ∀ S : Finset (Fin 13), S.card ≤ 3 →
    C.eval (List.ofFn (testInput S (nonneighbors S))) = false ∧
    C.eval (List.ofFn (testInput (nonneighbors S) S)) = false

lemma embedded_adjacent (p l : Fin 13) (h : incidence p l) :
    reviewAdjacent (Fin.castAdd 13 p) (Fin.natAdd 13 l) := by
  left
  refine ⟨p.isLt, by simp, ?_⟩
  simpa [incidence, Nat.add_mod, Nat.add_assoc] using h

lemma singleton_input (p l : Fin 13) :
    testInput {p} {l} = pairAssignment (Fin.castAdd 13 p) (Fin.natAdd 13 l) := by
  funext i
  have hip : i.val < 26 := i.isLt
  have hpp : p.val < 13 := p.isLt
  have hlp : l.val < 13 := l.isLt
  by_cases hi : i.val < 13
  · have hcast : Fin.ofNat 13 i.val = p ↔ i = Fin.castAdd 13 p := by
      simp only [Fin.ext_iff, Fin.val_ofNat, Fin.val_castAdd]
      omega
    have hnat : i ≠ Fin.natAdd 13 l := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_natAdd]
      omega
    simp only [testInput, ite_eq_left hi, Finset.mem_singleton,
      pairAssignment, hcast, hnat, or_false]
  · have hcast : i ≠ Fin.castAdd 13 p := by
      simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd]
      omega
    have hnat : Fin.ofNat 13 i.val = l ↔ i = Fin.natAdd 13 l := by
      simp only [Fin.ext_iff, Fin.val_ofNat, Fin.val_natAdd]
      omega
    simp only [testInput, ite_eq_right hi, Finset.mem_singleton,
      pairAssignment, hcast, hnat, false_or]

lemma pruned_negative (u v w : Fin 26) (D : Circuit)
    (hC : Monotone2 (original u v w D)) (x : Fin 26 → Bool)
    (hfalse : (original u v w D).eval (List.ofFn x) = false) :
    (pruned u v w D).eval (List.ofFn x) = false := by
  cases he : (pruned u v w D).eval (List.ofFn x)
  · rfl
  · have ht := prefix_le u v w D hC x he
    rw [hfalse] at ht
    contradiction

lemma preserves_posted_tests (u v w : Fin 26) (D : Circuit)
    (hC : Monotone2 (original u v w D)) (hvw : v ≠ w)
    (hnot : ¬ reviewAdjacent v w) (htest : postedTests (original u v w D)) :
    postedTests (pruned u v w D) := by
  constructor
  · intro p l hpl
    have he := prefix_positive (Fin.castAdd 13 p) (Fin.natAdd 13 l) u v w D
      (embedded_adjacent p l hpl) hvw hnot
    rw [← singleton_input p l] at he
    exact he.trans (htest.1 p l hpl)
  · intro S hS
    exact ⟨pruned_negative u v w D hC _ (htest.2 S hS).1,
      pruned_negative u v w D hC _ (htest.2 S hS).2⟩

lemma prefix_certificate (u v w : Fin 26) (D : Circuit)
    (hC : Monotone2 (original u v w D)) (hvw : v ≠ w)
    (hnot : ¬ reviewAdjacent v w) :
    Monotone2 (pruned u v w D) ∧
      (pruned u v w D).size = (original u v w D).size ∧
      (pruned u v w D).output = (original u v w D).output ∧
      (postedTests (original u v w D) → postedTests (pruned u v w D)) :=
  ⟨prefix_monotone u v w D hC, prefix_size u v w D, rfl,
    preserves_posted_tests u v w D hC hvw hnot⟩

lemma postedTests_exact (C : Circuit) : postedTests C ↔
    let x2 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x2 x3 : Fin (13 : ℕ)) => (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];       have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);       have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x2 x6 x5};       have x5 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Bool := fun (x5 x6 : Finset (Fin (13 : ℕ))) => C.eval (List.ofFn (x3 x5 x6));       (∀ (x6 x7 : Fin (13 : ℕ)), x2 x6 x7 → x5 {x6} {x7} = Bool.true) ∧ ∀ (x6 : Finset (Fin (13 : ℕ))), x6.card ≤ (3 : ℕ) → x5 x6 (x4 x6) = Bool.false ∧ x5 (x4 x6) x6 = Bool.false := Iff.rfl


def neighbors (p : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter fun l => incidence p l

lemma degree_four : ∀ p : Fin 13, (neighbors p).card = 4 := by
  unfold neighbors incidence
  decide +kernel

lemma pair_inter_small : ∀ p q : Fin 13, p ≠ q →
    (neighbors p ∩ neighbors q).card ≤ 1 := by
  unfold neighbors incidence
  decide +kernel

lemma four_off_small (S : Finset (Fin 13)) (hS : S.card = 4) :
    (nonneighbors S).card ≤ 3 := by
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, rfl⟩ :=
    Finset.card_eq_four.mp hS
  have h1 := Finset.card_union_add_card_inter (neighbors p) (neighbors q)
  have h2 := Finset.card_union_add_card_inter (neighbors p ∪ neighbors q) (neighbors r)
  have h3 := Finset.card_union_add_card_inter
    (neighbors p ∪ neighbors q ∪ neighbors r) (neighbors s)
  have hi2 : ((neighbors p ∪ neighbors q) ∩ neighbors r).card ≤ 2 := by
    rw [Finset.union_inter_distrib_right]
    have := Finset.card_union_le (neighbors p ∩ neighbors r) (neighbors q ∩ neighbors r)
    have := pair_inter_small p r hpr
    have := pair_inter_small q r hqr
    omega
  have hi3 : ((neighbors p ∪ neighbors q ∪ neighbors r) ∩ neighbors s).card ≤ 3 := by
    rw [Finset.union_inter_distrib_right, Finset.union_inter_distrib_right]
    have := Finset.card_union_le
      (neighbors p ∩ neighbors s ∪ neighbors q ∩ neighbors s) (neighbors r ∩ neighbors s)
    have := Finset.card_union_le (neighbors p ∩ neighbors s) (neighbors q ∩ neighbors s)
    have := pair_inter_small p s hps
    have := pair_inter_small q s hqs
    have := pair_inter_small r s hrs
    omega
  have hunion : 10 ≤ (neighbors p ∪ neighbors q ∪ neighbors r ∪ neighbors s).card := by
    have := degree_four p
    have := degree_four q
    have := degree_four r
    have := degree_four s
    have := pair_inter_small p q hpq
    omega
  have hoff : nonneighbors {p, q, r, s} = Finset.univ \
      (neighbors p ∪ neighbors q ∪ neighbors r ∪ neighbors s) := by
    ext l
    simp [nonneighbors, neighbors, not_or, and_assoc]
  rw [hoff, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  omega


lemma nonneighbors_antitone {S T : Finset (Fin 13)} (h : S ⊆ T) :
    nonneighbors T ⊆ nonneighbors S := by
  intro l hl
  simp only [nonneighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
  exact fun p hp => hl p (h hp)

lemma small_or_small_off
    (h4 : ∀ S : Finset (Fin 13), S.card = 4 → (nonneighbors S).card ≤ 3)
    (S : Finset (Fin 13)) : S.card ≤ 3 ∨ (nonneighbors S).card ≤ 3 := by
  by_cases hS : S.card ≤ 3
  · exact Or.inl hS
  · right
    obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq (show 4 ≤ S.card by omega)
    exact (Finset.card_le_card (nonneighbors_antitone hT)).trans (h4 T hTc)

lemma subset_double_nonneighbors (S : Finset (Fin 13)) :
    S ⊆ nonneighbors (nonneighbors S) := by
  intro p hp
  simp only [nonneighbors, Finset.mem_filter, Finset.mem_univ, true_and]
  intro l hl
  have h := hl p hp
  simpa only [incidence, Nat.add_comm] using h

lemma eval_mono_of_pointwise (C : Circuit) (hC : Monotone2 C)
    (x y : Fin 26 → Bool) (hxy : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  unfold Circuit.eval Circuit.wires
  apply prefix_fold_mono C.gates (fun g hg => (hC g hg).1) _ _ _ (by simp)
  intro i hi
  by_cases hi' : i < 26
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi', dite_true,
      Option.getD_some] at hi ⊢
    exact hxy ⟨i, hi'⟩ hi
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi', dite_false,
      Option.getD_none] at hi
    contradiction

lemma testInput_mono {S T S' T' : Finset (Fin 13)}
    (hS : S ⊆ S') (hT : T ⊆ T') (i : Fin 26) :
    testInput S T i = true → testInput S' T' i = true := by
  unfold testInput
  split <;> simp only [decide_eq_true_eq]
  · exact fun h => hS h
  · exact fun h => hT h

lemma independent_false
    (h4 : ∀ S : Finset (Fin 13), S.card = 4 → (nonneighbors S).card ≤ 3)
    (C : Circuit) (hC : Monotone2 C) (hTests : postedTests C)
    (S T : Finset (Fin 13)) (hInd : ∀ p ∈ S, ∀ l ∈ T, ¬ incidence p l) :
    C.eval (List.ofFn (testInput S T)) = false := by
  have hT : T ⊆ nonneighbors S := by
    intro l hl
    simp only [nonneighbors, Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun p hp => hInd p hp l hl
  cases he : C.eval (List.ofFn (testInput S T))
  · rfl
  · rcases small_or_small_off h4 S with hS | hS
    · have hh : C.eval (List.ofFn (testInput S (nonneighbors S))) = true :=
        eval_mono_of_pointwise C hC (testInput S T)
          (testInput S (nonneighbors S))
          (testInput_mono (Finset.Subset.refl S) hT) he
      have hf : C.eval (List.ofFn (testInput S (nonneighbors S))) = false :=
        (hTests.2 S hS).1
      exact Bool.noConfusion (hh.symm.trans hf)
    · have hh : C.eval
          (List.ofFn (testInput (nonneighbors (nonneighbors S)) (nonneighbors S))) = true :=
        eval_mono_of_pointwise C hC (testInput S T)
          (testInput (nonneighbors (nonneighbors S)) (nonneighbors S))
          (testInput_mono (subset_double_nonneighbors S) hT) he
      have hf : C.eval
          (List.ofFn (testInput (nonneighbors (nonneighbors S)) (nonneighbors S))) = false :=
        (hTests.2 (nonneighbors S) hS).2
      exact Bool.noConfusion (hh.symm.trans hf)

lemma edge_true (C : Circuit) (hC : Monotone2 C) (hTests : postedTests C)
    (S T : Finset (Fin 13)) (hEdge : ∃ p ∈ S, ∃ l ∈ T, incidence p l) :
    C.eval (List.ofFn (testInput S T)) = true := by
  obtain ⟨p, hp, l, hl, hpl⟩ := hEdge
  exact eval_mono_of_pointwise C hC _ _
    (testInput_mono (Finset.singleton_subset_iff.mpr hp)
      (Finset.singleton_subset_iff.mpr hl)) (hTests.1 p l hpl)

lemma postedTests_complete
    (h4 : ∀ S : Finset (Fin 13), S.card = 4 → (nonneighbors S).card ≤ 3)
    (C : Circuit) (hC : Monotone2 C) (hTests : postedTests C)
    (S T : Finset (Fin 13)) :
    C.eval (List.ofFn (testInput S T)) =
      decide (∃ p ∈ S, ∃ l ∈ T, incidence p l) := by
  by_cases hEdge : ∃ p ∈ S, ∃ l ∈ T, incidence p l
  · have hd : decide (∃ p ∈ S, ∃ l ∈ T, incidence p l) = true := by
      simpa only [decide_eq_true_eq] using hEdge
    exact (edge_true C hC hTests S T hEdge).trans hd.symm
  · have hInd : ∀ p ∈ S, ∀ l ∈ T, ¬ incidence p l := by
      intro p hp l hl hpl
      exact hEdge ⟨p, hp, l, hl, hpl⟩
    have hd : decide (∃ p ∈ S, ∃ l ∈ T, incidence p l) = false := by
      simpa only [decide_eq_false_iff_not] using hEdge
    exact (independent_false h4 C hC hTests S T hInd).trans hd.symm

def pointSet (x : Fin 26 → Bool) : Finset (Fin 13) :=
  {p | x (Fin.castAdd 13 p) = true}

def lineSet (x : Fin 26 → Bool) : Finset (Fin 13) :=
  {l | x (Fin.natAdd 13 l) = true}

lemma testInput_decompose (x : Fin 26 → Bool) :
    testInput (pointSet x) (lineSet x) = x := by
  funext i
  have hi26 : i.val < 26 := i.isLt
  by_cases hi : i.val < 13
  · have he : Fin.castAdd 13 (Fin.ofNat 13 i.val) = i := by
      apply Fin.ext
      simp only [Fin.val_castAdd, Fin.val_ofNat]
      exact Nat.mod_eq_of_lt hi
    simp only [testInput, ite_eq_left hi, pointSet, Finset.mem_filter,
      Finset.mem_univ, true_and, he, Bool.decide_eq_true]
  · have he : Fin.natAdd 13 (Fin.ofNat 13 i.val) = i := by
      apply Fin.ext
      simp only [Fin.val_natAdd, Fin.val_ofNat]
      omega
    simp only [testInput, ite_eq_right hi, lineSet, Finset.mem_filter,
      Finset.mem_univ, true_and, he, Bool.decide_eq_true]

lemma postedTests_complete_input
    (h4 : ∀ S : Finset (Fin 13), S.card = 4 → (nonneighbors S).card ≤ 3)
    (C : Circuit) (hC : Monotone2 C) (hTests : postedTests C)
    (x : Fin 26 → Bool) :
    C.eval (List.ofFn x) = decide (∃ p l : Fin 13,
      incidence p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) := by
  have h := postedTests_complete h4 C hC hTests (pointSet x) (lineSet x)
  rw [testInput_decompose] at h
  have he : (∃ p ∈ pointSet x, ∃ l ∈ lineSet x, incidence p l) ↔
      (∃ p l : Fin 13, incidence p l ∧ x (Fin.castAdd 13 p) = true ∧
        x (Fin.natAdd 13 l) = true) := by
    constructor
    · rintro ⟨p, hp, l, hl, hpl⟩
      exact ⟨p, l, hpl, (Finset.mem_filter.mp hp).2, (Finset.mem_filter.mp hl).2⟩
    · rintro ⟨p, l, hpl, hp, hl⟩
      exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩,
        l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩, hpl⟩
  simpa only [he] using h

lemma postedTests_compute_incidence
    (C : Circuit) (hC : Monotone2 C) (hTests : postedTests C)
    (x : Fin 26 → Bool) :
    C.eval (List.ofFn x) = decide (∃ p l : Fin 13,
      incidence p l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) :=
  postedTests_complete_input four_off_small C hC hTests x

end PrefixPrune

end PEqualNP.Outside.L_meta_2056
