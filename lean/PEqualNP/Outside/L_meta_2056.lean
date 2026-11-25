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

namespace AndLower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def andCount : List Gate → ℕ
  | [] => 0
  | g :: gs => (match g.op with | .and => 1 | _ => 0) + andCount gs

def choices : List Gate → List Bool → List Bool
  | [], _ => []
  | g :: gs, w =>
    match g.op with
    | .and => (g.inputs.map fun i => w.getD i false).headD false :: choices gs (step w g)
    | _ => choices gs (step w g)

lemma choices_length (gs : List Gate) (w : List Bool) :
    (choices gs w).length = andCount gs := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    cases h : g.op <;> simp [choices, andCount, h, ih, Nat.add_comm]

def FalseUnion (a b c : List Bool) : Prop :=
  a.length = b.length ∧ a.length = c.length ∧
    ∀ i, a.getD i false = false → b.getD i false = false → c.getD i false = false

lemma falseUnion_append (a b c : List Bool) (x y z : Bool)
    (h : FalseUnion a b c) (hxyz : x = false → y = false → z = false) :
    FalseUnion (a ++ [x]) (b ++ [y]) (c ++ [z]) := by
  have hab := h.1
  have hac := h.2.1
  refine ⟨by simp [h.1], by simp [h.2.1], ?_⟩
  intro i ha hb
  by_cases hi : i < a.length
  · rw [List.getD_append a [x] false i hi] at ha
    rw [List.getD_append b [y] false i (by omega)] at hb
    rw [List.getD_append c [z] false i (by omega)]
    exact h.2.2 i ha hb
  · rw [List.getD_append_right a [x] false i (by omega)] at ha
    rw [List.getD_append_right b [y] false i (by omega), ← h.1] at hb
    rw [List.getD_append_right c [z] false i (by omega), ← h.2.1]
    cases hs : i - a.length with
    | zero => simp only [hs, List.getD_cons_zero] at ha hb ⊢; exact hxyz ha hb
    | succ k => simp

lemma and_false_union (ix : List ℕ) (a b c : List Bool)
    (h : ∀ i, a.getD i false = false → b.getD i false = false → c.getD i false = false)
    (hlen : ix.length ≤ 2)
    (hhead : (ix.map fun i => a.getD i false).headD false =
      (ix.map fun i => b.getD i false).headD false)
    (ha : GateOp.and.eval (ix.map fun i => a.getD i false) = false)
    (hb : GateOp.and.eval (ix.map fun i => b.getD i false) = false) :
    GateOp.and.eval (ix.map fun i => c.getD i false) = false := by
  cases ix with
  | nil => simp [GateOp.eval] at ha
  | cons i is =>
    cases is with
    | nil =>
      simpa [GateOp.eval] using h i (by simpa [GateOp.eval] using ha)
        (by simpa [GateOp.eval] using hb)
    | cons j js =>
      have hjs : js = [] := by
        cases js with
        | nil => rfl
        | cons k ks => simp only [List.length_cons] at hlen; omega
      subst js
      simp only [List.map_cons, List.map_nil, List.headD_cons] at hhead
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
        List.all_nil, id_eq, Bool.and_true] at ha hb ⊢
      cases hai : a.getD i false with
      | false =>
        have hbi : b.getD i false = false := hhead.symm.trans hai
        rw [h i hai hbi]
        rfl
      | true =>
        have hbi : b.getD i false = true := hhead.symm.trans hai
        have haj : a.getD j false = false := by simpa only [hai, Bool.true_and] using ha
        have hbj : b.getD j false = false := by simpa only [hbi, Bool.true_and] using hb
        rw [h j haj hbj]
        exact Bool.and_false _

lemma or_false_union (ix : List ℕ) (a b c : List Bool)
    (h : ∀ i, a.getD i false = false → b.getD i false = false → c.getD i false = false)
    (ha : GateOp.or.eval (ix.map fun i => a.getD i false) = false)
    (hb : GateOp.or.eval (ix.map fun i => b.getD i false) = false) :
    GateOp.or.eval (ix.map fun i => c.getD i false) = false := by
  simp only [GateOp.eval, List.any_map, List.any_eq_false] at ha hb ⊢
  intro i hi
  have hai : a.getD i false = false := Bool.eq_false_iff.mpr (by simpa using ha i hi)
  have hbi : b.getD i false = false := Bool.eq_false_iff.mpr (by simpa using hb i hi)
  simpa using Bool.eq_false_iff.mp (h i hai hbi)

lemma fold_falseUnion (gs : List Gate) (a b c : List Bool)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (h : FalseUnion a b c) (hc : choices gs a = choices gs b) :
    FalseUnion (gs.foldl step a) (gs.foldl step b) (gs.foldl step c) := by
  induction gs generalizing a b c with
  | nil => exact h
  | cons g gs ih =>
    have htail : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hm g' (List.mem_cons_of_mem _ hg')
    obtain ⟨hop, hlen⟩ := hm g (by simp)
    rcases hop with hop | hop
    · simp only [choices, hop, List.cons.injEq] at hc
      apply ih (step a g) (step b g) (step c g) htail _ hc.2
      apply falseUnion_append _ _ _ _ _ _ h
      simpa only [hop] using and_false_union g.inputs a b c h.2.2 hlen hc.1
    · simp only [choices, hop] at hc
      apply ih (step a g) (step b g) (step c g) htail _ hc
      apply falseUnion_append _ _ _ _ _ _ h
      simpa only [hop] using or_false_union g.inputs a b c h.2.2

lemma falseUnion_ofFn {n : ℕ} (x y : Fin n → Bool) :
    FalseUnion (List.ofFn x) (List.ofFn y) (List.ofFn fun i => x i || y i) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i hx hy
  by_cases hi : i < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi,
      Option.getD_some] at hx hy ⊢
    simp [hx, hy]
  · simp [List.getD_eq_getElem?_getD, hi]

lemma choices_eq_of_code_eq (gs : List Gate) (a b : List Bool)
    (hc : (fun i : Fin (andCount gs) => (choices gs a).getD i.val false) =
      (fun i : Fin (andCount gs) => (choices gs b).getD i.val false)) :
    choices gs a = choices gs b := by
  apply List.ext_getElem (by simp [choices_length])
  intro i hi hj
  have hlt : i < andCount gs := by simpa [choices_length] using hi
  have hh := congrFun hc ⟨i, hlt⟩
  simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using hh

lemma negative_family_bound {n m : ℕ} (C : Circuit) (hm : Monotone2 C)
    (X : Fin m → Fin n → Bool)
    (hneg : ∀ i, C.eval (List.ofFn (X i)) = false)
    (hunion : ∀ i j, i ≠ j → C.eval (List.ofFn fun z => X i z || X j z) = true) :
    m ≤ 2 ^ andCount C.gates := by
  let code : Fin m → Fin (andCount C.gates) → Bool := fun j i =>
    (choices C.gates (List.ofFn (X j))).getD i.val false
  have hinj : Function.Injective code := by
    intro i j hij
    by_contra hne
    have hcodes : choices C.gates (List.ofFn (X i)) = choices C.gates (List.ofFn (X j)) :=
      choices_eq_of_code_eq C.gates _ _ hij
    have hf := fold_falseUnion C.gates (List.ofFn (X i)) (List.ofFn (X j))
      (List.ofFn fun z => X i z || X j z)
      (fun g hg => ⟨by simpa using (hm g hg).1, (hm g hg).2⟩)
      (falseUnion_ofFn (X i) (X j)) hcodes
    have hfalse := hf.2.2 C.output (hneg i) (hneg j)
    change C.eval (List.ofFn fun z => X i z || X j z) = false at hfalse
    rw [hunion i j hne] at hfalse
    contradiction
  have hcard := Fintype.card_le_of_injective code hinj
  simpa using hcard


def theta4Edges : List (ℕ × ℕ) :=
  [(0,6),(0,7),(0,8),(0,9),(1,5),(1,6),(2,5),(2,7),(3,5),(3,8),(4,5),(4,9)]

abbrev theta4Edge (p q : Fin 10) : Prop := (p.val, q.val) ∈ theta4Edges

def theta4Value (x : Fin 10 → Bool) : Bool :=
  decide (∃ p q : Fin 10, theta4Edge p q ∧ x p = true ∧ x q = true)

def theta4NegativeMasks : List ℕ :=
  [31,33,92,154,216,278,340,402,464,526,588,650,712,774,836,898,992]

def theta4Input (i : Fin 17) (p : Fin 10) : Bool :=
  Nat.testBit (theta4NegativeMasks.getD i.val 0) p.val

set_option maxHeartbeats 4000000 in
lemma theta4_negative : ∀ i : Fin 17, theta4Value (theta4Input i) = false := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma theta4_union_positive : ∀ i j : Fin 17, i ≠ j →
    theta4Value (fun p => theta4Input i p || theta4Input j p) = true := by
  decide +kernel

lemma theta4_and_lower (C : Circuit) (hm : Monotone2 C)
    (hc : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = theta4Value x) :
    5 ≤ andCount C.gates := by
  have hb : 17 ≤ 2 ^ andCount C.gates := negative_family_bound C hm theta4Input
    (by intro i; rw [hc]; exact theta4_negative i)
    (by intro i j hij; rw [hc]; exact theta4_union_positive i j hij)
  by_contra hn
  have hk : andCount C.gates ≤ 4 := by omega
  have hp : 2 ^ andCount C.gates ≤ 16 := by
    calc
      2 ^ andCount C.gates ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) hk
      _ = 16 := by decide
  omega

end AndLower

namespace Pruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- Bypass helpers adapted from L_meta_2668 and its credited L_meta_1499 source.

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

lemma foldl_getD_lt2 (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
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
      rw [Nat.add_zero, foldl_getD_lt2 gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, foldl_getD_lt2 gs (stepWire w g) i (by simp [stepWire]; omega)]
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
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt2 _ _ _ (by omega)

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

lemma val_prefix {n : ℕ} {C D : Circuit} {x : List Bool} (hx : x.length = n) {m : ℕ}
    (hmC : m ≤ C.gates.length) (hmD : m ≤ D.gates.length)
    (hg : ∀ k < m, gateAt D k = gateAt C k) : ∀ u, u < n + m → val D x u = val C x u := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases hun : u < n
    · rw [val_input hx hun, val_input hx hun]
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < m := by omega
      rw [val_gate hx (by omega), val_gate hx (by omega), hg k hk]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + k
      · rw [if_pos hi, if_pos hi]; exact ih i hi (by omega)
      · rw [if_neg hi, if_neg hi]

def aliasWire (w i u : ℕ) : ℕ := if u = w then i else if w < u then u - 1 else u

def aliasGate (w i : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (aliasWire w i)⟩

def bypass (n : ℕ) (C : Circuit) (r i : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (fun k =>
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1))),
    aliasWire (n + r) i C.output⟩

lemma bypass_length (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).gates.length = C.gates.length - 1 := by simp [bypass]

lemma bypass_output (n : ℕ) (C : Circuit) (r i : ℕ) :
    (bypass n C r i).output = aliasWire (n + r) i C.output := rfl

lemma gateAt_bypass {n : ℕ} {C : Circuit} {r i k : ℕ} (hk : k < C.gates.length - 1) :
    gateAt (bypass n C r i) k =
      if k < r then gateAt C k else aliasGate (n + r) i (gateAt C (k + 1)) := by
  have hk' : k < (bypass n C r i).gates.length := by rw [bypass_length]; exact hk
  rw [gateAt_eq hk']
  simp [bypass]

lemma bypass_val_lt {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r i : ℕ}
    (hr : r < C.gates.length) : ∀ u, u < n + r → val (bypass n C r i) x u = val C x u := by
  apply val_prefix hx (by omega) (by rw [bypass_length]; omega)
  intro k hk
  rw [gateAt_bypass (by omega), if_pos hk]

lemma aliasWire_self (w i : ℕ) : aliasWire w i w = i := by simp [aliasWire]

lemma aliasWire_lt_self {w i u : ℕ} (hu : u < w) : aliasWire w i u = u := by
  unfold aliasWire; rw [if_neg (by omega), if_neg (by omega)]

lemma aliasWire_gt_self {w i u : ℕ} (hu : w < u) : aliasWire w i u = u - 1 := by
  unfold aliasWire; rw [if_neg (by omega), if_pos hu]

lemma bypass_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : (∃ k, r < k ∧ k < C.gates.length ∧ n + r ∈ (gateAt C k).inputs) →
      R (val C x (n + r)) (val C x i)) :
    ∀ u, u ≠ n + r → R (val C x u) (val (bypass n C r i) x (aliasWire (n + r) i u)) := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hne
    by_cases hlt : u < n + r
    · rw [aliasWire_lt_self hlt, bypass_val_lt hx hr u hlt]; exact hrefl _
    · rw [aliasWire_gt_self (by omega)]
      by_cases hge : n + C.gates.length ≤ u
      · rw [val_ge hx hge, val_ge hx (by rw [bypass_length]; omega)]; exact hrefl _
      · obtain ⟨k, rfl⟩ : ∃ k, u = n + (k + 1) := ⟨u - n - 1, by omega⟩
        have hk1 : k + 1 < C.gates.length := by omega
        have hkr : ¬ k < r := by omega
        have e : n + (k + 1) - 1 = n + k := by omega
        rw [e, val_gate hx hk1, val_gate hx (by rw [bypass_length]; omega),
          gateAt_bypass (by omega), if_neg hkr]
        simp only [aliasGate, List.map_map]
        refine hmono _ (hAO _ hk1) _ _ _ ?_
        intro i' hi'
        simp only [Function.comp_apply]
        by_cases h1 : i' = n + r
        · subst h1
          rw [aliasWire_self, if_pos (by omega)]
          have hgi : (if i < n + k then val (bypass n C r i) x i else false) = val C x i := by
            rcases hi with hi | hi
            · rw [if_pos (by omega), bypass_val_lt hx hr i hi]
            · rw [if_neg (by omega), val_ge hx hi]
          rw [hgi]
          exact hR ⟨k + 1, by omega, hk1, hi'⟩
        · by_cases h2 : i' < n + r
          · rw [aliasWire_lt_self h2, if_pos (by omega), if_pos (by omega),
              bypass_val_lt hx hr i' h2]
            exact hrefl _
          · by_cases h3 : i' < n + (k + 1)
            · have key := ih i' h3 h1
              rw [aliasWire_gt_self (by omega)] at key
              rw [aliasWire_gt_self (by omega), if_pos h3, if_pos (by omega)]
              exact key
            · rw [aliasWire_gt_self (by omega), if_neg h3, if_neg (by omega)]
              exact hrefl _

lemma bypass_eval_rel {R : Bool → Bool → Prop} (hrefl : ∀ b, R b b) (hmono : OpMono R)
    {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n)
    (hAO : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {r i : ℕ} (hr : r < C.gates.length) (hi : i < n + r ∨ n + C.gates.length ≤ i)
    (hR : R (val C x (n + r)) (val C x i)) :
    R (C.eval x) ((bypass n C r i).eval x) := by
  rw [eval_eq_val, eval_eq_val, bypass_output]
  by_cases h : C.output = n + r
  · have hgi : val (bypass n C r i) x i = val C x i := by
      rcases hi with hi | hi
      · exact bypass_val_lt hx hr i hi
      · rw [val_ge hx hi, val_ge hx (by rw [bypass_length]; omega)]
    rw [h, aliasWire_self, hgi]; exact hR
  · exact bypass_rel hrefl hmono hx hAO hr hi (fun _ => hR) _ h

lemma bypass_mem {n : ℕ} {C : Circuit} {r i : ℕ} :
    ∀ g ∈ (bypass n C r i).gates, ∃ g' ∈ C.gates, g.op = g'.op ∧
      g.inputs.length = g'.inputs.length := by
  intro g hg
  simp only [bypass, List.mem_map, List.mem_range] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  split_ifs with h
  · exact ⟨gateAt C k, gateAt_mem (by omega), rfl, rfl⟩
  · exact ⟨gateAt C (k + 1), gateAt_mem (by omega), rfl, by simp [aliasGate]⟩

lemma erase_eq_bypass (n : ℕ) (C : Circuit) (r i : ℕ) (hr : r < C.gates.length) :
    PEqualNP.CircuitMoves.eraseGate n C r i = bypass n C r i := by
  unfold PEqualNP.CircuitMoves.eraseGate
  rw [if_pos hr]
  change Circuit.mk _ (aliasWire (n + r) i C.output) = Circuit.mk _ (aliasWire (n + r) i C.output)
  congr 1
  apply List.ext_getElem
  · simp [bypass]; omega
  · intro k hk hk'
    have hlen : (C.gates.take r).length = r := by simp; omega
    have hklen : k < C.gates.length - 1 := by simpa [bypass] using hk'
    simp only [bypass, List.getElem_map, List.getElem_range]
    by_cases hkr : k < r
    · rw [if_pos hkr, List.getElem_append_left (by omega), List.getElem_take,
        gateAt_eq (by omega)]
    · rw [if_neg hkr, List.getElem_append_right (by omega), List.getElem_map,
        List.getElem_drop]
      simp only [hlen]
      have he : r + 1 + (k - r) = k + 1 := by omega
      simp only [he]
      rw [gateAt_eq (by omega : k + 1 < C.gates.length)]
      rfl

lemma mono_ops {C : Circuit} (hM : Monotone2 C) :
    ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  intro k hk
  exact (hM _ (gateAt_mem hk)).1

lemma opMono_reverse : OpMono (fun a b => b = true → a = true) := by
  intro op hop l f g h
  exact opMono_imp op hop l g f h

lemma bypass_mono {n : ℕ} {C : Circuit} {r i : ℕ} (hM : Monotone2 C) :
    Monotone2 (bypass n C r i) := by
  intro g hg
  obtain ⟨g', hg', hop, hlen⟩ := bypass_mem g hg
  rw [hop, hlen]
  exact hM g' hg'

lemma opMono_eq : OpMono (fun a b => a = b) := by
  intro op _ l f g h
  congr 1
  exact List.map_congr_left h

lemma input_false_value {n : ℕ} (C : Circuit) (u : Fin n) (x : Fin n → Bool)
    (hu : x u = false) : val C (List.ofFn x) u.val = false := by
  rw [val_input (by simp) u.isLt]
  simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, u.isLt] using hu

lemma two_values_of_mem (l : List ℕ) (u : ℕ) (hlen : l.length ≤ 2) (hu : u ∈ l) :
    ∃ v : ℕ, ∀ i, i ∈ l ↔ i = u ∨ i = v := by
  cases l with
  | nil => simp at hu
  | cons a rest =>
    cases rest with
    | nil =>
      have he : u = a := by simpa using hu
      subst u
      exact ⟨a, by simp⟩
    | cons b rest =>
      have hrest : rest = [] := by
        cases rest with
        | nil => rfl
        | cons c cs => simp only [List.length_cons] at hlen; omega
      subst rest
      have he : u = a ∨ u = b := by simpa using hu
      rcases he with rfl | rfl
      · exact ⟨b, by simp⟩
      · refine ⟨a, ?_⟩
        intro i
        simp [or_comm]

lemma reader_alias_on_zero {n : ℕ} {C : Circuit} (hM : Monotone2 C)
    (u : Fin n) {r : ℕ} (hr : r < C.gates.length)
    (hu : u.val ∈ (gateAt C r).inputs) :
    ∃ i : ℕ, i < n + r ∧ ∀ x : Fin n → Bool, x u = false →
      val C (List.ofFn x) (n + r) = val C (List.ofFn x) i := by
  rcases mono_ops hM r hr with hop | hop
  · refine ⟨u.val, by omega, ?_⟩
    intro x hxu
    have huf := input_false_value C u x hxu
    rw [huf]
    apply Bool.eq_false_iff.mpr
    intro ht
    have hutrue := ((val_and (n := n) (C := C) (x := List.ofFn x)
      (by simp) hr hop).mp ht u.val hu).2
    rw [huf] at hutrue
    contradiction
  · obtain ⟨v, hshape⟩ := two_values_of_mem (gateAt C r).inputs u.val
      (hM _ (gateAt_mem hr)).2 hu
    by_cases hv : v < n + r
    · refine ⟨v, hv, ?_⟩
      intro x hxu
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro ht
        obtain ⟨i, hi, _, hit⟩ := (val_or (n := n) (C := C)
          (x := List.ofFn x) (by simp) hr hop).mp ht
        rcases (hshape i).mp hi with hiu | hiv
        · subst i
          rw [input_false_value C u x hxu] at hit
          contradiction
        · subst i
          exact hit
      · intro ht
        exact (val_or (n := n) (C := C) (x := List.ofFn x) (by simp) hr hop).mpr
          ⟨v, (hshape v).mpr (Or.inr rfl), hv, ht⟩
    · refine ⟨u.val, by omega, ?_⟩
      intro x hxu
      rw [input_false_value C u x hxu]
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨i, hi, hib, hit⟩ := (val_or (n := n) (C := C)
        (x := List.ofFn x) (by simp) hr hop).mp ht
      rcases (hshape i).mp hi with hiu | hiv
      · subst i
        rw [input_false_value C u x hxu] at hit
        contradiction
      · subst i
        exact hv hib

lemma prune_input_false {n : ℕ} {C : Circuit} (hM : Monotone2 C)
    (u : Fin n) {r : ℕ} (hr : r < C.gates.length)
    (hu : u.val ∈ (gateAt C r).inputs) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, x u = false → D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  obtain ⟨i, hi, heq⟩ := reader_alias_on_zero hM u hr hu
  refine ⟨bypass n C r i, bypass_mono hM, ?_, ?_⟩
  · change (bypass n C r i).gates.length + 1 = C.gates.length
    rw [bypass_length]
    omega
  · intro x hxu
    exact (bypass_eval_rel (R := fun a b => a = b) (fun _ => rfl) opMono_eq
      (n := n) (C := C) (x := List.ofFn x) (by simp) (mono_ops hM) hr
      (Or.inl hi) (heq x hxu)).symm

def SameExcept (u : ℕ) (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, i ≠ u → w.getD i false = z.getD i false

lemma sameExcept_append (u : ℕ) (w z : List Bool) (b : Bool)
    (h : SameExcept u w z) : SameExcept u (w ++ [b]) (z ++ [b]) := by
  refine ⟨by simpa using h.1, ?_⟩
  have hlen := h.1
  intro i hi
  by_cases hlt : i < w.length
  · rw [List.getD_append w [b] false i hlt,
      List.getD_append z [b] false i (by omega)]
    exact h.2 i hi
  · rw [List.getD_append_right w [b] false i (by omega),
      List.getD_append_right z [b] false i (by omega), h.1]

lemma step_sameExcept (u : ℕ) (w z : List Bool) (g : Gate)
    (h : SameExcept u w z) (hg : u ∉ g.inputs) :
    SameExcept u (stepWire w g) (stepWire z g) := by
  have he : g.inputs.map (fun i => w.getD i false) =
      g.inputs.map (fun i => z.getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact h.2 i (by intro e; subst i; exact hg hi)
  unfold stepWire
  rw [he]
  exact sameExcept_append u w z _ h

lemma fold_sameExcept (u : ℕ) (gs : List Gate) (w z : List Bool)
    (h : SameExcept u w z) (hg : ∀ g ∈ gs, u ∉ g.inputs) :
    SameExcept u (gs.foldl stepWire w) (gs.foldl stepWire z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    exact ih (stepWire w g) (stepWire z g) (step_sameExcept u w z g h (hg g (by simp)))
      (by intro g hg'; exact hg g (by simp [hg']))

lemma sameExcept_ofFn {n : ℕ} (u : Fin n) (x y : Fin n → Bool)
    (h : ∀ i, i ≠ u → x i = y i) :
    SameExcept u.val (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hin : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hin),
      List.getD_eq_getElem _ _ (by simpa using hin)]
    simpa using h ⟨i, hin⟩ (by intro e; exact hi (congrArg Fin.val e))
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hin),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hin)]

lemma exists_gate_read_of_essential {n : ℕ} (C : Circuit) (u : Fin n)
    (hout : C.output ≠ u.val) (x y : Fin n → Bool)
    (hxy : ∀ i, i ≠ u → x i = y i)
    (hdiff : C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ r, r < C.gates.length ∧ u.val ∈ (gateAt C r).inputs := by
  by_contra hn
  push Not at hn
  have hmem : ∀ g ∈ C.gates, u.val ∉ g.inputs := by
    intro g hg
    obtain ⟨r, hr, hgr⟩ := List.mem_iff_getElem.mp hg
    subst g
    simpa only [gateAt, List.getD_eq_getElem _ _ hr] using hn r hr
  have he := (fold_sameExcept u.val C.gates (List.ofFn x) (List.ofFn y)
    (sameExcept_ofFn u x y hxy) hmem).2 C.output hout
  exact hdiff he

lemma restrict_essential_input_false {n : ℕ} {C : Circuit} (hM : Monotone2 C)
    (u : Fin n) (hout : C.output ≠ u.val) (x y : Fin n → Bool)
    (hxy : ∀ i, i ≠ u → x i = y i)
    (hdiff : C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 = C.size ∧
      ∀ z : Fin n → Bool, z u = false → D.eval (List.ofFn z) = C.eval (List.ofFn z) := by
  obtain ⟨r, hr, hu⟩ := exists_gate_read_of_essential C u hout x y hxy hdiff
  exact prune_input_false hM u hr hu

end Pruning

namespace MixedSixBoundary

abbrev graph : SimpleGraph (Fin 26) :=
  SimpleGraph.fromRel fun u v => u.val < 13 ∧ 13 ≤ v.val ∧
    (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)

def support : Finset (Fin 26) := {0, 15, 17, 18, 19, 20}

def neighbors : Finset (Fin 26) :=
  Finset.univ.filter fun v => ∃ u ∈ support, graph.Adj u v

def edge (A : Finset (Fin 26)) : Bool :=
  decide (∃ p ∈ A, ∃ q ∈ A, graph.Adj p q)

def preMask (A : Finset (Fin 26)) : Bool :=
  edge A || decide (support ⊆ A)

def mask (A : Finset (Fin 26)) : Bool :=
  decide (∃ v ∈ A, v ∈ neighbors)

theorem support_size : support.card = 6 := by decide +kernel

theorem support_shores :
    (support.filter fun v => v.val < 13).card = 1 ∧
    (support.filter fun v => 13 ≤ v.val).card = 5 := by decide +kernel

theorem support_independent :
    ∀ u ∈ support, ∀ v ∈ support, ¬ graph.Adj u v := by decide +kernel

set_option synthInstance.maxSize 1000 in
theorem neighborhood_covers_edges : ∀ a b, graph.Adj a b →
    (∃ u ∈ support, graph.Adj u a) ∨ (∃ u ∈ support, graph.Adj u b) := by
  decide +kernel

theorem neighborhood_size : neighbors.card = 16 := by decide +kernel

theorem not_dominating_witness :
    (21 : Fin 26) ∉ support ∧ ∀ u ∈ support, ¬ graph.Adj u 21 := by
  decide +kernel

theorem edge_support : edge support = false := by decide +kernel

theorem preMask_support : preMask support = true := by
  simp [preMask]

theorem preMask_mono (A B : Finset (Fin 26)) (hAB : A ⊆ B)
    (h : preMask A = true) : preMask B = true := by
  simp only [preMask, Bool.or_eq_true, edge, decide_eq_true_eq] at h ⊢
  rcases h with ⟨p, hp, q, hq, hpq⟩ | hs
  · exact Or.inl ⟨p, hAB hp, q, hAB hq, hpq⟩
  · exact Or.inr (fun u hu => hAB (hs hu))

lemma neighborhood_cover_mask_identity
    {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (U : Finset α)
    (cover : ∀ a b, G.Adj a b →
      (∃ u ∈ U, G.Adj u a) ∨ (∃ u ∈ U, G.Adj u b))
    (A : Finset α) :
    ((decide (∃ a ∈ A, ∃ b ∈ A, G.Adj a b) || decide (U ⊆ A)) &&
      decide (∃ v ∈ A, ∃ u ∈ U, G.Adj u v)) =
        decide (∃ a ∈ A, ∃ b ∈ A, G.Adj a b) := by
  by_cases he : ∃ a ∈ A, ∃ b ∈ A, G.Adj a b
  · have hit : ∃ v ∈ A, ∃ u ∈ U, G.Adj u v := by
      obtain ⟨a, ha, b, hb, hab⟩ := he
      rcases cover a b hab with h | h
      · exact ⟨a, ha, h⟩
      · exact ⟨b, hb, h⟩
    simp [he, hit]
  · by_cases hs : U ⊆ A
    · have miss : ¬ ∃ v ∈ A, ∃ u ∈ U, G.Adj u v := by
        rintro ⟨v, hv, u, hu, huv⟩
        exact he ⟨u, hs hu, v, hv, huv⟩
      simp [he, miss]
    · simp [he, hs]

theorem masked_eq (A : Finset (Fin 26)) :
    (preMask A && mask A) = edge A := by
  have h := neighborhood_cover_mask_identity graph support neighborhood_covers_edges A
  simpa [preMask, mask, edge, neighbors] using h

end MixedSixBoundary

namespace FalseOrCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {m : ℕ}

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def cost (w : List Bool) (g : Gate) : ℕ :=
  match g.op with
  | .or => if g.op.eval (g.inputs.map fun i => w.getD i false) = false then 1 else 0
  | _ => 0

def falseOrCount : List Gate → List Bool → ℕ
  | [], _ => 0
  | g :: gs, w => cost w g + falseOrCount gs (step w g)

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ)
    (h : j ≠ L.length) : (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin m))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

-- Weighted adaptation of the support-count argument in Helpers/Support.lean.
lemma cnt_step (t k : ℕ) (L : List (Finset (Fin m))) (P : Finset ℕ)
    (hp : P.card ≤ k + 1) (h : Cnt t L) :
    Cnt (t + k) (L ++ [P.biUnion fun j => L.getD j ∅]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j =>
          (L ++ [P.biUnion fun a => L.getD a ∅]).getD j ∅)
        ⊆ ((W.erase L.length ∪ P).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        have hij' : i ∈ P.biUnion (fun a => L.getD a ∅) := by simpa using hij
        obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hij'
        exact ⟨a, Finset.mem_union_right _ ha, hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ P).card ≤ (W.card - 1) + (k + 1) := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left hp _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ P)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j =>
          (L ++ [P.biUnion fun a => L.getD a ∅]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

lemma gate_parents (w : List Bool) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length ≤ 2) :
    ∃ P : Finset ℕ, P.card ≤ cost w g + 1 ∧
      ∀ z : List Bool,
        g.op.eval (g.inputs.map fun i => w.getD i false) = false →
        g.op.eval (g.inputs.map fun i => z.getD i false) = true →
        ∃ j ∈ P, w.getD j false = false ∧ z.getD j false = true := by
  classical
  by_cases hb : g.op.eval (g.inputs.map fun i => w.getD i false) = false
  · rcases hop with hop | hop
    · have hf : ∃ j ∈ g.inputs, w.getD j false = false := by
        simpa [hop, GateOp.eval, List.all_eq_false] using hb
      obtain ⟨j, hj, hwj⟩ := hf
      refine ⟨{j}, by simp [cost, hop], ?_⟩
      intro z _ hz
      have hzj : z.getD j false = true := by
        have hz' : ∀ a ∈ g.inputs, z.getD a false = true := by
          simpa [hop, GateOp.eval] using hz
        exact hz' j hj
      exact ⟨j, by simp, hwj, hzj⟩
    · refine ⟨g.inputs.toFinset, ?_, ?_⟩
      · have hc : cost w g = 1 := by
          unfold cost
          rw [hop]
          exact ite_eq_left (by simpa only [hop] using hb)
        rw [hc]
        exact le_trans (List.toFinset_card_le _) hlen
      · intro z _ hz
        have hf : ∃ j ∈ g.inputs, z.getD j false = true := by
          simpa [hop, GateOp.eval] using hz
        obtain ⟨j, hj, hzj⟩ := hf
        have hwj : w.getD j false = false := by
          have hw' : ∀ a ∈ g.inputs, w.getD a false = false := by
            simpa [hop, GateOp.eval, List.any_eq_false] using hb
          exact hw' j hj
        exact ⟨j, List.mem_toFinset.mpr hj, hwj, hzj⟩
  · refine ⟨∅, by simp, ?_⟩
    intro z hz _
    exact (hb hz).elim

def Covers (L : List (Finset (Fin m))) (w : List Bool)
    (X : Fin m → List Bool) : Prop :=
  L.length = w.length ∧ (∀ i, (X i).length = w.length) ∧
    ∀ j, w.getD j false = false → ∀ i, (X i).getD j false = true → i ∈ L.getD j ∅

lemma covers_step (L : List (Finset (Fin m))) (w : List Bool)
    (X : Fin m → List Bool) (g : Gate) (P : Finset ℕ)
    (h : Covers L w X)
    (hp : ∀ z : List Bool,
        g.op.eval (g.inputs.map fun i => w.getD i false) = false →
        g.op.eval (g.inputs.map fun i => z.getD i false) = true →
        ∃ j ∈ P, w.getD j false = false ∧ z.getD j false = true) :
    Covers (L ++ [P.biUnion fun j => L.getD j ∅]) (step w g)
      (fun i => step (X i) g) := by
  refine ⟨by simp [step, h.1], ?_, ?_⟩
  · intro i; simp [step, h.2.1 i]
  · intro j hj i hi
    by_cases heq : j = L.length
    · subst j
      have hj' : g.op.eval (g.inputs.map fun a => w.getD a false) = false := by
        simpa [step, h.1] using hj
      have hi' : g.op.eval (g.inputs.map fun a => (X i).getD a false) = true := by
        simpa [step, h.1, ← h.2.1 i] using hi
      obtain ⟨a, ha, hwa, hxa⟩ := hp (X i) hj' hi'
      simpa using Finset.mem_biUnion.mpr ⟨a, ha, h.2.2 a hwa i hxa⟩
    · rw [getD_snoc_ne _ _ _ _ heq]
      apply h.2.2 j
      · have hL := h.1
        change (w ++ [_]).getD j false = false at hj
        rw [getD_snoc_ne w _ false j (by omega)] at hj
        exact hj
      · have hL := h.1
        have hiL := h.2.1 i
        change (X i ++ [_]).getD j false = true at hi
        rw [getD_snoc_ne (X i) _ false j (by omega)] at hi
        exact hi

lemma count_fold (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (t : ℕ) (L : List (Finset (Fin m))) (w : List Bool)
    (X : Fin m → List Bool) (hc : Cnt t L) (hv : Covers L w X) :
    ∃ L', Cnt (t + falseOrCount gs w) L' ∧
      Covers L' (gs.foldl step w) (fun i => gs.foldl step (X i)) := by
  induction gs generalizing t L w X with
  | nil => exact ⟨L, hc, hv⟩
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hm g (by simp)
    obtain ⟨P, hpc, hp⟩ := gate_parents w g hop hlen
    have htail : ∀ g' ∈ gs, (g'.op = .and ∨ g'.op = .or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hm g' (List.mem_cons_of_mem _ hg')
    obtain ⟨L', hc', hv'⟩ := ih htail (t + cost w g)
      (L ++ [P.biUnion fun j => L.getD j ∅]) (step w g) (fun i => step (X i) g)
      (cnt_step t (cost w g) L P hpc hc) (covers_step L w X g P hv hp)
    exact ⟨L', by simpa [falseOrCount, Nat.add_assoc] using hc', hv'⟩

def inputSupports (w : List Bool) (X : Fin m → List Bool) : List (Finset (Fin m)) :=
  List.ofFn fun j : Fin w.length =>
    Finset.univ.filter fun i => w.getD j.val false = false ∧ (X i).getD j.val false = true

lemma cnt_inputs (w : List Bool) (X : Fin m → List Bool)
    (hsep : ∀ j, w.getD j false = false → ∀ i k,
      (X i).getD j false = true → (X k).getD j false = true → i = k) :
    Cnt 0 (inputSupports w X) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j < w.length
  · simp only [inputSupports, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      dite_eq_left hj, Option.getD_some]
    apply Finset.card_le_one.mpr
    intro i hi k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hk
    exact hsep j hi.1 i k hi.2 hk.2
  · rw [List.getD_eq_default _ _ (by simp [inputSupports]; omega)]
    simp

lemma covers_inputs (w : List Bool) (X : Fin m → List Bool)
    (hlen : ∀ i, (X i).length = w.length) : Covers (inputSupports w X) w X := by
  refine ⟨by simp [inputSupports], hlen, ?_⟩
  intro j hj i hi
  have hjlt : j < w.length := by
    by_contra h
    have : (X i).getD j false = false := List.getD_eq_default _ _ (by rw [hlen i]; omega)
    rw [this] at hi
    contradiction
  simp only [inputSupports, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dite_eq_left hjlt, Option.getD_some, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hj, hi⟩

/-- Disjoint singleton changes at false raw inputs require one fewer false OR gates. -/
theorem finite_tests_false_or_bound (C : Circuit) (hm : Monotone2 C)
    (w : List Bool) (X : Fin m → List Bool)
    (hlen : ∀ i, (X i).length = w.length)
    (hsep : ∀ j, w.getD j false = false → ∀ i k,
      (X i).getD j false = true → (X k).getD j false = true → i = k)
    (hneg : C.eval w = false) (hpos : ∀ i, C.eval (X i) = true) :
    m ≤ falseOrCount C.gates w + 1 := by
  obtain ⟨L, hc, hv⟩ := count_fold C.gates hm 0 (inputSupports w X) w X
    (cnt_inputs w X hsep) (covers_inputs w X hlen)
  have hall : ∀ i : Fin m, i ∈ L.getD C.output ∅ := by
    intro i
    exact hv.2.2 C.output hneg i (hpos i)
  have heq : L.getD C.output ∅ = Finset.univ := Finset.eq_univ_of_forall hall
  have hbound := hc {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hbound
  rw [heq] at hbound
  simpa only [Finset.card_univ, Fintype.card_fin] using hbound

def extension {n : ℕ} (M : Fin n → Bool) (outside : Fin m → Fin n)
    (i : Fin m) (j : Fin n) : Bool :=
  if j = outside i then true else M j

lemma extension_true_unique {n : ℕ} (M : Fin n → Bool) (outside : Fin m → Fin n)
    (hinj : Function.Injective outside) (j : Fin n) (hbase : M j = false)
    (i k : Fin m) (hi : extension M outside i j = true)
    (hk : extension M outside k j = true) : i = k := by
  have hij : j = outside i := by
    by_contra hne
    simp [extension, hne, hbase] at hi
  have hkj : j = outside k := by
    by_contra hne
    simp [extension, hne, hbase] at hk
  exact hinj (hij.symm.trans hkj)

/-- Only the base negative and the distinct singleton extensions are required. -/
theorem singleton_extensions_false_or_bound {n : ℕ}
    (C : Circuit) (hm : Monotone2 C) (M : Fin n → Bool)
    (outside : Fin m → Fin n) (hinj : Function.Injective outside)
    (hneg : C.eval (List.ofFn M) = false)
    (hpos : ∀ i, C.eval (List.ofFn (extension M outside i)) = true) :
    m ≤ falseOrCount C.gates (List.ofFn M) + 1 := by
  apply finite_tests_false_or_bound C hm (List.ofFn M)
    (fun i => List.ofFn (extension M outside i)) (by intro i; simp) _ hneg hpos
  intro j hj i k hi hk
  by_cases hjn : j < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      dite_eq_left hjn, Option.getD_some] at hj hi hk
    exact extension_true_unique M outside hinj ⟨j, hjn⟩ hj i k hi hk
  · have hfalse : (List.ofFn (extension M outside i)).getD j false = false :=
      List.getD_eq_default _ _ (by simp; omega)
    rw [hfalse] at hi
    contradiction

def orCount : List Gate → ℕ
  | [] => 0
  | g :: gs => (match g.op with | .or => 1 | _ => 0) + orCount gs

def trueCost (w : List Bool) (g : Gate) : ℕ :=
  match g.op with
  | .or => if g.op.eval (g.inputs.map fun i => w.getD i false) = true then 1 else 0
  | _ => 0

def trueOrCount : List Gate → List Bool → ℕ
  | [], _ => 0
  | g :: gs, w => trueCost w g + trueOrCount gs (step w g)

lemma orCount_partition (gs : List Gate) (w : List Bool) :
    falseOrCount gs w + trueOrCount gs w = orCount gs := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hpart := ih (step w g)
    have hc : cost w g + trueCost w g = (match g.op with | .or => 1 | _ => 0) := by
      cases hop : g.op <;> simp only [cost, trueCost, hop]
      cases hv : GateOp.or.eval (g.inputs.map fun i => w.getD i false) <;> simp
    simp only [falseOrCount, trueOrCount, orCount]
    omega

/-- Equivalent cut on the number of OR gates true at the base assignment. -/
theorem singleton_extensions_true_or_cut {n : ℕ}
    (C : Circuit) (hm : Monotone2 C) (M : Fin n → Bool)
    (outside : Fin m → Fin n) (hinj : Function.Injective outside)
    (hneg : C.eval (List.ofFn M) = false)
    (hpos : ∀ i, C.eval (List.ofFn (extension M outside i)) = true) :
    trueOrCount C.gates (List.ofFn M) + m ≤ orCount C.gates + 1 := by
  have hbound := singleton_extensions_false_or_bound C hm M outside hinj hneg hpos
  have hpart := orCount_partition C.gates (List.ofFn M)
  omega

end FalseOrCut

end PEqualNP.Outside.L_meta_2056
