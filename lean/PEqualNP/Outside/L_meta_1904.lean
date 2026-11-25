import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1904

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev EdgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def Computes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
  ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (EdgeTrue G x)

def SafeAt {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (j : ℕ) : Prop :=
  ∀ g, C.gates[j]? = some g → g.op = .and →
    ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = true → EdgeTrue G x

noncomputable def badSet {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) : Finset ℕ :=
  by classical exact (Finset.range C.size).filter fun j => ¬ SafeAt G C j

lemma mem_badSet {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) (j : ℕ) :
    j ∈ badSet G C ↔ j < C.size ∧ ¬ SafeAt G C j := by
  classical
  simp [badSet]

lemma badSet_card_lt_of_repair {n : ℕ} (G : SimpleGraph (Fin n)) (C D : Circuit)
    (size : D.size = C.size)
    (preserve : ∀ j, SafeAt G C j → SafeAt G D j)
    (j : ℕ) (bound : j < C.size) (bad : ¬ SafeAt G C j) (fixed : SafeAt G D j) :
    (badSet G D).card < (badSet G C).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro k hk
    rw [mem_badSet] at hk ⊢
    exact ⟨by omega, fun h => hk.2 (preserve k h)⟩
  · intro eq
    have member : j ∈ badSet G C := (mem_badSet G C j).mpr ⟨bound, bad⟩
    rw [← eq, mem_badSet] at member
    exact member.2 fixed

lemma exists_extremal {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (initial : ∃ C : Circuit, Monotone2 C ∧ Computes G C) :
    ∃ C : Circuit, Monotone2 C ∧ Computes G C ∧
      (∀ D : Circuit, Monotone2 D → Computes G D → C.size ≤ D.size) ∧
      (∀ D : Circuit, Monotone2 D → Computes G D → D.size ≤ C.size →
        (badSet G C).card ≤ (badSet G D).card) := by
  classical
  let sizes (k : ℕ) := ∃ C : Circuit, Monotone2 C ∧ Computes G C ∧ C.size = k
  have hex : ∃ k, sizes k := by
    obtain ⟨C, hm, hc⟩ := initial
    exact ⟨C.size, C, hm, hc, rfl⟩
  obtain ⟨B, hmB, hcB, hsizeB⟩ := Nat.find_spec hex
  have least (D : Circuit) (hm : Monotone2 D) (hc : Computes G D) : B.size ≤ D.size := by
    rw [hsizeB]
    exact Nat.find_min' hex ⟨D, hm, hc, rfl⟩
  let counts (k : ℕ) := ∃ C : Circuit,
    Monotone2 C ∧ Computes G C ∧ C.size = B.size ∧ (badSet G C).card = k
  have hex2 : ∃ k, counts k := ⟨(badSet G B).card, B, hmB, hcB, rfl, rfl⟩
  obtain ⟨C, hmC, hcC, hsizeC, hcountC⟩ := Nat.find_spec hex2
  refine ⟨C, hmC, hcC, ?_, ?_⟩
  · intro D hm hc
    rw [hsizeC]
    exact least D hm hc
  · intro D hm hc hs
    have heq : D.size = B.size := by
      have h := least D hm hc
      omega
    rw [hcountC]
    exact Nat.find_min' hex2 ⟨D, hm, hc, heq, rfl⟩

lemma extremal_repair_impossible {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit)
    (extremal : ∀ D : Circuit, Monotone2 D → Computes G D → D.size ≤ C.size →
      (badSet G C).card ≤ (badSet G D).card)
    (D : Circuit) (mono : Monotone2 D) (correct : Computes G D)
    (size : D.size = C.size)
    (preserve : ∀ j, SafeAt G C j → SafeAt G D j)
    (j : ℕ) (bound : j < C.size) (bad : ¬ SafeAt G C j) (fixed : SafeAt G D j) : False := by
  have hle := extremal D mono correct (Nat.le_of_eq size)
  have hlt := badSet_card_lt_of_repair G C D size preserve j bound bad fixed
  omega

namespace Activation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev EdgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def NegativeAt {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (j : ℕ) (x : Fin n → Bool) : Prop :=
  ¬ EdgeTrue G x ∧ ∃ g, C.gates[j]? = some g ∧ g.op = .and ∧
    (C.wires (List.ofFn x)).getD (n + j) false = true

noncomputable def negativeActivations {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit) :
    Finset (ℕ × (Fin n → Bool)) := by
  classical
  exact ((Finset.range C.size).product Finset.univ).filter fun p => NegativeAt G C p.1 p.2

lemma mem_negativeActivations {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (j : ℕ) (x : Fin n → Bool) :
    (j, x) ∈ negativeActivations G C ↔ j < C.size ∧ NegativeAt G C j x := by
  classical
  simp [negativeActivations]

lemma negativeAt_of_decrease {n : ℕ} (G : SimpleGraph (Fin n)) (C D : Circuit)
    (ops : ∀ (j : ℕ) (g : Gate), D.gates[j]? = some g → g.op = .and →
      ∃ h : Gate, C.gates[j]? = some h ∧ h.op = .and)
    (decrease : ∀ (j : ℕ) (x : Fin n → Bool), ¬ EdgeTrue G x →
      (D.wires (List.ofFn x)).getD (n + j) false = true →
        (C.wires (List.ofFn x)).getD (n + j) false = true) :
    ∀ j x, NegativeAt G D j x → NegativeAt G C j x := by
  rintro j x ⟨noedge, g, entry, op, active⟩
  obtain ⟨h, hentry, hop⟩ := ops j g entry op
  exact ⟨noedge, h, hentry, hop, decrease j x noedge active⟩

lemma activation_card_lt {n : ℕ} (G : SimpleGraph (Fin n)) (C D : Circuit)
    (size : D.size = C.size)
    (preserve : ∀ j x, NegativeAt G D j x → NegativeAt G C j x)
    (j : ℕ) (x : Fin n → Bool) (bound : j < C.size)
    (old : NegativeAt G C j x) (fixed : ¬ NegativeAt G D j x) :
    (negativeActivations G D).card < (negativeActivations G C).card := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · rintro ⟨k, y⟩ hk
    rw [mem_negativeActivations] at hk ⊢
    exact ⟨by omega, preserve k y hk.2⟩
  · intro eq
    have member : (j, x) ∈ negativeActivations G C :=
      (mem_negativeActivations G C j x).mpr ⟨bound, old⟩
    rw [← eq, mem_negativeActivations] at member
    exact fixed member.2

lemma exists_measure_minimum {P : Circuit → Prop} (initial : ∃ C, P C)
    (measure : Circuit → ℕ) :
    ∃ C : Circuit, P C ∧ (∀ D : Circuit, P D → C.size ≤ D.size) ∧
      ∀ D : Circuit, P D → D.size ≤ C.size → measure C ≤ measure D := by
  classical
  let sizes (k : ℕ) := ∃ C : Circuit, P C ∧ C.size = k
  have hex : ∃ k, sizes k := by
    obtain ⟨C, hc⟩ := initial
    exact ⟨C.size, C, hc, rfl⟩
  obtain ⟨B, hcB, hsizeB⟩ := Nat.find_spec hex
  have least (D : Circuit) (hc : P D) : B.size ≤ D.size := by
    rw [hsizeB]
    exact Nat.find_min' hex ⟨D, hc, rfl⟩
  let counts (k : ℕ) := ∃ C : Circuit, P C ∧ C.size = B.size ∧ measure C = k
  have hex2 : ∃ k, counts k := ⟨measure B, B, hcB, rfl, rfl⟩
  obtain ⟨C, hcC, hsizeC, hcountC⟩ := Nat.find_spec hex2
  refine ⟨C, hcC, ?_, ?_⟩
  · intro D hc
    rw [hsizeC]
    exact least D hc
  · intro D hc hs
    have heq : D.size = B.size := by
      have h := least D hc
      omega
    rw [hcountC]
    exact Nat.find_min' hex2 ⟨D, hc, heq, rfl⟩

lemma exists_activation_minimum {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (initial : ∃ C : Circuit, Monotone2 C ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (EdgeTrue G x)) :
    ∃ C : Circuit, Monotone2 C ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (EdgeTrue G x)) ∧
      (∀ D : Circuit, Monotone2 D →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (EdgeTrue G x)) → C.size ≤ D.size) ∧
      (∀ D : Circuit, Monotone2 D →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (EdgeTrue G x)) → D.size ≤ C.size →
          (negativeActivations G C).card ≤ (negativeActivations G D).card) := by
  obtain ⟨C, hc, least, rank⟩ := exists_measure_minimum initial
    (fun C => (negativeActivations G C).card)
  exact ⟨C, hc.1, hc.2, fun D hm hd => least D ⟨hm, hd⟩,
    fun D hm hd hs => rank D ⟨hm, hd⟩ hs⟩

end Activation

namespace P4Obstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def graph : SimpleGraph (Fin 4) where
  Adj u v := u.val + 1 = v.val ∨ v.val + 1 = u.val
  symm := ⟨fun _ _ => Or.symm⟩
  loopless := ⟨by intro u h; omega⟩

lemma no_triangle : ∀ a b c : Fin 4,
    graph.Adj a b → graph.Adj b c → ¬ graph.Adj c a := by
  dsimp only [graph]
  decide

lemma no_square : ∀ a b c d : Fin 4,
    graph.Adj a b → graph.Adj b c → graph.Adj c d → graph.Adj d a →
      a = c ∨ b = d := by
  dsimp only [graph]
  decide

def edgeFn (x : Fin 4 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3)

lemma edgeFn_correct : ∀ x : Fin 4 → Bool,
    edgeFn x = true ↔ ∃ a b, graph.Adj a b ∧ x a = true ∧ x b = true := by
  dsimp only [graph]
  decide

def cnf : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [1, 2]⟩, ⟨.and, [6, 7]⟩], 8⟩

def safe : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [2, 3]⟩,
    ⟨.or, [5, 6]⟩], 7⟩

def bypassLeft : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [1, 2]⟩,
    ⟨.and, [4, 6]⟩], 7⟩

def bypassRight : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [1, 2]⟩,
    ⟨.and, [5, 6]⟩], 7⟩

def singleton (v : Fin 4) : Fin 4 → Bool := fun i => decide (i = v)

def nonedge : Fin 4 → Bool := fun i => decide (i = 0 ∨ i = 3)

lemma cnf_monotone : Monotone2 cnf := by simp [Monotone2, cnf]

lemma cnf_size : cnf.size = 5 := rfl

lemma cnf_correct : ∀ x : Fin 4 → Bool, cnf.eval (List.ofFn x) = edgeFn x := by decide

lemma nonedge_rejected : edgeFn nonedge = false := by decide

lemma middle_and_active : (cnf.wires (List.ofFn nonedge)).getD 6 false = true := by decide

lemma middle_and_tag : cnf.gates[2]? = some ⟨GateOp.and, [4, 5]⟩ := rfl

lemma cnf_rejects_singletons :
    ∀ v : Fin 4, (cnf.wires (List.ofFn (singleton v))).getD 6 false = false ∧
      (cnf.wires (List.ofFn (singleton v))).getD 8 false = false := by decide

lemma bypass_left_fails :
    bypassLeft.eval (List.ofFn (singleton 2)) = true ∧ edgeFn (singleton 2) = false := by decide

lemma bypass_right_fails :
    bypassRight.eval (List.ofFn (singleton 1)) = true ∧ edgeFn (singleton 1) = false := by decide

lemma safe_monotone : Monotone2 safe := by simp [Monotone2, safe]

lemma safe_size : safe.size = 4 := rfl

lemma safe_correct : ∀ x : Fin 4 → Bool, safe.eval (List.ofFn x) = edgeFn x := by decide

lemma safe_and_gates :
    ∀ x : Fin 4 → Bool,
      ((safe.wires (List.ofFn x)).getD 5 false = true → edgeFn x = true) ∧
      ((safe.wires (List.ofFn x)).getD 6 false = true → edgeFn x = true) := by decide

lemma safe_and_indices (j : ℕ) (g : Gate) (atGate : safe.gates[j]? = some g)
    (op : g.op = GateOp.and) : j = 1 ∨ j = 2 := by
  have bound : j < 4 := by
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp atGate
    simpa [safe] using bound
  interval_cases j <;> simp [safe] at atGate <;> subst g <;> simp_all

lemma all_and_safe (j : ℕ) (g : Gate) (atGate : safe.gates[j]? = some g)
    (op : g.op = GateOp.and) (x : Fin 4 → Bool)
    (active : (safe.wires (List.ofFn x)).getD (4 + j) false = true) : edgeFn x = true := by
  rcases safe_and_indices j g atGate op with rfl | rfl
  · exact (safe_and_gates x).1 active
  · exact (safe_and_gates x).2 active

end P4Obstruction

namespace EightNarrowing

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma absorption_narrowing : ∀ a x y z w r : Bool,
    (w && z = true → r = true) →
    (((a || x && (y || z)) && (w || y)) || r) =
      (((a || x && y) && (w || y)) || r) := by decide

def edges : List (Fin 8 × Fin 8) :=
  [(0,4),(0,6),(1,5),(1,6),(1,7),(2,6),(3,7),(4,7)]

def original : Circuit :=
  ⟨[⟨.or,[3,4]⟩,⟨.or,[4,6]⟩,⟨.and,[8,7]⟩,⟨.or,[10,1]⟩,
    ⟨.or,[6,7]⟩,⟨.and,[2,12]⟩,⟨.or,[0,13]⟩,⟨.and,[14,9]⟩,
    ⟨.or,[5,12]⟩,⟨.and,[11,16]⟩,⟨.or,[15,17]⟩],18⟩

def narrowed : Circuit :=
  ⟨[⟨.or,[3,4]⟩,⟨.or,[4,6]⟩,⟨.and,[8,7]⟩,⟨.or,[10,1]⟩,
    ⟨.or,[6,7]⟩,⟨.and,[2,6]⟩,⟨.or,[0,13]⟩,⟨.and,[14,9]⟩,
    ⟨.or,[5,12]⟩,⟨.and,[11,16]⟩,⟨.or,[15,17]⟩],18⟩

def edgeFn (x : Fin 8 → Bool) : Bool := edges.any fun e => x e.1 && x e.2

def eFormula (a b c d e f g h : Bool) : Bool :=
  a && e || a && g || b && f || b && g || b && h || c && g || d && h || e && h

def oldFormula (a b c d e f g h : Bool) : Bool :=
  ((a || c && (g || h)) && (e || g)) ||
    ((((d || e) && h) || b) && (f || (g || h)))

def newFormula (a b c d e f g h : Bool) : Bool :=
  ((a || c && g) && (e || g)) ||
    ((((d || e) && h) || b) && (f || (g || h)))

lemma formulas_agree : ∀ a b c d e f g h : Bool,
    oldFormula a b c d e f g h = eFormula a b c d e f g h ∧
    newFormula a b c d e f g h = eFormula a b c d e f g h := by decide

lemma original_formula (a b c d e f g h : Bool) :
    original.eval [a,b,c,d,e,f,g,h] = oldFormula a b c d e f g h := by
  simp [original, Circuit.eval, Circuit.wires, GateOp.eval,
    List.getD_eq_getElem?_getD, oldFormula]

lemma narrowed_formula (a b c d e f g h : Bool) :
    narrowed.eval [a,b,c,d,e,f,g,h] = newFormula a b c d e f g h := by
  simp [narrowed, Circuit.eval, Circuit.wires, GateOp.eval,
    List.getD_eq_getElem?_getD, newFormula]

lemma edge_formula (x : Fin 8 → Bool) :
    edgeFn x = eFormula (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) := by
  simp [edgeFn, edges, eFormula, Bool.or_assoc]

lemma computes (x : Fin 8 → Bool) :
    original.eval (List.ofFn x) = edgeFn x ∧ narrowed.eval (List.ofFn x) = edgeFn x := by
  have entries : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7] := rfl
  rw [entries, original_formula, narrowed_formula, edge_formula]
  exact formulas_agree _ _ _ _ _ _ _ _

lemma original_size : original.size = 11 := rfl

lemma narrowed_size : narrowed.size = original.size := rfl

lemma original_monotone : Monotone2 original := by simp [Monotone2, original]

lemma narrowed_monotone : Monotone2 narrowed := by simp [Monotone2, narrowed]

def badInput : Fin 8 → Bool := fun i => decide (i = 2 ∨ i = 7)

lemma original_bad :
    (original.wires (List.ofFn badInput)).getD 13 false = true ∧
      edgeFn badInput = false := by decide

lemma narrowed_bad_input_fixed :
    (narrowed.wires (List.ofFn badInput)).getD 13 false = false := by decide

lemma formula_safety : ∀ a b c d e f g h : Bool,
    (((d || e) && h) = true → eFormula a b c d e f g h = true) ∧
    ((c && g) = true → eFormula a b c d e f g h = true) ∧
    (((a || c && g) && (e || g)) = true → eFormula a b c d e f g h = true) ∧
    (((((d || e) && h) || b) && (f || (g || h))) = true →
      eFormula a b c d e f g h = true) := by decide

lemma narrowed_and_outputs_safe (x : Fin 8 → Bool) :
    ((narrowed.wires (List.ofFn x)).getD 10 false = true → edgeFn x = true) ∧
    ((narrowed.wires (List.ofFn x)).getD 13 false = true → edgeFn x = true) ∧
    ((narrowed.wires (List.ofFn x)).getD 15 false = true → edgeFn x = true) ∧
    ((narrowed.wires (List.ofFn x)).getD 17 false = true → edgeFn x = true) := by
  have entries : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7] := rfl
  rw [entries, edge_formula]
  simpa [narrowed, Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD] using
    formula_safety (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)

lemma narrowed_and_indices (j : ℕ) (g : Gate) (atGate : narrowed.gates[j]? = some g)
    (op : g.op = GateOp.and) : j = 2 ∨ j = 5 ∨ j = 7 ∨ j = 9 := by
  have bound : j < 11 := by
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp atGate
    simpa [narrowed] using bound
  interval_cases j <;> simp [narrowed] at atGate <;> subst g <;> simp_all

lemma narrowed_safe (j : ℕ) (g : Gate) (atGate : narrowed.gates[j]? = some g)
    (op : g.op = GateOp.and) (x : Fin 8 → Bool)
    (active : (narrowed.wires (List.ofFn x)).getD (8 + j) false = true) :
    edgeFn x = true := by
  have safe := narrowed_and_outputs_safe x
  rcases narrowed_and_indices j g atGate op with rfl | rfl | rfl | rfl
  · exact safe.1 active
  · exact safe.2.1 active
  · exact safe.2.2.1 active
  · exact safe.2.2.2 active

end EightNarrowing

namespace CloneObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (Fin 9 × Fin 9) :=
  [(0,4),(0,6),(1,5),(1,6),(1,7),(2,6),(3,7),(4,7),(8,6)]

def adjacent (u v : Fin 9) : Bool := edges.contains (u,v) || edges.contains (v,u)

def edgeValue (x : Fin 9 → Bool) : Bool := edges.any fun p => x p.1 && x p.2

def witness : Circuit :=
  ⟨[⟨.or,[2,8]⟩,⟨.or,[3,4]⟩,⟨.or,[4,6]⟩,⟨.and,[10,7]⟩,
    ⟨.or,[12,1]⟩,⟨.or,[6,7]⟩,⟨.and,[9,14]⟩,⟨.or,[0,15]⟩,
    ⟨.and,[16,11]⟩,⟨.or,[5,14]⟩,⟨.and,[13,18]⟩,⟨.or,[17,19]⟩],20⟩

def repaired : Circuit :=
  ⟨[⟨.or,[2,8]⟩,⟨.or,[3,4]⟩,⟨.or,[4,6]⟩,⟨.and,[10,7]⟩,
    ⟨.or,[12,1]⟩,⟨.or,[6,7]⟩,⟨.and,[9,6]⟩,⟨.or,[0,15]⟩,
    ⟨.and,[16,11]⟩,⟨.or,[5,14]⟩,⟨.and,[13,18]⟩,⟨.or,[17,19]⟩],20⟩

def killed : Circuit :=
  ⟨[⟨.or,[2,8]⟩,⟨.or,[3,4]⟩,⟨.or,[4,6]⟩,⟨.and,[10,7]⟩,
    ⟨.or,[12,1]⟩,⟨.or,[6,7]⟩,⟨.or,[]⟩,⟨.or,[0,15]⟩,
    ⟨.and,[16,11]⟩,⟨.or,[5,14]⟩,⟨.and,[13,18]⟩,⟨.or,[17,19]⟩],20⟩

def pair (u v : Fin 9) (i : Fin 9) : Bool := decide (i=u ∨ i=v)

def originalFormula (a b c d e f g h : Bool) : Bool :=
  ((a || c && (g || h)) && (e || g)) || ((((d || e) && h) || b) && (f || (g || h)))

def targetFormula (a b c d e f g h : Bool) : Bool :=
  a && e || a && g || b && f || b && g || b && h || c && g || d && h || e && h

lemma clone_formula : ∀ a b c d e f g h k : Bool,
    originalFormula a b (c || k) d e f g h =
      (targetFormula a b c d e f g h || (k && g)) := by decide

lemma eval_formula (x : Fin 9 → Bool) :
    witness.eval (List.ofFn x) = originalFormula (x 0) (x 1) (x 2 || x 8)
      (x 3) (x 4) (x 5) (x 6) (x 7) := by
  change witness.eval [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8] = _
  simp [witness,Circuit.eval,Circuit.wires,GateOp.eval,List.getD_eq_getElem?_getD,
    originalFormula]

lemma correct (x : Fin 9 → Bool) : witness.eval (List.ofFn x) = edgeValue x := by
  rw [eval_formula,clone_formula]
  simp [edgeValue,edges,targetFormula,Bool.or_assoc]

set_option maxRecDepth 8192 in
lemma repaired_correct (x : Fin 9 → Bool) : repaired.eval (List.ofFn x) = edgeValue x := by
  have rule : ∀ a b c d e f g h k : Bool,
      (((a || (c || k) && g) && (e || g)) || ((((d || e) && h) || b) && (f || (g || h))))
        = (targetFormula a b c d e f g h || (k && g)) := by decide
  change repaired.eval [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8] = _
  have formula : repaired.eval [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8] =
      (((x 0 || (x 2 || x 8) && x 6) && (x 4 || x 6)) ||
        ((((x 3 || x 4) && x 7) || x 1) && (x 5 || (x 6 || x 7)))) := by
    simp [repaired,Circuit.eval,Circuit.wires,GateOp.eval,List.getD_eq_getElem?_getD]
  rw [formula]
  rw [rule]
  simp [edgeValue,edges,targetFormula,Bool.or_assoc]

lemma witness_mono : Monotone2 witness := by
  intro g hg
  simp only [witness,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

lemma repaired_mono : Monotone2 repaired := by
  intro g hg
  simp only [repaired,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp

lemma gate_count : witness.size = 12 ∧ repaired.size = 12 := by decide

lemma bad_pair : adjacent 2 7 = false ∧ adjacent 8 7 = false ∧
    (witness.wires (List.ofFn (pair 2 7))).getD 15 false = true ∧
    (witness.wires (List.ofFn (pair 8 7))).getD 15 false = true := by decide

lemma essential_pairs : adjacent 2 6 = true ∧ adjacent 8 6 = true ∧
    witness.eval (List.ofFn (pair 2 6)) = true ∧
    witness.eval (List.ofFn (pair 8 6)) = true ∧
    killed.eval (List.ofFn (pair 2 6)) = false ∧
    killed.eval (List.ofFn (pair 8 6)) = false := by decide

set_option maxRecDepth 8192 in
lemma repaired_safe (x : Fin 9 → Bool) :
    ((repaired.wires (List.ofFn x)).getD 12 false = true ∨
     (repaired.wires (List.ofFn x)).getD 15 false = true ∨
     (repaired.wires (List.ofFn x)).getD 17 false = true ∨
     (repaired.wires (List.ofFn x)).getD 19 false = true) → edgeValue x = true := by
  have rule : ∀ a b c d e f g h k : Bool,
      (((d || e) && h) = true ∨ ((c || k) && g) = true ∨
       ((a || (c || k) && g) && (e || g)) = true ∨
       ((((d || e) && h) || b) && (f || (g || h))) = true) →
        (targetFormula a b c d e f g h || (k && g)) = true := by decide
  have entries : List.ofFn x = [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8] := rfl
  rw [entries]
  simpa [repaired,Circuit.wires,GateOp.eval,List.getD_eq_getElem?_getD,
    edgeValue,edges,targetFormula,Bool.or_assoc] using
    rule (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8)

set_option maxHeartbeats 2000000 in
lemma no_triangle : ∀ a b c : Fin 9,
    adjacent a b = true → adjacent b c = true → adjacent c a = false := by decide

set_option maxHeartbeats 4000000 in
lemma no_four_cycle : ∀ a b c d : Fin 9,
    adjacent a b = true → adjacent b c = true → adjacent c d = true →
      adjacent d a = true → a=c ∨ b=d := by decide

end CloneObstruction

-- Abstract incidence bounds for distinct source labels and gate output labels.
-- The hypotheses explicitly provide reader coverage and operand capacities.
namespace ConstantSourceCount

lemma true_operand_incidence_bound {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (P D : Finset ι) (T : ι → Finset α) (hPD : P ⊆ D)
    (htrue : ∀ j ∈ P, (T j).card ≤ 2)
    (hfalse : ∀ j ∈ D, j ∉ P → (T j).card ≤ 1) :
    ∑ j ∈ D, (T j).card ≤ D.card + P.card := by
  have indicator : (∑ j ∈ D, if j ∈ P then 1 else 0) = P.card := by
    calc
      (∑ j ∈ D, if j ∈ P then 1 else 0) =
          ∑ j ∈ P, if j ∈ P then 1 else 0 := by
        symm
        apply Finset.sum_subset hPD
        intro j _ hj
        simp [hj]
      _ = P.card := by simp
  calc
    ∑ j ∈ D, (T j).card ≤ ∑ j ∈ D, (1 + if j ∈ P then 1 else 0) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hp : j ∈ P
      · simpa [hp] using htrue j hp
      · simpa [hp] using hfalse j hj hp
    _ = D.card + P.card := by simp [Finset.sum_add_distrib,indicator]

lemma distinct_source_incidence_bound {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (S : Finset α) (P D : Finset ι) (out : ι → α) (T : ι → Finset α)
    (hinj : Set.InjOn out P) (hdisj : Disjoint S (P.image out))
    (hread : S ∪ P.image out ⊆ D.biUnion T) :
    S.card + P.card ≤ ∑ j ∈ D, (T j).card := by
  have himage : (P.image out).card = P.card := Finset.card_image_iff.mpr hinj
  calc
    S.card + P.card = (S ∪ P.image out).card := by
      rw [Finset.card_union_of_disjoint hdisj,himage]
    _ ≤ (D.biUnion T).card := Finset.card_le_card hread
    _ ≤ ∑ j ∈ D, (T j).card := Finset.card_biUnion_le

lemma constant_source_count_le {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (S : Finset α) (P D : Finset ι) (out : ι → α) (T : ι → Finset α)
    (hinj : Set.InjOn out P) (hdisj : Disjoint S (P.image out))
    (hread : S ∪ P.image out ⊆ D.biUnion T) (hPD : P ⊆ D)
    (htrue : ∀ j ∈ P, (T j).card ≤ 2)
    (hfalse : ∀ j ∈ D, j ∉ P → (T j).card ≤ 1) : S.card ≤ D.card := by
  have hl := distinct_source_incidence_bound S P D out T hinj hdisj hread
  have hu := true_operand_incidence_bound P D T hPD htrue hfalse
  omega

end ConstantSourceCount

namespace OneBitCut

variable {V : Type*} [DecidableEq V]

def HasEdge (G : SimpleGraph V) (T : Finset V) : Prop :=
  ∃ u ∈ T, ∃ v ∈ T, G.Adj u v

omit [DecidableEq V] in
lemma no_edge_empty (G : SimpleGraph V) : ¬ HasEdge G ∅ := by
  simp [HasEdge]

omit [DecidableEq V] in
lemma no_edge_singleton (G : SimpleGraph V) (v : V) : ¬ HasEdge G {v} := by
  simp [HasEdge]

lemma edge_pair (G : SimpleGraph V) (u v : V) : HasEdge G {u,v} ↔ G.Adj u v := by
  simp [HasEdge, G.adj_comm]

def Factors (G : SimpleGraph V) (S O : Finset V)
    (code : Finset V → Bool) (decode : Bool → Finset V → Bool) : Prop :=
  ∀ I ⊆ S, ∀ J ⊆ O, HasEdge G (I ∪ J) ↔ decode (code I) J = true

lemma bool_same_when_ne {a b c : Bool} (hab : a ≠ c) (hbc : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

lemma internal_code_ne_empty (G : SimpleGraph V) (S O : Finset V)
    (code : Finset V → Bool) (decode : Bool → Finset V → Bool)
    (factors : Factors G S O code decode) (internal : HasEdge G S) :
    code S ≠ code ∅ := by
  intro same
  have yes : decode (code S) ∅ = true :=
    (factors S Finset.Subset.rfl ∅ (Finset.empty_subset O)).mp (by simpa using internal)
  rw [same] at yes
  have empty : HasEdge G ∅ := by
    simpa using (factors ∅ (Finset.empty_subset S) ∅ (Finset.empty_subset O)).mpr yes
  exact no_edge_empty G empty

lemma crossing_code_ne_empty (G : SimpleGraph V) (S O : Finset V)
    (code : Finset V → Bool) (decode : Bool → Finset V → Bool)
    (factors : Factors G S O code decode) {u v : V}
    (inside : u ∈ S) (outside : v ∈ O) (crossing : G.Adj u v) :
    code {u} ≠ code ∅ := by
  have usub : ({u} : Finset V) ⊆ S := by simpa using inside
  have vsub : ({v} : Finset V) ⊆ O := by simpa using outside
  have edge : HasEdge G ({u} ∪ {v}) := by
    simpa only [Finset.singleton_union] using (edge_pair G u v).mpr crossing
  have yes := (factors {u} usub {v} vsub).mp edge
  intro same
  rw [same] at yes
  have single : HasEdge G {v} := by
    simpa using (factors ∅ (Finset.empty_subset S) {v} vsub).mpr yes
  exact no_edge_singleton G v single

lemma internal_edge_forbids_boundary (G : SimpleGraph V) (S O : Finset V)
    (code : Finset V → Bool) (decode : Bool → Finset V → Bool)
    (factors : Factors G S O code decode) (internal : HasEdge G S) :
    ∀ u ∈ S, ∀ v ∈ O, ¬ G.Adj u v := by
  intro u inside v outside crossing
  have internalCode := internal_code_ne_empty G S O code decode factors internal
  have crossingCode := crossing_code_ne_empty G S O code decode factors inside outside crossing
  have same : code {u} = code S := bool_same_when_ne crossingCode internalCode
  have yes : decode (code S) ∅ = true :=
    (factors S Finset.Subset.rfl ∅ (Finset.empty_subset O)).mp (by simpa using internal)
  rw [← same] at yes
  have single : HasEdge G {u} := by
    simpa using (factors {u} (by simpa using inside) ∅ (Finset.empty_subset O)).mpr yes
  exact no_edge_singleton G u single

lemma active_singletons_same_code (G : SimpleGraph V) (S O : Finset V)
    (code : Finset V → Bool) (decode : Bool → Finset V → Bool)
    (factors : Factors G S O code decode) {u v : V}
    (hu : u ∈ S) (hv : v ∈ S)
    (activeU : ∃ a ∈ O, G.Adj u a) (activeV : ∃ b ∈ O, G.Adj v b) :
    code {u} = code {v} := by
  obtain ⟨a, ha, ua⟩ := activeU
  obtain ⟨b, hb, vb⟩ := activeV
  exact bool_same_when_ne
    (crossing_code_ne_empty G S O code decode factors hu ha ua)
    (crossing_code_ne_empty G S O code decode factors hv hb vb)

lemma active_vertices_same_outside_neighbors (G : SimpleGraph V) (S O : Finset V)
    (code : Finset V → Bool) (decode : Bool → Finset V → Bool)
    (factors : Factors G S O code decode) {u v : V}
    (hu : u ∈ S) (hv : v ∈ S)
    (activeU : ∃ a ∈ O, G.Adj u a) (activeV : ∃ b ∈ O, G.Adj v b) :
    ∀ w ∈ O, G.Adj u w ↔ G.Adj v w := by
  have same := active_singletons_same_code G S O code decode factors hu hv activeU activeV
  intro w hw
  have left := factors {u} (by simpa using hu) {w} (by simpa using hw)
  have right := factors {v} (by simpa using hv) {w} (by simpa using hw)
  simp only [Finset.singleton_union, edge_pair] at left right
  rw [same] at left
  exact left.trans right.symm

lemma distinct_active_vertices_have_one_outside_neighbor
    (G : SimpleGraph V) (S O : Finset V)
    (code : Finset V → Bool) (decode : Bool → Finset V → Bool)
    (factors : Factors G S O code decode)
    (noFour : ∀ a b c d : V,
      G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) (different : u ≠ v)
    (activeU : ∃ a ∈ O, G.Adj u a) (activeV : ∃ b ∈ O, G.Adj v b) :
    ∃ w ∈ O, ∀ z ∈ O, (G.Adj u z ↔ z = w) ∧ (G.Adj v z ↔ z = w) := by
  have same := active_vertices_same_outside_neighbors G S O code decode factors hu hv activeU activeV
  obtain ⟨w, hw, uw⟩ := activeU
  have vw : G.Adj v w := (same w hw).mp uw
  refine ⟨w, hw, ?_⟩
  intro z hz
  have only : G.Adj u z ↔ z = w := by
    constructor
    · intro uz
      have vz : G.Adj v z := (same z hz).mp uz
      rcases noFour u w v z uw vw.symm vz uz.symm with equal | equal
      · exact (different equal).elim
      · exact equal.symm
    · rintro rfl
      exact uw
  exact ⟨only, (same z hz).symm.trans only⟩

end OneBitCut

namespace FiniteCut

open OneBitCut

variable {V Code : Type*} [DecidableEq V]

def Factors (G : SimpleGraph V) (S O : Finset V)
    (code : Finset V → Code) (decode : Code → Finset V → Bool) : Prop :=
  ∀ I ⊆ S, ∀ J ⊆ O, HasEdge G (I ∪ J) ↔ decode (code I) J = true

lemma equal_singleton_codes_same_neighbors
    (G : SimpleGraph V) (S O : Finset V)
    (code : Finset V → Code) (decode : Code → Finset V → Bool)
    (factors : Factors G S O code decode) {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) (same : code {u} = code {v}) :
    ∀ w ∈ O, G.Adj u w ↔ G.Adj v w := by
  intro w hw
  have left := factors {u} (by simpa using hu) {w} (by simpa using hw)
  have right := factors {v} (by simpa using hv) {w} (by simpa using hw)
  simp only [Finset.singleton_union, edge_pair] at left right
  rw [same] at left
  exact left.trans right.symm

lemma crossing_code_ne_empty
    (G : SimpleGraph V) (S O : Finset V)
    (code : Finset V → Code) (decode : Code → Finset V → Bool)
    (factors : Factors G S O code decode) {u v : V}
    (inside : u ∈ S) (outside : v ∈ O) (crossing : G.Adj u v) :
    code {u} ≠ code ∅ := by
  have edge : HasEdge G ({u} ∪ {v}) := by
    simpa only [Finset.singleton_union] using (edge_pair G u v).mpr crossing
  have yes := (factors {u} (by simpa using inside) {v} (by simpa using outside)).mp edge
  intro same
  rw [same] at yes
  have single : HasEdge G {v} := by
    simpa using (factors ∅ (Finset.empty_subset S) {v} (by simpa using outside)).mpr yes
  exact no_edge_singleton G v single

lemma internal_code_ne_empty
    (G : SimpleGraph V) (S O : Finset V)
    (code : Finset V → Code) (decode : Code → Finset V → Bool)
    (factors : Factors G S O code decode) (internal : HasEdge G S) :
    code S ≠ code ∅ := by
  intro same
  have yes : decode (code S) ∅ = true :=
    (factors S Finset.Subset.rfl ∅ (Finset.empty_subset O)).mp (by simpa using internal)
  rw [same] at yes
  have empty : HasEdge G ∅ := by
    simpa using (factors ∅ (Finset.empty_subset S) ∅ (Finset.empty_subset O)).mpr yes
  exact no_edge_empty G empty

lemma internal_code_ne_singleton
    (G : SimpleGraph V) (S O : Finset V)
    (code : Finset V → Code) (decode : Code → Finset V → Bool)
    (factors : Factors G S O code decode) (internal : HasEdge G S)
    {u : V} (inside : u ∈ S) : code S ≠ code {u} := by
  intro same
  have yes : decode (code S) ∅ = true :=
    (factors S Finset.Subset.rfl ∅ (Finset.empty_subset O)).mp (by simpa using internal)
  rw [same] at yes
  have single : HasEdge G {u} := by
    simpa using (factors {u} (by simpa using inside) ∅ (Finset.empty_subset O)).mpr yes
  exact no_edge_singleton G u single

lemma representative_codes_injective
    (G : SimpleGraph V) (S O A : Finset V)
    (code : Finset V → Code) (decode : Code → Finset V → Bool)
    (factors : Factors G S O code decode) (subset : A ⊆ S)
    (different : ∀ u ∈ A, ∀ v ∈ A, u ≠ v →
      ∃ w ∈ O, ¬ (G.Adj u w ↔ G.Adj v w)) :
    Set.InjOn (fun u => code {u}) A := by
  intro u hu v hv same
  by_contra separate
  obtain ⟨w, hw, differs⟩ := different u hu v hv separate
  exact differs
    (equal_singleton_codes_same_neighbors G S O code decode factors (subset hu) (subset hv) same w hw)

lemma active_neighborhood_capacity [Fintype Code]
    (G : SimpleGraph V) (S O A : Finset V)
    (code : Finset V → Code) (decode : Code → Finset V → Bool)
    (factors : Factors G S O code decode) (subset : A ⊆ S)
    (active : ∀ u ∈ A, ∃ w ∈ O, G.Adj u w)
    (different : ∀ u ∈ A, ∀ v ∈ A, u ≠ v →
      ∃ w ∈ O, ¬ (G.Adj u w ↔ G.Adj v w)) :
    A.card + 1 ≤ Fintype.card Code := by
  classical
  let B := A.image fun u => code {u}
  have size : B.card = A.card :=
    Finset.card_image_iff.mpr (representative_codes_injective G S O A code decode factors subset different)
  have absent : code ∅ ∉ B := by
    intro mem
    obtain ⟨u, hu, equal⟩ := Finset.mem_image.mp mem
    obtain ⟨w, hw, edge⟩ := active u hu
    exact crossing_code_ne_empty G S O code decode factors (subset hu) hw edge equal
  have bound := Finset.card_le_univ (insert (code ∅) B)
  simpa [Finset.card_insert_of_notMem absent, size] using bound

lemma internal_edge_capacity [Fintype Code]
    (G : SimpleGraph V) (S O A : Finset V)
    (code : Finset V → Code) (decode : Code → Finset V → Bool)
    (factors : Factors G S O code decode) (subset : A ⊆ S)
    (active : ∀ u ∈ A, ∃ w ∈ O, G.Adj u w)
    (different : ∀ u ∈ A, ∀ v ∈ A, u ≠ v →
      ∃ w ∈ O, ¬ (G.Adj u w ↔ G.Adj v w))
    (internal : HasEdge G S) :
    A.card + 2 ≤ Fintype.card Code := by
  classical
  let B := A.image fun u => code {u}
  have size : B.card = A.card :=
    Finset.card_image_iff.mpr (representative_codes_injective G S O A code decode factors subset different)
  have absentEmpty : code ∅ ∉ B := by
    intro mem
    obtain ⟨u, hu, equal⟩ := Finset.mem_image.mp mem
    obtain ⟨w, hw, edge⟩ := active u hu
    exact crossing_code_ne_empty G S O code decode factors (subset hu) hw edge equal
  have absentInternal : code S ∉ insert (code ∅) B := by
    intro mem
    rcases Finset.mem_insert.mp mem with equal | mem
    · exact internal_code_ne_empty G S O code decode factors internal equal
    · obtain ⟨u, hu, equal⟩ := Finset.mem_image.mp mem
      exact internal_code_ne_singleton G S O code decode factors internal (subset hu) equal.symm
  have bound := Finset.card_le_univ (insert (code S) (insert (code ∅) B))
  simpa [Finset.card_insert_of_notMem absentInternal,
    Finset.card_insert_of_notMem absentEmpty, size, Nat.add_assoc] using bound

lemma two_bit_neighborhood_capacity
    (G : SimpleGraph V) (S O A : Finset V)
    (code : Finset V → Bool × Bool) (decode : Bool × Bool → Finset V → Bool)
    (factors : Factors G S O code decode) (subset : A ⊆ S)
    (active : ∀ u ∈ A, ∃ w ∈ O, G.Adj u w)
    (different : ∀ u ∈ A, ∀ v ∈ A, u ≠ v →
      ∃ w ∈ O, ¬ (G.Adj u w ↔ G.Adj v w)) : A.card ≤ 3 := by
  have bound := active_neighborhood_capacity G S O A code decode factors subset active different
  simp only [Fintype.card_prod, Fintype.card_bool] at bound
  omega

lemma two_bit_internal_edge_capacity
    (G : SimpleGraph V) (S O A : Finset V)
    (code : Finset V → Bool × Bool) (decode : Bool × Bool → Finset V → Bool)
    (factors : Factors G S O code decode) (subset : A ⊆ S)
    (active : ∀ u ∈ A, ∃ w ∈ O, G.Adj u w)
    (different : ∀ u ∈ A, ∀ v ∈ A, u ≠ v →
      ∃ w ∈ O, ¬ (G.Adj u w ↔ G.Adj v w))
    (internal : HasEdge G S) : A.card ≤ 2 := by
  have bound := internal_edge_capacity G S O A code decode factors subset active different internal
  simp only [Fintype.card_prod, Fintype.card_bool] at bound
  omega

end FiniteCut

namespace LiteralGridRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def rect₁ (a b c d : Bool) : Bool := (a || c) && (b || d)

def rect₂ (a b c d : Bool) : Bool := (a || d) && (b || c)

lemma grid_identity (a b c d : Bool) :
    (rect₁ a b c d && rect₂ a b c d) = ((a && b) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

def hit {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

def pair {n : ℕ} (u v : Fin n) (i : Fin n) : Bool := decide (i = u ∨ i = v)

lemma adjacent_of_pair {n : ℕ} (G : SimpleGraph (Fin n)) {u v p q : Fin n}
    (huv : G.Adj u v) (hpq : p ≠ q)
    (hp : pair u v p = true) (hq : pair u v q = true) : G.Adj p q := by
  have hp' : p = u ∨ p = v := of_decide_eq_true hp
  have hq' : q = u ∨ q = v := of_decide_eq_true hq
  rcases hp' with rfl|rfl <;> rcases hq' with rfl|rfl
  · exact (hpq rfl).elim
  · exact huv
  · exact huv.symm
  · exact (hpq rfl).elim

lemma hit_pair_iff {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    hit G (pair u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨p,q,hpq,hp,hq⟩
    have hp' : p = u ∨ p = v := of_decide_eq_true hp
    have hq' : q = u ∨ q = v := of_decide_eq_true hq
    rcases hp' with rfl|rfl <;> rcases hq' with rfl|rfl
    · exact (G.irrefl hpq).elim
    · exact hpq
    · exact hpq.symm
    · exact (G.irrefl hpq).elim
  · intro huv
    exact ⟨u,v,huv,by simp [pair],by simp [pair]⟩

lemma cross_exclusion {n : ℕ} (G : SimpleGraph (Fin n)) (a b c d : Fin n)
    (triangle : ∀ x y z, G.Adj x y → G.Adj y z → ¬ G.Adj z x)
    (square : ∀ w x y z, G.Adj w x → G.Adj x y → G.Adj y z → G.Adj z w →
      w = y ∨ x = z)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (G.Adj a c → ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d) ∧
    (G.Adj a d → ¬ G.Adj b c ∧ ¬ G.Adj b d) ∧
    (G.Adj b c → ¬ G.Adj b d) := by
  refine ⟨?_,?_,?_⟩
  · intro he
    refine ⟨?_,?_,?_⟩
    · intro hf
      exact triangle a c d he hcd hf.symm
    · intro hf
      exact triangle a b c hab hf he.symm
    · intro hf
      rcases square a b d c hab hf hcd.symm he.symm with h|h
      · exact had h
      · exact hbc h
  · intro he
    constructor
    · intro hf
      rcases square a b c d hab hf hcd he.symm with h|h
      · exact hac h
      · exact hbd h
    · intro hf
      exact triangle a b d hab hf he.symm
  · intro he hf
    exact triangle b c d he hcd hf.symm

lemma rectangles_have_negative_witnesses {n : ℕ} (G : SimpleGraph (Fin n))
    (a b c d : Fin n)
    (hcross : (G.Adj a c → ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d) ∧
      (G.Adj a d → ¬ G.Adj b c ∧ ¬ G.Adj b d) ∧
      (G.Adj b c → ¬ G.Adj b d)) :
    (∃ x : Fin n → Bool, ¬ hit G x ∧ rect₁ (x a) (x b) (x c) (x d) = true) ∧
    (∃ x : Fin n → Bool, ¬ hit G x ∧ rect₂ (x a) (x b) (x c) (x d) = true) := by
  classical
  constructor
  · by_cases had : G.Adj a d
    · refine ⟨pair b c,?_,by simp [rect₁,pair]⟩
      exact fun h => (hcross.2.1 had).1 ((hit_pair_iff G b c).mp h)
    · refine ⟨pair a d,?_,by simp [rect₁,pair]⟩
      exact fun h => had ((hit_pair_iff G a d).mp h)
  · by_cases hac : G.Adj a c
    · refine ⟨pair b d,?_,by simp [rect₂,pair]⟩
      exact fun h => (hcross.1 hac).2.2 ((hit_pair_iff G b d).mp h)
    · refine ⟨pair a c,?_,by simp [rect₂,pair]⟩
      exact fun h => hac ((hit_pair_iff G a c).mp h)

def firstValue {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n) (x : Fin n → Bool) : Bool :=
  if G.Adj a c then x a && (x b || x c)
  else if G.Adj a d then x a && (x b || x d)
  else if G.Adj b c then x b && (x a || x c)
  else if G.Adj b d then x b && (x a || x d)
  else x a && x b

def repairValue {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n) (x : Fin n → Bool) : Bool :=
  firstValue G a b c d x || (x c && x d)

def inducedValue {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n) (x : Fin n → Bool) : Bool :=
  (x a && x b) || (x c && x d) ||
    (decide (G.Adj a c) && (x a && x c)) ||
    (decide (G.Adj a d) && (x a && x d)) ||
    (decide (G.Adj b c) && (x b && x c)) ||
    (decide (G.Adj b d) && (x b && x d))

lemma repair_eq_induced {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n)
    (hcross : (G.Adj a c → ¬ G.Adj a d ∧ ¬ G.Adj b c ∧ ¬ G.Adj b d) ∧
      (G.Adj a d → ¬ G.Adj b c ∧ ¬ G.Adj b d) ∧
      (G.Adj b c → ¬ G.Adj b d)) (x : Fin n → Bool) :
    repairValue G a b c d x = inducedValue G a b c d x := by
  by_cases hac : G.Adj a c
  · obtain ⟨had,hbc,hbd⟩ := hcross.1 hac
    cases ha : x a <;> cases hb : x b <;> cases hc : x c <;> cases hd : x d <;>
      simp [repairValue,firstValue,inducedValue,hac,had,hbc,hbd,ha,hb,hc,hd]
  · by_cases had : G.Adj a d
    · obtain ⟨hbc,hbd⟩ := hcross.2.1 had
      cases ha : x a <;> cases hb : x b <;> cases hc : x c <;> cases hd : x d <;>
        simp [repairValue,firstValue,inducedValue,hac,had,hbc,hbd,ha,hb,hc,hd]
    · by_cases hbc : G.Adj b c
      · have hbd := hcross.2.2 hbc
        cases ha : x a <;> cases hb : x b <;> cases hc : x c <;> cases hd : x d <;>
          simp [repairValue,firstValue,inducedValue,hac,had,hbc,hbd,ha,hb,hc,hd]
      · by_cases hbd : G.Adj b d
        · cases ha : x a <;> cases hb : x b <;> cases hc : x c <;> cases hd : x d <;>
            simp [repairValue,firstValue,inducedValue,hac,had,hbc,hbd,ha,hb,hc,hd]
        · simp [repairValue,firstValue,inducedValue,hac,had,hbc,hbd]

lemma first_safe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n) (hab : G.Adj a b) (x : Fin n → Bool) :
    firstValue G a b c d x = true → hit G x := by
  unfold firstValue
  split_ifs with hac had hbc hbd
  · simp only [Bool.and_eq_true,Bool.or_eq_true]
    rintro ⟨ha,hb|hc⟩
    · exact ⟨a,b,hab,ha,hb⟩
    · exact ⟨a,c,hac,ha,hc⟩
  · simp only [Bool.and_eq_true,Bool.or_eq_true]
    rintro ⟨ha,hb|hd⟩
    · exact ⟨a,b,hab,ha,hb⟩
    · exact ⟨a,d,had,ha,hd⟩
  · simp only [Bool.and_eq_true,Bool.or_eq_true]
    rintro ⟨hb,ha|hc⟩
    · exact ⟨a,b,hab,ha,hb⟩
    · exact ⟨b,c,hbc,hb,hc⟩
  · simp only [Bool.and_eq_true,Bool.or_eq_true]
    rintro ⟨hb,ha|hd⟩
    · exact ⟨a,b,hab,ha,hb⟩
    · exact ⟨b,d,hbd,hb,hd⟩
  · simp only [Bool.and_eq_true]
    rintro ⟨ha,hb⟩
    exact ⟨a,b,hab,ha,hb⟩

lemma repair_safe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n) (hab : G.Adj a b) (hcd : G.Adj c d) (x : Fin n → Bool) :
    repairValue G a b c d x = true → hit G x := by
  simp only [repairValue,Bool.or_eq_true,Bool.and_eq_true]
  rintro (hf|⟨hc,hd⟩)
  · exact first_safe G a b c d hab x hf
  · exact ⟨c,d,hcd,hc,hd⟩

lemma repair_zero_on_negative {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n) (hab : G.Adj a b) (hcd : G.Adj c d) (x : Fin n → Bool)
    (hx : ¬ hit G x) : repairValue G a b c d x = false := by
  apply Bool.eq_false_iff.mpr
  exact fun h => hx (repair_safe G a b c d hab hcd x h)

lemma induced_dominates_rectangles {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (u v : Fin n) (huv : G.Adj u v) :
    (rect₁ (pair u v a) (pair u v b) (pair u v c) (pair u v d) = true →
      inducedValue G a b c d (pair u v) = true) ∧
    (rect₂ (pair u v a) (pair u v b) (pair u v c) (pair u v d) = true →
      inducedValue G a b c d (pair u v) = true) := by
  constructor
  · simp only [rect₁,Bool.and_eq_true,Bool.or_eq_true]
    rintro ⟨ha|hc,hb|hd⟩
    · simp [inducedValue,ha,hb]
    · have he := adjacent_of_pair G huv had ha hd
      simp [inducedValue,he,ha,hd]
    · have he := adjacent_of_pair G huv hbc hb hc
      simp [inducedValue,he,hb,hc]
    · simp [inducedValue,hc,hd]
  · simp only [rect₂,Bool.and_eq_true,Bool.or_eq_true]
    rintro ⟨ha|hd,hb|hc⟩
    · simp [inducedValue,ha,hb]
    · have he := adjacent_of_pair G huv hac ha hc
      simp [inducedValue,he,ha,hc]
    · have he := adjacent_of_pair G huv hbd hb hd
      simp [inducedValue,he,hb,hd]
    · simp [inducedValue,hc,hd]

def borrowedInputs {n : ℕ} (a b c d : Fin n) (x : Fin n → Bool) : List Bool :=
  [x a,x b,x c,x d,x a || x c,x b || x d,x a || x d,x b || x c]

def firstGate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n) : Gate :=
  if G.Adj a c then ⟨.and,[0,7]⟩
  else if G.Adj a d then ⟨.and,[0,5]⟩
  else if G.Adj b c then ⟨.and,[1,4]⟩
  else if G.Adj b d then ⟨.and,[1,6]⟩
  else ⟨.and,[0,1]⟩

def block {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n) : Circuit :=
  ⟨[firstGate G a b c d,⟨.and,[2,3]⟩,⟨.or,[8,9]⟩],10⟩

lemma block_size {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n) : (block G a b c d).size = 3 := rfl

lemma block_mono {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n) : Monotone2 (block G a b c d) := by
  unfold block firstGate
  split_ifs <;> simp [Monotone2]

lemma block_values {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n) (x : Fin n → Bool) :
    ((block G a b c d).wires (borrowedInputs a b c d x)).getD 8 false =
        firstValue G a b c d x ∧
    ((block G a b c d).wires (borrowedInputs a b c d x)).getD 9 false = (x c && x d) ∧
    (block G a b c d).eval (borrowedInputs a b c d x) = repairValue G a b c d x := by
  unfold block firstGate firstValue repairValue
  split_ifs <;>
    simp_all [firstValue,Circuit.wires,Circuit.eval,borrowedInputs,GateOp.eval,
      List.getD_eq_getElem?_getD]

lemma block_safe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n) (hab : G.Adj a b) (hcd : G.Adj c d) :
    ∀ j g, (block G a b c d).gates[j]? = some g → g.op = .and →
      ∀ x : Fin n → Bool,
        ((block G a b c d).wires (borrowedInputs a b c d x)).getD (8+j) false = true → hit G x := by
  intro j g hj hop x hx
  have bound : j < 3 := by
    obtain ⟨hh,_⟩ := List.getElem?_eq_some_iff.mp hj
    simpa [block] using hh
  interval_cases j
  · change ((block G a b c d).wires (borrowedInputs a b c d x)).getD 8 false = true at hx
    rw [(block_values G a b c d x).1] at hx
    exact first_safe G a b c d hab x hx
  · change ((block G a b c d).wires (borrowedInputs a b c d x)).getD 9 false = true at hx
    rw [(block_values G a b c d x).2.1] at hx
    obtain ⟨hc,hd⟩ := Bool.and_eq_true_iff.mp hx
    exact ⟨c,d,hcd,hc,hd⟩
  · have he : g = ⟨.or,[8,9]⟩ := by simpa [block] using hj.symm
    simp [he] at hop

lemma signed_grid_certificate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b c d : Fin n)
    (triangle : ∀ x y z, G.Adj x y → G.Adj y z → ¬ G.Adj z x)
    (square : ∀ w x y z, G.Adj w x → G.Adj x y → G.Adj y z → G.Adj z w →
      w = y ∨ x = z)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (block G a b c d).size = 3 ∧ Monotone2 (block G a b c d) ∧
    (∀ x : Fin n → Bool, ¬ hit G x →
      (block G a b c d).eval (borrowedInputs a b c d x) = false) ∧
    (∀ u v : Fin n, G.Adj u v →
      (rect₁ (pair u v a) (pair u v b) (pair u v c) (pair u v d) = true ∨
       rect₂ (pair u v a) (pair u v b) (pair u v c) (pair u v d) = true) →
        (block G a b c d).eval (borrowedInputs a b c d (pair u v)) = true) ∧
    (∀ j g, (block G a b c d).gates[j]? = some g → g.op = .and →
      ∀ x : Fin n → Bool,
        ((block G a b c d).wires (borrowedInputs a b c d x)).getD (8+j) false = true → hit G x) := by
  refine ⟨block_size G a b c d,block_mono G a b c d,?_,?_,block_safe G a b c d hab hcd⟩
  · intro x hx
    rw [(block_values G a b c d x).2.2]
    exact repair_zero_on_negative G a b c d hab hcd x hx
  · intro u v huv hrect
    rw [(block_values G a b c d (pair u v)).2.2,
      repair_eq_induced G a b c d
        (cross_exclusion G a b c d triangle square hab hcd hac had hbc hbd)]
    exact hrect.elim
      (induced_dominates_rectangles G a b c d hac had hbc hbd u v huv).1
      (induced_dominates_rectangles G a b c d hac had hbc hbd u v huv).2

end LiteralGridRepair

end PEqualNP.Outside.L_meta_1904
