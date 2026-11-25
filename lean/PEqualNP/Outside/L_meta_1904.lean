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

end PEqualNP.Outside.L_meta_1904
