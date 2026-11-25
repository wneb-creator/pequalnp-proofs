import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1904_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (Fin 11 × Fin 11) :=
  [(0,4),(0,6),(1,5),(1,6),(1,7),(2,6),(3,7),(4,7),
    (8,2),(8,7),(9,2),(9,4),(8,10)]

def adjacent (u v : Fin 11) : Bool :=
  edges.contains (u,v) || edges.contains (v,u)

abbrev graph : SimpleGraph (Fin 11) where
  Adj u v := adjacent u v = true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

def witness : Circuit :=
  ⟨[⟨.or,[4,6]⟩,⟨.or,[6,7]⟩,⟨.or,[2,4]⟩,⟨.or,[2,7]⟩,
    ⟨.and,[13,12]⟩,⟨.and,[15,14]⟩,⟨.or,[0,16]⟩,⟨.and,[17,11]⟩,
    ⟨.and,[3,7]⟩,⟨.or,[1,19]⟩,⟨.or,[5,12]⟩,⟨.and,[20,21]⟩,
    ⟨.or,[18,22]⟩,⟨.or,[14,10]⟩,⟨.and,[8,24]⟩,⟨.and,[9,13]⟩,
    ⟨.or,[23,25]⟩,⟨.or,[27,26]⟩],28⟩

def bitsAdj (u v : Fin 11) : Bool :=
  (0x4000a48423401c01281100d0070050 : Nat).testBit (11*u.val+v.val)

set_option maxHeartbeats 0 in
lemma adjBits : ∀ u v : Fin 11, adjacent u v = true ↔ bitsAdj u v = true := by
  decide +kernel

set_option maxHeartbeats 0 in
lemma noTriangle : ∀ (a b c : Fin 11),
    graph.Adj a b → graph.Adj b c → ¬ graph.Adj c a := by
  have fast : ∀ a b c : Fin 11,
      bitsAdj a b = true → bitsAdj b c = true → ¬ bitsAdj c a = true := by
    decide +kernel
  simpa only [adjBits] using fast

set_option maxHeartbeats 0 in
lemma noFour : PEqualNP.TopForm.NoFourCycle graph := by
  have fast : ∀ a b : Fin 11, a ≠ b →
      (Finset.univ.filter fun w => bitsAdj a w = true ∧ bitsAdj b w = true).card ≤ 1 := by
    decide +kernel
  intro a b ne
  have eq : (Finset.univ.filter fun w => graph.Adj a w ∧ graph.Adj b w) =
      (Finset.univ.filter fun w => bitsAdj a w = true ∧ bitsAdj b w = true) := by
    ext w
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,adjBits]
  rw [eq]
  exact fast a b ne

lemma mono : Monotone2 witness := by
  intro g belongs
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at belongs
  rcases belongs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp

lemma size_eq : witness.size = 18 := rfl

def nOr (C : Circuit) : Nat :=
  (C.gates.filter fun g => match g.op with | .or => true | _ => false).length

lemma or_eq : nOr witness = 11 := rfl

set_option maxHeartbeats 0 in
lemma edgeCard : graph.edgeFinset.card = 13 := by decide +kernel

lemma badIndex : 4 < witness.gates.length := by decide

lemma badOp : (NestedCover.gateAt witness 4).op = GateOp.and := rfl

lemma badInput :
    PEqualNP.EdgeOwnership.gateVal 11 witness 4
      (PEqualNP.EdgeOwnership.pairInput 2 7) = true := by
  decide +kernel

lemma noEdge : ¬ graph.Adj 2 7 := by decide +kernel

lemma graph_any (x : Fin 11 → Bool) :
    NestedCover.graphFun graph ∅ x = edges.any (fun uv => x uv.1 && x uv.2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [NestedCover.graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
    Bool.false_or,decide_eq_true_eq,List.any_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨u,v,h,hu,hv⟩
    change adjacent u v = true at h
    rcases Bool.or_eq_true_iff.mp h with direct|back
    · exact ⟨(u,v),List.contains_iff_mem.mp direct,hu,hv⟩
    · exact ⟨(v,u),List.contains_iff_mem.mp back,hv,hu⟩
  · rintro ⟨⟨u,v⟩,mem,hu,hv⟩
    refine ⟨u,v,?_,hu,hv⟩
    change ((edges.contains (u,v)) || edges.contains (v,u)) = true
    exact Bool.or_eq_true_iff.mpr (Or.inl (List.contains_iff_mem.mpr mem))

def eFormula (a b c d e f g h i j k : Bool) :=
  a && e || a && g || b && f || b && g || b && h || c && g || d && h || e && h ||
    i && c || i && h || j && c || j && e || i && k

def wFormula (a b c d e f g h i j k : Bool) :=
  (((a || (((c || e) && (g || h)) && (c || h))) && (e || g)) ||
    ((b || (d && h)) && (f || (g || h)))) ||
    (i && ((c || h) || k)) || (j && (c || e))

set_option maxHeartbeats 0 in
lemma circuits_agree : ∀ a b c d e f g h i j k : Bool,
    wFormula a b c d e f g h i j k = eFormula a b c d e f g h i j k := by
  decide +kernel

lemma eval_formula (a b c d e f g h i j k : Bool) :
    witness.eval [a,b,c,d,e,f,g,h,i,j,k] = wFormula a b c d e f g h i j k := by
  simp [witness,Circuit.eval,Circuit.wires,GateOp.eval,List.getD_eq_getElem?_getD,wFormula]

lemma outcome_formula (x : Fin 11 → Bool) :
    edges.any (fun uv => x uv.1 && x uv.2) =
      eFormula (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) := by
  simp [edges,eFormula,Bool.or_assoc]

lemma computes : circuitFun 11 witness = NestedCover.graphFun graph ∅ := by
  funext x
  rw [graph_any,outcome_formula]
  have entries : List.ofFn x =
      [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10] := rfl
  change witness.eval (List.ofFn x) = _
  rw [entries,eval_formula,circuits_agree]

lemma or_bound_fails : ¬ graph.edgeFinset.card - 1 ≤ nOr witness := by
  rw [edgeCard,or_eq]
  decide

lemma noFour_raw : ∀ a b c d : Fin 11,
    graph.Adj a b → graph.Adj b c → graph.Adj c d → graph.Adj d a →
      a = c ∨ b = d := by
  intro a b c d hab hbc hcd hda
  by_cases same : a = c
  · exact Or.inl same
  · right
    exact (Finset.card_le_one.mp (noFour a c same)) b
      (by simp only [Finset.mem_filter,Finset.mem_univ,true_and]
          exact ⟨hab,graph.adj_symm hbc⟩) d
      (by simp only [Finset.mem_filter,Finset.mem_univ,true_and]
          exact ⟨graph.adj_symm hda,hcd⟩)

def zeroedDirty : Circuit :=
  { witness with gates := witness.gates.set 4 ⟨.or,[]⟩ }

lemma zeroed_loses_edges :
    graph.Adj 2 6 ∧ graph.Adj 4 7 ∧
    zeroedDirty.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (n := 11) 2 6)) = false ∧
    zeroedDirty.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (n := 11) 4 7)) = false := by
  decide +kernel

lemma dirty_support_output_false :
    witness.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (n := 11) 2 7)) = false := by
  decide +kernel

lemma refutes_or_lower_bound :
    ¬ (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
        a = c ∨ b = d) →
      ∀ C : Circuit, Monotone2 C →
        circuitFun n C = NestedCover.graphFun G ∅ → G.edgeFinset.card - 1 ≤ nOr C) := by
  intro claimed
  exact or_bound_fails (claimed 11 graph noTriangle noFour_raw witness mono computes)

end PEqualNP.Outside.L_meta_1904_aux
