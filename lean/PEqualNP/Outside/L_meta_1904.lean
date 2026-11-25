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


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def safeWitness : Circuit :=
  ⟨[⟨.or,[4,6]⟩,⟨.or,[6,7]⟩,⟨.or,[2,4]⟩,⟨.or,[2,7]⟩,
    ⟨.and,[0,11]⟩,⟨.and,[2,6]⟩,⟨.or,[3,4]⟩,⟨.and,[7,17]⟩,
    ⟨.or,[5,12]⟩,⟨.and,[1,19]⟩,⟨.or,[14,10]⟩,⟨.and,[8,21]⟩,
    ⟨.and,[9,13]⟩,⟨.or,[15,16]⟩,⟨.or,[24,18]⟩,⟨.or,[25,20]⟩,
    ⟨.or,[26,22]⟩,⟨.or,[27,23]⟩],28⟩

lemma safeSize : safeWitness.size = 18 := rfl

lemma safeOr : nOr safeWitness = 12 := rfl

lemma safeAnd :
    (safeWitness.gates.filter fun g => match g.op with | .and => true | _ => false).length = 6 := rfl

lemma safeSameSize : safeWitness.size = witness.size := rfl

lemma safeMono : Monotone2 safeWitness := by
  intro g belongs
  simp only [safeWitness, List.mem_cons, List.not_mem_nil, or_false] at belongs
  rcases belongs with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp

def safeFormula (a b c d e f g h i j k : Bool) :=
  (a && (e || g) || c && g || h && (d || e) || b && (f || (g || h)) ||
    i && ((c || h) || k) || j && (c || e))

set_option maxHeartbeats 0 in
lemma safeFormula_agrees : ∀ a b c d e f g h i j k : Bool,
    safeFormula a b c d e f g h i j k = eFormula a b c d e f g h i j k := by
  decide +kernel

lemma safe_eval_formula (a b c d e f g h i j k : Bool) :
    safeWitness.eval [a,b,c,d,e,f,g,h,i,j,k] = safeFormula a b c d e f g h i j k := by
  simp [safeWitness,Circuit.eval,Circuit.wires,GateOp.eval,List.getD_eq_getElem?_getD,
    safeFormula]

lemma safeComputes : circuitFun 11 safeWitness = NestedCover.graphFun graph ∅ := by
  funext x
  rw [graph_any,outcome_formula]
  have entries : List.ofFn x =
      [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10] := rfl
  change safeWitness.eval (List.ofFn x) = _
  rw [entries,safe_eval_formula,safeFormula_agrees]

lemma edge_exists_of_formula (x : Fin 11 → Bool)
    (h : eFormula (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9) (x 10) = true) :
    ∃ u v : Fin 11, graph.Adj u v ∧ x u = true ∧ x v = true := by
  have out : NestedCover.graphFun graph ∅ x = true := by
    rw [graph_any,outcome_formula]
    exact h
  simpa only [NestedCover.graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
    Bool.false_or,decide_eq_true_eq] using out

set_option maxHeartbeats 0 in
lemma safeAndSafety : ∀ (j : ℕ) (g : Gate),
    safeWitness.gates[j]? = some g → g.op = GateOp.and →
    ∀ (x : Fin 11 → Bool),
      (safeWitness.wires (List.ofFn x)).getD (11 + j) false = true →
      ∃ u v : Fin 11, graph.Adj u v ∧ x u = true ∧ x v = true := by
  intro j g seen isAnd x on
  have entries : List.ofFn x =
      [x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 7,x 8,x 9,x 10] := rfl
  rw [entries] at on
  obtain ⟨lt,hval⟩ := List.getElem?_eq_some_iff.mp seen
  clear hval
  change j < 18 at lt
  interval_cases j <;> simp [safeWitness] at seen <;> subst g <;> cases isAnd
  all_goals
    simp [safeWitness,Circuit.wires,GateOp.eval,List.getD_eq_getElem?_getD] at on
    try simp only [or_assoc] at on
  · rcases on with ⟨ha,he|hg⟩
    · exact ⟨0,4,by decide +kernel,ha,he⟩
    · exact ⟨0,6,by decide +kernel,ha,hg⟩
  · rcases on with ⟨hc,hg⟩
    exact ⟨2,6,by decide +kernel,hc,hg⟩
  · rcases on with ⟨hh,hd|he⟩
    · exact ⟨7,3,by decide +kernel,hh,hd⟩
    · exact ⟨7,4,by decide +kernel,hh,he⟩
  · rcases on with ⟨hb,hf|hg|hh⟩
    · exact ⟨1,5,by decide +kernel,hb,hf⟩
    · exact ⟨1,6,by decide +kernel,hb,hg⟩
    · exact ⟨1,7,by decide +kernel,hb,hh⟩
  · rcases on with ⟨hi,hc|hh|hk⟩
    · exact ⟨8,2,by decide +kernel,hi,hc⟩
    · exact ⟨8,7,by decide +kernel,hi,hh⟩
    · exact ⟨8,10,by decide +kernel,hi,hk⟩
  · rcases on with ⟨hj,hc|he⟩
    · exact ⟨9,2,by decide +kernel,hj,hc⟩
    · exact ⟨9,4,by decide +kernel,hj,he⟩

lemma local_five_input_cleanup : ∀ a c e g h : Bool,
    ((e || g) && (a || (((c || e) && (g || h)) && (c || h)))) =
      ((g && (a || c)) || (e && (a || h))) := by
  decide +kernel

namespace Amplification

def amplifierAdj {n s : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin s → Fin n) :
    (Fin n ⊕ (Fin s ⊕ Fin s)) → (Fin n ⊕ (Fin s ⊕ Fin s)) → Prop
  | .inl a, .inl b => G.Adj a b
  | .inl a, .inr (.inl i) => a = u i ∨ a = v i
  | .inr (.inl i), .inl a => a = u i ∨ a = v i
  | .inr (.inl i), .inr (.inr j) => i = j
  | .inr (.inr j), .inr (.inl i) => i = j
  | _, _ => False

def amplifierGraph {n s : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin s → Fin n) :
    SimpleGraph (Fin n ⊕ (Fin s ⊕ Fin s)) where
  Adj := amplifierAdj G u v
  symm := by
    constructor
    intro a b h
    rcases a with a | a | a <;> rcases b with b | b | b <;>
      simp only [amplifierAdj] at h ⊢
    · exact h.symm
    all_goals assumption
  loopless := by
    constructor
    intro a
    rcases a with a | a | a <;> simp [amplifierAdj]

def amplifierBaseEmb {n s : ℕ} : Fin n ↪ (Fin n ⊕ (Fin s ⊕ Fin s)) :=
  ⟨Sum.inl, Sum.inl_injective⟩

def amplifierCenterEmb {n s : ℕ} : Fin s ↪ (Fin n ⊕ (Fin s ⊕ Fin s)) :=
  ⟨fun i => Sum.inr (Sum.inl i), by intro i j h; simpa using h⟩

def amplifierLiftCover {n s : ℕ} (T : Finset (Fin n)) :
    Finset (Fin n ⊕ (Fin s ⊕ Fin s)) :=
  T.map amplifierBaseEmb ∪ Finset.univ.map amplifierCenterEmb

lemma amplifierLiftCover_card {n s : ℕ} (T : Finset (Fin n)) :
    (amplifierLiftCover (s := s) T).card = T.card + s := by
  unfold amplifierLiftCover
  rw [Finset.card_union_of_disjoint]
  · simp
  · rw [Finset.disjoint_left]
    intro x hx hy
    rcases Finset.mem_map.mp hx with ⟨a, _, rfl⟩
    rcases Finset.mem_map.mp hy with ⟨i, _, hi⟩
    cases hi

lemma amplifierLiftCover_covers {n s : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin s → Fin n) (T : Finset (Fin n)) (hT : G.IsVertexCover (T : Set (Fin n))) :
    (amplifierGraph G u v).IsVertexCover (amplifierLiftCover (s := s) T : Set _) := by
  intro a b hab
  rcases a with a | a | a <;> rcases b with b | b | b <;>
    simp only [amplifierGraph, amplifierAdj] at hab
  · rcases hT hab with ha | hb
    · left
      exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
    · right
      exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨b, hb, rfl⟩)
  · right
    exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨b, Finset.mem_univ _, rfl⟩)
  · left
    exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨a, Finset.mem_univ _, rfl⟩)
  · left
    exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨a, Finset.mem_univ _, rfl⟩)
  · right
    exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨b, Finset.mem_univ _, rfl⟩)

lemma amplifier_cover_lower {n s : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin s → Fin n) (t : ℕ)
    (hmin : ∀ T : Finset (Fin n), G.IsVertexCover (T : Set _) → t ≤ T.card)
    (S : Finset (Fin n ⊕ (Fin s ⊕ Fin s)))
    (hS : (amplifierGraph G u v).IsVertexCover (S : Set _)) :
    t + s ≤ S.card := by
  classical
  let T : Finset (Fin n) := Finset.univ.filter fun a => Sum.inl a ∈ S
  have hT : G.IsVertexCover (T : Set _) := by
    intro a b hab
    rcases hS (show (amplifierGraph G u v).Adj (Sum.inl a) (Sum.inl b) from hab) with ha | hb
    · left; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
    · right; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩
  let pick : Fin s → (Fin n ⊕ (Fin s ⊕ Fin s)) := fun i =>
    if Sum.inr (Sum.inl i) ∈ S then Sum.inr (Sum.inl i) else Sum.inr (Sum.inr i)
  have hpick (i : Fin s) : pick i ∈ S := by
    dsimp only [pick]
    split
    · assumption
    · rename_i h
      rcases hS (show (amplifierGraph G u v).Adj
        (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr i)) from rfl) with hi | hi
      · exact (h hi).elim
      · exact hi
  have hinj : Function.Injective pick := by
    intro i j h
    dsimp only [pick] at h
    split_ifs at h <;> simpa using h
  let B := T.map (amplifierBaseEmb (s := s))
  let P := Finset.univ.image pick
  have hB : B ⊆ S := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
    exact (Finset.mem_filter.mp ha).2
  have hP : P ⊆ S := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    exact hpick i
  have hd : Disjoint B P := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rcases Finset.mem_map.mp hx with ⟨a, _, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨i, _, hi⟩
    dsimp only [pick, amplifierBaseEmb, Function.Embedding.coeFn_mk] at hi
    split_ifs at hi <;> cases hi
  have hcount : T.card + s ≤ S.card := by
    have := Finset.card_le_card (Finset.union_subset hB hP)
    rw [Finset.card_union_of_disjoint hd] at this
    simpa [B, P, Finset.card_image_of_injective _ hinj] using this
  exact Nat.add_le_add_right (hmin T hT) s |>.trans hcount

lemma amplifier_min_cover {n s : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin s → Fin n) (T : Finset (Fin n))
    (hT : G.IsVertexCover (T : Set _))
    (hmin : ∀ U : Finset (Fin n), G.IsVertexCover (U : Set _) → T.card ≤ U.card) :
    (amplifierGraph G u v).IsVertexCover (amplifierLiftCover (s := s) T : Set _) ∧
    (amplifierLiftCover (s := s) T).card = T.card + s ∧
    ∀ S : Finset (Fin n ⊕ (Fin s ⊕ Fin s)),
      (amplifierGraph G u v).IsVertexCover (S : Set _) → T.card + s ≤ S.card := by
  exact ⟨amplifierLiftCover_covers G u v T hT, amplifierLiftCover_card T,
    amplifier_cover_lower G u v T.card hmin⟩

lemma amplifier_pair_nonadj {n s : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin s → Fin n) (hnon : ∀ i, ¬G.Adj (u i) (v i))
    (i : Fin s) (a b : Fin n) (ha : a = u i ∨ a = v i) (hb : b = u i ∨ b = v i) :
    ¬G.Adj a b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact G.irrefl
  · exact hnon i
  · exact fun h => hnon i h.symm
  · exact G.irrefl

lemma amplifier_no_triangle {n s : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin s → Fin n)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬G.Adj c a)
    (hnon : ∀ i, ¬G.Adj (u i) (v i)) :
    ∀ a b c, (amplifierGraph G u v).Adj a b →
      (amplifierGraph G u v).Adj b c → ¬(amplifierGraph G u v).Adj c a := by
  intro a b c hab hbc hca
  rcases a with a | a | a <;> rcases b with b | b | b <;>
    rcases c with c | c | c <;> simp only [amplifierGraph, amplifierAdj] at hab hbc hca
  all_goals try contradiction
  · exact htri a b c hab hbc hca
  · exact amplifier_pair_nonadj G u v hnon c a b hca hbc hab
  · exact amplifier_pair_nonadj G u v hnon b c a hbc hab hca
  · exact amplifier_pair_nonadj G u v hnon a b c hab hca hbc

lemma amplifier_pair_common_unique {n s : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin s → Fin n)
    (hcommon : ∀ i w, ¬(G.Adj (u i) w ∧ G.Adj (v i) w))
    (i : Fin s) (w a b : Fin n)
    (ha : a = u i ∨ a = v i) (hb : b = u i ∨ b = v i)
    (hwa : G.Adj w a) (hwb : G.Adj w b) : a = b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · exact (hcommon i w ⟨hwa.symm, hwb.symm⟩).elim
  · exact (hcommon i w ⟨hwb.symm, hwa.symm⟩).elim
  · rfl

lemma amplifier_pair_intersection {n s : ℕ} (u v : Fin s → Fin n)
    (hpairs : ∀ i j, (u i = u j ∧ v i = v j) ∨ (u i = v j ∧ v i = u j) → i = j)
    (i j : Fin s) (a b : Fin n)
    (hai : a = u i ∨ a = v i) (hbi : b = u i ∨ b = v i)
    (haj : a = u j ∨ a = v j) (hbj : b = u j ∨ b = v j) : i = j ∨ a = b := by
  by_cases hab : a = b
  · exact Or.inr hab
  left
  apply hpairs i j
  have order (x y : Fin n) (ha : a = x ∨ a = y) (hb : b = x ∨ b = y) :
      (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact (hab (ha.trans hb.symm)).elim
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hb⟩
    · exact (hab (ha.trans hb.symm)).elim
  rcases order (u i) (v i) hai hbi with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases order (u j) (v j) haj hbj with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · exact Or.inl ⟨ha.symm.trans hc, hb.symm.trans hd⟩
  · exact Or.inr ⟨ha.symm.trans hc, hb.symm.trans hd⟩
  · exact Or.inr ⟨hb.symm.trans hd, ha.symm.trans hc⟩
  · exact Or.inl ⟨hb.symm.trans hd, ha.symm.trans hc⟩

lemma amplifier_no_four_cycle {n s : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin s → Fin n)
    (hfour : ∀ a b c d, G.Adj a c → G.Adj b c → G.Adj a d → G.Adj b d → a = b ∨ c = d)
    (hcommon : ∀ i w, ¬(G.Adj (u i) w ∧ G.Adj (v i) w))
    (hpairs : ∀ i j, (u i = u j ∧ v i = v j) ∨ (u i = v j ∧ v i = u j) → i = j) :
    ∀ a b c d, (amplifierGraph G u v).Adj a c →
      (amplifierGraph G u v).Adj b c → (amplifierGraph G u v).Adj a d →
      (amplifierGraph G u v).Adj b d → a = b ∨ c = d := by
  intro a b c d hac hbc had hbd
  rcases a with a | a | a <;> rcases b with b | b | b <;>
    rcases c with c | c | c <;> rcases d with d | d | d <;>
    simp only [amplifierGraph, amplifierAdj] at hac hbc had hbd
  all_goals try contradiction
  all_goals simp only [Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
    Sum.inr_ne_inl, false_or]
  · exact hfour a b c d hac hbc had hbd
  · exact Or.inl (amplifier_pair_common_unique G u v hcommon d c a b had hbd hac.symm hbc.symm)
  · exact Or.inl (amplifier_pair_common_unique G u v hcommon c d a b hac hbc had.symm hbd.symm)
  · exact (amplifier_pair_intersection u v hpairs c d a b hac hbc had hbd).symm
  · exact amplifier_pair_common_unique G u v hcommon b a c d hbc hbd hac had
  · exact hbc.trans hbd.symm
  · exact amplifier_pair_common_unique G u v hcommon a b c d hac had hbc hbd
  · exact amplifier_pair_intersection u v hpairs a b c d hac had hbc hbd
  · exact Or.inl (had.trans hbd.symm)
  · exact Or.inl (hac.trans hbc.symm)
  · exact Or.inl (hac.trans hbc.symm)
  · exact hac.trans had.symm
  · exact Or.inl (hac.symm.trans hbc)


def amplifierEdgeCode {n s : ℕ} (u v : Fin s → Fin n) :
    Sym2 (Fin n) ⊕ (Fin s ⊕ (Fin s ⊕ Fin s)) → Sym2 (Fin n ⊕ (Fin s ⊕ Fin s))
  | .inl e => e.map Sum.inl
  | .inr (.inl i) => s(Sum.inl (u i), Sum.inr (Sum.inl i))
  | .inr (.inr (.inl i)) => s(Sum.inl (v i), Sum.inr (Sum.inl i))
  | .inr (.inr (.inr i)) => s(Sum.inr (Sum.inl i), Sum.inr (Sum.inr i))

lemma amplifierEdgeCode_injective {n s : ℕ} (u v : Fin s → Fin n)
    (hne : ∀ i, u i ≠ v i) : Function.Injective (amplifierEdgeCode u v) := by
  intro e f h
  rcases e with e | i | i | i <;> rcases f with f | j | j | j
  · exact congrArg Sum.inl ((Sym2.map.injective Sum.inl_injective) h)
  · induction e using Sym2.ind with
    | _ a b => simp [amplifierEdgeCode, Sym2.eq_iff] at h
  · induction e using Sym2.ind with
    | _ a b => simp [amplifierEdgeCode, Sym2.eq_iff] at h
  · induction e using Sym2.ind with
    | _ a b => simp [amplifierEdgeCode, Sym2.eq_iff] at h
  · induction f using Sym2.ind with
    | _ a b => simp [amplifierEdgeCode, Sym2.eq_iff] at h
  · have hij : i = j := by
      rcases Sym2.eq_iff.mp h with ⟨_, hij⟩ | ⟨hbad, _⟩
      · simpa using hij
      · cases hbad
    subst j
    rfl
  · have he : u i = v j ∧ i = j := by
      simpa [amplifierEdgeCode, Sym2.eq_iff] using h
    obtain ⟨he, rfl⟩ := he
    exact (hne i he).elim
  · simp [amplifierEdgeCode, Sym2.eq_iff] at h
  · induction f using Sym2.ind with
    | _ a b => simp [amplifierEdgeCode, Sym2.eq_iff] at h
  · have he : v i = u j ∧ i = j := by
      simpa [amplifierEdgeCode, Sym2.eq_iff] using h
    obtain ⟨he, rfl⟩ := he
    exact (hne i he.symm).elim
  · have hij : i = j := by
      rcases Sym2.eq_iff.mp h with ⟨_, hij⟩ | ⟨hbad, _⟩
      · simpa using hij
      · cases hbad
    subst j
    rfl
  · simp [amplifierEdgeCode, Sym2.eq_iff] at h
  · induction f using Sym2.ind with
    | _ a b => simp [amplifierEdgeCode, Sym2.eq_iff] at h
  · simp [amplifierEdgeCode, Sym2.eq_iff] at h
  · simp [amplifierEdgeCode, Sym2.eq_iff] at h
  · have hij : i = j := by
      rcases Sym2.eq_iff.mp h with ⟨hij, _⟩ | ⟨hbad, _⟩
      · simpa using hij
      · cases hbad
    subst j
    rfl

lemma amplifier_edgeFinset {n s : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin s → Fin n) [DecidableRel G.Adj]
    [DecidableRel (amplifierGraph G u v).Adj] :
    (amplifierGraph G u v).edgeFinset =
      (G.edgeFinset.disjSum (Finset.univ : Finset (Fin s ⊕ (Fin s ⊕ Fin s)))).image
        (amplifierEdgeCode u v) := by
  classical
  ext e
  constructor
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      have he := SimpleGraph.mem_edgeFinset.mp he
      change amplifierAdj G u v a b at he
      rcases a with a | i | i <;> rcases b with b | j | j <;>
        simp only [amplifierAdj] at he
      · exact Finset.mem_image.mpr ⟨Sum.inl s(a, b), by simpa using he, rfl⟩
      · rcases he with rfl | rfl
        · exact Finset.mem_image.mpr ⟨Sum.inr (Sum.inl j), by simp, rfl⟩
        · exact Finset.mem_image.mpr ⟨Sum.inr (Sum.inr (Sum.inl j)), by simp, rfl⟩
      · rcases he with rfl | rfl
        · exact Finset.mem_image.mpr ⟨Sum.inr (Sum.inl i), by simp, Sym2.eq_swap⟩
        · exact Finset.mem_image.mpr ⟨Sum.inr (Sum.inr (Sum.inl i)), by simp, Sym2.eq_swap⟩
      · subst j
        exact Finset.mem_image.mpr ⟨Sum.inr (Sum.inr (Sum.inr i)), by simp, rfl⟩
      · subst j
        exact Finset.mem_image.mpr ⟨Sum.inr (Sum.inr (Sum.inr i)), by simp, Sym2.eq_swap⟩
  · rintro himage
    rcases Finset.mem_image.mp himage with ⟨e, hsource, rfl⟩
    rcases e with e | i | i | i
    · have he' : e ∈ G.edgeFinset := Finset.inl_mem_disjSum.mp hsource
      induction e using Sym2.ind with
      | _ a b =>
        apply SimpleGraph.mem_edgeFinset.mpr
        change G.Adj a b
        exact SimpleGraph.mem_edgeFinset.mp he'
    · apply SimpleGraph.mem_edgeFinset.mpr
      change u i = u i ∨ u i = v i
      exact Or.inl rfl
    · apply SimpleGraph.mem_edgeFinset.mpr
      change v i = u i ∨ v i = v i
      exact Or.inr rfl
    · apply SimpleGraph.mem_edgeFinset.mpr
      change i = i
      rfl

lemma amplifier_edge_card {n s : ℕ} (G : SimpleGraph (Fin n))
    (u v : Fin s → Fin n) [DecidableRel G.Adj]
    [DecidableRel (amplifierGraph G u v).Adj] (hne : ∀ i, u i ≠ v i) :
    (amplifierGraph G u v).edgeFinset.card = G.edgeFinset.card + 3 * s := by
  rw [amplifier_edgeFinset, Finset.card_image_of_injective _ (amplifierEdgeCode_injective u v hne)]
  simp only [Finset.card_disjSum, Finset.card_univ, Fintype.card_sum, Fintype.card_fin]
  omega

end Amplification

namespace UniqueClause

def hit {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true

def clause {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ a ∈ S, x a = true

lemma singleton_of_unique_used_clause {n : ℕ} {I : Type} [DecidableEq I]
    (G : SimpleGraph (Fin n)) (B : I → Finset (Fin n)) (U : Finset I)
    (q : I) (v : Fin n) (hv : v ∈ B q)
    (hne : ∃ w, G.Adj v w)
    (hunique : ∀ i ∈ U, v ∈ B i → i = q)
    (hpacking : ∀ a ∈ B q, ∀ b ∈ B q, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    (hmono : ∀ x y : Fin n → Bool,
      (∀ i ∈ U, clause (B i) x → clause (B i) y) → hit G x → hit G y) :
    B q = {v} := by
  classical
  obtain ⟨w, hvw⟩ := hne
  apply Finset.ext
  intro u
  constructor
  · intro hu
    by_contra hu'
    have huv : u ≠ v := by simpa only [Finset.mem_singleton] using hu'
    have huw : ¬ G.Adj u w := fun h => hpacking u hu v hv huv w ⟨h, hvw⟩
    let x : Fin n → Bool := fun a => decide (a = v ∨ a = w)
    let y : Fin n → Bool := fun a => decide (a = u ∨ a = w)
    have hxy : ∀ i ∈ U, clause (B i) x → clause (B i) y := by
      intro i hi hiX
      obtain ⟨a, ha, hax⟩ := hiX
      have ea : a = v ∨ a = w := of_decide_eq_true hax
      rcases ea with ea | ea
      · have eq : i = q := hunique i hi (ea ▸ ha)
        exact ⟨u, eq.symm ▸ hu, by simp [y]⟩
      · exact ⟨w, ea ▸ ha, by simp [y]⟩
    have good : hit G x := ⟨v, w, hvw, by simp [x], by simp [x]⟩
    obtain ⟨a, b, hab, hay, hby⟩ := hmono x y hxy good
    have ea : a = u ∨ a = w := of_decide_eq_true hay
    have eb : b = u ∨ b = w := of_decide_eq_true hby
    rcases ea with rfl | rfl <;> rcases eb with rfl | rfl
    · exact G.irrefl hab
    · exact huw hab
    · exact huw hab.symm
    · exact G.irrefl hab
  · intro hu
    have eu : u = v := Finset.mem_singleton.mp hu
    simpa only [eu] using hv

end UniqueClause

end PEqualNP.Outside.L_meta_1904_aux
