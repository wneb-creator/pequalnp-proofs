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


namespace PairCounting

/-- A cover by sets of size at most two has at least as many sets as vertices
  when every uniquely covered vertex belongs to a singleton set. -/
lemma card_le_card_of_unique_membership_singleton
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (V : Finset α) (U : Finset β) (B : β → Finset α)
    (hsub : ∀ i ∈ U, B i ⊆ V)
    (hcard : ∀ i ∈ U, (B i).card ≤ 2)
    (hcover : ∀ v ∈ V, ∃ i ∈ U, v ∈ B i)
    (hunique : ∀ v ∈ V, ∀ i ∈ U, v ∈ B i →
      (∀ j ∈ U, v ∈ B j → j = i) → B i = {v}) :
    V.card ≤ U.card := by
  classical
  let w : β → ℕ := fun i => if (B i).card = 1 then 2 else 1
  let f : β → α → ℕ := fun i v => if v ∈ B i then w i else 0
  have hw (i : β) : 1 ≤ w i := by
    dsimp [w]
    split_ifs <;> omega
  have clause_bound (i : β) (hi : i ∈ U) : (∑ v ∈ V, f i v) ≤ 2 := by
    have hfilter : V.filter (fun v => v ∈ B i) = B i := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨And.right, fun hv => ⟨hsub i hi hv, hv⟩⟩
    change (∑ v ∈ V, if v ∈ B i then w i else 0) ≤ 2
    rw [← Finset.sum_filter, hfilter]
    simp only [Finset.sum_const, Nat.nsmul_eq_mul]
    dsimp [w]
    split_ifs with h
    · omega
    · simpa using hcard i hi
  have vertex_bound (v : α) (hv : v ∈ V) : 2 ≤ ∑ i ∈ U, f i v := by
    obtain ⟨i, hi, hvi⟩ := hcover v hv
    by_cases hall : ∀ j ∈ U, v ∈ B j → j = i
    · have hBi : B i = {v} := hunique v hv i hi hvi hall
      have hwi : w i = 2 := by simp [w, hBi]
      have hs := Finset.single_le_sum (f := fun j => f j v)
        (fun j hj => Nat.zero_le _) hi
      simpa only [f, ite_eq_left hvi, hwi] using hs
    · push Not at hall
      obtain ⟨j, hj, hvj, hji⟩ := hall
      have hpair : ({i, j} : Finset β) ⊆ U := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact hi
        · exact hj
      have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => f k v)
        hpair (fun k hk hnot => Nat.zero_le _)
      have hs' : w i + w j ≤ ∑ k ∈ U, f k v := by
        simpa only [Finset.sum_pair hji.symm, f, ite_eq_left hvi, ite_eq_left hvj] using hs
      have hiw := hw i
      have hjw := hw j
      omega
  have hl : 2 * V.card ≤ ∑ v ∈ V, ∑ i ∈ U, f i v := by
    calc
      2 * V.card = ∑ v ∈ V, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ V, ∑ i ∈ U, f i v := Finset.sum_le_sum vertex_bound
  have hu : (∑ i ∈ U, ∑ v ∈ V, f i v) ≤ 2 * U.card := by
    calc
      (∑ i ∈ U, ∑ v ∈ V, f i v) ≤ ∑ i ∈ U, 2 := Finset.sum_le_sum clause_bound
      _ = 2 * U.card := by simp [Nat.mul_comm]
  have hc : (∑ v ∈ V, ∑ i ∈ U, f i v) = ∑ i ∈ U, ∑ v ∈ V, f i v :=
    Finset.sum_comm
  omega

end PairCounting

namespace ReplacementSupport

def hit {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true

def clause {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ a ∈ S, x a = true

lemma replacement_support_has_edge {n : ℕ} {I : Type}
    (G : SimpleGraph (Fin n)) (B : I → Finset (Fin n)) (U : Finset I)
    (v : Fin n) (R : Finset (Fin n))
    (hne : ∃ w, G.Adj v w)
    (hreplace : ∀ i ∈ U, v ∈ B i → ∃ a ∈ B i, a ∈ R)
    (hremote : ∀ a ∈ R, ∀ w, ¬(G.Adj v w ∧ G.Adj a w))
    (hmono : ∀ x y : Fin n → Bool,
      (∀ i ∈ U, clause (B i) x → clause (B i) y) → hit G x → hit G y) :
    ∃ a ∈ R, ∃ b ∈ R, G.Adj a b := by
  classical
  obtain ⟨w, hvw⟩ := hne
  let x : Fin n → Bool := fun a => decide (a = v ∨ a = w)
  let y : Fin n → Bool := fun a => decide (a ∈ R ∨ a = w)
  have hxy : ∀ i ∈ U, clause (B i) x → clause (B i) y := by
    intro i hi hiX
    obtain ⟨a, ha, hax⟩ := hiX
    have ea : a = v ∨ a = w := of_decide_eq_true hax
    rcases ea with ea | ea
    · obtain ⟨b, hb, hbR⟩ := hreplace i hi (ea ▸ ha)
      exact ⟨b, hb, by simp [y, hbR]⟩
    · exact ⟨w, ea ▸ ha, by simp [y]⟩
  have good : hit G x := ⟨v, w, hvw, by simp [x], by simp [x]⟩
  obtain ⟨a, b, hab, hay, hby⟩ := hmono x y hxy good
  have ea : a ∈ R ∨ a = w := of_decide_eq_true hay
  have eb : b ∈ R ∨ b = w := of_decide_eq_true hby
  rcases ea with ha | ha <;> rcases eb with hb | hb
  · exact ⟨a, ha, b, hb, hab⟩
  · exact (hremote a ha w ⟨hvw, hb ▸ hab⟩).elim
  · have hbw : G.Adj b w := by simpa only [ha] using hab.symm
    exact (hremote b hb w ⟨hvw, hbw⟩).elim
  · have hww : G.Adj w w := by simpa only [ha, hb] using hab
    exact (G.irrefl hww).elim

lemma pair_partners_adjacent {n : ℕ} {I : Type}
    (G : SimpleGraph (Fin n)) (B : I → Finset (Fin n)) (U : Finset I)
    (v a b : Fin n)
    (hne : ∃ w, G.Adj v w)
    (hreplace : ∀ i ∈ U, v ∈ B i → a ∈ B i ∨ b ∈ B i)
    (ha : ∀ w, ¬(G.Adj v w ∧ G.Adj a w))
    (hb : ∀ w, ¬(G.Adj v w ∧ G.Adj b w))
    (hmono : ∀ x y : Fin n → Bool,
      (∀ i ∈ U, clause (B i) x → clause (B i) y) → hit G x → hit G y) :
    G.Adj a b := by
  classical
  obtain ⟨c, hc, d, hd, hcd⟩ := replacement_support_has_edge G B U v {a, b} hne
    (by
      intro i hi hv
      rcases hreplace i hi hv with hai | hbi
      · exact ⟨a, hai, by simp⟩
      · exact ⟨b, hbi, by simp⟩)
    (by
      intro c hc w
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · exact ha w
      · exact hb w) hmono
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc hd
  rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
  · exact (G.irrefl hcd).elim
  · exact hcd
  · exact hcd.symm
  · exact (G.irrefl hcd).elim

end ReplacementSupport

namespace PairSources

lemma card_le_used_pair_sources {n : ℕ} {I : Type} [DecidableEq I]
    (G : SimpleGraph (Fin n)) (B : I → Finset (Fin n)) (U : Finset I)
    (hne : ∀ v, ∃ w, G.Adj v w)
    (hcard : ∀ i ∈ U, (B i).card ≤ 2)
    (hpacking : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    (hmono : ∀ x y : Fin n → Bool,
      (∀ i ∈ U, UniqueClause.clause (B i) x → UniqueClause.clause (B i) y) →
      UniqueClause.hit G x → UniqueClause.hit G y) :
    n ≤ U.card := by
  classical
  have hcover (v : Fin n) : ∃ i ∈ U, v ∈ B i := by
    by_contra hv
    have hreplace : ∀ i ∈ U, v ∈ B i → ∃ a ∈ B i, a ∈ (∅ : Finset (Fin n)) := by
      intro i hi hvi
      exact (hv ⟨i, hi, hvi⟩).elim
    obtain ⟨a, ha, b, hb, hab⟩ := ReplacementSupport.replacement_support_has_edge
      G B U v ∅ (hne v) hreplace (by simp) hmono
    simpa using ha
  have hc := PairCounting.card_le_card_of_unique_membership_singleton
    (Finset.univ : Finset (Fin n)) U B
    (by intros; exact Finset.subset_univ _) hcard
    (by intro v hv; exact hcover v)
    (by
      intro v hv i hi hvi huniq
      exact UniqueClause.singleton_of_unique_used_clause G B U i v hvi (hne v)
        huniq (hpacking i hi) hmono)
  simpa using hc

end PairSources

namespace SoleOrDominating

lemma degree_le_card_of_dominating_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfour : ∀ a b c d : V, G.Adj a b → G.Adj b c →
      G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (t : V) (I : Finset V) (htI : t ∉ I)
    (hdom : ∀ r : V, G.Adj t r → ∃ v ∈ I, G.Adj r v) :
    G.degree t ≤ I.card := by
  classical
  let f : V → V := fun r =>
    if h : G.Adj t r then (hdom r h).choose else t
  have hf (r : V) (hr : G.Adj t r) : f r ∈ I ∧ G.Adj r (f r) := by
    simpa [f, hr] using (hdom r hr).choose_spec
  change (G.neighborFinset t).card ≤ I.card
  apply Finset.card_le_card_of_injOn f
  · intro r hr
    exact (hf r ((G.mem_neighborFinset t r).mp hr)).1
  · intro r hr s hs hsame
    have htr : G.Adj t r := (G.mem_neighborFinset t r).mp hr
    have hts : G.Adj t s := (G.mem_neighborFinset t s).mp hs
    have hfrs : G.Adj (f r) s := by
      rw [hsame]
      exact (hf s hts).2.symm
    rcases hfour t r (f r) s htr (hf r htr).2 hfrs hts.symm with h | h
    · exact (htI (h.symm ▸ (hf r htr).1)).elim
    · exact h

lemma exists_neighbor_avoiding_of_card_lt_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfour : ∀ a b c d : V, G.Adj a b → G.Adj b c →
      G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (t : V) (I : Finset V) (htI : t ∉ I)
    (hcard : I.card < G.degree t) :
    ∃ r : V, G.Adj t r ∧ ∀ v ∈ I, ¬ G.Adj r v := by
  classical
  by_contra hnone
  have hdom : ∀ r : V, G.Adj t r → ∃ v ∈ I, G.Adj r v := by
    intro r hr
    by_contra hmiss
    apply hnone
    refine ⟨r, hr, ?_⟩
    intro v hv hrv
    exact hmiss ⟨v, hv, hrv⟩
  exact (Nat.not_le_of_lt hcard)
    (degree_le_card_of_dominating_neighbors G hfour t I htI hdom)

lemma exists_neighbor_avoiding_small_set
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfour : ∀ a b c d : V, G.Adj a b → G.Adj b c →
      G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (t : V) (I : Finset V) (htI : t ∉ I)
    (hdegree : 2 < G.degree t) (hcard : I.card ≤ 2) :
    ∃ r : V, G.Adj t r ∧ ∀ v ∈ I, ¬ G.Adj r v := by
  exact exists_neighbor_avoiding_of_card_lt_degree G hfour t I htI
    (lt_of_le_of_lt hcard hdegree)

end SoleOrDominating

namespace SoleOrToggle

def edgePresent {V : Type*} (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ u ∈ S, ∃ v ∈ S, G.Adj u v

lemma independent_not_edgePresent {V : Type*} {G : SimpleGraph V} {S : Finset V}
    (hS : G.IsIndepSet (S : Set V)) : ¬ edgePresent G S := by
  rintro ⟨u, hu, v, hv, huv⟩
  exact hS hu hv (G.ne_of_adj huv) huv

lemma toggle_true_independent_avoids {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (t : V) (q : Finset V → Prop)
    (hstable : ∀ S, q S → edgePresent G (insert t S) → edgePresent G S)
    {I : Finset V} (hI : G.IsIndepSet (I : Set V)) (hqI : q I) :
    ∀ r, G.Adj t r → r ∉ I := by
  intro r htr hr
  apply independent_not_edgePresent hI
  apply hstable I hqI
  exact ⟨t, Finset.mem_insert_self _ _, r, Finset.mem_insert_of_mem hr, htr⟩

lemma toggle_true_independent_dominates {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (t : V) (q : Finset V → Prop)
    (hq : Monotone q)
    (hstable : ∀ S, q S → edgePresent G (insert t S) → edgePresent G S)
    {I : Finset V} (hI : G.IsIndepSet (I : Set V)) (hqI : q I) :
    ∀ r, G.Adj t r → ∃ v ∈ I, G.Adj r v := by
  classical
  intro r htr
  by_contra hn
  push Not at hn
  have hinsert : G.IsIndepSet ((insert r I : Finset V) : Set V) := by
    intro a ha b hb hab habAdj
    rcases Finset.mem_insert.mp ha with har | haI
    · subst a
      rcases Finset.mem_insert.mp hb with hbr | hbI
      · subst b
        exact G.irrefl habAdj
      · exact hn b hbI habAdj
    · rcases Finset.mem_insert.mp hb with hbr | hbI
      · subst b
        exact hn a haI habAdj.symm
      · exact hI haI hbI hab habAdj
  apply independent_not_edgePresent hinsert
  apply hstable (insert r I) (hq (Finset.subset_insert _ _) hqI)
  exact ⟨t, Finset.mem_insert_self _ _, r,
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), htr⟩


lemma degree_le_card_of_toggle_true_independent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfour : ∀ a b c d : V, G.Adj a b → G.Adj b c →
      G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (t : V) (q : Finset V → Prop) (hq : Monotone q)
    (hstable : ∀ S, q S → edgePresent G (insert t S) → edgePresent G S)
    {I : Finset V} (htI : t ∉ I) (hI : G.IsIndepSet (I : Set V)) (hqI : q I) :
    G.degree t ≤ I.card := by
  exact PEqualNP.Outside.L_meta_1904_aux.SoleOrDominating.degree_le_card_of_dominating_neighbors G hfour t I htI
    (toggle_true_independent_dominates G t q hq hstable hI hqI)

lemma toggle_true_tfree_small_has_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfour : ∀ a b c d : V, G.Adj a b → G.Adj b c →
      G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (t : V) (q : Finset V → Prop) (hq : Monotone q)
    (hstable : ∀ S, q S → edgePresent G (insert t S) → edgePresent G S)
    {I : Finset V} (htI : t ∉ I) (hcard : I.card < G.degree t) (hqI : q I) :
    edgePresent G I := by
  classical
  by_contra hn
  have hI : G.IsIndepSet (I : Set V) := by
    intro u hu v hv _ huv
    exact hn ⟨u, hu, v, hv, huv⟩
  exact (Nat.not_le_of_lt hcard)
    (degree_le_card_of_toggle_true_independent G hfour t q hq hstable htI hI hqI)

lemma toggle_true_small_has_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfour : ∀ a b c d : V, G.Adj a b → G.Adj b c →
      G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (t : V) (q : Finset V → Prop) (hq : Monotone q)
    (hstable : ∀ S, q S → edgePresent G (insert t S) → edgePresent G S)
    (herase : ∀ S, q S → q (S.erase t))
    {I : Finset V} (hcard : I.card < G.degree t) (hqI : q I) :
    edgePresent G I := by
  have hsmall : (I.erase t).card < G.degree t :=
    lt_of_le_of_lt (Finset.card_le_card (Finset.erase_subset _ _)) hcard
  obtain ⟨u, hu, v, hv, huv⟩ := toggle_true_tfree_small_has_edge
    G hfour t q hq hstable (Finset.notMem_erase _ _) hsmall (herase I hqI)
  exact ⟨u, Finset.mem_of_mem_erase hu, v, Finset.mem_of_mem_erase hv, huv⟩

lemma toggle_true_pair_has_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfour : ∀ a b c d : V, G.Adj a b → G.Adj b c →
      G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (t : V) (q : Finset V → Prop) (hq : Monotone q)
    (hstable : ∀ S, q S → edgePresent G (insert t S) → edgePresent G S)
    (herase : ∀ S, q S → q (S.erase t))
    (hdegree : 2 < G.degree t)
    {I : Finset V} (hcard : I.card ≤ 2) (hqI : q I) :
    edgePresent G I := by
  exact toggle_true_small_has_edge G hfour t q hq hstable herase
    (lt_of_le_of_lt hcard hdegree) hqI

end SoleOrToggle

namespace SignalAgreement

def hit {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true

def clause {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ a ∈ S, x a = true

lemma replacement_support_has_edge {n : ℕ} {I : Type}
    (G : SimpleGraph (Fin n)) (B : I → Finset (Fin n)) (U : Finset I)
    (v : Fin n) (R : Finset (Fin n))
    (hne : ∃ w, G.Adj v w)
    (hreplace : ∀ i ∈ U, v ∈ B i → ∃ a ∈ B i, a ∈ R)
    (hremote : ∀ a ∈ R, ∀ w, ¬(G.Adj v w ∧ G.Adj a w))
    (hagree : ∀ x y : Fin n → Bool,
      (∀ i ∈ U, clause (B i) x ↔ clause (B i) y) → hit G x → hit G y) :
    ∃ a ∈ R, ∃ b ∈ R, G.Adj a b := by
  classical
  obtain ⟨w, hvw⟩ := hne
  let x : Fin n → Bool := fun a => decide (a ∈ R ∨ a = w ∨ a = v)
  let y : Fin n → Bool := fun a => decide (a ∈ R ∨ a = w)
  have hxy : ∀ i ∈ U, clause (B i) x ↔ clause (B i) y := by
    intro i hi
    constructor
    · rintro ⟨a, ha, hax⟩
      have ea : a ∈ R ∨ a = w ∨ a = v := of_decide_eq_true hax
      rcases ea with haR | haw | ea
      · exact ⟨a,ha,by simp [y,haR]⟩
      · exact ⟨a,ha,by simp [y,haw]⟩
      · obtain ⟨b,hb,hbR⟩ := hreplace i hi (ea ▸ ha)
        exact ⟨b,hb,by simp [y,hbR]⟩
    · rintro ⟨a,ha,hay⟩
      have ea : a ∈ R ∨ a = w := of_decide_eq_true hay
      rcases ea with haR | haw
      · exact ⟨a,ha,by simp [x,haR]⟩
      · exact ⟨a,ha,by simp [x,haw]⟩
  have good : hit G x := ⟨v,w,hvw,by simp [x],by simp [x]⟩
  obtain ⟨a,b,hab,hay,hby⟩ := hagree x y hxy good
  have ea : a ∈ R ∨ a = w := of_decide_eq_true hay
  have eb : b ∈ R ∨ b = w := of_decide_eq_true hby
  rcases ea with ha | ha <;> rcases eb with hb | hb
  · exact ⟨a,ha,b,hb,hab⟩
  · exact (hremote a ha w ⟨hvw,hb ▸ hab⟩).elim
  · have hbw : G.Adj b w := by simpa only [ha] using hab.symm
    exact (hremote b hb w ⟨hvw,hbw⟩).elim
  · have hww : G.Adj w w := by simpa only [ha,hb] using hab
    exact (G.irrefl hww).elim

end SignalAgreement

namespace PackingTransversal

/-- A greedy independent transversal, allowing one vertex to hit several sets.
  Each previously chosen vertex forbids at most one element of the next set. -/
lemma independent_hitting_set
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (U : Finset β) (A : β → Finset α)
    (hlocal : ∀ i ∈ U, ∀ w, ((A i).filter (G.Adj w)).card ≤ 1)
    (hlarge : ∀ J ⊆ U, J.Nonempty → ∃ i ∈ J, J.card ≤ (A i).card) :
    ∃ R : Finset α, R.card ≤ U.card ∧ R ⊆ U.biUnion A ∧
      (∀ a ∈ R, ∀ b ∈ R, ¬ G.Adj a b) ∧
      (∀ i ∈ U, ∃ a ∈ R, a ∈ A i) := by
  classical
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    by_cases hU : U.Nonempty
    · obtain ⟨i, hi, hsize⟩ := hlarge U Finset.Subset.rfl hU
      have hproper : U.erase i ⊂ U := Finset.erase_ssubset hi
      obtain ⟨R, hRcard, hRsub, hRind, hRhit⟩ := ih (U.erase i) hproper
        (fun j hj w => hlocal j (Finset.mem_of_mem_erase hj) w)
        (fun J hJ hne => hlarge J (hJ.trans (Finset.erase_subset i U)) hne)
      let bad : Finset α := R.biUnion (fun r => (A i).filter (G.Adj r))
      have hbad : bad.card ≤ R.card := by
        calc
          bad.card ≤ ∑ r ∈ R, ((A i).filter (G.Adj r)).card := Finset.card_biUnion_le
          _ ≤ ∑ r ∈ R, 1 := Finset.sum_le_sum (fun r hr => hlocal i hi r)
          _ = R.card := by simp
      have herase : (U.erase i).card + 1 = U.card := Finset.card_erase_add_one hi
      have hlt : bad.card < (A i).card := by omega
      obtain ⟨a, ha, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      have hfree : ∀ r ∈ R, ¬ G.Adj r a := by
        intro r hr hadj
        exact hnot (Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_filter.mpr ⟨ha, hadj⟩⟩)
      refine ⟨insert a R, ?_, ?_, ?_, ?_⟩
      · have h := Finset.card_insert_le a R
        omega
      · intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact Finset.mem_biUnion.mpr ⟨i, hi, ha⟩
        · obtain ⟨j, hj, hrj⟩ := Finset.mem_biUnion.mp (hRsub hr)
          exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_of_mem_erase hj, hrj⟩
      · intro r hr s hs hadj
        rcases Finset.mem_insert.mp hr with hra | hrR
        · subst r
          rcases Finset.mem_insert.mp hs with hsa | hsR
          · subst s
            exact G.irrefl hadj
          · exact hfree s hsR hadj.symm
        · rcases Finset.mem_insert.mp hs with hsa | hsR
          · subst s
            exact hfree r hrR hadj
          · exact hRind r hrR s hsR hadj
      · intro j hj
        by_cases hji : j = i
        · subst j
          exact ⟨a, Finset.mem_insert_self a R, ha⟩
        · obtain ⟨r, hr, hrj⟩ := hRhit j (Finset.mem_erase.mpr ⟨hji, hj⟩)
          exact ⟨r, Finset.mem_insert_of_mem hr, hrj⟩
    · have hempty : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      subst U
      exact ⟨∅, by simp⟩

end PackingTransversal

namespace WeightedSourceCount

lemma card_le_of_small_incidence_blocks {α ι : Type} [DecidableEq α] [DecidableEq ι]
    (V : Finset α) (U : Finset ι) (B : ι → Finset α)
    (hsub : ∀ i ∈ U, B i ⊆ V)
    (hblocks : ∀ v ∈ V, ∃ J : Finset ι, J.Nonempty ∧ J ⊆ U ∧
      ∀ i ∈ J, v ∈ B i ∧ (B i).card ≤ J.card) :
    V.card ≤ U.card := by
  classical
  let weight : α → ι → ℚ := fun v i => if v ∈ B i then 1 / (B i).card else 0
  have nonneg (v : α) (i : ι) : 0 ≤ weight v i := by
    dsimp only [weight]
    split_ifs
    · positivity
    · exact le_rfl
  have row (v : α) (hv : v ∈ V) : 1 ≤ ∑ i ∈ U, weight v i := by
    obtain ⟨J, hJ, hJU, hJi⟩ := hblocks v hv
    have hposJ : (0 : ℚ) < J.card := by exact_mod_cast hJ.card_pos
    calc
      (1 : ℚ) = ∑ i ∈ J, (1 : ℚ) / J.card := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        field_simp
      _ ≤ ∑ i ∈ J, weight v i := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨hvi, hc⟩ := hJi i hi
        have hpos : (0 : ℚ) < (B i).card := by
          exact_mod_cast (Finset.card_pos.mpr ⟨v, hvi⟩)
        dsimp only [weight]
        rw [ite_eq_left hvi]
        exact one_div_le_one_div_of_le hpos (by exact_mod_cast hc)
      _ ≤ ∑ i ∈ U, weight v i :=
        Finset.sum_le_sum_of_subset_of_nonneg hJU (fun i _ _ => nonneg v i)
  have column (i : ι) (hi : i ∈ U) : (∑ v ∈ V, weight v i) ≤ 1 := by
    have reduce : (∑ v ∈ V, weight v i) = ∑ v ∈ B i, weight v i := by
      symm
      apply Finset.sum_subset (hsub i hi)
      intro v _ hv
      simp [weight, hv]
    rw [reduce]
    simp only [weight, Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const,
      nsmul_eq_mul]
    by_cases empty : (B i).card = 0
    · simp [empty]
    · have nz : ((B i).card : ℚ) ≠ 0 := by exact_mod_cast empty
      field_simp
      norm_num
  have bound : (V.card : ℚ) ≤ U.card := by
    calc
      (V.card : ℚ) = ∑ v ∈ V, (1 : ℚ) := by simp
      _ ≤ ∑ v ∈ V, ∑ i ∈ U, weight v i := Finset.sum_le_sum row
      _ = ∑ i ∈ U, ∑ v ∈ V, weight v i := Finset.sum_comm
      _ ≤ ∑ i ∈ U, (1 : ℚ) := Finset.sum_le_sum column
      _ = U.card := by simp
  exact_mod_cast bound

end WeightedSourceCount

namespace PackingSources

lemma small_subfamily_of_essential_vertex {n : ℕ} {I : Type} [DecidableEq I]
    (G : SimpleGraph (Fin n)) (B : I → Finset (Fin n)) (U : Finset I)
    (v : Fin n) (hne : ∃ w, G.Adj v w)
    (hpacking : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    (hagree : ∀ x y : Fin n → Bool,
      (∀ i ∈ U, SignalAgreement.clause (B i) x ↔
        SignalAgreement.clause (B i) y) →
      SignalAgreement.hit G x → SignalAgreement.hit G y) :
    ∃ J : Finset I, J.Nonempty ∧ J ⊆ U ∧
      ∀ i ∈ J, v ∈ B i ∧ (B i).card ≤ J.card := by
  classical
  let W : Finset I := U.filter (fun i => v ∈ B i)
  let A : I → Finset (Fin n) := fun i => (B i).erase v
  by_contra hnone
  have hlocal : ∀ i ∈ W, ∀ w, ((A i).filter (G.Adj w)).card ≤ 1 := by
    intro i hi w
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have hai := (Finset.mem_filter.mp ha).1
    have hbi := (Finset.mem_filter.mp hb).1
    by_contra hab
    exact hpacking i (Finset.mem_filter.mp hi).1 a (Finset.mem_of_mem_erase hai)
      b (Finset.mem_of_mem_erase hbi) hab w
      ⟨(Finset.mem_filter.mp ha).2.symm, (Finset.mem_filter.mp hb).2.symm⟩
  have hlarge : ∀ J ⊆ W, J.Nonempty → ∃ i ∈ J, J.card ≤ (A i).card := by
    intro J hJW hJ
    by_contra hsmall
    push Not at hsmall
    apply hnone
    refine ⟨J, hJ, fun i hi => (Finset.mem_filter.mp (hJW hi)).1, ?_⟩
    intro i hi
    have hvi := (Finset.mem_filter.mp (hJW hi)).2
    have hci := hsmall i hi
    have he := Finset.card_erase_add_one hvi
    change ((B i).erase v).card < J.card at hci
    exact ⟨hvi, by omega⟩
  obtain ⟨R, hRc, hRU, hRI, hhit⟩ :=
    PackingTransversal.independent_hitting_set G W A hlocal hlarge
  have hreplace : ∀ i ∈ U, v ∈ B i → ∃ a ∈ B i, a ∈ R := by
    intro i hi hvi
    obtain ⟨a, haR, haA⟩ := hhit i (Finset.mem_filter.mpr ⟨hi, hvi⟩)
    exact ⟨a, Finset.mem_of_mem_erase haA, haR⟩
  have hremote : ∀ a ∈ R, ∀ w, ¬ (G.Adj v w ∧ G.Adj a w) := by
    intro a ha w
    obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp (hRU ha)
    have hiU := (Finset.mem_filter.mp hi).1
    have hvi := (Finset.mem_filter.mp hi).2
    have hai' := Finset.mem_erase.mp hai
    exact hpacking i hiU v hvi a hai'.2 hai'.1.symm w
  obtain ⟨a, ha, b, hb, hab⟩ :=
    SignalAgreement.replacement_support_has_edge G B U v R hne hreplace hremote hagree
  exact hRI a ha b hb hab

lemma card_le_used_packing_sources {n : ℕ} {I : Type} [DecidableEq I]
    (G : SimpleGraph (Fin n)) (B : I → Finset (Fin n)) (U : Finset I)
    (hne : ∀ v, ∃ w, G.Adj v w)
    (hpacking : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    (hagree : ∀ x y : Fin n → Bool,
      (∀ i ∈ U, SignalAgreement.clause (B i) x ↔
        SignalAgreement.clause (B i) y) →
      SignalAgreement.hit G x → SignalAgreement.hit G y) :
    n ≤ U.card := by
  classical
  have hc := WeightedSourceCount.card_le_of_small_incidence_blocks
    (Finset.univ : Finset (Fin n)) U B
    (by intros; exact Finset.subset_univ _)
    (by
      intro v hv
      exact small_subfamily_of_essential_vertex G B U v (hne v) hpacking hagree)
  simpa using hc

end PackingSources

namespace InputSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {n : ℕ}

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

def SupportsImplication (x y : Fin n → Bool) (L : List (Finset (Fin n)))
    (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = true → y i = true) →
      w.getD j false = true → w'.getD j false = true

lemma gate_implication (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true) :
    g.op.eval (g.inputs.map fun i => w.getD i false) = true →
      g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg
  · simp only [hg, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro hall i hi
    exact h i hi (hall i hi)
  · simp only [hg, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, hval⟩
    exact ⟨i, hi, h i hi hval⟩

lemma implication_wiresFrom (x y : Fin n → Bool) (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), SupportsImplication x y L w w' →
      SupportsImplication x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (fun a ha => hmono a (List.mem_cons_of_mem _ ha)) (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      apply gate_implication g (hmono g List.mem_cons_self)
      intro a ha hval
      apply h3 a ?_ hval
      intro i hi
      exact hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩)
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

lemma implication_inputs (x y : Fin n → Bool) :
    SupportsImplication x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = true → y ⟨j, hjn⟩ = true := hj _ (by simp [inputSupps, hjn])
    simpa [hjn] using hx
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp

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

lemma small_input_support {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    ∃ S : Finset (Fin n), S.card ≤ C.size + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = true → y i = true) →
        C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  let S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅
  refine ⟨S, ?_, ?_⟩
  · have hc := cnt_suppsFrom C.gates 0 (inputSupps n)
      (fun g hg => (hmono g hg).2) cnt_inputs {C.output}
    simpa only [Finset.singleton_biUnion, Finset.card_singleton, zero_add, S, Circuit.size] using hc
  · intro x y hS hx
    have himp := implication_wiresFrom x y C.gates
      (fun g hg => by simpa using (hmono g hg).1) _ _ _ (implication_inputs x y)
    exact himp.2.2 C.output hS hx

lemma separation_of_support {n : ℕ} (C : Circuit) (S : Finset (Fin n))
    (hsupport : ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = true → y i = true) →
      C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true)
    (x y : Fin n → Bool) (hx : C.eval (List.ofFn x) = true)
    (hy : C.eval (List.ofFn y) = false) :
    ∃ i ∈ S, x i = true ∧ y i = false := by
  classical
  have hnot : ¬ ∀ i ∈ S, x i = true → y i = true := by
    intro himp
    have htrue := hsupport x y himp hx
    rw [hy] at htrue
    contradiction
  push Not at hnot
  obtain ⟨i, hi, hxi, hyi⟩ := hnot
  exact ⟨i, hi, hxi, Bool.eq_false_iff.mpr hyi⟩

lemma small_input_separating_support {n : ℕ} (C : Circuit) (hmono : Monotone2 C) :
    ∃ S : Finset (Fin n), S.card ≤ C.size + 1 ∧
      ∀ x y : Fin n → Bool, C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = false →
        ∃ i ∈ S, x i = true ∧ y i = false := by
  obtain ⟨S, hcard, hsupport⟩ := small_input_support C hmono
  exact ⟨S, hcard, separation_of_support C S hsupport⟩


end InputSupport

namespace InputSupport

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def clauseInput {n m : ℕ} (B : Fin m → Finset (Fin n)) (x : Fin n → Bool) :
    Fin m → Bool :=
  fun i => decide (∃ a ∈ B i, x a = true)

lemma clauseInput_eq_true {n m : ℕ} (B : Fin m → Finset (Fin n))
    (x : Fin n → Bool) (i : Fin m) :
    clauseInput B x i = true ↔ UniqueClause.clause (B i) x := by
  simp only [clauseInput, decide_eq_true_eq, UniqueClause.clause]

lemma small_clause_support {n m : ℕ}
    (G : SimpleGraph (Fin n)) (B : Fin m → Finset (Fin n))
    (C : Circuit) (hC : Monotone2 C)
    (hcorrect : ∀ x : Fin n → Bool,
      C.eval (List.ofFn (clauseInput B x)) = true ↔
        UniqueClause.hit G x) :
    ∃ U : Finset (Fin m), U.card ≤ C.size + 1 ∧
      ∀ x y : Fin n → Bool,
        (∀ i ∈ U, UniqueClause.clause (B i) x → UniqueClause.clause (B i) y) →
        UniqueClause.hit G x → UniqueClause.hit G y := by
  obtain ⟨U, hcard, hsupport⟩ := small_input_support (n := m) C hC
  refine ⟨U, hcard, ?_⟩
  intro x y hxy hx
  apply (hcorrect y).mp
  apply hsupport (clauseInput B x) (clauseInput B y)
  · intro i hi hxi
    exact (clauseInput_eq_true B y i).mpr
      (hxy i hi ((clauseInput_eq_true B x i).mp hxi))
  · exact (hcorrect x).mpr hx

end InputSupport

namespace PackingSources

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma packing_factorization_lower_bound {n m : ℕ}
    (G : SimpleGraph (Fin n)) (B : Fin m → Finset (Fin n))
    (F : (Fin m → Bool) → Bool)
    (hne : ∀ v, ∃ w, G.Adj v w)
    (hpacking : ∀ i, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    (hcorrect : ∀ x : Fin n → Bool,
      F (InputSupport.clauseInput B x) = true ↔ UniqueClause.hit G x) :
    n ≤ m := by
  classical
  have hc := card_le_used_packing_sources G B Finset.univ hne
    (fun i _ => hpacking i) (by
      intro x y hxy hx
      apply (hcorrect y).mp
      have he : InputSupport.clauseInput B x = InputSupport.clauseInput B y := by
        funext i
        have hi : InputSupport.clauseInput B x i = true ↔
            InputSupport.clauseInput B y i = true :=
          (InputSupport.clauseInput_eq_true B x i).trans
            ((hxy i (Finset.mem_univ i)).trans
              (InputSupport.clauseInput_eq_true B y i).symm)
        cases ha : InputSupport.clauseInput B x i <;>
          cases hb : InputSupport.clauseInput B y i <;> simp_all
      rw [← he]
      exact (hcorrect x).mpr hx)
  simpa using hc

lemma packing_paid_gate_lower_bound {n m : ℕ}
    (G : SimpleGraph (Fin n)) (B : Fin m → Finset (Fin n))
    (C : Circuit) (hC : Monotone2 C)
    (hne : ∀ v, ∃ w, G.Adj v w)
    (hpacking : ∀ i, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    (hcorrect : ∀ x : Fin n → Bool,
      C.eval (List.ofFn (InputSupport.clauseInput B x)) = true ↔
        UniqueClause.hit G x) :
    n ≤ C.size + 1 := by
  classical
  obtain ⟨U, hU, hmono⟩ := InputSupport.small_clause_support G B C hC hcorrect
  have hc := card_le_used_packing_sources G B U hne (fun i _ => hpacking i)
    (fun x y hxy => hmono x y (fun i hi => (hxy i hi).mp))
  exact hc.trans hU

end PackingSources


namespace WeightedSourceCount

lemma card_le_of_small_incidence_blocks_general {α ι : Type}
    [DecidableEq α] [DecidableEq ι]
    (V : Finset α) (U : Finset ι) (B : ι → Finset α)
    (hblocks : ∀ v ∈ V, ∃ J : Finset ι, J.Nonempty ∧ J ⊆ U ∧
      ∀ i ∈ J, v ∈ B i ∧ (B i).card ≤ J.card) :
    V.card ≤ U.card := by
  classical
  let weight : α → ι → ℚ := fun v i => if v ∈ B i then 1 / (B i).card else 0
  have nonneg (v : α) (i : ι) : 0 ≤ weight v i := by
    dsimp only [weight]
    split_ifs
    · positivity
    · exact le_rfl
  have row (v : α) (hv : v ∈ V) : 1 ≤ ∑ i ∈ U, weight v i := by
    obtain ⟨J, hJ, hJU, hJi⟩ := hblocks v hv
    have hposJ : (0 : ℚ) < J.card := by exact_mod_cast hJ.card_pos
    calc
      (1 : ℚ) = ∑ i ∈ J, (1 : ℚ) / J.card := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        field_simp
      _ ≤ ∑ i ∈ J, weight v i := by
        apply Finset.sum_le_sum
        intro i hi
        obtain ⟨hvi, hc⟩ := hJi i hi
        have hpos : (0 : ℚ) < (B i).card := by
          exact_mod_cast (Finset.card_pos.mpr ⟨v, hvi⟩)
        dsimp only [weight]
        rw [ite_eq_left hvi]
        exact one_div_le_one_div_of_le hpos (by exact_mod_cast hc)
      _ ≤ ∑ i ∈ U, weight v i :=
        Finset.sum_le_sum_of_subset_of_nonneg hJU (fun i _ _ => nonneg v i)
  have column (i : ι) : (∑ v ∈ V, weight v i) ≤ 1 := by
    simp only [weight, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
    by_cases empty : (B i).card = 0
    · simp [empty]
    · have nz : ((B i).card : ℚ) ≠ 0 := by exact_mod_cast empty
      calc
        ((V ∩ B i).card : ℚ) * (1 / (B i).card) ≤
            ((B i).card : ℚ) * (1 / (B i).card) := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : V ∩ B i ⊆ B i)
          · positivity
        _ = 1 := by field_simp
  have bound : (V.card : ℚ) ≤ U.card := by
    calc
      (V.card : ℚ) = ∑ v ∈ V, (1 : ℚ) := by simp
      _ ≤ ∑ v ∈ V, ∑ i ∈ U, weight v i := Finset.sum_le_sum row
      _ = ∑ i ∈ U, ∑ v ∈ V, weight v i := Finset.sum_comm
      _ ≤ ∑ i ∈ U, (1 : ℚ) := Finset.sum_le_sum (fun i _ => column i)
      _ = U.card := by simp
  exact_mod_cast bound

end WeightedSourceCount

namespace InputSupport

open PEqualNP.CircuitLowerBounds

def SupportsAgreement {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n)))
    (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) →
      w.getD j false = w'.getD j false

lemma agreement_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), SupportsAgreement x y L w w' →
      SupportsAgreement x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
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
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro a ha
      apply h3 a
      intro i hi
      exact hj i ((mem_gateSupp L g i).mpr ⟨a, ha, hi⟩)
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

lemma agreement_inputs {n : ℕ} (x y : Fin n → Bool) :
    SupportsAgreement x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hxy : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simpa [hjn] using hxy
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma small_input_agree_support {n : ℕ} (C : Circuit)
    (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∃ S : Finset (Fin n), S.card ≤ C.size + 1 ∧
      ∀ x y : Fin n → Bool, (∀ i ∈ S, x i = y i) →
        C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
  let S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅
  refine ⟨S, ?_, ?_⟩
  · have hc := cnt_suppsFrom C.gates 0 (inputSupps n) hfanin cnt_inputs {C.output}
    simpa only [Finset.singleton_biUnion, Finset.card_singleton, zero_add, S, Circuit.size] using hc
  · intro x y hS
    have hagree := agreement_wiresFrom x y C.gates _ _ _ (agreement_inputs x y)
    exact hagree.2.2 C.output hS

lemma small_clause_agree_support {n m : ℕ}
    (G : SimpleGraph (Fin n)) (B : Fin m → Finset (Fin n))
    (C : Circuit) (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hcorrect : ∀ x : Fin n → Bool,
      C.eval (List.ofFn (clauseInput B x)) = true ↔ UniqueClause.hit G x) :
    ∃ U : Finset (Fin m), U.card ≤ C.size + 1 ∧
      ∀ x y : Fin n → Bool,
        (∀ i ∈ U, UniqueClause.clause (B i) x ↔ UniqueClause.clause (B i) y) →
        (UniqueClause.hit G x ↔ UniqueClause.hit G y) := by
  obtain ⟨U, hcard, hsupport⟩ := small_input_agree_support (n := m) C hfanin
  refine ⟨U, hcard, ?_⟩
  intro x y hxy
  have hinputs : ∀ i ∈ U, clauseInput B x i = clauseInput B y i := by
    intro i hi
    apply Bool.eq_iff_iff.mpr
    simpa only [clauseInput_eq_true] using hxy i hi
  have heq := hsupport (clauseInput B x) (clauseInput B y) hinputs
  rw [← hcorrect x, ← hcorrect y, heq]

end InputSupport

namespace PackingSources

open PEqualNP.CircuitLowerBounds

lemma essential_set_card_le_used_packing_sources {n : ℕ} {I : Type} [DecidableEq I]
    (G : SimpleGraph (Fin n)) (B : I → Finset (Fin n)) (U : Finset I)
    (V : Finset (Fin n)) (hne : ∀ v ∈ V, ∃ w, G.Adj v w)
    (hpacking : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    (hagree : ∀ x y : Fin n → Bool,
      (∀ i ∈ U, SignalAgreement.clause (B i) x ↔
        SignalAgreement.clause (B i) y) →
      SignalAgreement.hit G x → SignalAgreement.hit G y) :
    V.card ≤ U.card := by
  exact WeightedSourceCount.card_le_of_small_incidence_blocks_general V U B
    (fun v hv => small_subfamily_of_essential_vertex G B U v (hne v hv) hpacking hagree)

lemma packing_binary_gate_lower_bound {n m : ℕ}
    (G : SimpleGraph (Fin n)) (B : Fin m → Finset (Fin n))
    (C : Circuit) (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (V : Finset (Fin n)) (hne : ∀ v ∈ V, ∃ w, G.Adj v w)
    (hpacking : ∀ i, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    (hcorrect : ∀ x : Fin n → Bool,
      C.eval (List.ofFn (InputSupport.clauseInput B x)) = true ↔
        UniqueClause.hit G x) :
    V.card ≤ C.size + 1 := by
  classical
  obtain ⟨U, hU, hagree⟩ := InputSupport.small_clause_agree_support G B C hfanin hcorrect
  have hc := essential_set_card_le_used_packing_sources G B U V hne
    (fun i _ => hpacking i) (fun x y hxy => (hagree x y hxy).mp)
  exact hc.trans hU

lemma packing_binary_gate_lower_bound_no_isolates {n m : ℕ}
    (G : SimpleGraph (Fin n)) (B : Fin m → Finset (Fin n))
    (C : Circuit) (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hne : ∀ v, ∃ w, G.Adj v w)
    (hpacking : ∀ i, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    (hcorrect : ∀ x : Fin n → Bool,
      C.eval (List.ofFn (InputSupport.clauseInput B x)) = true ↔
        UniqueClause.hit G x) :
    n ≤ C.size + 1 := by
  simpa using packing_binary_gate_lower_bound G B C hfanin Finset.univ
    (fun v _ => hne v) hpacking hcorrect

end PackingSources

namespace RectangleNeighborhood

open SoleOrToggle

lemma pair_edge {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b : V}
    (h : edgePresent G {a, b}) : G.Adj a b := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact (G.irrefl huv).elim
  · exact huv
  · exact huv.symm
  · exact (G.irrefl huv).elim

lemma triple_edge {V : Type*} [DecidableEq V] {G : SimpleGraph V} {a b s : V}
    (h : edgePresent G {a, b, s}) (hab : ¬ G.Adj a b) (hbs : ¬ G.Adj b s) :
    G.Adj a s := by
  obtain ⟨u, hu, v, hv, huv⟩ := h
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact (G.irrefl huv).elim
  · exact (hab huv).elim
  · exact huv
  · exact (hab huv.symm).elim
  · exact (G.irrefl huv).elim
  · exact (hbs huv).elim
  · exact huv.symm
  · exact (hbs huv.symm).elim
  · exact (G.irrefl huv).elim

end RectangleNeighborhood

namespace RectangleNeighborhood

open SoleOrToggle

lemma crossing_of_large_neighborhood_filter_without_overlap
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hfour : ∀ a b c d : V, G.Adj a b → G.Adj b c →
      G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (c : V) (A B R : Finset V) (hcA : c ∉ A) (hcB : c ∉ B)
    (hR : ∀ r ∈ R, G.Adj c r) (hcard : 3 ≤ R.card)
    (hsafe : ∀ S : Finset V,
      (∃ a ∈ A, a ∈ S) → (∃ b ∈ B, b ∈ S) → (∃ r ∈ R, r ∈ S) →
      edgePresent G S) :
    ∀ a ∈ A, ∀ b ∈ B, G.Adj a b := by
  classical
  have hnonempty : R.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨r, hrR⟩ := hnonempty
  have htwo : 1 < (R.erase r).card := by
    have hc := Finset.card_erase_add_one hrR
    omega
  obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.mp htwo
  obtain ⟨hsr, hsR⟩ := Finset.mem_erase.mp hs
  obtain ⟨htr, htR⟩ := Finset.mem_erase.mp ht
  have hone (x : V) (hxc : x ≠ c) (v : V) (hv : v ∈ R)
      (w : V) (hw : w ∈ R) (hvw : v ≠ w)
      (hxv : G.Adj x v) : ¬ G.Adj x w := by
    intro hxw
    rcases hfour c v x w (hR v hv) hxv.symm hxw (hR w hw).symm with h | h
    · exact hxc h.symm
    · exact hvw h
  intro a ha b hb
  have hac : a ≠ c := fun h => hcA (h ▸ ha)
  have hbc : b ≠ c := fun h => hcB (h ▸ hb)
  by_contra hab
  have hedge (v : V) (hv : v ∈ R) : edgePresent G {a, b, v} := by
    apply hsafe {a, b, v}
    · exact ⟨a, ha, by simp⟩
    · exact ⟨b, hb, by simp⟩
    · exact ⟨v, hv, by simp⟩
  by_cases hbr : G.Adj b r
  · have hbs : ¬ G.Adj b s := hone b hbc r hrR s hsR hsr.symm hbr
    have hbt : ¬ G.Adj b t := hone b hbc r hrR t htR htr.symm hbr
    have has : G.Adj a s := triple_edge (hedge s hsR) hab hbs
    have hat : G.Adj a t := triple_edge (hedge t htR) hab hbt
    exact hone a hac s hsR t htR hst has hat
  · have har : G.Adj a r := triple_edge (hedge r hrR) hab hbr
    have has : ¬ G.Adj a s := hone a hac r hrR s hsR hsr.symm har
    have hat : ¬ G.Adj a t := hone a hac r hrR t htR htr.symm har
    have hbs : G.Adj b s := by
      by_contra hbs
      exact has (triple_edge (hedge s hsR) hab hbs)
    have hbt : G.Adj b t := by
      by_contra hbt
      exact hat (triple_edge (hedge t htR) hab hbt)
    exact hone b hbc s hsR t htR hst hbs hbt

lemma crossing_or_center_of_large_neighborhood_filter
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (hfour : ∀ a b c d : V, G.Adj a b → G.Adj b c →
      G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (c : V) (A B R : Finset V)
    (hR : ∀ r ∈ R, G.Adj c r) (hcard : 3 ≤ R.card)
    (hsafe : ∀ S : Finset V,
      (∃ a ∈ A, a ∈ S) → (∃ b ∈ B, b ∈ S) → (∃ r ∈ R, r ∈ S) →
      edgePresent G S) :
    ∀ a ∈ A, ∀ b ∈ B, a = c ∨ b = c ∨ G.Adj a b := by
  have herased : ∀ a ∈ A.erase c, ∀ b ∈ B.erase c, G.Adj a b := by
    apply crossing_of_large_neighborhood_filter_without_overlap
      G hfour c (A.erase c) (B.erase c) R
      (Finset.notMem_erase _ _) (Finset.notMem_erase _ _) hR hcard
    intro S hAS hBS hRS
    obtain ⟨a, ha, haS⟩ := hAS
    obtain ⟨b, hb, hbS⟩ := hBS
    exact hsafe S ⟨a, Finset.mem_of_mem_erase ha, haS⟩
      ⟨b, Finset.mem_of_mem_erase hb, hbS⟩ hRS
  intro a ha b hb
  by_cases hac : a = c
  · exact Or.inl hac
  by_cases hbc : b = c
  · exact Or.inr (Or.inl hbc)
  exact Or.inr (Or.inr (herased a (Finset.mem_erase.mpr ⟨hac, ha⟩)
    b (Finset.mem_erase.mpr ⟨hbc, hb⟩)))

end RectangleNeighborhood


namespace PackingTransversal

lemma filter_loss_le_one {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) (a : α)
    (h : (S.filter (G.Adj a)).card ≤ 1) :
    S.card ≤ (S.filter (fun x => ¬ G.Adj a x)).card + 1 := by
  have hp := Finset.card_filter_add_card_filter_not (s := S) (p := G.Adj a)
  omega

lemma filter_local {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (S T : Finset α)
    (hST : S ⊆ T) (hT : ∀ w, (T.filter (G.Adj w)).card ≤ 1) :
    ∀ w, (S.filter (G.Adj w)).card ≤ 1 := by
  intro w
  exact (Finset.card_le_card (by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hST (Finset.mem_filter.mp hx).1,
      (Finset.mem_filter.mp hx).2⟩)).trans (hT w)

lemma insert_independent {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    (S : Finset α) (a : α)
    (hS : ∀ x ∈ S, ∀ y ∈ S, ¬ G.Adj x y)
    (ha : ∀ x ∈ S, ¬ G.Adj a x) :
    ∀ x ∈ insert a S, ∀ y ∈ insert a S, ¬ G.Adj x y := by
  intro x hx y hy hxy
  rcases Finset.mem_insert.mp hx with hxa | hxS
  · subst x
    rcases Finset.mem_insert.mp hy with hya | hyS
    · subst y
      exact G.irrefl hxy
    · exact ha y hyS hxy
  · rcases Finset.mem_insert.mp hy with hya | hyS
    · subst y
      exact ha x hxS hxy.symm
    · exact hS x hxS y hyS hxy

/-- A path through three different classes improves the greedy size threshold
  from the number of classes to one less, in a triangle-free graph. -/
lemma independent_hitting_set_of_three_class_path
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (U : Finset β) (A : β → Finset α)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → ¬ G.Adj z x)
    (hlocal : ∀ i ∈ U, ∀ w, ((A i).filter (G.Adj w)).card ≤ 1)
    (hsize : ∀ i ∈ U, U.card ≤ (A i).card + 1)
    (i j k : β) (hi : i ∈ U) (hj : j ∈ U) (hk : k ∈ U)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b c : α) (ha : a ∈ A i) (hb : b ∈ A j) (hc : c ∈ A k)
    (hac : G.Adj a c) (hbc : G.Adj b c) :
    ∃ R : Finset α, R.card ≤ U.card ∧ R ⊆ U.biUnion A ∧
      (∀ x ∈ R, ∀ y ∈ R, ¬ G.Adj x y) ∧
      (∀ l ∈ U, ∃ x ∈ R, x ∈ A l) := by
  classical
  let D := ((U.erase i).erase j).erase k
  have hj' : j ∈ U.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have hk' : k ∈ (U.erase i).erase j :=
    Finset.mem_erase.mpr ⟨hjk.symm, Finset.mem_erase.mpr ⟨hik.symm, hk⟩⟩
  have hDcard : D.card + 3 = U.card := by
    have h₁ := Finset.card_erase_add_one hi
    have h₂ := Finset.card_erase_add_one hj'
    have h₃ := Finset.card_erase_add_one hk'
    dsimp [D]
    omega
  have hDU : D ⊆ U := by
    intro l hl
    exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hl))
  let F := fun l => ((A l).filter (fun x => ¬ G.Adj a x)).filter (fun x => ¬ G.Adj b x)
  have hFsub (l : β) : F l ⊆ A l := by
    intro x hx
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hFlocal (l : β) (hl : l ∈ U) := filter_local G (F l) (A l) (hFsub l) (hlocal l hl)
  have hFsize (l : β) (hl : l ∈ U) : U.card ≤ (F l).card + 3 := by
    have h₁ := filter_loss_le_one G (A l) a (hlocal l hl a)
    have h₂ := filter_loss_le_one G ((A l).filter (fun x => ¬ G.Adj a x)) b
      (filter_local G _ (A l) (Finset.filter_subset _ _) (hlocal l hl) b)
    have h₃ := hsize l hl
    change _ ≤ (F l).card + 1 at h₂
    omega
  obtain ⟨R, hRcard, hRsub, hRind, hRhit⟩ := independent_hitting_set G D F
    (fun l hl => hFlocal l (hDU hl)) (by
      intro J hJ hJne
      obtain ⟨l, hl⟩ := hJne
      have hs := hFsize l (hDU (hJ hl))
      have hjd := Finset.card_le_card hJ
      exact ⟨l, hl, by omega⟩)
  have hcenter : A k \ {c} ⊆ F k := by
    intro x hx
    obtain ⟨hxk, hxc⟩ := Finset.mem_sdiff.mp hx
    have hxc' : x ≠ c := by simpa using hxc
    have hax : ¬ G.Adj a x := by
      intro hax
      exact hxc' ((Finset.card_le_one.mp (hlocal k hk a)) x
        (Finset.mem_filter.mpr ⟨hxk, hax⟩) c (Finset.mem_filter.mpr ⟨hc, hac⟩))
    have hbx : ¬ G.Adj b x := by
      intro hbx
      exact hxc' ((Finset.card_le_one.mp (hlocal k hk b)) x
        (Finset.mem_filter.mpr ⟨hxk, hbx⟩) c (Finset.mem_filter.mpr ⟨hc, hbc⟩))
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxk, hax⟩, hbx⟩
  have hcenter_size : U.card ≤ (F k).card + 2 := by
    have hs := Finset.card_le_card hcenter
    have he := Finset.card_erase_add_one hc
    have ht := hsize k hk
    have heq : A k \ {c} = (A k).erase c := by ext x; simp [and_comm]
    rw [heq] at hs
    omega
  let bad := R.biUnion (fun r => (F k).filter (G.Adj r))
  have hbad : bad.card ≤ R.card := by
    calc
      bad.card ≤ ∑ r ∈ R, ((F k).filter (G.Adj r)).card := Finset.card_biUnion_le
      _ ≤ ∑ r ∈ R, 1 := Finset.sum_le_sum (fun r hr => hFlocal k hk r)
      _ = R.card := by simp
  obtain ⟨d, hd, hdnot⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show bad.card < (F k).card by omega)
  have hdR : ∀ r ∈ R, ¬ G.Adj d r := by
    intro r hr hdr
    exact hdnot (Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_filter.mpr ⟨hd, hdr.symm⟩⟩)
  have hRavoid : ∀ r ∈ R, ¬ G.Adj a r ∧ ¬ G.Adj b r := by
    intro r hr
    obtain ⟨l, hl, hrl⟩ := Finset.mem_biUnion.mp (hRsub hr)
    exact ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hrl).1).2,
      (Finset.mem_filter.mp hrl).2⟩
  have had : ¬ G.Adj a d := (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2
  have hbd : ¬ G.Adj b d := (Finset.mem_filter.mp hd).2
  have hab : ¬ G.Adj a b := fun hab => htri a b c hab hbc hac.symm
  have h₁ := insert_independent G R d hRind hdR
  have h₂ := insert_independent G (insert d R) b h₁ (by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hbd
    · exact (hRavoid r hr).2)
  have h₃ := insert_independent G (insert b (insert d R)) a h₂ (by
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact hab
    · rcases Finset.mem_insert.mp hr with rfl | hr
      · exact had
      · exact (hRavoid r hr).1)
  refine ⟨insert a (insert b (insert d R)), ?_, ?_, h₃, ?_⟩
  · have h₁ := Finset.card_insert_le d R
    have h₂ := Finset.card_insert_le b (insert d R)
    have h₃ := Finset.card_insert_le a (insert b (insert d R))
    omega
  · intro r hr
    simp only [Finset.mem_insert] at hr
    rcases hr with rfl | rfl | rfl | hr
    · exact Finset.mem_biUnion.mpr ⟨i, hi, ha⟩
    · exact Finset.mem_biUnion.mpr ⟨j, hj, hb⟩
    · exact Finset.mem_biUnion.mpr ⟨k, hk, hFsub k hd⟩
    · obtain ⟨l, hl, hrl⟩ := Finset.mem_biUnion.mp (hRsub hr)
      exact Finset.mem_biUnion.mpr ⟨l, hDU hl, hFsub l hrl⟩
  · intro l hl
    by_cases hli : l = i
    · subst l
      exact ⟨a, by simp, ha⟩
    by_cases hlj : l = j
    · subst l
      exact ⟨b, by simp, hb⟩
    by_cases hlk : l = k
    · subst l
      exact ⟨d, by simp, hFsub k hd⟩
    have hld : l ∈ D := by simp [D, hli, hlj, hlk, hl]
    obtain ⟨r, hr, hrl⟩ := hRhit l hld
    exact ⟨r, by simp [hr], hFsub l hrl⟩

end PackingTransversal

namespace PackingTransversal

def HasThreeClassPath {α β : Type*} (G : SimpleGraph α)
    (U : Finset β) (A : β → Finset α) : Prop :=
  ∃ i ∈ U, ∃ j ∈ U, ∃ k ∈ U, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
    ∃ a ∈ A i, ∃ b ∈ A j, ∃ c ∈ A k, G.Adj a c ∧ G.Adj b c

def classLiftGraph {α β : Type*} (G : SimpleGraph α)
    (U : Finset β) (A : β → Finset α) : SimpleGraph (β × α) where
  Adj p q := p.1 ∈ U ∧ p.2 ∈ A p.1 ∧ q.1 ∈ U ∧ q.2 ∈ A q.1 ∧ G.Adj p.2 q.2
  symm := by
    constructor
    intro p q h
    exact ⟨h.2.2.1, h.2.2.2.1, h.1, h.2.1, h.2.2.2.2.symm⟩
  loopless := by
    constructor
    intro p h
    exact G.irrefl h.2.2.2.2

def classLiftSet {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : β → Finset α) (i : β) : Finset (β × α) :=
  (A i).image (fun a => (i, a))

lemma classLiftSet_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : β → Finset α) (i : β) : (classLiftSet A i).card = (A i).card :=
  Finset.card_image_of_injective _ (fun _a _b h => congrArg Prod.snd h)

lemma classLiftSet_disjoint {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : β → Finset α) {i j : β} (hij : i ≠ j) :
    Disjoint (classLiftSet A i) (classLiftSet A j) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨b, hb, he⟩ := Finset.mem_image.mp hq
  exact hij (congrArg Prod.fst he).symm

lemma classLiftGraph_local {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (U : Finset β) (A : β → Finset α)
    [DecidableRel (classLiftGraph G U A).Adj]
    (hlocal : ∀ i ∈ U, ∀ w, ((A i).filter (G.Adj w)).card ≤ 1) :
    ∀ i ∈ U, ∀ w, ((classLiftSet A i).filter ((classLiftGraph G U A).Adj w)).card ≤ 1 := by
  intro i hi w
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨hp, hwp⟩ := Finset.mem_filter.mp hp
  obtain ⟨hq, hwq⟩ := Finset.mem_filter.mp hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
  have hab := Finset.card_le_one.mp (hlocal i hi w.2) a
    (Finset.mem_filter.mpr ⟨ha, hwp.2.2.2.2⟩) b
    (Finset.mem_filter.mpr ⟨hb, hwq.2.2.2.2⟩)
  exact congrArg (fun x => (i, x)) hab

lemma classLiftGraph_degree_one {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (U : Finset β) (A : β → Finset α)
    (hlocal : ∀ i ∈ U, ∀ w, ((A i).filter (G.Adj w)).card ≤ 1)
    (hind : ∀ i ∈ U, ∀ a ∈ A i, ∀ b ∈ A i, ¬ G.Adj a b)
    (hnopath : ¬ HasThreeClassPath G U A) :
    ∀ p q r, (classLiftGraph G U A).Adj p q →
      (classLiftGraph G U A).Adj p r → q = r := by
  rintro ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ hpq hpr
  obtain ⟨hi, ha, hj, hb, hab⟩ := hpq
  obtain ⟨_, _, hk, hc, hac⟩ := hpr
  by_cases hjk : j = k
  · subst k
    have hbc := Finset.card_le_one.mp (hlocal j hj a) b
      (Finset.mem_filter.mpr ⟨hb, hab⟩) c (Finset.mem_filter.mpr ⟨hc, hac⟩)
    subst c
    rfl
  · have hji : j ≠ i := by
      intro hji
      subst j
      exact hind i hi a ha b hb hab
    have hki : k ≠ i := by
      intro hki
      subst k
      exact hind i hi a ha c hc hac
    exact (hnopath ⟨j, hj, k, hk, i, hi, hjk, hji, hki,
      b, hb, c, hc, a, ha, hab.symm, hac.symm⟩).elim

end PackingTransversal

namespace MatchingCompletion

lemma independent_insert {α : Type*} [DecidableEq α]
    (G : SimpleGraph α) (R : Finset α) (a : α)
    (hR : ∀ x ∈ R, ∀ y ∈ R, ¬G.Adj x y)
    (ha : ∀ r ∈ R, ¬G.Adj a r) :
    ∀ x ∈ insert a R, ∀ y ∈ insert a R, ¬G.Adj x y := by
  intro x hx y hy
  simp only [Finset.mem_insert] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · subst x; subst y
    exact G.irrefl
  · subst x
    exact ha y hy
  · subst y
    exact fun h => ha x hx h.symm
  · exact hR x hx y hy

lemma matching_completion {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) (U : Finset β) (A : β → Finset α)
    (hdegree : ∀ a b c, G.Adj a b → G.Adj a c → b = c)
    (hdisjoint : ∀ i ∈ U, ∀ j ∈ U, i ≠ j → Disjoint (A i) (A j))
    (hlarge : ∀ i ∈ U, U.card - 1 ≤ (A i).card)
    (hk : 3 ≤ U.card)
    (z : β) (hz : z ∈ U) (R : Finset α)
    (hRcard : R.card ≤ U.card - 1)
    (hRsub : R ⊆ (U.erase z).biUnion A)
    (hRind : ∀ a ∈ R, ∀ b ∈ R, ¬G.Adj a b)
    (hRhit : ∀ i ∈ U.erase z, ∃ a ∈ R, a ∈ A i) :
    ∃ S : Finset α, S.card ≤ U.card ∧ S ⊆ U.biUnion A ∧
      (∀ a ∈ S, ∀ b ∈ S, ¬G.Adj a b) ∧
      (∀ i ∈ U, ∃ a ∈ S, a ∈ A i) := by
  classical
  have oldSub : R ⊆ U.biUnion A := by
    intro r hr
    obtain ⟨i, hi, hri⟩ := Finset.mem_biUnion.mp (hRsub hr)
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_of_mem_erase hi, hri⟩
  by_cases free : ∃ a ∈ A z, ∀ r ∈ R, ¬G.Adj a r
  · obtain ⟨a, ha, hfree⟩ := free
    refine ⟨insert a R, ?_, ?_, independent_insert G R a hRind hfree, ?_⟩
    · have := Finset.card_insert_le a R
      omega
    · intro r hr
      rcases Finset.mem_insert.mp hr with hr | hr
      · subst r
        exact Finset.mem_biUnion.mpr ⟨z, hz, ha⟩
      · exact oldSub hr
    · intro i hi
      by_cases hiz : i = z
      · subst i
        exact ⟨a, Finset.mem_insert_self _ _, ha⟩
      · obtain ⟨r, hr, hri⟩ := hRhit i (Finset.mem_erase.mpr ⟨hiz, hi⟩)
        exact ⟨r, Finset.mem_insert_of_mem hr, hri⟩
  · push Not at free
    have chosen : ∀ a : {x // x ∈ A z}, ∃ r ∈ R, G.Adj a.val r := by
      intro a
      exact free a.val a.property
    choose f hf hfa using chosen
    have inj : Function.Injective f := by
      intro a b heq
      apply Subtype.ext
      apply hdegree (f a) a.val b.val
      · exact (hfa a).symm
      · simpa only [heq] using (hfa b).symm
    let T : Finset α := (A z).attach.image f
    have hTcard : T.card = (A z).card := by
      simp only [T, Finset.card_image_of_injective _ inj, Finset.card_attach]
    have hTsub : T ⊆ R := by
      intro r hr
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hr
      exact hf a
    have hTeq : T = R := by
      apply Finset.eq_of_subset_of_card_le hTsub
      rw [hTcard]
      exact hRcard.trans (hlarge z hz)
    have matched : ∀ r ∈ R, ∃ a ∈ A z, G.Adj r a := by
      intro r hr
      rw [← hTeq] at hr
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hr
      exact ⟨a.val, a.property, (hfa a).symm⟩
    have hzcard : 0 < (A z).card := by
      have := hlarge z hz
      omega
    obtain ⟨a0, ha0⟩ := Finset.card_pos.mp hzcard
    obtain ⟨r0, hr0, har⟩ := free a0 ha0
    obtain ⟨i, hi, hr0i⟩ := Finset.mem_biUnion.mp (hRsub hr0)
    have hiU : i ∈ U := Finset.mem_of_mem_erase hi
    have hiz : i ≠ z := (Finset.mem_erase.mp hi).1
    have hicard : 2 ≤ (A i).card := by
      have := hlarge i hiU
      omega
    have other : ∃ b ∈ A i, b ≠ r0 := by
      by_contra hn
      have hs : A i ⊆ {r0} := by
        intro b hb
        have he : b = r0 := by
          by_contra hne
          exact hn ⟨b, hb, hne⟩
        simp only [Finset.mem_singleton, he]
      have := Finset.card_le_card hs
      simp only [Finset.card_singleton] at this
      omega
    obtain ⟨b, hb, hbne⟩ := other
    have hbnot : b ∉ A z := by
      exact fun h => Finset.disjoint_left.mp (hdisjoint i hiU z hz hiz) hb h
    have hbfree : ∀ r ∈ R, ¬G.Adj b r := by
      intro r hr hbr
      obtain ⟨a, ha, hra⟩ := matched r hr
      have he : b = a := hdegree r b a hbr.symm hra
      exact hbnot (he.symm ▸ ha)
    have hafree : ∀ r ∈ R.erase r0, ¬G.Adj a0 r := by
      intro r hr hadj
      exact (Finset.mem_erase.mp hr).1 (hdegree a0 r r0 hadj har)
    have hab : ¬G.Adj a0 b := by
      intro hadj
      exact hbne (hdegree a0 b r0 hadj har)
    have herase : ∀ x ∈ R.erase r0, ∀ y ∈ R.erase r0, ¬G.Adj x y := by
      intro x hx y hy
      exact hRind x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)
    have hbind := independent_insert G (R.erase r0) b herase
      (fun r hr => hbfree r (Finset.mem_of_mem_erase hr))
    have hafree' : ∀ r ∈ insert b (R.erase r0), ¬G.Adj a0 r := by
      intro r hr
      rcases Finset.mem_insert.mp hr with hr | hr
      · subst r
        exact hab
      · exact hafree r hr
    refine ⟨insert a0 (insert b (R.erase r0)), ?_, ?_,
      independent_insert G _ a0 hbind hafree', ?_⟩
    · have h1 := Finset.card_insert_le a0 (insert b (R.erase r0))
      have h2 := Finset.card_insert_le b (R.erase r0)
      have h3 := Finset.card_erase_add_one hr0
      omega
    · intro r hr
      rcases Finset.mem_insert.mp hr with hr | hr
      · subst r
        exact Finset.mem_biUnion.mpr ⟨z, hz, ha0⟩
      · rcases Finset.mem_insert.mp hr with hr | hr
        · subst r
          exact Finset.mem_biUnion.mpr ⟨i, hiU, hb⟩
        · exact oldSub (Finset.mem_of_mem_erase hr)
    · intro j hj
      by_cases hjz : j = z
      · subst j
        exact ⟨a0, Finset.mem_insert_self _ _, ha0⟩
      · by_cases hji : j = i
        · subst j
          exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), hb⟩
        · obtain ⟨r, hr, hrj⟩ := hRhit j (Finset.mem_erase.mpr ⟨hjz, hj⟩)
          have hrne : r ≠ r0 := by
            intro he
            exact Finset.disjoint_left.mp (hdisjoint i hiU j hj (Ne.symm hji))
              hr0i (he ▸ hrj)
          exact ⟨r, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨hrne, hr⟩)), hrj⟩

end MatchingCompletion

namespace PackingTransversal

/-- Triangle-free packing classes of size at least one less than their number
  have an independent hitting set, when there are at least three classes. -/
lemma independent_hitting_set_triangle_free
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) [DecidableRel G.Adj]
    (U : Finset β) (A : β → Finset α)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → ¬ G.Adj z x)
    (hlocal : ∀ i ∈ U, ∀ w, ((A i).filter (G.Adj w)).card ≤ 1)
    (hind : ∀ i ∈ U, ∀ a ∈ A i, ∀ b ∈ A i, ¬ G.Adj a b)
    (hsize : ∀ i ∈ U, U.card ≤ (A i).card + 1)
    (hcount : 3 ≤ U.card) :
    ∃ R : Finset α, R.card ≤ U.card ∧ R ⊆ U.biUnion A ∧
      (∀ x ∈ R, ∀ y ∈ R, ¬ G.Adj x y) ∧
      (∀ i ∈ U, ∃ x ∈ R, x ∈ A i) := by
  classical
  by_cases hpath : HasThreeClassPath G U A
  · obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk, a, ha, b, hb, c, hc, hac, hbc⟩ := hpath
    exact independent_hitting_set_of_three_class_path G U A htri hlocal hsize
      i j k hi hj hk hij hik hjk a b c ha hb hc hac hbc
  · let H := classLiftGraph G U A
    let B := classLiftSet A
    have hdegree := classLiftGraph_degree_one G U A hlocal hind hpath
    have hloc : ∀ i ∈ U, ∀ w, ((B i).filter (H.Adj w)).card ≤ 1 :=
      classLiftGraph_local G U A hlocal
    have hcard : ∀ i ∈ U, U.card - 1 ≤ (B i).card := by
      intro i hi
      change U.card - 1 ≤ (classLiftSet A i).card
      rw [classLiftSet_card]
      have := hsize i hi
      omega
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < U.card by omega)
    have herase : (U.erase z).card + 1 = U.card := Finset.card_erase_add_one hz
    obtain ⟨R, hRcard, hRsub, hRind, hRhit⟩ := independent_hitting_set H (U.erase z) B
      (fun i hi => hloc i (Finset.mem_of_mem_erase hi)) (by
        intro J hJ hne
        obtain ⟨i, hi⟩ := hne
        have hs := hcard i (Finset.mem_of_mem_erase (hJ hi))
        have hjc := Finset.card_le_card hJ
        exact ⟨i, hi, by omega⟩)
    obtain ⟨S, hScard, hSsub, hSind, hShit⟩ :=
      PEqualNP.Outside.L_meta_1904_aux.MatchingCompletion.matching_completion H U B hdegree
        (fun i hi j hj hij => classLiftSet_disjoint A hij) hcard hcount z hz R
        (by omega) hRsub hRind hRhit
    have hactive (p : β × α) (hp : p ∈ S) : p.1 ∈ U ∧ p.2 ∈ A p.1 := by
      obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp (hSsub hp)
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hpi
      exact ⟨hi, ha⟩
    refine ⟨S.image Prod.snd, (Finset.card_image_le).trans hScard, ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_biUnion.mpr ⟨p.1, (hactive p hp).1, (hactive p hp).2⟩
    · intro a ha b hb hab
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hb
      exact hSind p hp q hq ⟨(hactive p hp).1, (hactive p hp).2,
        (hactive q hq).1, (hactive q hq).2, hab⟩
    · intro i hi
      obtain ⟨p, hp, hpi⟩ := hShit i hi
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hpi
      exact ⟨a, Finset.mem_image.mpr ⟨(i, a), hp, rfl⟩, ha⟩

end PackingTransversal

namespace WeightedEquality

def weight {α ι : Type*} [DecidableEq α] (B : ι → Finset α) (v : α) (i : ι) : ℚ :=
  if v ∈ B i then 1 / (B i).card else 0

lemma weight_nonneg {α ι : Type*} [DecidableEq α]
    (B : ι → Finset α) (v : α) (i : ι) : 0 ≤ weight B v i := by
  dsimp only [weight]
  split_ifs
  · positivity
  · exact le_rfl

lemma weight_pos {α ι : Type*} [DecidableEq α]
    (B : ι → Finset α) (v : α) (i : ι) (hv : v ∈ B i) : 0 < weight B v i := by
  have hpos : (0 : ℚ) < (B i).card := by
    exact_mod_cast (Finset.card_pos.mpr ⟨v, hv⟩)
  dsimp only [weight]
  rw [ite_eq_left hv]
  exact one_div_pos.mpr hpos

lemma column_le_one {α ι : Type*} [DecidableEq α]
    (V : Finset α) (B : ι → Finset α) (i : ι) :
    (∑ v ∈ V, weight B v i) ≤ 1 := by
  simp only [weight, Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul]
  by_cases empty : (B i).card = 0
  · simp [empty]
  · have nz : ((B i).card : ℚ) ≠ 0 := by exact_mod_cast empty
    calc
      ((V ∩ B i).card : ℚ) * (1 / (B i).card) ≤
          ((B i).card : ℚ) * (1 / (B i).card) := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : V ∩ B i ⊆ B i)
        · positivity
      _ = 1 := by field_simp

lemma row_eq_one_of_card_eq {α ι : Type*} [DecidableEq α]
    (V : Finset α) (U : Finset ι) (B : ι → Finset α)
    (hrow : ∀ v ∈ V, 1 ≤ ∑ i ∈ U, weight B v i)
    (heq : V.card = U.card) :
    ∀ v ∈ V, (∑ i ∈ U, weight B v i) = 1 := by
  have htotal : (∑ v ∈ V, ∑ i ∈ U, weight B v i) ≤ (V.card : ℚ) := by
    calc
      (∑ v ∈ V, ∑ i ∈ U, weight B v i) =
          ∑ i ∈ U, ∑ v ∈ V, weight B v i := Finset.sum_comm
      _ ≤ ∑ _i ∈ U, (1 : ℚ) := Finset.sum_le_sum (fun i _ => column_le_one V B i)
      _ = V.card := by simp [heq]
  intro v hv
  apply le_antisymm _ (hrow v hv)
  by_contra hnot
  have hlt : (1 : ℚ) < ∑ i ∈ U, weight B v i := lt_of_not_ge hnot
  have hsum := Finset.sum_lt_sum hrow ⟨v, hv, hlt⟩
  have hstrict : (V.card : ℚ) < ∑ v ∈ V, ∑ i ∈ U, weight B v i := by
    simpa using hsum
  exact (not_lt_of_ge htotal) hstrict

lemma block_lower_bound {α ι : Type*} [DecidableEq α]
    (B : ι → Finset α) (v : α) (J : Finset ι) (hJ : J.Nonempty)
    (hJi : ∀ i ∈ J, v ∈ B i ∧ (B i).card ≤ J.card) :
    1 ≤ ∑ i ∈ J, weight B v i := by
  have hposJ : (0 : ℚ) < J.card := by exact_mod_cast hJ.card_pos
  calc
    (1 : ℚ) = ∑ i ∈ J, (1 : ℚ) / J.card := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp
    _ ≤ ∑ i ∈ J, weight B v i := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hvi, hc⟩ := hJi i hi
      have hpos : (0 : ℚ) < (B i).card := by
        exact_mod_cast (Finset.card_pos.mpr ⟨v, hvi⟩)
      dsimp only [weight]
      rw [ite_eq_left hvi]
      exact one_div_le_one_div_of_le hpos (by exact_mod_cast hc)

lemma row_ge_one_of_block {α ι : Type*} [DecidableEq α]
    (U J : Finset ι) (B : ι → Finset α) (v : α)
    (hJ : J.Nonempty) (hJU : J ⊆ U)
    (hJi : ∀ i ∈ J, v ∈ B i ∧ (B i).card ≤ J.card) :
    1 ≤ ∑ i ∈ U, weight B v i := by
  exact le_trans (block_lower_bound B v J hJ hJi)
    (Finset.sum_le_sum_of_subset_of_nonneg hJU (fun i _ _ => weight_nonneg B v i))

lemma block_saturation {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U J : Finset ι) (B : ι → Finset α) (v : α)
    (hrow : (∑ i ∈ U, weight B v i) = 1)
    (hJ : J.Nonempty) (hJU : J ⊆ U)
    (hJi : ∀ i ∈ J, v ∈ B i ∧ (B i).card ≤ J.card) :
    J = U.filter (fun i => v ∈ B i) ∧ ∀ i ∈ J, (B i).card = J.card := by
  have hsumJ : (∑ i ∈ J, weight B v i) = 1 := by
    apply le_antisymm _ (block_lower_bound B v J hJ hJi)
    calc
      (∑ i ∈ J, weight B v i) ≤ ∑ i ∈ U, weight B v i :=
        Finset.sum_le_sum_of_subset_of_nonneg hJU (fun i _ _ => weight_nonneg B v i)
      _ = 1 := hrow
  constructor
  · apply Finset.Subset.antisymm
    · intro i hi
      exact Finset.mem_filter.mpr ⟨hJU hi, (hJi i hi).1⟩
    · intro i hi
      obtain ⟨hiU, hvi⟩ := Finset.mem_filter.mp hi
      by_contra hiJ
      have hsub : insert i J ⊆ U := by
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact hiU
        · exact hJU hj
      have hbound := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun j _ _ => weight_nonneg B v j)
      rw [Finset.sum_insert hiJ, hsumJ, hrow] at hbound
      have hpos := weight_pos B v i hvi
      linarith
  · intro i hi
    apply le_antisymm (hJi i hi).2
    by_contra hnot
    have hlt : (B i).card < J.card := Nat.lt_of_not_ge hnot
    have hposJ : (0 : ℚ) < J.card := by exact_mod_cast hJ.card_pos
    have hconst : (∑ _j ∈ J, (1 : ℚ) / J.card) = 1 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      field_simp
    have hterms : ∀ j ∈ J, (1 : ℚ) / J.card ≤ weight B v j := by
      intro j hj
      have hvj := (hJi j hj).1
      have hpos : (0 : ℚ) < (B j).card := by
        exact_mod_cast (Finset.card_pos.mpr ⟨v, hvj⟩)
      dsimp only [weight]
      rw [ite_eq_left hvj]
      exact one_div_le_one_div_of_le hpos (by exact_mod_cast (hJi j hj).2)
    have hstrict : (1 : ℚ) / J.card < weight B v i := by
      have hvi := (hJi i hi).1
      have hpos : (0 : ℚ) < (B i).card := by
        exact_mod_cast (Finset.card_pos.mpr ⟨v, hvi⟩)
      dsimp only [weight]
      rw [ite_eq_left hvi]
      exact one_div_lt_one_div_of_lt hpos (by exact_mod_cast hlt)
    have hsum := Finset.sum_lt_sum hterms ⟨i, hi, hstrict⟩
    rw [hconst, hsumJ] at hsum
    exact (lt_irrefl (1 : ℚ)) hsum

lemma uniform_incidence_of_card_eq {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (V : Finset α) (U : Finset ι) (B : ι → Finset α)
    (hblocks : ∀ v ∈ V, ∃ J : Finset ι, J.Nonempty ∧ J ⊆ U ∧
      ∀ i ∈ J, v ∈ B i ∧ (B i).card ≤ J.card)
    (heq : V.card = U.card) :
    ∀ v ∈ V, (U.filter (fun i => v ∈ B i)).Nonempty ∧
      ∀ i ∈ U.filter (fun i => v ∈ B i),
        (B i).card = (U.filter (fun i => v ∈ B i)).card := by
  have hrow : ∀ v ∈ V, 1 ≤ ∑ i ∈ U, weight B v i := by
    intro v hv
    obtain ⟨J, hJ, hJU, hJi⟩ := hblocks v hv
    exact row_ge_one_of_block U J B v hJ hJU hJi
  intro v hv
  obtain ⟨J, hJ, hJU, hJi⟩ := hblocks v hv
  obtain ⟨hJW, hcards⟩ := block_saturation U J B v
    (row_eq_one_of_card_eq V U B hrow heq v hv) hJ hJU hJi
  subst J
  exact ⟨hJ, hcards⟩

lemma large_source_has_uniform_incidence {α ι : Type*}
    [DecidableEq α] [DecidableEq ι]
    (V : Finset α) (U : Finset ι) (B : ι → Finset α)
    (hsub : ∀ i ∈ U, B i ⊆ V)
    (hblocks : ∀ v ∈ V, ∃ J : Finset ι, J.Nonempty ∧ J ⊆ U ∧
      ∀ i ∈ J, v ∈ B i ∧ (B i).card ≤ J.card)
    (heq : V.card = U.card) {i : ι} (hi : i ∈ U) (hlarge : 3 ≤ (B i).card) :
    ∃ v ∈ V, 3 ≤ (U.filter (fun j => v ∈ B j)).card ∧
      ∀ j ∈ U.filter (fun j => v ∈ B j),
        (B j).card = (U.filter (fun j => v ∈ B j)).card := by
  obtain ⟨v, hvi⟩ := Finset.card_pos.mp (show 0 < (B i).card by omega)
  have hv : v ∈ V := hsub i hi hvi
  have hc := (uniform_incidence_of_card_eq V U B hblocks heq v hv).2
  refine ⟨v, hv, ?_, hc⟩
  rw [← hc i (Finset.mem_filter.mpr ⟨hi, hvi⟩)]
  exact hlarge

lemma supports_card_le_two_of_no_large_uniform_incidence {α ι : Type*}
    [DecidableEq α] [DecidableEq ι]
    (V : Finset α) (U : Finset ι) (B : ι → Finset α)
    (hsub : ∀ i ∈ U, B i ⊆ V)
    (hblocks : ∀ v ∈ V, ∃ J : Finset ι, J.Nonempty ∧ J ⊆ U ∧
      ∀ i ∈ J, v ∈ B i ∧ (B i).card ≤ J.card)
    (heq : V.card = U.card)
    (hno : ∀ v ∈ V, ¬ (3 ≤ (U.filter (fun j => v ∈ B j)).card ∧
      ∀ j ∈ U.filter (fun j => v ∈ B j),
        (B j).card = (U.filter (fun j => v ∈ B j)).card)) :
    ∀ i ∈ U, (B i).card ≤ 2 := by
  intro i hi
  by_contra hnot
  obtain ⟨v, hv, hlarge, hcards⟩ :=
    large_source_has_uniform_incidence V U B hsub hblocks heq hi (by omega)
  exact hno v hv ⟨hlarge, hcards⟩

end WeightedEquality

namespace PackingSources

lemma no_large_uniform_incidence {n : ℕ} {I : Type} [DecidableEq I]
    (G : SimpleGraph (Fin n)) (B : I → Finset (Fin n)) (U : Finset I)
    (v : Fin n) (hne : ∃ w, G.Adj v w)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → ¬ G.Adj z x)
    (hind : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, ¬ G.Adj a b)
    (hpacking : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    (hagree : ∀ x y : Fin n → Bool,
      (∀ i ∈ U, SignalAgreement.clause (B i) x ↔
        SignalAgreement.clause (B i) y) →
      SignalAgreement.hit G x → SignalAgreement.hit G y) :
    ¬ (3 ≤ (U.filter (fun j => v ∈ B j)).card ∧
      ∀ j ∈ U.filter (fun j => v ∈ B j),
        (B j).card = (U.filter (fun j => v ∈ B j)).card) := by
  classical
  let W : Finset I := U.filter (fun i => v ∈ B i)
  let A : I → Finset (Fin n) := fun i => (B i).erase v
  rintro ⟨hcount, hcards⟩
  have hlocal : ∀ i ∈ W, ∀ w, ((A i).filter (G.Adj w)).card ≤ 1 := by
    intro i hi w
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have hai := (Finset.mem_filter.mp ha).1
    have hbi := (Finset.mem_filter.mp hb).1
    by_contra hab
    exact hpacking i (Finset.mem_filter.mp hi).1 a (Finset.mem_of_mem_erase hai)
      b (Finset.mem_of_mem_erase hbi) hab w
      ⟨(Finset.mem_filter.mp ha).2.symm, (Finset.mem_filter.mp hb).2.symm⟩
  have hAi : ∀ i ∈ W, ∀ a ∈ A i, ∀ b ∈ A i, ¬ G.Adj a b := by
    intro i hi a ha b hb
    exact hind i (Finset.mem_filter.mp hi).1 a (Finset.mem_of_mem_erase ha)
      b (Finset.mem_of_mem_erase hb)
  have hsize : ∀ i ∈ W, W.card ≤ (A i).card + 1 := by
    intro i hi
    have he := Finset.card_erase_add_one (Finset.mem_filter.mp hi).2
    have hc := hcards i hi
    change W.card ≤ ((B i).erase v).card + 1
    change (B i).card = W.card at hc
    omega
  obtain ⟨R, hRc, hRU, hRI, hhit⟩ :=
    PackingTransversal.independent_hitting_set_triangle_free G W A htri hlocal hAi hsize hcount
  have hreplace : ∀ i ∈ U, v ∈ B i → ∃ a ∈ B i, a ∈ R := by
    intro i hi hvi
    obtain ⟨a, haR, haA⟩ := hhit i (Finset.mem_filter.mpr ⟨hi, hvi⟩)
    exact ⟨a, Finset.mem_of_mem_erase haA, haR⟩
  have hremote : ∀ a ∈ R, ∀ w, ¬ (G.Adj v w ∧ G.Adj a w) := by
    intro a ha w
    obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp (hRU ha)
    have hiU := (Finset.mem_filter.mp hi).1
    have hvi := (Finset.mem_filter.mp hi).2
    have hai' := Finset.mem_erase.mp hai
    exact hpacking i hiU v hvi a hai'.2 hai'.1.symm w
  obtain ⟨a, ha, b, hb, hab⟩ :=
    SignalAgreement.replacement_support_has_edge G B U v R hne hreplace hremote hagree
  exact hRI a ha b hb hab

lemma equality_forces_singletons_or_pairs {n : ℕ} {I : Type} [DecidableEq I]
    (G : SimpleGraph (Fin n)) (B : I → Finset (Fin n)) (U : Finset I)
    (hne : ∀ v, ∃ w, G.Adj v w)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → ¬ G.Adj z x)
    (hind : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, ¬ G.Adj a b)
    (hpacking : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    (hagree : ∀ x y : Fin n → Bool,
      (∀ i ∈ U, SignalAgreement.clause (B i) x ↔
        SignalAgreement.clause (B i) y) →
      SignalAgreement.hit G x → SignalAgreement.hit G y)
    (heq : n = U.card) :
    ∀ i ∈ U, (B i).card ≤ 2 := by
  classical
  apply WeightedEquality.supports_card_le_two_of_no_large_uniform_incidence
    (Finset.univ : Finset (Fin n)) U B
    (by intros; exact Finset.subset_univ _)
    (fun v _ => small_subfamily_of_essential_vertex G B U v (hne v) hpacking hagree)
    (by simpa using heq)
  intro v hv
  exact no_large_uniform_incidence G B U v (hne v) htri hind hpacking hagree

lemma large_clause_forces_extra_source {n : ℕ} {I : Type} [DecidableEq I]
    (G : SimpleGraph (Fin n)) (B : I → Finset (Fin n)) (U : Finset I)
    (hne : ∀ v, ∃ w, G.Adj v w)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → ¬ G.Adj z x)
    (hind : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, ¬ G.Adj a b)
    (hpacking : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    (hagree : ∀ x y : Fin n → Bool,
      (∀ i ∈ U, SignalAgreement.clause (B i) x ↔
        SignalAgreement.clause (B i) y) →
      SignalAgreement.hit G x → SignalAgreement.hit G y)
    (hlarge : ∃ i ∈ U, 3 ≤ (B i).card) :
    n + 1 ≤ U.card := by
  have hle := card_le_used_packing_sources G B U hne hpacking hagree
  have hnequ : n ≠ U.card := by
    intro heq
    obtain ⟨i, hi, hci⟩ := hlarge
    have hsmall := equality_forces_singletons_or_pairs G B U hne htri hind hpacking hagree heq i hi
    omega
  omega

end PackingSources


namespace ReadOnceExchange

open PEqualNP.MetaComplexity

def vars {n : ℕ} : DMFormula n → Finset (Fin n)
  | .lit i _ => {i}
  | .and φ ψ => vars φ ∪ vars ψ
  | .or φ ψ => vars φ ∪ vars ψ

def PositiveReadOnce {n : ℕ} : DMFormula n → Prop
  | .lit _ b => b = true
  | .and φ ψ => PositiveReadOnce φ ∧ PositiveReadOnce ψ ∧ Disjoint (vars φ) (vars ψ)
  | .or φ ψ => PositiveReadOnce φ ∧ PositiveReadOnce ψ ∧ Disjoint (vars φ) (vars ψ)

def IsTerm {n : ℕ} : DMFormula n → Finset (Fin n) → Prop
  | .lit i b, S => b = true ∧ S = {i}
  | .and φ ψ, S => ∃ A B, IsTerm φ A ∧ IsTerm ψ B ∧ S = A ∪ B
  | .or φ ψ, S => IsTerm φ S ∨ IsTerm ψ S

def evalSet {n : ℕ} (φ : DMFormula n) (S : Finset (Fin n)) : Bool :=
  φ.eval (fun i => decide (i ∈ S))

def IsMinterm {α : Type*} (f : Finset α → Bool) (M : Finset α) : Prop :=
  f M = true ∧ ∀ T ⊆ M, f T = true → M ⊆ T

lemma term_subset_vars {n : ℕ} {φ : DMFormula n} {S : Finset (Fin n)}
    (hS : IsTerm φ S) : S ⊆ vars φ := by
  induction φ generalizing S with
  | lit i b => rcases hS with ⟨_, rfl⟩; exact Finset.Subset.rfl
  | and φ ψ ihφ ihψ =>
      obtain ⟨A, B, hA, hB, rfl⟩ := hS
      exact Finset.union_subset_union (ihφ hA) (ihψ hB)
  | or φ ψ ihφ ihψ =>
      rcases hS with hS | hS
      · exact (ihφ hS).trans Finset.subset_union_left
      · exact (ihψ hS).trans Finset.subset_union_right

lemma term_nonempty {n : ℕ} {φ : DMFormula n} {S : Finset (Fin n)}
    (hS : IsTerm φ S) : S.Nonempty := by
  induction φ generalizing S with
  | lit i b => rcases hS with ⟨_, rfl⟩; exact Finset.singleton_nonempty i
  | and φ ψ ihφ ihψ =>
      obtain ⟨A, B, hA, hB, rfl⟩ := hS
      exact (ihφ hA).mono Finset.subset_union_left
  | or φ ψ ihφ ihψ =>
      rcases hS with hS | hS
      · exact ihφ hS
      · exact ihψ hS

lemma term_true {n : ℕ} {φ : DMFormula n} {T S : Finset (Fin n)}
    (hT : IsTerm φ T) (hTS : T ⊆ S) : evalSet φ S = true := by
  induction φ generalizing T with
  | lit i b =>
      obtain ⟨rfl, rfl⟩ := hT
      have hi := hTS (Finset.mem_singleton_self i)
      simpa [evalSet, DMFormula.eval] using hi
  | and φ ψ ihφ ihψ =>
      obtain ⟨A, B, hA, hB, rfl⟩ := hT
      exact Bool.and_eq_true_iff.mpr ⟨ihφ hA (Finset.subset_union_left.trans hTS),
        ihψ hB (Finset.subset_union_right.trans hTS)⟩
  | or φ ψ ihφ ihψ =>
      rcases hT with hT | hT
      · exact Bool.or_eq_true_iff.mpr (Or.inl (ihφ hT hTS))
      · exact Bool.or_eq_true_iff.mpr (Or.inr (ihψ hT hTS))

lemma eval_has_term {n : ℕ} {φ : DMFormula n} (hRO : PositiveReadOnce φ)
    {S : Finset (Fin n)} (hS : evalSet φ S = true) :
    ∃ T, IsTerm φ T ∧ T ⊆ S := by
  induction φ with
  | lit i b =>
      change b = true at hRO
      subst b
      have hi : i ∈ S := by simpa [evalSet, DMFormula.eval] using hS
      exact ⟨{i}, ⟨rfl, rfl⟩, Finset.singleton_subset_iff.mpr hi⟩
  | and φ ψ ihφ ihψ =>
      obtain ⟨hφ, hψ⟩ := Bool.and_eq_true_iff.mp hS
      obtain ⟨A, hA, hAS⟩ := ihφ hRO.1 hφ
      obtain ⟨B, hB, hBS⟩ := ihψ hRO.2.1 hψ
      exact ⟨A ∪ B, ⟨A, B, hA, hB, rfl⟩, Finset.union_subset hAS hBS⟩
  | or φ ψ ihφ ihψ =>
      rcases Bool.or_eq_true_iff.mp hS with hφ | hψ
      · obtain ⟨A, hA, hAS⟩ := ihφ hRO.1 hφ
        exact ⟨A, Or.inl hA, hAS⟩
      · obtain ⟨B, hB, hBS⟩ := ihψ hRO.2.1 hψ
        exact ⟨B, Or.inr hB, hBS⟩

lemma minterm_is_term {n : ℕ} {φ : DMFormula n} (hRO : PositiveReadOnce φ)
    {M : Finset (Fin n)} (hM : IsMinterm (evalSet φ) M) : IsTerm φ M := by
  obtain ⟨T, hT, hTM⟩ := eval_has_term hRO hM.1
  have hMT := hM.2 T hTM (term_true hT Finset.Subset.rfl)
  have heq : T = M := Finset.Subset.antisymm hTM hMT
  exact heq ▸ hT

lemma left_extract {α : Type*} [DecidableEq α]
    {L R X A B C D : Finset α} (hd : Disjoint L R) (hXL : X ⊆ L)
    (hBR : B ⊆ R) (hDR : D ⊆ R) (hX : X ⊆ (A ∪ B) ∪ (C ∪ D)) :
    X ⊆ A ∪ C := by
  intro x hx
  rcases Finset.mem_union.mp (hX hx) with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact Finset.mem_union_left C h
    · exact (Finset.disjoint_left.mp hd (hXL hx) (hBR h)).elim
  · rcases Finset.mem_union.mp h with h | h
    · exact Finset.mem_union_right A h
    · exact (Finset.disjoint_left.mp hd (hXL hx) (hDR h)).elim

lemma term_exchange {n : ℕ} {φ : DMFormula n} (hRO : PositiveReadOnce φ)
    {M N P : Finset (Fin n)} (hM : IsTerm φ M) (hN : IsTerm φ N) (hP : IsTerm φ P)
    (hsub : P ⊆ M ∪ N) (havoid : Disjoint P (M ∩ N)) :
    ∃ Q, IsTerm φ Q ∧ Q ⊆ (M ∪ N) \ P := by
  induction φ generalizing M N P with
  | lit i b =>
      obtain ⟨_, rfl⟩ := hM
      obtain ⟨_, rfl⟩ := hN
      obtain ⟨_, rfl⟩ := hP
      have := Finset.disjoint_left.mp havoid (Finset.mem_singleton_self i)
        (Finset.mem_inter.mpr ⟨Finset.mem_singleton_self i, Finset.mem_singleton_self i⟩)
      exact this.elim
  | and φ ψ ihφ ihψ =>
      obtain ⟨Ml, Mr, hMl, hMr, rfl⟩ := hM
      obtain ⟨Nl, Nr, hNl, hNr, rfl⟩ := hN
      obtain ⟨Pl, Pr, hPl, hPr, rfl⟩ := hP
      have hleft : Pl ⊆ Ml ∪ Nl := left_extract hRO.2.2 (term_subset_vars hPl)
        (term_subset_vars hMr) (term_subset_vars hNr) (Finset.subset_union_left.trans hsub)
      have hright : Pr ⊆ Mr ∪ Nr := by
        apply left_extract hRO.2.2.symm (term_subset_vars hPr)
          (term_subset_vars hMl) (term_subset_vars hNl)
        simpa only [Finset.union_comm Ml Mr, Finset.union_comm Nl Nr] using
          (Finset.subset_union_right.trans hsub : Pr ⊆ (Ml ∪ Mr) ∪ (Nl ∪ Nr))
      have hlavoid : Disjoint Pl (Ml ∩ Nl) := by
        apply Finset.disjoint_left.mpr
        intro x hp hm
        exact Finset.disjoint_left.mp havoid (Finset.mem_union_left Pr hp)
          (Finset.mem_inter.mpr ⟨Finset.mem_union_left Mr (Finset.mem_inter.mp hm).1,
            Finset.mem_union_left Nr (Finset.mem_inter.mp hm).2⟩)
      have hravoid : Disjoint Pr (Mr ∩ Nr) := by
        apply Finset.disjoint_left.mpr
        intro x hp hm
        exact Finset.disjoint_left.mp havoid (Finset.mem_union_right Pl hp)
          (Finset.mem_inter.mpr ⟨Finset.mem_union_right Ml (Finset.mem_inter.mp hm).1,
            Finset.mem_union_right Nl (Finset.mem_inter.mp hm).2⟩)
      obtain ⟨Ql, hQl, hQls⟩ := ihφ hRO.1 hMl hNl hPl hleft hlavoid
      obtain ⟨Qr, hQr, hQrs⟩ := ihψ hRO.2.1 hMr hNr hPr hright hravoid
      refine ⟨Ql ∪ Qr, ⟨Ql, Qr, hQl, hQr, rfl⟩, ?_⟩
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨hxm, hxp⟩ := Finset.mem_sdiff.mp (hQls hx)
        refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · rcases Finset.mem_union.mp hxm with hm | hn
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ hm)
          · exact Finset.mem_union_right _ (Finset.mem_union_left _ hn)
        · intro hp
          rcases Finset.mem_union.mp hp with hp | hp
          · exact hxp hp
          · exact Finset.disjoint_left.mp hRO.2.2 (term_subset_vars hQl hx) (term_subset_vars hPr hp)
      · obtain ⟨hxm, hxp⟩ := Finset.mem_sdiff.mp (hQrs hx)
        refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
        · rcases Finset.mem_union.mp hxm with hm | hn
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ hm)
          · exact Finset.mem_union_right _ (Finset.mem_union_right _ hn)
        · intro hp
          rcases Finset.mem_union.mp hp with hp | hp
          · exact Finset.disjoint_left.mp hRO.2.2 (term_subset_vars hPl hp) (term_subset_vars hQr hx)
          · exact hxp hp
  | or φ ψ ihφ ihψ =>
      have left_right {A B : Finset (Fin n)} (hA : IsTerm φ A) (hB : IsTerm ψ B) :
          Disjoint A B := Finset.disjoint_left.mpr (fun x hxA hxB =>
            Finset.disjoint_left.mp hRO.2.2 (term_subset_vars hA hxA) (term_subset_vars hB hxB))
      have pick_left {A B C : Finset (Fin n)} (hA : IsTerm φ A) (hC : IsTerm ψ C) :
          ∃ Q, IsTerm (.or φ ψ) Q ∧ Q ⊆ (A ∪ B) \ C := by
        refine ⟨A, Or.inl hA, ?_⟩
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left B hx,
          fun hc => Finset.disjoint_left.mp (left_right hA hC) hx hc⟩
      have pick_right {A B C : Finset (Fin n)} (hB : IsTerm ψ B) (hC : IsTerm φ C) :
          ∃ Q, IsTerm (.or φ ψ) Q ∧ Q ⊆ (A ∪ B) \ C := by
        refine ⟨B, Or.inr hB, ?_⟩
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right A hx,
          fun hc => Finset.disjoint_left.mp (left_right hC hB) hc hx⟩
      rcases hM with hM | hM <;> rcases hN with hN | hN <;> rcases hP with hP | hP
      · obtain ⟨Q, hQ, hQs⟩ := ihφ hRO.1 hM hN hP hsub havoid
        exact ⟨Q, Or.inl hQ, hQs⟩
      · obtain ⟨x, hx⟩ := term_nonempty hP
        rcases Finset.mem_union.mp (hsub hx) with hm | hn
        · exact (Finset.disjoint_left.mp (left_right hM hP) hm hx).elim
        · exact (Finset.disjoint_left.mp (left_right hN hP) hn hx).elim
      · exact pick_right hN hP
      · exact pick_left hM hP
      · simpa only [Finset.union_comm M N] using (pick_right (A := N) hM hP)
      · simpa only [Finset.union_comm M N] using (pick_left (B := M) hN hP)
      · obtain ⟨x, hx⟩ := term_nonempty hP
        rcases Finset.mem_union.mp (hsub hx) with hm | hn
        · exact (Finset.disjoint_left.mp (left_right hP hM) hx hm).elim
        · exact (Finset.disjoint_left.mp (left_right hP hN) hx hn).elim
      · obtain ⟨Q, hQ, hQs⟩ := ihψ hRO.2.1 hM hN hP hsub havoid
        exact ⟨Q, Or.inr hQ, hQs⟩

/-- Three minterms can be exchanged across a disjoint middle minterm. -/
lemma read_once_exchange {n : ℕ} {φ : DMFormula n} (hRO : PositiveReadOnce φ)
    {M N P : Finset (Fin n)}
    (hM : IsMinterm (evalSet φ) M) (hN : IsMinterm (evalSet φ) N)
    (hP : IsMinterm (evalSet φ) P) (hsub : P ⊆ M ∪ N)
    (havoid : Disjoint P (M ∩ N)) :
    ∃ Q, evalSet φ Q = true ∧ Q ⊆ (M ∪ N) \ P := by
  obtain ⟨Q, hQ, hQs⟩ := term_exchange hRO
    (minterm_is_term hRO hM) (minterm_is_term hRO hN) (minterm_is_term hRO hP) hsub havoid
  exact ⟨Q, term_true hQ Finset.Subset.rfl, hQs⟩

end ReadOnceExchange

namespace SaturatedReadOnce

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1904_aux.InputSupport
open PEqualNP.Outside.L_meta_1904_aux.ReadOnceExchange

def Forest {n : ℕ} (L : List (Finset (Fin n)))
    (w : (Fin n → Bool) → List Bool) (W : Finset ℕ) : Prop :=
  ∃ F : ℕ → DMFormula n,
    (∀ j ∈ W, PositiveReadOnce (F j) ∧ vars (F j) = L.getD j ∅ ∧
      ∀ x, (F j).eval x = (w x).getD j false) ∧
    ∀ i ∈ W, ∀ j ∈ W, i ≠ j → Disjoint (vars (F i)) (vars (F j))

def Saturated {n : ℕ} (t : ℕ) (L : List (Finset (Fin n)))
    (w : (Fin n → Bool) → List Bool) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion (fun j => L.getD j ∅)).card = t + W.card → Forest L w W

lemma saturation_nonempty {n : ℕ} {t : ℕ} {L : List (Finset (Fin n))}
    (hc : Cnt t L) {W : Finset ℕ}
    (hs : (W.biUnion (fun j => L.getD j ∅)).card = t + W.card)
    {j : ℕ} (hj : j ∈ W) : (L.getD j ∅).Nonempty := by
  by_contra hn
  have hz := Finset.not_nonempty_iff_eq_empty.mp hn
  have he : W.biUnion (fun j => L.getD j ∅) =
      (W.erase j).biUnion (fun j => L.getD j ∅) := by
    conv_lhs => rw [← Finset.insert_erase hj]
    rw [Finset.biUnion_insert, hz, Finset.empty_union]
  have hbound := hc (W.erase j)
  have hcard := Finset.card_erase_add_one hj
  rw [he] at hs
  omega

lemma saturated_inputs {n : ℕ} (hn : 0 < n) :
    Saturated 0 (inputSupps n) (fun x => List.ofFn x) := by
  intro W hs
  have hvalid (j : ℕ) (hj : j ∈ W) : j < n := by
    have hne := saturation_nonempty cnt_inputs hs hj
    by_contra hjn
    have hz : (inputSupps n).getD j ∅ = ∅ := List.getD_eq_default _ _ (by simp [inputSupps]; omega)
    rw [hz] at hne
    exact Finset.not_nonempty_empty hne
  let F : ℕ → DMFormula n := fun j =>
    if h : j < n then .lit ⟨j, h⟩ true else .lit ⟨0, hn⟩ true
  refine ⟨F, ?_, ?_⟩
  · intro j hj
    have hv := hvalid j hj
    refine ⟨by simp [F, hv, PositiveReadOnce], ?_, ?_⟩
    · simp [F, hv, vars, inputSupps]
    · intro x
      simp [F, hv, DMFormula.eval]
  · intro i hi j hj hij
    have hvi := hvalid i hi
    have hvj := hvalid j hj
    simp only [F, dite_eq_left hvi, dite_eq_left hvj, vars, Finset.disjoint_singleton_left,
      Finset.mem_singleton]
    intro he
    exact hij (congrArg Fin.val he)

lemma saturated_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n)))
    (w : (Fin n → Bool) → List Bool) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hg : g.inputs.length ≤ 2)
    (hlen : ∀ x, (w x).length = L.length) (hc : Cnt t L) (hsat : Saturated t L w) :
    Saturated (t + 1) (L ++ [gateSupp L g])
      (fun x => w x ++ [g.op.eval (g.inputs.map (fun i => (w x).getD i false))]) := by
  classical
  intro W hs
  have hnew : L.length ∈ W := by
    by_contra hn
    have he : W.biUnion (fun j => (L ++ [gateSupp L g]).getD j ∅) =
        W.biUnion (fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hn (e ▸ hj))
    rw [he] at hs
    have := hc W
    omega
  let V := W.erase L.length ∪ g.inputs.toFinset
  have hsub : W.biUnion (fun j => (L ++ [gateSupp L g]).getD j ∅) ⊆
      V.biUnion (fun j => L.getD j ∅) := by
    intro i hi
    obtain ⟨j, hjW, hij⟩ := Finset.mem_biUnion.mp hi
    by_cases hjl : j = L.length
    · subst j
      rw [getD_snoc_eq] at hij
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).mp hij
      exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_union_right _ (List.mem_toFinset.mpr ha), hia⟩
    · rw [getD_snoc_ne _ _ _ _ hjl] at hij
      exact Finset.mem_biUnion.mpr ⟨j,
        Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hjl, hjW⟩), hij⟩
  have hvc : V.card ≤ (W.erase L.length).card + g.inputs.toFinset.card := Finset.card_union_le _ _
  have hic : g.inputs.toFinset.card ≤ g.inputs.length := List.toFinset_card_le _
  have hwe : (W.erase L.length).card + 1 = W.card := Finset.card_erase_add_one hnew
  have hbound := hc V
  have hsupport := Finset.card_le_card hsub
  have hvcard : V.card = W.card + 1 := by omega
  have hsV : (V.biUnion (fun j => L.getD j ∅)).card = t + V.card := by omega
  have hinputcard : g.inputs.toFinset.card = 2 := by omega
  have hinputlen : g.inputs.length = 2 := by omega
  have hdis : Disjoint (W.erase L.length) g.inputs.toFinset :=
    Finset.card_union_eq_card_add_card.mp (by change V.card = _; omega)
  obtain ⟨a, b, hablist⟩ : ∃ a b, g.inputs = [a, b] := by
    refine ⟨g.inputs[0]'(by omega), g.inputs[1]'(by omega), ?_⟩
    exact List.eq_getElem_of_length_eq_two g.inputs hinputlen
  have hab : a ≠ b := by
    intro he
    subst b
    simp [hablist] at hinputcard
  have haV : a ∈ V := Finset.mem_union_right _ (by simp [hablist])
  have hbV : b ∈ V := Finset.mem_union_right _ (by simp [hablist])
  have holdV {j : ℕ} (hj : j ∈ W) (hjnew : j ≠ L.length) : j ∈ V :=
    Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hjnew, hj⟩)
  have holdne {j : ℕ} (hj : j ∈ W) (hjnew : j ≠ L.length) : j ≠ a ∧ j ≠ b := by
    have hn : j ∉ g.inputs.toFinset := fun h =>
      Finset.disjoint_left.mp hdis (Finset.mem_erase.mpr ⟨hjnew, hj⟩) h
    simpa [hablist] using hn
  obtain ⟨F, hF, hFd⟩ := hsat V hsV
  have hA := hF a haV
  have hB := hF b hbV
  let φ : DMFormula n := if g.op = GateOp.and then .and (F a) (F b) else .or (F a) (F b)
  have hφ : PositiveReadOnce φ := by
    dsimp [φ]
    split <;> exact ⟨hA.1, hB.1, hFd a haV b hbV hab⟩
  have hφvars : vars φ = vars (F a) ∪ vars (F b) := by dsimp [φ]; split <;> rfl
  have hφsupp : vars φ = gateSupp L g := by
    rw [hφvars, hA.2.1, hB.2.1]
    simp [gateSupp, hablist]
  have hφeval : ∀ x, φ.eval x = g.op.eval (g.inputs.map (fun i => (w x).getD i false)) := by
    intro x
    rcases hop with hop | hop <;>
      simp [φ, hop, DMFormula.eval, hablist, GateOp.eval, hA.2.2 x, hB.2.2 x]
  let F' : ℕ → DMFormula n := fun j => if j = L.length then φ else F j
  refine ⟨F', ?_, ?_⟩
  · intro j hj
    by_cases hjnew : j = L.length
    · subst j
      refine ⟨by simpa [F'] using hφ, ?_, ?_⟩
      · simpa [F', getD_snoc_eq] using hφsupp
      · intro x
        rw [show F' L.length = φ by simp [F'], ← hlen x, getD_snoc_eq]
        exact hφeval x
    · have hjF := hF j (holdV hj hjnew)
      refine ⟨by simpa [F', hjnew] using hjF.1, ?_, ?_⟩
      · rw [show F' j = F j by simp [F', hjnew], getD_snoc_ne _ _ _ _ hjnew]
        exact hjF.2.1
      · intro x
        rw [getD_snoc_ne _ _ _ _ (by rw [hlen x]; exact hjnew)]
        simpa [F', hjnew] using hjF.2.2 x
  · intro i hi j hj hij
    by_cases hinew : i = L.length
    · subst i
      have hjnew : j ≠ L.length := Ne.symm hij
      have hjV := holdV hj hjnew
      have hjne := holdne hj hjnew
      rw [show F' L.length = φ by simp [F'], show F' j = F j by simp [F', hjnew], hφvars]
      exact Finset.disjoint_union_left.mpr ⟨hFd a haV j hjV hjne.1.symm,
        hFd b hbV j hjV hjne.2.symm⟩
    · by_cases hjnew : j = L.length
      · subst j
        have hiV := holdV hi hinew
        have hine := holdne hi hinew
        rw [show F' i = F i by simp [F', hinew], show F' L.length = φ by simp [F'], hφvars]
        exact Finset.disjoint_union_right.mpr ⟨hFd i hiV a haV hine.1,
          hFd i hiV b hbV hine.2⟩
      · simpa [F', hinew, hjnew] using hFd i (holdV hi hinew) j (holdV hj hjnew) hij


lemma saturated_suppsFrom {n : ℕ} (gs : List Gate) :
    ∀ (t : ℕ) (L : List (Finset (Fin n))) (w : (Fin n → Bool) → List Bool),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ x, (w x).length = L.length) → Cnt t L → Saturated t L w →
    Saturated (t + gs.length) (suppsFrom gs L) (fun x => wiresFrom gs (w x)) := by
  induction gs with
  | nil => intro t L w hm hl hc hs; exact hs
  | cons g gs ih =>
    intro t L w hm hl hc hs
    have hg := hm g List.mem_cons_self
    have hnext := saturated_step t L w g hg.1 hg.2 hl hc hs
    have hcnext := cnt_step t L g hg.2 hc
    have hresult := ih (t + 1) (L ++ [gateSupp L g])
      (fun x => w x ++ [g.op.eval (g.inputs.map (fun i => (w x).getD i false))])
      (fun a ha => hm a (List.mem_cons_of_mem g ha))
      (fun x => by simp [hl x]) hcnext hnext
    change Saturated (t + (gs.length + 1))
      (suppsFrom gs (L ++ [gateSupp L g]))
      (fun x => wiresFrom gs (w x ++ [g.op.eval (g.inputs.map (fun i => (w x).getD i false))]))
    rw [show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact hresult

/-- Saturating the binary input-support bound forces a positive read-once formula. -/
lemma read_once_of_saturated_support {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (hcard : ((suppsFrom C.gates (inputSupps n)).getD C.output ∅).card = C.size + 1) :
    ∃ φ : DMFormula n, PositiveReadOnce φ ∧
      vars φ = (suppsFrom C.gates (inputSupps n)).getD C.output ∅ ∧
      ∀ x : Fin n → Bool, φ.eval x = C.eval (List.ofFn x) := by
  have hn : 0 < n := by
    have h := Finset.card_le_univ ((suppsFrom C.gates (inputSupps n)).getD C.output ∅)
    simp only [Fintype.card_fin] at h
    omega
  have hs := saturated_suppsFrom C.gates 0 (inputSupps n) (fun x => List.ofFn x)
    (fun g hg => ⟨by simpa using (hmono g hg).1, (hmono g hg).2⟩)
    (fun x => by simp [inputSupps]) cnt_inputs (saturated_inputs hn)
  have he : (({C.output} : Finset ℕ).biUnion
      (fun j => (suppsFrom C.gates (inputSupps n)).getD j ∅)).card =
      0 + C.gates.length + ({C.output} : Finset ℕ).card := by
    simpa only [Finset.singleton_biUnion, Finset.card_singleton, Nat.zero_add, Circuit.size]
      using hcard
  obtain ⟨F, hF, hd⟩ := hs {C.output} he
  have h := hF C.output (Finset.mem_singleton_self _)
  exact ⟨F C.output, h.1, h.2.1, h.2.2⟩

end SaturatedReadOnce

namespace InputSupport

open PEqualNP.CircuitLowerBounds

def structuralSupport (n : ℕ) (C : Circuit) : Finset (Fin n) :=
  (suppsFrom C.gates (inputSupps n)).getD C.output ∅

lemma structuralSupport_card {n : ℕ} (C : Circuit)
    (hfanin : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    (structuralSupport n C).card ≤ C.size + 1 := by
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) hfanin cnt_inputs {C.output}
  simpa only [Finset.singleton_biUnion, Finset.card_singleton, zero_add,
    structuralSupport, Circuit.size] using hc

lemma structuralSupport_agreement {n : ℕ} (C : Circuit)
    (x y : Fin n → Bool) (hxy : ∀ i ∈ structuralSupport n C, x i = y i) :
    C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
  exact (agreement_wiresFrom x y C.gates _ _ _ (agreement_inputs x y)).2.2 C.output hxy

lemma structural_clause_agreement {n m : ℕ}
    (G : SimpleGraph (Fin n)) (B : Fin m → Finset (Fin n)) (C : Circuit)
    (hcorrect : ∀ x : Fin n → Bool,
      C.eval (List.ofFn (clauseInput B x)) = true ↔ UniqueClause.hit G x) :
    ∀ x y : Fin n → Bool,
      (∀ i ∈ structuralSupport m C,
        UniqueClause.clause (B i) x ↔ UniqueClause.clause (B i) y) →
      (UniqueClause.hit G x ↔ UniqueClause.hit G y) := by
  intro x y hxy
  have heq := structuralSupport_agreement C (clauseInput B x) (clauseInput B y) (by
    intro i hi
    apply Bool.eq_iff_iff.mpr
    simpa only [clauseInput_eq_true] using hxy i hi)
  rw [← hcorrect x, ← hcorrect y, heq]

end InputSupport

namespace SignatureP4

open ReadOnceExchange

def signature {α ι : Type*} [DecidableEq α] (B : ι → Finset α)
    (U : Finset ι) (v : α) : Finset ι := U.filter (fun i => v ∈ B i)

lemma erase_signature_mimic {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (G : SimpleGraph α) (B : ι → Finset α) (U : Finset ι)
    (hpacking : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    (hsmall : ∀ i ∈ U, (B i).card ≤ 2)
    (huniform : ∀ v, ∀ i ∈ signature B U v,
      (B i).card = (signature B U v).card)
    {u v : α} (huv : G.Adj u v) {i : ι} (hi : i ∈ signature B U u) :
    ∃ a, ¬ G.Adj a v ∧ (signature B U u).erase i ⊆ signature B U a := by
  have hiU := (Finset.mem_filter.mp hi).1
  have hcard : (signature B U u).card ≤ 2 := by
    rw [← huniform u i hi]
    exact hsmall i hiU
  by_cases hlow : (signature B U u).card ≤ 1
  · refine ⟨v, G.irrefl, ?_⟩
    intro j hj
    have hji : j = i := Finset.card_le_one.mp hlow j (Finset.mem_of_mem_erase hj) i hi
    exact ((Finset.mem_erase.mp hj).1 hji).elim
  · have htwo : (signature B U u).card = 2 := by omega
    have herase : ((signature B U u).erase i).card = 1 := by
      have := Finset.card_erase_add_one hi
      omega
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp herase
    have hjS : j ∈ signature B U u := by
      apply Finset.mem_of_mem_erase (a := i)
      rw [hj]
      exact Finset.mem_singleton_self j
    obtain ⟨hjU, huB⟩ := Finset.mem_filter.mp hjS
    have hBtwo : (B j).card = 2 := (huniform u j hjS).trans htwo
    have hBerase : ((B j).erase u).card = 1 := by
      have := Finset.card_erase_add_one huB
      omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hBerase
    have haerase : a ∈ (B j).erase u := by rw [ha]; exact Finset.mem_singleton_self a
    have hane := (Finset.mem_erase.mp haerase).1
    have haB := Finset.mem_of_mem_erase haerase
    refine ⟨a, fun hav => hpacking j hjU u huB a haB hane.symm v ⟨huv, hav⟩, ?_⟩
    rw [hj]
    exact Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨hjU, haB⟩)

lemma edge_signature_minterm {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (G : SimpleGraph α) (B : ι → Finset α) (U : Finset ι) (F : Finset ι → Bool)
    (hmono : ∀ S T, S ⊆ T → F S = true → F T = true)
    (hcorrect : ∀ u v, F (signature B U u ∪ signature B U v) = true ↔ G.Adj u v)
    (hpacking : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    (hsmall : ∀ i ∈ U, (B i).card ≤ 2)
    (huniform : ∀ v, ∀ i ∈ signature B U v,
      (B i).card = (signature B U v).card)
    {u v : α} (huv : G.Adj u v) :
    IsMinterm F (signature B U u ∪ signature B U v) := by
  have essential {a b : α} (hab : G.Adj a b) {i : ι}
      (hi : i ∈ signature B U a) {T : Finset ι}
      (hT : T ⊆ signature B U a ∪ signature B U b) (hFT : F T = true) : i ∈ T := by
    by_contra hiT
    obtain ⟨c, hcb, hmimic⟩ := erase_signature_mimic G B U hpacking hsmall huniform hab hi
    have hsub : T ⊆ signature B U c ∪ signature B U b := by
      intro j hj
      rcases Finset.mem_union.mp (hT hj) with hja | hjb
      · have hji : j ≠ i := by intro e; subst j; exact hiT hj
        exact Finset.mem_union_left _ (hmimic (Finset.mem_erase.mpr ⟨hji, hja⟩))
      · exact Finset.mem_union_right _ hjb
    exact hcb ((hcorrect c b).mp (hmono _ _ hsub hFT))
  refine ⟨(hcorrect u v).mpr huv, ?_⟩
  intro T hT hFT i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · exact essential huv hi hT hFT
  · apply essential huv.symm hi _ hFT
    simpa only [Finset.union_comm] using hT

lemma signature_disjoint_adj {α ι : Type*} [DecidableEq α]
    (G : SimpleGraph α) (B : ι → Finset α) (U : Finset ι)
    (hind : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, ¬ G.Adj a b)
    {u v : α} (huv : G.Adj u v) :
    Disjoint (signature B U u) (signature B U v) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨hiU, hu⟩ := Finset.mem_filter.mp hi
  exact hind i hiU u hu v (Finset.mem_filter.mp hj).2 huv

lemma signature_disjoint_common {α ι : Type*} [DecidableEq α]
    (G : SimpleGraph α) (B : ι → Finset α) (U : Finset ι)
    (hpacking : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    {u v w : α} (hne : u ≠ v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    Disjoint (signature B U u) (signature B U v) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨hiU, hu⟩ := Finset.mem_filter.mp hi
  exact hpacking i hiU u hu v (Finset.mem_filter.mp hj).2 hne w ⟨huw, hvw⟩

lemma no_three_edge_walk_to_nonedge {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (G : SimpleGraph α) (B : ι → Finset α) (U : Finset ι) (F : Finset ι → Bool)
    (hmono : ∀ S T, S ⊆ T → F S = true → F T = true)
    (hcorrect : ∀ u v, F (signature B U u ∪ signature B U v) = true ↔ G.Adj u v)
    (hind : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, ¬ G.Adj a b)
    (hpacking : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    (hsmall : ∀ i ∈ U, (B i).card ≤ 2)
    (huniform : ∀ v, ∀ i ∈ signature B U v,
      (B i).card = (signature B U v).card)
    (hexchange : ∀ M N P, IsMinterm F M → IsMinterm F N → IsMinterm F P →
      P ⊆ M ∪ N → Disjoint P (M ∩ N) →
      ∃ Q, F Q = true ∧ Q ⊆ (M ∪ N) \ P)
    {u v w z : α} (huv : G.Adj u v) (hvw : G.Adj v w) (hwz : G.Adj w z)
    (huz : ¬ G.Adj u z) : False := by
  have huwne : u ≠ w := by intro e; subst w; exact huz hwz
  have hvzne : v ≠ z := by intro e; subst z; exact huz huv
  have duw := signature_disjoint_common G B U hpacking huwne huv hvw.symm
  have dvz := signature_disjoint_common G B U hpacking hvzne hvw hwz.symm
  have dvw := signature_disjoint_adj G B U hind hvw
  let M := signature B U u ∪ signature B U v
  let N := signature B U w ∪ signature B U z
  let P := signature B U v ∪ signature B U w
  have hM : IsMinterm F M := edge_signature_minterm G B U F hmono hcorrect hpacking hsmall huniform huv
  have hN : IsMinterm F N := edge_signature_minterm G B U F hmono hcorrect hpacking hsmall huniform hwz
  have hP : IsMinterm F P := edge_signature_minterm G B U F hmono hcorrect hpacking hsmall huniform hvw
  have hsub : P ⊆ M ∪ N := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hi)
  have havoid : Disjoint P (M ∩ N) := by
    apply Finset.disjoint_left.mpr
    intro i hi hiMN
    obtain ⟨hiM, hiN⟩ := Finset.mem_inter.mp hiMN
    rcases Finset.mem_union.mp hi with hi | hi
    · rcases Finset.mem_union.mp hiN with hiw | hiz
      · exact Finset.disjoint_left.mp dvw hi hiw
      · exact Finset.disjoint_left.mp dvz hi hiz
    · rcases Finset.mem_union.mp hiM with hiu | hiv
      · exact Finset.disjoint_left.mp duw hiu hi
      · exact Finset.disjoint_left.mp dvw hiv hi
  obtain ⟨Q, hFQ, hQ⟩ := hexchange M N P hM hN hP hsub havoid
  have hQsub : Q ⊆ signature B U u ∪ signature B U z := by
    intro i hi
    obtain ⟨hiMN, hiP⟩ := Finset.mem_sdiff.mp (hQ hi)
    rcases Finset.mem_union.mp hiMN with hiM | hiN
    · rcases Finset.mem_union.mp hiM with hiu | hiv
      · exact Finset.mem_union_left _ hiu
      · exact (hiP (Finset.mem_union_left _ hiv)).elim
    · rcases Finset.mem_union.mp hiN with hiw | hiz
      · exact (hiP (Finset.mem_union_right _ hiw)).elim
      · exact Finset.mem_union_right _ hiz
  exact huz ((hcorrect u z).mp (hmono _ _ hQsub hFQ))

lemma formula_support_agreement {m : ℕ} (φ : PEqualNP.MetaComplexity.DMFormula m)
    (x y : Fin m → Bool) (hxy : ∀ i ∈ vars φ, x i = y i) : φ.eval x = φ.eval y := by
  induction φ with
  | lit i b =>
      have hi := hxy i (Finset.mem_singleton_self i)
      simp only [PEqualNP.MetaComplexity.DMFormula.eval, hi]
  | and φ ψ ihφ ihψ =>
      have hl := ihφ (fun i hi => hxy i (Finset.mem_union_left _ hi))
      have hr := ihψ (fun i hi => hxy i (Finset.mem_union_right _ hi))
      simp only [PEqualNP.MetaComplexity.DMFormula.eval, hl, hr]
  | or φ ψ ihφ ihψ =>
      have hl := ihφ (fun i hi => hxy i (Finset.mem_union_left _ hi))
      have hr := ihψ (fun i hi => hxy i (Finset.mem_union_right _ hi))
      simp only [PEqualNP.MetaComplexity.DMFormula.eval, hl, hr]

lemma read_once_no_three_edge_walk_to_nonedge {α : Type*} [DecidableEq α] {m : ℕ}
    (G : SimpleGraph α) (B : Fin m → Finset α) (U : Finset (Fin m))
    (φ : PEqualNP.MetaComplexity.DMFormula m) (hRO : PositiveReadOnce φ)
    (hvars : vars φ ⊆ U)
    (hcorrect : ∀ u v, φ.eval (fun i => decide (u ∈ B i ∨ v ∈ B i)) = true ↔ G.Adj u v)
    (hind : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, ¬ G.Adj a b)
    (hpacking : ∀ i ∈ U, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    (hsmall : ∀ i ∈ U, (B i).card ≤ 2)
    (huniform : ∀ v, ∀ i ∈ signature B U v,
      (B i).card = (signature B U v).card)
    {u v w z : α} (huv : G.Adj u v) (hvw : G.Adj v w) (hwz : G.Adj w z)
    (huz : ¬ G.Adj u z) : False := by
  apply no_three_edge_walk_to_nonedge G B U (evalSet φ)
    (fun S T hST hS => ?_) (fun a b => ?_) hind hpacking hsmall huniform
    (fun M N P hM hN hP hsub havoid => read_once_exchange hRO hM hN hP hsub havoid)
    huv hvw hwz huz
  · obtain ⟨R, hR, hRS⟩ := eval_has_term hRO hS
    exact term_true hR (hRS.trans hST)
  · have heq : evalSet φ (signature B U a ∪ signature B U b) =
        φ.eval (fun i => decide (a ∈ B i ∨ b ∈ B i)) := by
      apply formula_support_agreement
      intro i hi
      have hiU := hvars hi
      simp [signature, hiU]
    rw [heq]
    exact hcorrect a b

lemma pair_input_correct_of_encoder {α : Type*} [DecidableEq α] {m : ℕ}
    (G : SimpleGraph α) (B : Fin m → Finset α)
    (F : (Fin m → Bool) → Bool) (encode : (α → Bool) → Fin m → Bool)
    (hencode : ∀ x i, encode x i = true ↔ ∃ a ∈ B i, x a = true)
    (hcorrect : ∀ x, F (encode x) = true ↔
      ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true) :
    ∀ u v, F (fun i => decide (u ∈ B i ∨ v ∈ B i)) = true ↔ G.Adj u v := by
  intro u v
  let x : α → Bool := fun a => decide (a = u ∨ a = v)
  have henc : encode x = fun i => decide (u ∈ B i ∨ v ∈ B i) := by
    funext i
    apply Bool.eq_iff_iff.mpr
    rw [hencode]
    simp only [x, decide_eq_true_eq]
    constructor
    · rintro ⟨a, ha, rfl | rfl⟩
      · exact Or.inl ha
      · exact Or.inr ha
    · rintro (hu | hv)
      · exact ⟨u, hu, Or.inl rfl⟩
      · exact ⟨v, hv, Or.inr rfl⟩
  rw [← henc, hcorrect]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have ha' : a = u ∨ a = v := of_decide_eq_true ha
    have hb' : b = u ∨ b = v := of_decide_eq_true hb
    rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro huv
    exact ⟨u, v, huv, by simp [x], by simp [x]⟩

end SignatureP4

namespace PackingSources

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma three_edge_walk_packing_gate_lower_bound {n m : ℕ}
    (G : SimpleGraph (Fin n)) (B : Fin m → Finset (Fin n))
    (C : Circuit) (hC : Monotone2 C)
    (hne : ∀ v, ∃ w, G.Adj v w)
    (htri : ∀ x y z, G.Adj x y → G.Adj y z → ¬ G.Adj z x)
    (hind : ∀ i, ∀ a ∈ B i, ∀ b ∈ B i, ¬ G.Adj a b)
    (hpacking : ∀ i, ∀ a ∈ B i, ∀ b ∈ B i, a ≠ b →
      ∀ w, ¬ (G.Adj a w ∧ G.Adj b w))
    (hcorrect : ∀ x : Fin n → Bool,
      C.eval (List.ofFn (InputSupport.clauseInput B x)) = true ↔
        UniqueClause.hit G x)
    {u v w z : Fin n} (huv : G.Adj u v) (hvw : G.Adj v w) (hwz : G.Adj w z)
    (huz : ¬ G.Adj u z) :
    n ≤ C.size := by
  classical
  let U := InputSupport.structuralSupport m C
  have hU : U.card ≤ C.size + 1 :=
    InputSupport.structuralSupport_card C (fun g hg => (hC g hg).2)
  have hagree : ∀ x y : Fin n → Bool,
      (∀ i ∈ U, SignalAgreement.clause (B i) x ↔
        SignalAgreement.clause (B i) y) →
      SignalAgreement.hit G x → SignalAgreement.hit G y := by
    intro x y hxy
    exact (InputSupport.structural_clause_agreement G B C hcorrect x y hxy).mp
  have hnU := card_le_used_packing_sources G B U hne (fun i _ => hpacking i) hagree
  by_contra hnot
  have heq : n = U.card := by omega
  have hsat : U.card = C.size + 1 := by omega
  have hsmall := equality_forces_singletons_or_pairs G B U hne htri
    (fun i _ => hind i) (fun i _ => hpacking i) hagree heq
  have huniform := WeightedEquality.uniform_incidence_of_card_eq
    (Finset.univ : Finset (Fin n)) U B
    (fun a _ => small_subfamily_of_essential_vertex G B U a (hne a)
      (fun i _ => hpacking i) hagree) (by simpa using heq)
  obtain ⟨φ, hRO, hvars, hsem⟩ :=
    SaturatedReadOnce.read_once_of_saturated_support (n := m) C hC hsat
  have hpair := SignatureP4.pair_input_correct_of_encoder G B φ.eval
    (InputSupport.clauseInput B)
    (fun x i => InputSupport.clauseInput_eq_true B x i)
    (by intro x; rw [hsem]; exact hcorrect x)
  apply SignatureP4.read_once_no_three_edge_walk_to_nonedge G B U φ hRO
    (by rw [hvars]; exact Finset.Subset.rfl) hpair
    (fun i _ => hind i) (fun i _ => hpacking i) hsmall
    (fun a i hi => (huniform a (Finset.mem_univ a)).2 i hi) huv hvw hwz huz

end PackingSources

end PEqualNP.Outside.L_meta_1904_aux
