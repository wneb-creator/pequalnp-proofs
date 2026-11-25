import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.SplitIfs
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

def petersenEdges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
   (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

abbrev adjacent (i j : Fin 10) : Prop :=
  (i, j) ∈ petersenEdges ∨ (j, i) ∈ petersenEdges

def pairAut : Fin 10 → Fin 10 → Fin 10 → Fin 10 :=
  ![![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9],
      ![0, 5, 7, 2, 1, 4, 8, 9, 3, 6],
      ![0, 5, 8, 6, 1, 4, 7, 3, 9, 2],
      ![0, 5, 8, 3, 4, 1, 7, 6, 2, 9],
      ![0, 1, 6, 9, 4, 5, 2, 8, 7, 3],
      ![0, 5, 7, 9, 4, 1, 8, 2, 6, 3],
      ![0, 5, 8, 3, 4, 1, 7, 6, 2, 9],
      ![0, 5, 8, 6, 1, 4, 7, 3, 9, 2]],
    ![![1, 0, 5, 8, 6, 2, 4, 7, 3, 9],
      ![1, 0, 5, 8, 6, 2, 4, 7, 3, 9],
      ![5, 0, 1, 2, 7, 8, 4, 6, 3, 9],
      ![5, 0, 1, 2, 7, 8, 4, 6, 3, 9],
      ![1, 0, 5, 7, 2, 6, 4, 8, 9, 3],
      ![1, 0, 5, 8, 6, 2, 4, 7, 3, 9],
      ![5, 0, 4, 9, 7, 8, 1, 3, 6, 2],
      ![5, 0, 1, 6, 8, 7, 4, 2, 9, 3],
      ![5, 0, 4, 3, 8, 7, 1, 9, 2, 6],
      ![5, 0, 4, 9, 7, 8, 1, 3, 6, 2]],
    ![![2, 1, 0, 5, 7, 3, 6, 4, 8, 9],
      ![2, 1, 0, 5, 7, 3, 6, 4, 8, 9],
      ![9, 4, 0, 1, 6, 7, 3, 5, 2, 8],
      ![9, 4, 0, 1, 6, 7, 3, 5, 2, 8],
      ![3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
      ![3, 4, 0, 5, 8, 2, 9, 1, 7, 6],
      ![6, 1, 0, 5, 8, 9, 2, 4, 7, 3],
      ![9, 4, 0, 5, 7, 6, 3, 1, 8, 2],
      ![9, 4, 0, 1, 6, 7, 3, 5, 2, 8],
      ![9, 4, 0, 5, 7, 6, 3, 1, 8, 2]],
    ![![2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
      ![3, 2, 1, 0, 4, 8, 7, 6, 5, 9],
      ![9, 6, 1, 0, 4, 7, 8, 2, 5, 3],
      ![9, 7, 5, 0, 4, 6, 2, 8, 1, 3],
      ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
      ![3, 8, 5, 0, 4, 2, 6, 7, 1, 9],
      ![9, 7, 5, 0, 4, 6, 2, 8, 1, 3],
      ![9, 6, 1, 0, 4, 7, 8, 2, 5, 3],
      ![9, 7, 5, 0, 4, 6, 2, 8, 1, 3],
      ![6, 9, 4, 0, 1, 8, 7, 3, 5, 2]],
    ![![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
      ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
      ![5, 7, 2, 1, 0, 8, 9, 3, 6, 4],
      ![5, 8, 6, 1, 0, 7, 3, 9, 2, 4],
      ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
      ![1, 6, 9, 4, 0, 2, 8, 7, 3, 5],
      ![5, 7, 9, 4, 0, 8, 2, 6, 3, 1],
      ![5, 8, 3, 4, 0, 7, 6, 2, 9, 1],
      ![5, 8, 6, 1, 0, 7, 3, 9, 2, 4],
      ![5, 8, 3, 4, 0, 7, 6, 2, 9, 1]],
    ![![1, 2, 3, 8, 6, 0, 7, 4, 5, 9],
      ![1, 2, 3, 8, 6, 0, 7, 4, 5, 9],
      ![5, 7, 2, 3, 8, 0, 9, 1, 4, 6],
      ![5, 8, 3, 2, 7, 0, 6, 4, 1, 9],
      ![1, 6, 9, 7, 2, 0, 8, 4, 5, 3],
      ![1, 2, 3, 8, 6, 0, 7, 4, 5, 9],
      ![5, 7, 9, 6, 8, 0, 2, 4, 1, 3],
      ![5, 8, 6, 9, 7, 0, 3, 1, 4, 2],
      ![5, 8, 3, 2, 7, 0, 6, 4, 1, 9],
      ![5, 8, 6, 9, 7, 0, 3, 1, 4, 2]],
    ![![2, 1, 6, 9, 7, 3, 0, 8, 4, 5],
      ![2, 1, 6, 9, 7, 3, 0, 8, 4, 5],
      ![6, 1, 2, 3, 8, 9, 0, 7, 4, 5],
      ![9, 4, 3, 2, 7, 6, 0, 8, 1, 5],
      ![3, 4, 9, 7, 2, 8, 0, 6, 5, 1],
      ![3, 4, 9, 6, 8, 2, 0, 7, 1, 5],
      ![9, 4, 3, 8, 6, 7, 0, 2, 5, 1],
      ![9, 4, 3, 8, 6, 7, 0, 2, 5, 1],
      ![9, 4, 3, 2, 7, 6, 0, 8, 1, 5],
      ![9, 4, 3, 8, 6, 7, 0, 2, 5, 1]],
    ![![2, 3, 4, 9, 7, 1, 8, 0, 6, 5],
      ![3, 2, 1, 6, 8, 4, 7, 0, 9, 5],
      ![9, 6, 1, 2, 7, 4, 8, 0, 3, 5],
      ![9, 6, 1, 2, 7, 4, 8, 0, 3, 5],
      ![3, 8, 5, 7, 2, 4, 6, 0, 9, 1],
      ![2, 3, 4, 9, 7, 1, 8, 0, 6, 5],
      ![9, 7, 5, 8, 6, 4, 2, 0, 3, 1],
      ![9, 7, 5, 8, 6, 4, 2, 0, 3, 1],
      ![6, 9, 4, 3, 8, 1, 7, 0, 2, 5],
      ![9, 7, 5, 8, 6, 4, 2, 0, 3, 1]],
    ![![2, 3, 8, 5, 7, 1, 4, 6, 0, 9],
      ![3, 2, 7, 5, 8, 4, 1, 9, 0, 6],
      ![9, 7, 2, 1, 6, 4, 5, 3, 0, 8],
      ![9, 7, 2, 1, 6, 4, 5, 3, 0, 8],
      ![3, 8, 6, 1, 2, 4, 5, 9, 0, 7],
      ![2, 3, 8, 5, 7, 1, 4, 6, 0, 9],
      ![9, 6, 8, 5, 7, 4, 1, 3, 0, 2],
      ![6, 9, 7, 5, 8, 1, 4, 2, 0, 3],
      ![9, 7, 2, 1, 6, 4, 5, 3, 0, 8],
      ![9, 6, 8, 5, 7, 4, 1, 3, 0, 2]],
    ![![2, 3, 8, 6, 1, 7, 4, 5, 9, 0],
      ![3, 2, 7, 9, 4, 8, 1, 5, 6, 0],
      ![9, 7, 2, 3, 4, 6, 5, 1, 8, 0],
      ![6, 9, 7, 2, 1, 8, 4, 5, 3, 0],
      ![2, 3, 8, 6, 1, 7, 4, 5, 9, 0],
      ![3, 8, 6, 9, 4, 2, 5, 1, 7, 0],
      ![9, 6, 8, 3, 4, 7, 1, 5, 2, 0],
      ![9, 7, 2, 3, 4, 6, 5, 1, 8, 0],
      ![9, 6, 8, 3, 4, 7, 1, 5, 2, 0],
      ![9, 7, 2, 3, 4, 6, 5, 1, 8, 0]] ]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 200000 in
set_option synthInstance.maxHeartbeats 1000000 in
lemma pairAut_certificate : ∀ i j : Fin 10,
    Function.Bijective (pairAut i j) ∧
    (∀ u v : Fin 10, adjacent (pairAut i j u) (pairAut i j v) ↔ adjacent u v) ∧
    pairAut i j i = 0 ∧
    pairAut i j j = if i = j then 0 else if adjacent i j then 1 else 2 := by
  unfold Function.Bijective Function.Injective Function.Surjective
  decide +kernel

lemma adjacent_pair_orbit (i j : Fin 10) (h : adjacent i j) :
    ∃ p : Fin 10 → Fin 10, Function.Bijective p ∧
      (∀ u v : Fin 10, adjacent (p u) (p v) ↔ adjacent u v) ∧
      p i = 0 ∧ p j = 1 := by
  have hi : i ≠ j := by
    intro he
    subst j
    have hl : ∀ a : Fin 10, ¬ adjacent a a := by decide
    exact hl i h
  obtain ⟨hb, ha, hp, hq⟩ := pairAut_certificate i j
  exact ⟨pairAut i j, hb, ha, hp, by simpa [hi, h] using hq⟩

lemma nonadjacent_pair_orbit (i j : Fin 10) (hne : i ≠ j) (h : ¬ adjacent i j) :
    ∃ p : Fin 10 → Fin 10, Function.Bijective p ∧
      (∀ u v : Fin 10, adjacent (p u) (p v) ↔ adjacent u v) ∧
      p i = 0 ∧ p j = 2 := by
  obtain ⟨hb, ha, hp, hq⟩ := pairAut_certificate i j
  exact ⟨pairAut i j, hb, ha, hp, by simpa [hne, h] using hq⟩

lemma vertex_orbit (i : Fin 10) :
    ∃ p : Fin 10 → Fin 10, Function.Bijective p ∧
      (∀ u v : Fin 10, adjacent (p u) (p v) ↔ adjacent u v) ∧ p i = 0 := by
  obtain ⟨hb, ha, hp, _⟩ := pairAut_certificate i i
  exact ⟨pairAut i i, hb, ha, hp⟩

def graphFn (x : Fin 10 → Bool) : Bool :=
  petersenEdges.any (fun e => x e.1 && x e.2)

lemma graphFn_posted (x : Fin 10 → Bool) :
    graphFn x = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
      x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
  simp [graphFn, petersenEdges, Bool.or_assoc]

lemma graphFn_eq_true (x : Fin 10 → Bool) :
    graphFn x = true ↔ ∃ i j : Fin 10, adjacent i j ∧ x i = true ∧ x j = true := by
  simp only [graphFn, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨⟨i, j⟩, hij, hi, hj⟩
    exact ⟨i, j, Or.inl hij, hi, hj⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    rcases hij with hij | hji
    · exact ⟨(i, j), hij, hi, hj⟩
    · exact ⟨(j, i), hji, hj, hi⟩

lemma graphFn_invariant (p : Fin 10 → Fin 10) (hs : Function.Surjective p)
    (hp : ∀ i j : Fin 10, adjacent (p i) (p j) ↔ adjacent i j)
    (x : Fin 10 → Bool) : graphFn (fun i => x (p i)) = graphFn x := by
  apply Bool.eq_iff_iff.mpr
  rw [graphFn_eq_true, graphFn_eq_true]
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    exact ⟨p i, p j, (hp i j).mpr hij, hi, hj⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    obtain ⟨a, rfl⟩ := hs i
    obtain ⟨b, rfl⟩ := hs j
    exact ⟨a, b, (hp a b).mp hij, hi, hj⟩

lemma pairAut_graphFn (i j : Fin 10) (x : Fin 10 → Bool) :
    graphFn (fun k => x (pairAut i j k)) = graphFn x := by
  obtain ⟨hb, ha, _, _⟩ := pairAut_certificate i j
  exact graphFn_invariant (pairAut i j) hb.2 ha x



open PEqualNP.CircuitLowerBounds

def renameWire (n : ℕ) (p : Fin n → Fin n) (i : ℕ) : ℕ :=
  if h : i < n then p ⟨i, h⟩ else i

def renameGate (n : ℕ) (p : Fin n → Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (renameWire n p)⟩

def renameCircuit (n : ℕ) (p : Fin n → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (renameGate n p), renameWire n p C.output⟩

def wireRelated (n : ℕ) (p : Fin n → Fin n) (w v : List Bool) : Prop :=
  ∀ i : ℕ, v.getD (renameWire n p i) false = w.getD i false

lemma related_ofFn (n : ℕ) (p : Fin n → Fin n) (x : Fin n → Bool) :
    wireRelated n p (List.ofFn (fun i => x (p i))) (List.ofFn x) := by
  intro i
  by_cases hi : i < n
  · simp [renameWire, hi]
  · simp only [renameWire, hi, dite_false]
    rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi)]

lemma related_append (n : ℕ) (p : Fin n → Fin n) (w v : List Bool)
    (hr : wireRelated n p w v) (hl : w.length = v.length) (hn : n ≤ w.length) (b : Bool) :
    wireRelated n p (w ++ [b]) (v ++ [b]) := by
  intro i
  by_cases hi : i < w.length
  · have hj : renameWire n p i < v.length := by
      by_cases his : i < n
      · simp only [renameWire, his, dite_true]
        have := (p ⟨i, his⟩).isLt
        omega
      · simpa [renameWire, his, ← hl] using hi
    rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ hi]
    exact hr i
  · have his : ¬ i < n := by omega
    simp only [renameWire, his, dite_false]
    by_cases he : i = w.length
    · subst i
      calc
        (v ++ [b]).getD w.length false = b := by rw [hl]; simp
        _ = (w ++ [b]).getD w.length false := by simp
    · rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]

lemma renamed_gate_value (n : ℕ) (p : Fin n → Fin n) (w v : List Bool)
    (hr : wireRelated n p w v) (g : Gate) :
    (renameGate n p g).op.eval ((renameGate n p g).inputs.map (fun i => v.getD i false)) =
      g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
  simp only [renameGate, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hr i

lemma related_fold (n : ℕ) (p : Fin n → Fin n) (gs : List Gate) :
    ∀ w v : List Bool, wireRelated n p w v → w.length = v.length → n ≤ w.length →
    wireRelated n p
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
      ((gs.map (renameGate n p)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v) := by
  induction gs with
  | nil => intro w v hr hl hn; exact hr
  | cons g gs ih =>
    intro w v hr hl hn
    simp only [List.map_cons, List.foldl_cons]
    rw [renamed_gate_value n p w v hr g]
    apply ih
    · exact related_append n p w v hr hl hn _
    · simpa using hl
    · simp only [List.length_append, List.length_singleton]
      omega

lemma renameCircuit_eval (n : ℕ) (p : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) :
    (renameCircuit n p C).eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (p i))) := by
  exact related_fold n p C.gates _ _ (related_ofFn n p x) (by simp) (by simp) C.output

lemma renameCircuit_size (n : ℕ) (p : Fin n → Fin n) (C : Circuit) :
    (renameCircuit n p C).size = C.size := by
  simp [renameCircuit, Circuit.size]

lemma renameCircuit_fanin (n : ℕ) (p : Fin n → Fin n) (C : Circuit)
    (h : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (renameCircuit n p C) := by
  intro g hg
  change g ∈ C.gates.map (renameGate n p) at hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  simpa [renameGate] using h q hq

lemma renameCircuit_has_not (n : ℕ) (p : Fin n → Fin n) (C : Circuit)
    (h : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ g ∈ (renameCircuit n p C).gates, g.op = GateOp.not := by
  obtain ⟨g, hg, hop⟩ := h
  exact ⟨renameGate n p g, List.mem_map.mpr ⟨g, hg, rfl⟩, hop⟩


lemma rename_computes (C : Circuit) (p : Fin 10 → Fin 10)
    (hp : Function.Surjective p)
    (ha : ∀ i j : Fin 10, adjacent (p i) (p j) ↔ adjacent i j)
    (hc : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = graphFn x) :
    ∀ x : Fin 10 → Bool, (renameCircuit 10 p C).eval (List.ofFn x) = graphFn x := by
  intro x
  rw [renameCircuit_eval, hc]
  exact graphFn_invariant p hp ha x

lemma canonical_first_pair (C : Circuit) (gop : GateOp) (gs : List Gate)
    (a b : Fin 10) (hab : a ≠ b)
    (hg : C.gates = ⟨gop, [a, b]⟩ :: gs)
    (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = graphFn x) :
    ∃ D : Circuit, D.size = C.size ∧ PEqualNP.MetaComplexity.FanInTwo D ∧
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = graphFn x) ∧
      (∃ t : List Gate, D.gates = ⟨gop, [0, if adjacent a b then 1 else 2]⟩ :: t) ∧
      ((∃ g ∈ C.gates, g.op = GateOp.not) → ∃ g ∈ D.gates, g.op = GateOp.not) := by
  obtain ⟨hb, ha, hp, hq⟩ := pairAut_certificate a b
  refine ⟨renameCircuit 10 (pairAut a b) C,
    renameCircuit_size 10 (pairAut a b) C,
    renameCircuit_fanin 10 (pairAut a b) C hf,
    rename_computes C (pairAut a b) hb.2 ha hc, ?_, ?_⟩
  · refine ⟨gs.map (renameGate 10 (pairAut a b)), ?_⟩
    simp [renameCircuit, hg, renameGate, renameWire, a.isLt, b.isLt, hp, hq, hab]
    split_ifs <;> rfl
  · exact renameCircuit_has_not 10 (pairAut a b) C

lemma canonical_first_not (C : Circuit) (gs : List Gate) (a : Fin 10)
    (hg : C.gates = ⟨GateOp.not, [a]⟩ :: gs)
    (hf : PEqualNP.MetaComplexity.FanInTwo C)
    (hc : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = graphFn x) :
    ∃ D : Circuit, D.size = C.size ∧ PEqualNP.MetaComplexity.FanInTwo D ∧
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = graphFn x) ∧
      ∃ t : List Gate, D.gates = ⟨GateOp.not, [0]⟩ :: t := by
  obtain ⟨hb, ha, hp, _⟩ := pairAut_certificate a a
  refine ⟨renameCircuit 10 (pairAut a a) C,
    renameCircuit_size 10 (pairAut a a) C,
    renameCircuit_fanin 10 (pairAut a a) C hf,
    rename_computes C (pairAut a a) hb.2 ha hc,
    gs.map (renameGate 10 (pairAut a a)), ?_⟩
  simp [renameCircuit, hg, renameGate, renameWire, a.isLt, hp]

end PEqualNP.Outside.L_meta_2592
