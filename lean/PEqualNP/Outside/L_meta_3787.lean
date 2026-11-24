import Mathlib.Tactic.IntervalCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3787_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def reindexStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def reindexRun (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl reindexStep w

def selectedInputs : List (Fin 26) :=
  [2, 4, 5, 6, 7, 8, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]

def reindexWire (i : ℕ) : ℕ :=
  if i = 0 then 2 else if i < 6 then i + 3 else if i < 9 then i + 4 else i + 5

def reindexGate (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map reindexWire⟩

def reindexCircuit (C : Circuit) : Circuit :=
  ⟨C.gates.map reindexGate, reindexWire C.output⟩

lemma reindexWire_lt {i k : ℕ} (hk : 21 ≤ k) (hi : i < k) :
    reindexWire i < k + 5 := by
  unfold reindexWire
  split_ifs <;> omega

lemma reindexWire_ge {i : ℕ} (hi : 21 ≤ i) : reindexWire i = i + 5 := by
  simp [reindexWire, show i ≠ 0 by omega, show ¬i < 6 by omega,
    show ¬i < 9 by omega]

lemma reindex_getD_snoc_lt (w : List Bool) (b : Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

lemma reindex_getD_snoc_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD]

lemma reindexRun_agrees (gs : List Gate) (w₁ w₂ : List Bool)
    (h1 : 21 ≤ w₁.length) (h2 : w₂.length = w₁.length + 5)
    (hagree : ∀ i, w₂.getD (reindexWire i) false = w₁.getD i false) :
    ∀ i, (reindexRun (gs.map reindexGate) w₂).getD (reindexWire i) false =
      (reindexRun gs w₁).getD i false := by
  induction gs generalizing w₁ w₂ with
  | nil => exact hagree
  | cons g gs ih =>
    simp only [List.map_cons]
    change ∀ i, (reindexRun (gs.map reindexGate) (reindexStep w₂ (reindexGate g))).getD
      (reindexWire i) false = (reindexRun gs (reindexStep w₁ g)).getD i false
    apply ih (reindexStep w₁ g) (reindexStep w₂ (reindexGate g))
    · simp [reindexStep]; omega
    · simp [reindexStep]; omega
    · intro i
      have heval : (reindexGate g).op.eval
          ((reindexGate g).inputs.map fun j => w₂.getD j false) =
          g.op.eval (g.inputs.map fun j => w₁.getD j false) := by
        simp only [reindexGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro j _
        exact hagree j
      by_cases hlt : i < w₁.length
      · have hlt' : reindexWire i < w₂.length := by
          rw [h2]
          exact reindexWire_lt h1 hlt
        rw [reindexStep, reindexStep, reindex_getD_snoc_lt _ _ _ hlt',
          reindex_getD_snoc_lt _ _ _ hlt]
        exact hagree i
      · by_cases heq : i = w₁.length
        · subst i
          have hrm : reindexWire w₁.length = w₂.length := by
            rw [reindexWire_ge h1, h2]
          rw [hrm, reindexStep, reindexStep, reindex_getD_snoc_eq,
            reindex_getD_snoc_eq, heval]
        · have hge1 : (reindexStep w₁ g).length ≤ i := by
            simp [reindexStep]; omega
          have hge2 : (reindexStep w₂ (reindexGate g)).length ≤ reindexWire i := by
            rw [reindexWire_ge (by omega)]
            simp [reindexStep]; omega
          rw [List.getD_eq_default _ _ hge2, List.getD_eq_default _ _ hge1]

lemma selectedInputs_getD (x : Fin 26 → Bool) (i : ℕ) :
    (List.ofFn x).getD (reindexWire i) false =
      (selectedInputs.map x).getD i false := by
  by_cases hi : i < 21
  · interval_cases i <;> simp [selectedInputs, reindexWire, List.getD]
  · have hge : 26 ≤ reindexWire i := by
      rw [reindexWire_ge (by omega)]
      omega
    rw [List.getD_eq_default _ _ (by simpa using hge),
      List.getD_eq_default _ _ (by simp [selectedInputs]; omega)]

lemma reindexCircuit_size (C : Circuit) : (reindexCircuit C).size = C.size := by
  simp [reindexCircuit, Circuit.size]

lemma reindexCircuit_monotone (C : Circuit) (hC : Monotone2 C) :
    Monotone2 (reindexCircuit C) := by
  intro g hg
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
  obtain ⟨hop, hlen⟩ := hC g₀ hg₀
  exact ⟨hop, by simpa [reindexGate] using hlen⟩

lemma reindexCircuit_output (C : Circuit) (hC : C.output < 21 + C.size) :
    (reindexCircuit C).output < 26 + (reindexCircuit C).size := by
  rw [reindexCircuit_size]
  change reindexWire C.output < 26 + C.size
  have h := reindexWire_lt (k := 21 + C.size) (by omega) hC
  omega

lemma reindexCircuit_eval (C : Circuit) (x : Fin 26 → Bool) :
    (reindexCircuit C).eval (List.ofFn x) = C.eval (selectedInputs.map x) := by
  change (reindexRun (C.gates.map reindexGate) (List.ofFn x)).getD
    (reindexWire C.output) false = (reindexRun C.gates (selectedInputs.map x)).getD C.output false
  apply reindexRun_agrees C.gates (selectedInputs.map x) (List.ofFn x)
  · simp [selectedInputs]
  · simp [selectedInputs]
  · exact selectedInputs_getD x

end PEqualNP.Outside.L_meta_3787_aux
