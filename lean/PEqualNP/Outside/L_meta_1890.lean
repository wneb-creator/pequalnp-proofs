import Mathlib.Data.Fin.VecNotation
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890

def edge (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def seed (p : Fin 10 → Fin 10) (x : Fin 10 → Bool) : List Bool :=
  List.ofFn (x ∘ p) ++ [x 0 && x 2]

def neighbor : Fin 10 → Fin 10 := ![1, 0, 1, 2, 3, 0, 1, 2, 3, 4]

def singleton (v : Fin 10) (i : Fin 10) : Bool := i == v

def pair (v : Fin 10) (i : Fin 10) : Bool := (i == v) || (i == neighbor v)

lemma witnesses : ∀ v : Fin 10,
    edge (singleton (neighbor v)) = false ∧ edge (pair v) = true ∧
    (singleton (neighbor v) 0 && singleton (neighbor v) 2) = false ∧
    (pair v 0 && pair v 2) = false := by
  decide +kernel

lemma missing_counterexample (C : PEqualNP.CircuitLowerBounds.Circuit)
    (p : Fin 10 → Fin 10) (v : Fin 10) (hv : ∀ i, p i ≠ v) :
    ∃ x : Fin 10 → Bool, C.eval (seed p x) ≠ edge x := by
  have hm : singleton (neighbor v) ∘ p = pair v ∘ p := by
    funext i
    simp [singleton, pair, hv i]
  have hs : seed p (singleton (neighbor v)) = seed p (pair v) := by
    simp only [seed, hm, (witnesses v).2.2.1, (witnesses v).2.2.2]
  by_cases h : C.eval (seed p (singleton (neighbor v))) = edge (singleton (neighbor v))
  · refine ⟨pair v, ?_⟩
    rw [← hs, h, (witnesses v).1, (witnesses v).2.1]
    decide
  · exact ⟨singleton (neighbor v), h⟩

lemma computes_surjective (C : PEqualNP.CircuitLowerBounds.Circuit)
    (p : Fin 10 → Fin 10) (h : ∀ x, C.eval (seed p x) = edge x) :
    Function.Surjective p := by
  classical
  intro v
  by_contra hv
  have missing : ∀ i, p i ≠ v := fun i hi => hv ⟨i, hi⟩
  obtain ⟨x, hx⟩ := missing_counterexample C p v missing
  exact hx (h x)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def addr (p : Fin 10 → Fin 10) (i : Nat) : Nat :=
  if h : i < 10 then (p ⟨i, h⟩).val else i

def relabelGate (p : Fin 10 → Fin 10) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (addr p)⟩

def relabel (p : Fin 10 → Fin 10) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relabelGate p), addr p C.output⟩

lemma relabel_fan (p : Fin 10 → Fin 10) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (relabel p C) := by
  intro g hg
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp
    (show g ∈ C.gates.map (relabelGate p) from hg)
  exact ⟨(h u hu).1, by simpa [relabelGate] using (h u hu).2⟩

lemma relabel_size (p : Fin 10 → Fin 10) (C : Circuit) :
    (relabel p C).size = C.size := by
  simp [relabel, Circuit.size]

lemma relabel_run (p : Fin 10 → Fin 10) (gs : List Gate) (w z : List Bool)
    (hlen : w.length = z.length) (hbase : 10 ≤ w.length)
    (agree : ∀ i, z.getD (addr p i) false = w.getD i false) :
    ∀ i, ((⟨gs.map (relabelGate p), 0⟩ : Circuit).wires z).getD (addr p i) false =
      ((⟨gs, 0⟩ : Circuit).wires w).getD i false := by
  induction gs generalizing w z with
  | nil => exact agree
  | cons g gs ih =>
    let val := g.op.eval (g.inputs.map fun i => w.getD i false)
    have step : (relabelGate p g).op.eval
        ((relabelGate p g).inputs.map fun i => z.getD i false) = val := by
      simp only [relabelGate, List.map_map, Function.comp_def, agree, val]
    change ∀ i, ((⟨gs.map (relabelGate p), 0⟩ : Circuit).wires (z ++ [_])).getD
      (addr p i) false = ((⟨gs, 0⟩ : Circuit).wires (w ++ [val])).getD i false
    rw [step]
    apply ih _ _ (by simp [hlen]) (by simp; omega)
    intro i
    by_cases hi : i < w.length
    · have hr : addr p i < z.length := by
        by_cases hn : i < 10
        · have hp := (p ⟨i, hn⟩).isLt
          simp only [addr, dite_eq_left hn]
          omega
        · simp only [addr, dite_eq_right hn]
          omega
      rw [List.getD_append _ _ _ _ hr, List.getD_append _ _ _ _ hi]
      exact agree i
    · have hn : ¬i < 10 := by omega
      simp only [addr, dite_eq_right hn]
      rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega), hlen]

lemma relabel_eval (p : Fin 10 → Fin 10) (C : Circuit) (x : Fin 10 → Bool) :
    (relabel p C).eval (seed id x) = C.eval (seed p x) := by
  have read_input (f : Fin 10 → Bool) (i : Fin 10) :
      (List.ofFn f).getD i.val false = f i := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt,
      ↓reduceDIte, Option.getD_some]
  have initial (i : Nat) :
      (seed id x).getD (addr p i) false = (seed p x).getD i false := by
    by_cases hi : i < 10
    · simp only [addr, dite_eq_left hi, seed]
      rw [List.getD_append _ _ _ _ (by simpa using (p ⟨i, hi⟩).isLt),
        List.getD_append _ _ _ _ (by simpa using hi)]
      exact (read_input (x ∘ id) (p ⟨i, hi⟩)).trans (read_input (x ∘ p) ⟨i, hi⟩).symm
    · simp only [addr, dite_eq_right hi, seed]
      rw [List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by simp; omega)]
      simp
  exact relabel_run p C.gates (seed p x) (seed id x) (by simp [seed])
    (by simp [seed]) initial C.output

end PEqualNP.Outside.L_meta_1890
