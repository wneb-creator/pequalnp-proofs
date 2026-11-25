import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def liftRun (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def liftIndex (n m : ℕ) (f : Fin n → Fin m) (i : ℕ) : ℕ :=
  if h : i < n then (f ⟨i, h⟩).val else m + (i - n)

def liftedGate (n m : ℕ) (f : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (liftIndex n m f)⟩

lemma lift_snoc_read (w : List Bool) (v : Bool) (i : ℕ) :
    (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
  induction w generalizing i with
  | nil => cases i <;> rfl
  | cons b w ih =>
    cases i with
    | zero => rfl
    | succ i => simpa using ih i

lemma liftIndex_level (n m : ℕ) (f : Fin n → Fin m) (k i : ℕ) :
    liftIndex n m f i = m + k ↔ i = n + k := by
  unfold liftIndex
  split <;> rename_i h
  · have bound := (f ⟨i, h⟩).isLt
    omega
  · omega

lemma liftRun_equiv (n m : ℕ) (f : Fin n → Fin m) (gs : List Gate)
    (k : ℕ) (old new : List Bool)
    (oldlen : old.length = n + k) (newlen : new.length = m + k)
    (reads : ∀ i, new.getD (liftIndex n m f i) false = old.getD i false) :
    ∀ i, (liftRun (gs.map (liftedGate n m f)) new).getD (liftIndex n m f i) false =
      (liftRun gs old).getD i false := by
  induction gs generalizing k old new with
  | nil => exact reads
  | cons g gs ih =>
    let value := g.op.eval (g.inputs.map fun i => old.getD i false)
    have same : g.op.eval (g.inputs.map fun i => new.getD (liftIndex n m f i) false) = value := by
      congr 1
      apply List.map_congr_left
      intro i _
      exact reads i
    have next : ∀ i,
        (new ++ [value]).getD (liftIndex n m f i) false = (old ++ [value]).getD i false := by
      intro i
      simp only [lift_snoc_read, oldlen, newlen, liftIndex_level, reads]
    have proof := ih (k + 1) (old ++ [value]) (new ++ [value])
      (by simp [oldlen]; omega) (by simp [newlen]; omega) next
    simpa only [liftRun, List.map_cons, List.foldl_cons, liftedGate,
      List.map_map, Function.comp_def, same] using proof

def liftedCircuit (n m : ℕ) (f : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (liftedGate n m f), liftIndex n m f C.output⟩

lemma liftedCircuit_size (n m : ℕ) (f : Fin n → Fin m) (C : Circuit) :
    (liftedCircuit n m f C).size = C.size := by
  simp [liftedCircuit, Circuit.size]

lemma liftedCircuit_monotone (n m : ℕ) (f : Fin n → Fin m) (C : Circuit)
    (hm : Monotone2 C) : Monotone2 (liftedCircuit n m f C) := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  obtain ⟨op, arity⟩ := hm a ha
  exact ⟨op, by simpa [liftedGate] using arity⟩

lemma liftedCircuit_eval (n m : ℕ) (f : Fin n → Fin m) (C : Circuit)
    (x : Fin m → Bool) :
    (liftedCircuit n m f C).eval (List.ofFn x) =
      C.eval (List.ofFn fun i : Fin n => x (f i)) := by
  apply liftRun_equiv n m f C.gates 0 _ _ (by simp) (by simp)
  intro i
  by_cases h : i < n
  · simp [liftIndex, h, List.getD_eq_getElem?_getD]
  · have hm : m ≤ liftIndex n m f i := by simp [liftIndex, h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simpa using hm),
      List.getElem?_eq_none (by simp only [List.length_ofFn]; omega)]

end PEqualNP.Outside.L_meta_650
