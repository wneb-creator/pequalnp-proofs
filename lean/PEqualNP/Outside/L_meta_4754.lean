import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.Outside.L_meta_4754

def wire (i : ℕ) : ℕ :=
  if 16 ≤ i then i + 2 else if i = 10 then 17 else if i = 15 then 16 else i

def renameGate (g : Gate) : Gate := ⟨g.op, g.inputs.map wire⟩

def front : Gate := ⟨.or,[10,15]⟩

def extend (c : Circuit) : Circuit := ⟨front :: c.gates.map renameGate, wire c.output⟩

def value (w : List Bool) (g : Gate) : Bool := g.op.eval (g.inputs.map fun i => w.getD i false)

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl (fun x g => x ++ [value x g]) w

lemma snocRead (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i = w.length then b else w.getD i false := by
  by_cases h : i = w.length
  · subst i
    simp
  · simp only [h, if_false]
    by_cases hi : i < w.length
    · exact List.getD_append _ _ _ _ hi
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

-- Old gate j moves from wire 16+j to 18+j, including for out-of-range reads.
lemma simulate (gs : List Gate) (u w : List Bool) (hw : 16 ≤ w.length)
    (hu : u.length = w.length + 2) (agree : ∀ i, u.getD (wire i) false = w.getD i false) :
    ∀ i, (run (gs.map renameGate) u).getD (wire i) false = (run gs w).getD i false := by
  induction gs generalizing u w with
  | nil => exact agree
  | cons g gs ih =>
    have ev : value u (renameGate g) = value w g := by
      unfold value renameGate
      rw [List.map_map]
      exact congrArg g.op.eval (List.map_congr_left (fun i _ => agree i))
    change ∀ i, (run (gs.map renameGate) (u ++ [value u (renameGate g)])).getD (wire i) false =
      (run gs (w ++ [value w g])).getD i false
    rw [ev]
    apply ih _ _ (by simp; omega) (by simp; omega)
    intro i
    have hit : wire i = u.length ↔ i = w.length := by unfold wire; split_ifs <;> omega
    simp only [snocRead, hit, agree]

def oldInput (x : Fin 17 → Bool) (i : Fin 16) : Bool :=
  if i = 10 then x 10 || x 15 else if i = 15 then x 16 else x (Fin.ofNat 17 i.val)

lemma initial (x : Fin 17 → Bool) (i : ℕ) :
    (List.ofFn x ++ [x 10 || x 15]).getD (wire i) false = (List.ofFn (oldInput x)).getD i false := by
  by_cases hi : i < 16
  · have each (j : Fin 16) : (List.ofFn x ++ [x 10 || x 15]).getD (wire j.val) false =
        (List.ofFn (oldInput x)).getD j.val false := by
      fin_cases j <;> rfl
    exact each ⟨i,hi⟩
  · have ge : 16 ≤ i := by omega
    rw [List.getD_eq_default _ _ (by simp [wire,ge] <;> omega), List.getD_eq_default _ _ (by simp <;> omega)]

lemma monotone (c : Circuit) (hc : Monotone2 c) : Monotone2 (extend c) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | h
  · simp [front]
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp h
    simpa [renameGate] using hc a ha

lemma backward (c : Circuit) (hc : ReadsBack 16 c) : ReadsBack 17 (extend c) := by
  intro j hj i hi
  cases j with
  | zero =>
    change i ∈ [10,15] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    omega
  | succ j =>
    have hj' : j < c.gates.length := by simpa [extend] using hj
    have same : gateAt (extend c) (j+1) = renameGate (gateAt c j) := by
      unfold gateAt
      change (c.gates.map renameGate).getD j _ = renameGate (c.gates.getD j _)
      rw [List.getD_eq_getElem _ _ (by simpa using hj'), List.getD_eq_getElem _ _ hj']
      simp
    rw [same] at hi
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hi
    have h := hc j hj' k hk
    unfold wire
    split_ifs <;> omega

end PEqualNP.Outside.L_meta_4754

open PEqualNP.Outside.L_meta_4754

theorem PEqualNP.Outside.L_meta_4754 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (16 : ℕ) x1 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (17 : ℕ) x4 ∧ x4.size ≤ x1.size + (1 : ℕ) ∧ ∀ (x5 : Fin (17 : ℕ) → Bool), PEqualNP.MetaComplexity.circuitFun (17 : ℕ) x4 x5 = PEqualNP.MetaComplexity.circuitFun (16 : ℕ) x1 fun (x6 : Fin (16 : ℕ)) => if x6 = (10 : Fin (16 : ℕ)) then x5 (10 : Fin (17 : ℕ)) || x5 (15 : Fin (17 : ℕ)) else if x6 = (15 : Fin (16 : ℕ)) then x5 (16 : Fin (17 : ℕ)) else x5 (Fin.ofNat (17 : ℕ) ↑x6) := by
  intro c hm hb
  refine ⟨extend c, monotone c hm, backward c hb, by simp [extend, Circuit.size], ?_⟩
  intro x
  have ef : value (List.ofFn x) front = (x 10 || x 15) := by simp [value,front,GateOp.eval]
  change (run (c.gates.map renameGate) (List.ofFn x ++ [value (List.ofFn x) front])).getD (wire c.output) false =
    (run c.gates (List.ofFn (oldInput x))).getD c.output false
  rw [ef]
  exact simulate c.gates _ _ (by simp) (by simp) (initial x) c.output
