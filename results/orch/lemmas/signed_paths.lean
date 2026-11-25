import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds

abbrev SpDatum := (Bool × Bool) × (Bool × Bool)

def spZero : SpDatum := ((false, false), (false, false))

def spGood (d : SpDatum) : Prop :=
  (d.1.1 = false → d.2.2 ≤ d.2.1) ∧ (d.1.2 = false → d.2.1 ≤ d.2.2)

def spAnd (a b : SpDatum) : SpDatum :=
  ((a.1.1 || b.1.1, a.1.2 || b.1.2), (a.2.1 && b.2.1, a.2.2 && b.2.2))

def spOr (a b : SpDatum) : SpDatum :=
  ((a.1.1 || b.1.1, a.1.2 || b.1.2), (a.2.1 || b.2.1, a.2.2 || b.2.2))

def spNot (a : SpDatum) : SpDatum := ((a.1.2, a.1.1), (!a.2.1, !a.2.2))

lemma spAnd_good : ∀ a b : SpDatum, spGood a → spGood b → spGood (spAnd a b) := by
  decide

lemma spOr_good : ∀ a b : SpDatum, spGood a → spGood b → spGood (spOr a b) := by
  decide

lemma spNot_good : ∀ a : SpDatum, spGood a → spGood (spNot a) := by
  decide

def spGate (op : GateOp) (ds : List SpDatum) : SpDatum :=
  match op with
  | .and => ds.foldr spAnd ((false, false), (true, true))
  | .or => ds.foldr spOr spZero
  | .not => spNot (ds.headD spZero)
  | op => ((true, true), (op.eval (ds.map (fun d => d.2.1)),
      op.eval (ds.map (fun d => d.2.2))))

def spFlagGate (op : GateOp) (ds : List (Bool × Bool)) : Bool × Bool :=
  match op with
  | .and | .or => ds.foldr (fun a b => (a.1 || b.1, a.2 || b.2)) (false, false)
  | .not => let a := ds.headD (false, false); (a.2, a.1)
  | _ => (true, true)

lemma spFold_good (join : SpDatum → SpDatum → SpDatum)
    (hj : ∀ a b, spGood a → spGood b → spGood (join a b))
    (base : SpDatum) (hb : spGood base) :
    ∀ ds : List SpDatum, (∀ d ∈ ds, spGood d) → spGood (ds.foldr join base) := by
  intro ds
  induction ds with
  | nil => intro _; exact hb
  | cons d ds ih =>
    intro hd
    exact hj d _ (hd d (by simp)) (ih (fun e he => hd e (by simp [he])))

lemma spGate_good (op : GateOp) (ds : List SpDatum) (hd : ∀ d ∈ ds, spGood d) :
    spGood (spGate op ds) := by
  cases op with
  | and => exact spFold_good spAnd spAnd_good _ (by decide) ds hd
  | or => exact spFold_good spOr spOr_good _ (by decide) ds hd
  | not =>
    cases ds with
    | nil => exact spNot_good spZero (by decide)
    | cons d ds => exact spNot_good d (hd d (by simp))
  | mod m => simp [spGate, spGood]
  | maj => simp [spGate, spGood]

lemma spGate_flags (op : GateOp) (ds : List SpDatum) :
    (spGate op ds).1 = spFlagGate op (ds.map Prod.fst) := by
  cases op with
  | and => induction ds <;> simp_all [spGate, spFlagGate, spAnd]
  | or => induction ds <;> simp_all [spGate, spFlagGate, spOr, spZero]
  | not => cases ds <;> rfl
  | mod m => rfl
  | maj => rfl

lemma spGate_low (op : GateOp) (ds : List SpDatum) :
    (spGate op ds).2.1 = op.eval (ds.map (fun d => d.2.1)) := by
  cases op with
  | and => induction ds <;> simp_all [spGate, spAnd, GateOp.eval]
  | or => induction ds <;> simp_all [spGate, spOr, spZero, GateOp.eval]
  | not => cases ds <;> rfl
  | mod m => rfl
  | maj => rfl

lemma spGate_high (op : GateOp) (ds : List SpDatum) :
    (spGate op ds).2.2 = op.eval (ds.map (fun d => d.2.2)) := by
  cases op with
  | and => induction ds <;> simp_all [spGate, spAnd, GateOp.eval]
  | or => induction ds <;> simp_all [spGate, spOr, spZero, GateOp.eval]
  | not => cases ds <;> rfl
  | mod m => rfl
  | maj => rfl

def spStep (ds : List SpDatum) (g : Gate) : List SpDatum :=
  ds ++ [spGate g.op (g.inputs.map (fun j => ds.getD j spZero))]

def spRun (gs : List Gate) (ds : List SpDatum) : List SpDatum := gs.foldl spStep ds

lemma spGet_good (ds : List SpDatum) (hd : ∀ d ∈ ds, spGood d) (j : ℕ) :
    spGood (ds.getD j spZero) := by
  induction ds generalizing j with
  | nil => exact (by decide : spGood spZero)
  | cons d ds ih =>
    cases j with
    | zero => exact hd d (by simp)
    | succ j => exact ih (fun e he => hd e (by simp [he])) j

lemma spStep_good (ds : List SpDatum) (g : Gate) (hd : ∀ d ∈ ds, spGood d) :
    ∀ d ∈ spStep ds g, spGood d := by
  intro d hm
  simp only [spStep, List.mem_append, List.mem_singleton] at hm
  rcases hm with old | rfl
  · exact hd d old
  · apply spGate_good
    intro e he
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp he
    exact spGet_good ds hd j

lemma spRun_good (gs : List Gate) : ∀ ds : List SpDatum,
    (∀ d ∈ ds, spGood d) → ∀ d ∈ spRun gs ds, spGood d := by
  induction gs with
  | nil => intro ds hd; exact hd
  | cons g gs ih =>
    intro ds hd
    exact ih (spStep ds g) (spStep_good ds g hd)

lemma spRun_project {α : Type} (p : SpDatum → α) (zero : α)
    (applyGate : GateOp → List α → α) (hp : p spZero = zero)
    (hg : ∀ op ds, p (spGate op ds) = applyGate op (ds.map p))
    (gs : List Gate) (ds : List SpDatum) :
    (spRun gs ds).map p = gs.foldl (fun w g =>
      w ++ [applyGate g.op (g.inputs.map (fun j => w.getD j zero))]) (ds.map p) := by
  induction gs generalizing ds with
  | nil => rfl
  | cons g gs ih =>
    change (spRun gs (spStep ds g)).map p = _
    rw [ih]
    congr 1
    have get (j : ℕ) : p (ds.getD j spZero) = (ds.map p).getD j zero := by
      rw [← hp]
      exact (List.getD_map ds spZero p).symm
    simp only [spStep, List.map_append, List.map_singleton, hg, List.map_map]
    simp only [Function.comp_def, get]

def spInitial {n : ℕ} (i : Fin n) (x : Fin n → Bool) : List SpDatum :=
  List.ofFn (fun j => ((decide (j = i), false),
    ((Function.update x i false) j, (Function.update x i true) j)))

def spPaths (C : Circuit) (n : ℕ) (i : Fin n) : List (Bool × Bool) :=
  C.gates.foldl (fun w g =>
    w ++ [spFlagGate g.op (g.inputs.map (fun j => w.getD j (false, false)))])
    (List.ofFn (fun j : Fin n => (decide (j = i), false)))

lemma spInitial_good {n : ℕ} (i : Fin n) (x : Fin n → Bool) :
    ∀ d ∈ spInitial i x, spGood d := by
  intro d hd
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hd
  by_cases h : j = i
  · subst j
    simp [spGood]
  · simp [spGood, h, Function.update_of_ne h]

lemma spOutput_sound (C : Circuit) (n : ℕ) (i : Fin n) (x : Fin n → Bool) :
    let signs := (spPaths C n i).getD C.output (false, false)
    (signs.1 = false → C.eval (List.ofFn (Function.update x i true)) ≤
      C.eval (List.ofFn (Function.update x i false))) ∧
    (signs.2 = false → C.eval (List.ofFn (Function.update x i false)) ≤
      C.eval (List.ofFn (Function.update x i true))) := by
  let ds := spRun C.gates (spInitial i x)
  have good : spGood (ds.getD C.output spZero) :=
    spGet_good ds (spRun_good C.gates (spInitial i x) (spInitial_good i x)) C.output
  have flags : ds.map Prod.fst = spPaths C n i := by
    simpa only [ds, spPaths, spInitial, List.map_ofFn] using
      spRun_project Prod.fst (false, false) spFlagGate rfl spGate_flags C.gates (spInitial i x)
  have low : ds.map (fun d => d.2.1) = C.wires (List.ofFn (Function.update x i false)) := by
    simpa only [ds, Circuit.wires, spInitial, List.map_ofFn] using
      spRun_project (fun d => d.2.1) false GateOp.eval rfl spGate_low C.gates (spInitial i x)
  have high : ds.map (fun d => d.2.2) = C.wires (List.ofFn (Function.update x i true)) := by
    simpa only [ds, Circuit.wires, spInitial, List.map_ofFn] using
      spRun_project (fun d => d.2.2) false GateOp.eval rfl spGate_high C.gates (spInitial i x)
  have readFlags : (ds.getD C.output spZero).1 =
      (spPaths C n i).getD C.output (false, false) := by
    rw [← flags]
    exact (List.getD_map ds spZero Prod.fst).symm
  have readLow : (ds.getD C.output spZero).2.1 =
      C.eval (List.ofFn (Function.update x i false)) := by
    unfold Circuit.eval
    rw [← low]
    exact (List.getD_map ds spZero (fun d => d.2.1)).symm
  have readHigh : (ds.getD C.output spZero).2.2 =
      C.eval (List.ofFn (Function.update x i true)) := by
    unfold Circuit.eval
    rw [← high]
    exact (List.getD_map ds spZero (fun d => d.2.2)).symm
  change (_ = false → _) ∧ (_ = false → _)
  simpa only [spGood, readFlags, readLow, readHigh] using good

lemma spPositive_of_witness (C : Circuit) (n : ℕ) (i : Fin n) (x : Fin n → Bool)
    (hlo : C.eval (List.ofFn (Function.update x i false)) = false)
    (hhi : C.eval (List.ofFn (Function.update x i true)) = true) :
    ((spPaths C n i).getD C.output (false, false)).1 = true := by
  cases hs : ((spPaths C n i).getD C.output (false, false)).1
  · have h := (spOutput_sound C n i x).1 hs
    rw [hlo, hhi] at h
    exact False.elim ((by decide : ¬ (true : Bool) ≤ false) h)
  · rfl

end PEqualNP.Outside.L_meta_2592
