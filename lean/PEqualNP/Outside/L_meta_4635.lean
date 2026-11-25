import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4635

open PEqualNP.CircuitLowerBounds

def rd (g : Gate) : List ℕ := List.take (bif g.op.eval [false] then 1 else 2) g.inputs

def F (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl F x := rfl

def OkGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem ok_of_fan (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C) (g : Gate) (hg : g ∈ C.gates) :
    OkGate g := by
  obtain ⟨h1, h2⟩ := h g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
  exact ⟨h1, h2⟩

theorem evalRd (g : Gate) (hg : OkGate g) (f f' : ℕ → Bool) (h : ∀ i ∈ rd g, f i = f' i) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  obtain ⟨hop, hl⟩ := hg
  rcases hop with hop | hop | hop
  · have : rd g = g.inputs := by
      simp only [rd, hop, GateOp.eval]
      exact List.take_of_length_le (by simpa using hl)
    rw [this] at h
    rw [List.map_congr_left h]
  · have : rd g = g.inputs := by
      simp only [rd, hop, GateOp.eval]
      exact List.take_of_length_le (by simpa using hl)
    rw [this] at h
    rw [List.map_congr_left h]
  · rw [hop]
    simp only [rd, hop, GateOp.eval] at h
    cases hin : g.inputs with
    | nil => simp
    | cons a t =>
      rw [hin] at h
      simp only [List.map_cons]
      rw [h a (by simp)]
      simp [GateOp.eval]

theorem fold_len (gs : List Gate) (w : List Bool) : (gs.foldl F w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [F, List.length_append, List.length_cons, List.length_nil]
    omega

def dl (w i : ℕ) : ℕ := if i < w then i else i - 1

def rg (w : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (dl w)⟩

theorem F_rg (Q Q' : List Bool) (w : ℕ) (g : Gate) (hg : OkGate g)
    (h : ∀ i ∈ rd g, Q'.getD (dl w i) false = Q.getD i false) :
    (rg w g).op.eval ((rg w g).inputs.map fun i => Q'.getD i false)
      = g.op.eval (g.inputs.map fun i => Q.getD i false) := by
  simp only [rg, List.map_map]
  exact evalRd g hg _ _ h

theorem stageA (w : ℕ) (A : List Gate) (hA : ∀ g ∈ A, OkGate g) :
    ∀ Q : List Bool, Q.length + A.length ≤ w → (A.map (rg w)).foldl F Q = A.foldl F Q := by
  induction A with
  | nil => intro Q _; rfl
  | cons g A ih =>
    intro Q hQ
    simp only [List.map_cons, List.foldl_cons]
    have hg := hA g (by simp)
    have hF : F Q (rg w g) = F Q g := by
      unfold F
      rw [F_rg Q Q w g hg]
      intro i _
      simp only [List.length_cons] at hQ
      by_cases hiw : i < w
      · simp [dl, hiw]
      · simp only [dl, hiw, ite_false]
        rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
    rw [hF]
    apply ih (fun g' hg' => hA g' (by simp [hg']))
    simp only [F, List.length_append, List.length_cons, List.length_nil, List.length_cons] at hQ ⊢
    omega

theorem key (P M : List Bool) (v : Bool) (w : ℕ) (hP : P.length = w) (i : ℕ) (hi : i ≠ w) :
    (P ++ M).getD (dl w i) false = (P ++ v :: M).getD i false := by
  by_cases hiw : i < w
  · simp only [dl, hiw, ite_true]
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
  · simp only [dl, hiw, ite_false]
    rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), hP]
    obtain ⟨k, hk⟩ : ∃ k, i - w = k + 1 := ⟨i - w - 1, by omega⟩
    rw [hk, List.getD_cons_succ]
    congr 1
    omega

theorem stageB (w : ℕ) (P : List Bool) (v : Bool) (hP : P.length = w) (B : List Gate)
    (hB : ∀ g ∈ B, OkGate g ∧ w ∉ rd g) :
    ∀ M : List Bool, ∀ i, i ≠ w →
      ((B.map (rg w)).foldl F (P ++ M)).getD (dl w i) false = (B.foldl F (P ++ v :: M)).getD i false := by
  induction B with
  | nil => intro M i hi; exact key P M v w hP i hi
  | cons g B ih =>
    intro M i hi
    simp only [List.map_cons, List.foldl_cons]
    have hg := hB g (by simp)
    have h1 : F (P ++ M) (rg w g) = P ++ (M ++ [g.op.eval (g.inputs.map fun i => (P ++ v :: M).getD i false)]) := by
      unfold F
      rw [F_rg (P ++ v :: M) (P ++ M) w g hg.1, List.append_assoc]
      intro i hi
      exact key P M v w hP i (fun h => hg.2 (h ▸ hi))
    have h2 : F (P ++ v :: M) g = P ++ v :: (M ++ [g.op.eval (g.inputs.map fun i => (P ++ v :: M).getD i false)]) := by
      unfold F
      simp
    rw [h1, h2]
    exact ih (fun g' hg' => hB g' (by simp [hg'])) _ i hi

theorem del_getD (n j : ℕ) (gs : List Gate) (hj : j < gs.length)
    (hok : ∀ g ∈ gs, OkGate g) (hw : ∀ g ∈ gs.drop (j + 1), n + j ∉ rd g) (x : List Bool) (hx : x.length = n)
    (i : ℕ) (hi : i ≠ n + j) :
    (((gs.eraseIdx j).map (rg (n + j))).foldl F x).getD (dl (n + j) i) false
      = (gs.foldl F x).getD i false := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [List.drop_eq_getElem_cons hj]
  have herase : gs.eraseIdx j = gs.take j ++ gs.drop (j + 1) := List.eraseIdx_eq_take_drop_succ gs j
  rw [herase, List.map_append, List.foldl_append]
  conv_rhs => rw [hsplit, List.foldl_append, List.foldl_cons]
  rw [stageA (n + j) (gs.take j) (fun g hg => hok g (List.mem_of_mem_take hg)) x
    (by rw [hx, List.length_take]; omega)]
  have hP : (List.foldl F x (gs.take j)).length = n + j := by
    rw [fold_len, hx, List.length_take]; omega
  have := stageB (n + j) (List.foldl F x (gs.take j))
    (gs[j].op.eval (gs[j].inputs.map fun i => (List.foldl F x (gs.take j)).getD i false)) hP
    (gs.drop (j + 1)) (fun g hg => ⟨hok g (List.mem_of_mem_drop hg), hw g hg⟩) [] i hi
  simpa [F] using this

theorem fold_pre (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl F w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp only [F, List.length_append, List.length_cons, List.length_nil]; omega)]
    simp only [F, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem take_getD (gs : List Gate) (w : List Bool) (k i : ℕ) (hi : i < w.length + k) (hk : k ≤ gs.length) :
    ((gs.take k).foldl F w).getD i false = (gs.foldl F w).getD i false := by
  have hsplit : gs.foldl F w = (gs.drop k).foldl F ((gs.take k).foldl F w) := by
    rw [← List.foldl_append, List.take_append_drop]
  rw [hsplit, fold_pre (gs.drop k) _ i (by rw [fold_len, List.length_take]; omega)]

end PEqualNP.Outside.L_meta_4635

theorem PEqualNP.Outside.L_meta_4635 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit x1 x2 → (0 : ℕ) < x2.size → x2.output + (1 : ℕ) = x1 + x2.size ∧ ∀ (x5 : ℕ), x5 + (1 : ℕ) < x2.size → ∃ (x7 : Fin x2.gates.length), x5 < ↑x7 ∧ x1 + x5 ∈ (x2.gates.get x7).inputs := by
  intro n C hmin hpos
  obtain ⟨hfan, hle⟩ := hmin
  have hok : ∀ g ∈ C.gates, PEqualNP.Outside.L_meta_4635.OkGate g := PEqualNP.Outside.L_meta_4635.ok_of_fan C hfan
  have hsz : C.size = C.gates.length := rfl
  have hout : C.output + 1 = n + C.size := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · -- output is an earlier wire: drop the last gate
      let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨C.gates.take (C.gates.length - 1), C.output⟩
      have hfun : PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.circuitFun n C := by
        funext x
        unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
        rw [PEqualNP.Outside.L_meta_4635.wires_eq, PEqualNP.Outside.L_meta_4635.wires_eq]
        show (List.foldl PEqualNP.Outside.L_meta_4635.F (List.ofFn x) (C.gates.take (C.gates.length - 1))).getD C.output false = _
        exact PEqualNP.Outside.L_meta_4635.take_getD C.gates (List.ofFn x) _ _ (by simp only [List.length_ofFn]; omega) (by omega)
      have hfan' : PEqualNP.MetaComplexity.FanInTwo C' := fun g hg => hfan g (List.mem_of_mem_take hg)
      have h1 := hle C' hfan' hfun
      have h2 : C'.size = C.gates.length - 1 := by
        simp only [C', PEqualNP.CircuitLowerBounds.Circuit.size, List.length_take]; omega
      omega
    · -- output out of range: the function is constant false
      let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨[], n⟩
      have hfun : PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.circuitFun n C := by
        funext x
        unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
        rw [PEqualNP.Outside.L_meta_4635.wires_eq, PEqualNP.Outside.L_meta_4635.wires_eq]
        rw [List.getD_eq_default _ _ (by simp [C']), List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_4635.fold_len]; simp; omega)]
      have hfan' : PEqualNP.MetaComplexity.FanInTwo C' := fun g hg => by simp [C'] at hg
      have := hle C' hfan' hfun
      simp only [PEqualNP.CircuitLowerBounds.Circuit.size, C', List.length_nil] at this
      omega
  refine ⟨hout, ?_⟩
  intro k hk
  by_contra hno
  push Not at hno
  have hk' : k < C.gates.length := by omega
  have hw : ∀ g ∈ C.gates.drop (k + 1), n + k ∉ PEqualNP.Outside.L_meta_4635.rd g := by
    intro g hg hin
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hg
    rw [List.getElem_drop] at hin
    have hlen : k + 1 + t < C.gates.length := by simp at ht; omega
    apply hno ⟨k + 1 + t, hlen⟩ (by simp only; omega)
    exact List.mem_of_mem_take hin
  let C' : PEqualNP.CircuitLowerBounds.Circuit := ⟨(C.gates.eraseIdx k).map (PEqualNP.Outside.L_meta_4635.rg (n + k)), PEqualNP.Outside.L_meta_4635.dl (n + k) C.output⟩
  have hfun : PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.circuitFun n C := by
    funext x
    unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
    rw [PEqualNP.Outside.L_meta_4635.wires_eq, PEqualNP.Outside.L_meta_4635.wires_eq]
    exact PEqualNP.Outside.L_meta_4635.del_getD n k C.gates hk' hok hw (List.ofFn x) (by simp) C.output (by omega)
  have hfan' : PEqualNP.MetaComplexity.FanInTwo C' := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    have := hfan g0 (List.mem_of_mem_eraseIdx hg0)
    simpa [PEqualNP.Outside.L_meta_4635.rg] using this
  have := hle C' hfan' hfun
  simp only [PEqualNP.CircuitLowerBounds.Circuit.size, C', List.length_map, List.length_eraseIdx_of_lt hk'] at this
  omega
