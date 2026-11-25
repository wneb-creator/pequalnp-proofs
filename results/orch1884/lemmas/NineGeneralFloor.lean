import MonoBase
import Binary17

namespace PEqualNP.Outside.L_meta_1884.NineGeneralFloor

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_2590.Mono18

def gateFn {R : Type} (w : List (Wire R)) (g : Gate) : Wire R :=
  fun r => g.op.eval (g.inputs.map (fun i => (w.getD i (fun _ => false)) r))

def runFn {R : Type} (gs : List Gate) (w : List (Wire R)) : List (Wire R) :=
  gs.foldl (fun a g => a ++ [gateFn a g]) w

lemma read_available {u : Bool} {R : Type} (w bank : List (Wire R))
    (hw : ∀ a ∈ w, Available u bank a) (i : Nat) :
    Available u bank (w.getD i (fun _ => false)) := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hw _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Or.inr (Or.inl ⟨false, rfl⟩)

lemma gate_decompose {u : Bool} {R : Type} (w bank : List (Wire R)) (g : Gate)
    (hw : ∀ a ∈ w, Available u bank a)
    (hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    ∃ op a b, gateFn w g = combine op a b ∧
      Available u bank a ∧ Available u bank b := by
  have hf : Available u bank (fun _ : R => false) := Or.inr (Or.inl ⟨false, rfl⟩)
  have ht : Available u bank (fun _ : R => true) := Or.inr (Or.inl ⟨true, rfl⟩)
  have hr := read_available w bank hw
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen
  rcases hop with rfl | rfl
  · cases ins with
    | nil => exact ⟨false, (fun _ => true), (fun _ => true), rfl, ht, ht⟩
    | cons i ins =>
      cases ins with
      | nil =>
        refine ⟨false, w.getD i (fun _ => false), (fun _ => true), ?_, hr i, ht⟩
        funext r
        simp [gateFn, combine, GateOp.eval]
      | cons j ins =>
        cases ins with
        | nil =>
          refine ⟨false, w.getD i (fun _ => false), w.getD j (fun _ => false), ?_, hr i, hr j⟩
          funext r
          simp [gateFn, combine, GateOp.eval]
        | cons k rest => simp at hlen
  · cases ins with
    | nil => exact ⟨true, (fun _ => false), (fun _ => false), rfl, hf, hf⟩
    | cons i ins =>
      cases ins with
      | nil =>
        refine ⟨true, w.getD i (fun _ => false), (fun _ => false), ?_, hr i, hf⟩
        funext r
        simp [gateFn, combine, GateOp.eval]
      | cons j ins =>
        cases ins with
        | nil =>
          refine ⟨true, w.getD i (fun _ => false), w.getD j (fun _ => false), ?_, hr i, hr j⟩
          funext r
          simp [gateFn, combine, GateOp.eval]
        | cons k rest => simp at hlen

lemma not_available {u : Bool} {R : Type} (w bank : List (Wire R)) (g : Gate)
    (hw : ∀ a ∈ w, Available u bank a) (hg : g.op = .not) (hu : u = true) :
    Available u bank (gateFn w g) := by
  obtain ⟨op, ins⟩ := g
  simp only at hg
  subst op
  cases ins with
  | nil => exact Or.inr (Or.inl ⟨true, rfl⟩)
  | cons i rest => exact avail_inv hu (read_available w bank hw i)

lemma run_reachable {u : Bool} {R : Type} (gs : List Gate)
    (w roots bank : List (Wire R)) (p : Nat)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hn : ∀ g ∈ gs, g.op = .not → u = true)
    (hr : Reach u roots p bank) (hw : ∀ a ∈ w, Available u bank a) :
    ∃ next, Reach u roots (p + gs.countP (fun g => !isNot g)) next ∧
      ∀ a ∈ runFn gs w, Available u next a := by
  induction gs generalizing w bank p with
  | nil => exact ⟨bank, by simpa using hr, hw⟩
  | cons g gs ih =>
    by_cases hnot : g.op = .not
    · have hgate := not_available w bank g hw hnot (hn g (by simp) hnot)
      have hw' : ∀ v ∈ w ++ [gateFn w g], Available u bank v := by
        intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact hw v hv
        · simpa using List.mem_singleton.mp hv ▸ hgate
      obtain ⟨next, hh, hs⟩ := ih (w ++ [gateFn w g]) bank p
        (fun g' hg' => hg g' (by simp [hg']))
        (fun g' hg' => hn g' (by simp [hg'])) hr hw'
      refine ⟨next, ?_, hs⟩
      simpa [List.countP_cons, isNot, hnot] using hh
    · have hgo : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
        obtain ⟨h, hl⟩ := hg g (by simp)
        exact ⟨h.imp_right (fun h => h.resolve_right hnot), hl⟩
      obtain ⟨op, a, b, heq, ha, hb⟩ := gate_decompose w bank g hw hgo
      have hr' := Reach.two op hr ha hb
      have hw' : ∀ v ∈ w ++ [gateFn w g], Available u (combine op a b :: bank) v := by
        intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact available_cons _ (hw v hv)
        · have hv' : v = gateFn w g := List.mem_singleton.mp hv
          rw [hv', heq]
          exact Or.inl (by simp)
      obtain ⟨next, hh, hs⟩ := ih (w ++ [gateFn w g]) (combine op a b :: bank) (p + 1)
        (fun g' hg' => hg g' (by simp [hg']))
        (fun g' hg' => hn g' (by simp [hg'])) hr' hw'
      have his : isNot g = false := by
        obtain ⟨op, ins⟩ := g
        cases op <;> simp_all [isNot]
      refine ⟨next, ?_, hs⟩
      simpa [List.countP_cons, his, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

lemma read_row {R : Type} (w : List (Wire R)) (r : R) (i : Nat) :
    (w.getD i (fun _ => false)) r = (w.map (fun a => a r)).getD i false := by
  exact (List.getD_map w (fun _ => false) (n := i) (fun a => a r)).symm

lemma run_rows {R : Type} (gs : List Gate) (w : List (Wire R)) (r : R) :
    (runFn gs w).map (fun a => a r) =
      gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map (fun i => a.getD i false))])
        (w.map (fun a => a r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (runFn gs (w ++ [gateFn w g])).map (fun a => a r) = _
    rw [ih]
    simp only [List.foldl_cons, List.map_append, List.map_cons, List.map_nil, gateFn, read_row]

lemma root_rows (r : Row) :
    (inputs.map observe).map (fun a => a r) = List.ofFn (sample r) := by
  rw [sampled, List.map_map]
  rfl

theorem circuit_floor {u : Bool} {L : Nat} (lower : Lower u inputs graph L)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (hn : ∀ g ∈ C.gates, g.op = .not → u = true)
    (hcomputes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edge x) :
    L ≤ C.gates.countP (fun g => !isNot g) := by
  have hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hm
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using legal g hm
  obtain ⟨bank, hr, hs⟩ := run_reachable C.gates (inputs.map observe) (inputs.map observe)
    (inputs.map observe) 0 hg hn Reach.start (fun a ha => Or.inl ha)
  have hout := read_available (runFn C.gates (inputs.map observe)) bank hs C.output
  have heq : (runFn C.gates (inputs.map observe)).getD C.output (fun _ => false) =
      observe graph := by
    funext r
    rw [read_row, run_rows, root_rows]
    change C.eval (List.ofFn (sample r)) = bit r graph
    rw [hcomputes, edge_table]
  rw [heq] at hout
  exact lower _ bank (by simpa using hr) hout

lemma reach_to_signed {R : Type} {u : Bool} {roots : List (Wire R)} {p bank}
    (h : Reach u roots p bank) :
    PEqualNP.Outside.L_meta_2592.Binary17.Reach u roots p bank := by
  induction h using Reach.ind with
  | start => rfl
  | two op h ha hb ih => exact PEqualNP.Outside.L_meta_2592.Binary17.Reach.two op ih ha hb

lemma signed_floor : Lower true inputs graph 15 := by
  intro p bank h ha
  exact PEqualNP.Outside.L_meta_2592.Binary17.nineFloor p bank (reach_to_signed h) ha

lemma count_partition (C : Circuit) :
    C.gates.countP (fun g => !isNot g) + PEqualNP.NotBracket.notCount C = C.size := by
  have same :
      (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)) =
      isNot := by
    funext g
    obtain ⟨op, ins⟩ := g
    cases op <;> rfl
  have hc : PEqualNP.NotBracket.notCount C = C.gates.countP isNot := by
    rw [PEqualNP.NotBracket.notCount, same, List.countP_eq_length_filter]
  have h := List.length_eq_countP_add_countP isNot (l := C.gates)
  have heq : (fun g : Gate => decide (¬ isNot g = true)) = (fun g => !isNot g) := by
    funext g
    cases isNot g <;> rfl
  rw [heq] at h
  rw [hc]
  change _ = C.gates.length
  omega

theorem signed_fifteen_plus_not (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (hcomputes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edge x) :
    15 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  have hf := circuit_floor signed_floor C legal (by simp) hcomputes
  have hc := count_partition C
  omega

theorem nine_circuit_floor (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (hcomputes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edge x) : 16 ≤ C.size := by
  have hc := count_partition C
  by_cases hz : PEqualNP.NotBracket.notCount C = 0
  · have hn : ∀ g ∈ C.gates, g.op = .not → false = true := by
      intro g hg hop
      have hm : g ∈ C.gates.filter (fun g : Gate =>
          @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)) :=
        List.mem_filter.mpr ⟨hg, by simp [hop]⟩
      have he : C.gates.filter (fun g : Gate =>
          @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)) = [] :=
        List.length_eq_zero_iff.mp hz
      rw [he] at hm
      exact False.elim (List.not_mem_nil hm)
    have hf := circuit_floor nineMonoFloor C legal hn hcomputes
    omega
  · have hf := signed_fifteen_plus_not C legal hcomputes
    omega

end PEqualNP.Outside.L_meta_1884.NineGeneralFloor
