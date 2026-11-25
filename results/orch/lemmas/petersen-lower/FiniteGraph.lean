import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890_aux

def edges : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
   (5,7),(7,9),(9,6),(6,8),(8,5)]

def adj (u v : Fin 10) : Bool :=
  edges.any fun p => (u == p.1 && v == p.2) || (u == p.2 && v == p.1)

def graph (x : Fin 10 → Bool) : Bool :=
  edges.any fun p => x p.1 && x p.2

def cover (x : Fin 10 → Bool) : Bool :=
  edges.all fun p => x p.1 || x p.2

def selected (x : Fin 10 → Bool) : Nat := (List.ofFn x).count true

theorem fifteen_edges : edges.length = 15 := rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem three_neighbors : ∀ u : Fin 10,
    ((List.finRange 10).filter fun v => adj u v).length = 3 := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem no_triangle : ∀ a b c : Fin 10,
    adj a b = true → adj b c = true → adj c a = false := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem no_square : ∀ a b c d : Fin 10,
    adj a b = true → adj b c = true → adj c d = true → adj d a = true →
      a = c ∨ b = d := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem independence_bound : ∀ x : Fin 10 → Bool,
    graph x = false → selected x ≤ 4 := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vertex_cover_bound : ∀ x : Fin 10 → Bool,
    cover x = true → 6 ≤ selected x := by
  decide +kernel

-- Each edge belongs to one star. Building a star with d assigned edges costs
-- d gates, and joining s nonempty stars costs s-1 gates. This certificate
-- applies to that construction model; it does not bound arbitrary circuits.
theorem star_cover_cost (x : Fin 10 → Bool) (h : cover x = true) :
    20 ≤ edges.length + selected x - 1 := by
  have lower := vertex_cover_bound x h
  rw [fifteen_edges]
  omega


-- Monotonicity helpers adapted from the repository helper LineDegTest.
open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++
      [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_snoc {α : Type} (l : List α) (a d : α) (t : Nat) :
    (l ++ [a]).getD t d =
      if t < l.length then l.getD t d else if t = l.length then a else d := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : t < l.length
  · rw [ite_eq_left h1, List.getElem?_append_left h1]
  · rw [ite_eq_right h1, List.getElem?_append_right (by omega)]
    by_cases h2 : t = l.length
    · subst h2; simp
    · rw [ite_eq_right h2]
      have : t - l.length ≠ 0 := by omega
      simp [this]

def ListLE (x y : List Bool) : Prop :=
  ∀ i, x.getD i false = true → y.getD i false = true

theorem gate_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w w' : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false = true → w'.getD i false = true)
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp [GateOp.eval] at he ⊢
  · intro i hi; exact h i hi (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h i hi hv⟩

theorem run_mono (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hl : x.length = y.length) (hxy : ListLE x y) :
    ListLE (run gs x) (run gs y) := by
  induction gs using List.reverseRecOn with
  | nil => simpa [run] using hxy
  | append_singleton gs g ih =>
    have ih := ih (fun g' hg' => hm g' (by simp [hg']))
    intro t ht
    have hlen : (run gs x).length = (run gs y).length := by simp [run_length, hl]
    rw [run_snoc, getD_snoc] at ht ⊢
    rw [← hlen]
    by_cases h1 : t < (run gs x).length
    · rw [ite_eq_left h1] at ht ⊢; exact ih t ht
    · rw [ite_eq_right h1] at ht ⊢
      by_cases h2 : t = (run gs x).length
      · rw [ite_eq_left h2] at ht ⊢
        exact gate_mono g (hm g (by simp)) _ _ (fun i _ => ih i) ht
      · rw [ite_eq_right h2] at ht; simp at ht

def edgePoint (a b : Fin 10) (i : Fin 10) : Bool := i == a || i == b

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem edgePoint_seed : ∀ a b : Fin 10, (a,b) ∈ edges →
    (edgePoint a b 0 && edgePoint a b 2) = false := by
  decide +kernel

theorem edgePoint_graph (a b : Fin 10) (hab : (a,b) ∈ edges) :
    graph (edgePoint a b) = true := by
  simp only [graph, List.any_eq_true]
  exact ⟨(a,b), hab, by simp [edgePoint]⟩

theorem seed_removal_abstract (F : (Fin 10 → Bool) → Bool → Bool)
    (mono : ∀ (x y : Fin 10 → Bool) (s t : Bool),
      (∀ i, x i = true → y i = true) → (s = true → t = true) →
      F x s = true → F y t = true)
    (correct : ∀ x, F x (x 0 && x 2) = graph x) :
    ∀ x, F x false = graph x := by
  intro x
  cases hx : graph x with
  | false =>
    cases hf : F x false with
    | false => rfl
    | true =>
      have h := mono x x false (x 0 && x 2) (fun _ h => h) (by simp) hf
      rw [correct, hx] at h
      cases h
  | true =>
    have he : ∃ e ∈ edges, x e.1 = true ∧ x e.2 = true := by
      simpa only [graph, List.any_eq_true, Bool.and_eq_true] using hx
    obtain ⟨⟨a,b⟩, hab, ha, hb⟩ := he
    have hy := correct (edgePoint a b)
    rw [edgePoint_seed a b hab, edgePoint_graph a b hab] at hy
    apply mono (edgePoint a b) x false false ?_ (by simp) hy
    intro i hi
    simp only [edgePoint, Bool.or_eq_true, beq_iff_eq] at hi
    rcases hi with rfl | rfl
    · exact ha
    · exact hb

theorem seed_removal (C : Circuit) (p : Fin 10 → Fin 10)
    (hm : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (correct : ∀ x, C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) = graph x) :
    ∀ x, C.eval (List.ofFn (x ∘ p) ++ [false]) = graph x := by
  apply seed_removal_abstract (fun x b => C.eval (List.ofFn (x ∘ p) ++ [b])) ?_ correct
  intro x y s t hxy hst h
  apply run_mono C.gates hm (List.ofFn (x ∘ p) ++ [s])
    (List.ofFn (y ∘ p) ++ [t]) (by simp) ?_ C.output h
  intro i hi
  rw [getD_snoc] at hi ⊢
  simp only [List.length_ofFn] at hi ⊢
  by_cases hlt : i < 10
  · rw [ite_eq_left hlt] at hi ⊢
    have hin : ∀ z : Fin 10 → Bool,
        (List.ofFn (z ∘ p)).getD i false = z (p ⟨i,hlt⟩) := by
      intro z
      rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
      simp [hlt]
    rw [hin] at hi ⊢
    exact hxy _ hi
  · rw [ite_eq_right hlt] at hi ⊢
    by_cases heq : i = 10
    · rw [ite_eq_left heq] at hi ⊢
      exact hst hi
    · rw [ite_eq_right heq] at hi
      cases hi

end PEqualNP.Outside.L_meta_1890_aux
