import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5282_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]


lemma getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ (∀ g ∈ gs, g.op ≠ GateOp.not) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

lemma bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, nn, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, nn, le_trans len hs, ho, ev⟩

lemma bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, nn, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, nn, len, ho, fun w hw => by rw [ev w hw, e]⟩

lemma bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, by simp, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

lemma bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, nn1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, nn2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [Ok, h]
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact nn1 g hg
    · exact nn2 g hg
    · subst hg; rcases hop with h | h <;> simp [h]
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

lemma bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

lemma bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

/-- A built function is computed by a fan-in-two circuit with no NOT gate and at most `s`
gates. -/
lemma bld_circuit {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
    ∃ D : Circuit, FanInTwo D ∧ (∀ g ∈ D.gates, g.op ≠ GateOp.not) ∧
      circuitFun n D = F ∧ D.size ≤ s := by
  obtain ⟨gs, out, ok, nn, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, ok, nn, ?_, len⟩
  funext x
  have e := ev (List.ofFn x) (by simp)
  simp only [circuitFun, Circuit.eval, wires_eq, e]
  congr 1
  funext i
  simp


lemma bld_false (n : ℕ) : Bld n (fun _ => false) 1 := by
  intro m hm
  refine ⟨[⟨GateOp.or, []⟩], m, ?_, ?_, by simp, by simp, ?_⟩
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    simp [Ok]
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    simp
  · intro w hw
    simp [wiresFrom, GateOp.eval, ← hw]

lemma bld_edgeList {n : ℕ} (es : List (Fin n × Fin n)) :
    ∃ s, Bld n (fun x => es.any (fun e => x e.1 && x e.2)) s := by
  induction es with
  | nil => exact ⟨1, by simpa using bld_false n⟩
  | cons e es ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨1 + s + 1, ?_⟩
    simpa using bld_or (bld_and (bld_var e.1) (bld_var e.2)) hs

lemma edge_circuit_exists (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit, Monotone2 C ∧ ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) := by
  classical
  let E : Finset (Fin n × Fin n) := Finset.univ.filter (fun e => G.Adj e.1 e.2)
  obtain ⟨s, hs⟩ := bld_edgeList E.toList
  obtain ⟨C, hC, hn, he, _⟩ := bld_circuit hs
  refine ⟨C, ?_, ?_⟩
  · intro g hg
    obtain ⟨hop, hlen⟩ := hC g hg
    refine ⟨?_, hlen⟩
    have hnot := hn g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, hnot, or_false] using hop
  · intro x
    have hv := congrFun he x
    change C.eval (List.ofFn x) = _ at hv
    rw [hv]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Finset.mem_toList, Bool.and_eq_true, decide_eq_true_iff]
    constructor
    · rintro ⟨⟨i,j⟩, hij, hi, hj⟩
      exact ⟨i, j, (Finset.mem_filter.mp hij).2, hi, hj⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      exact ⟨(i,j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, hi, hj⟩

lemma minimum_exists {n : ℕ} (F : (Fin n → Bool) → Bool)
    (h : ∃ C : Circuit, Monotone2 C ∧ ∀ x, C.eval (List.ofFn x) = F x) :
    ∃ C : Circuit, Monotone2 C ∧ (∀ x, C.eval (List.ofFn x) = F x) ∧
      ∀ D : Circuit, Monotone2 D → (∀ x, D.eval (List.ofFn x) = F x) → C.size ≤ D.size := by
  classical
  let P : ℕ → Prop := fun s => ∃ C : Circuit, Monotone2 C ∧
    (∀ x, C.eval (List.ofFn x) = F x) ∧ C.size = s
  have hp : ∃ s, P s := by
    obtain ⟨C, hC, he⟩ := h
    exact ⟨C.size, C, hC, he, rfl⟩
  obtain ⟨C, hC, he, hs⟩ := Nat.find_spec hp
  refine ⟨C, hC, he, ?_⟩
  intro D hD hd
  rw [hs]
  exact Nat.find_min' hp ⟨D, hD, hd, rfl⟩

lemma edge_minimum_exists (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit, Monotone2 C ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      ∀ D : Circuit, Monotone2 D →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size :=
  minimum_exists _ (edge_circuit_exists n G)


def GateGood {n : ℕ} (G : SimpleGraph (Fin n)) (g : Gate) : Prop :=
  g.op = GateOp.or ∨ ∃ i j : Fin n, G.Adj i j ∧ g = ⟨GateOp.and, [i, j]⟩

def BuildsGood {n : ℕ} (G : SimpleGraph (Fin n)) (F : (Fin n → Bool) → Bool) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, GateGood G g ∧ g.inputs.length ≤ 2) ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

lemma good_false {n : ℕ} (G : SimpleGraph (Fin n)) : BuildsGood G (fun _ => false) := by
  intro m hm
  refine ⟨[⟨GateOp.or, []⟩], m, ?_, by simp, ?_⟩
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    exact ⟨Or.inl rfl, by simp⟩
  · intro w hw
    simp [wiresFrom, GateOp.eval, ← hw]

lemma good_edge {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) (hij : G.Adj i j) :
    BuildsGood G (fun x => x i && x j) := by
  intro m hm
  refine ⟨[⟨GateOp.and, [i, j]⟩], m, ?_, by simp, ?_⟩
  · intro g hg
    simp only [List.mem_singleton] at hg
    subst g
    exact ⟨Or.inr ⟨i, j, hij, rfl⟩, by simp⟩
  · intro w hw
    simp [wiresFrom, GateOp.eval, ← hw]

lemma good_or {n : ℕ} (G : SimpleGraph (Fin n))
    {F H : (Fin n → Bool) → Bool} (h1 : BuildsGood G F) (h2 : BuildsGood G H) :
    BuildsGood G (fun x => F x || H x) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨GateOp.or, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg
      exact ⟨Or.inl rfl, by simp⟩
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨GateOp.or, [o1, o2]⟩] u
        = u ++ [GateOp.or.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
      Bool.or_false, id]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

lemma good_edgeList {n : ℕ} (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n))
    (hes : ∀ e ∈ es, G.Adj e.1 e.2) :
    BuildsGood G (fun x => es.any (fun e => x e.1 && x e.2)) := by
  induction es with
  | nil => simpa using good_false G
  | cons e es ih =>
    simpa using good_or G (good_edge G e.1 e.2 (hes e (by simp)))
      (ih (fun e he => hes e (by simp [he])))

lemma good_circuit_exists (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit, (∀ g ∈ C.gates, GateGood G g ∧ g.inputs.length ≤ 2) ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) := by
  classical
  let E : Finset (Fin n × Fin n) := Finset.univ.filter (fun e => G.Adj e.1 e.2)
  have hb := good_edgeList G E.toList (fun e he => (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2)
  obtain ⟨gs, out, hg, _, hv⟩ := hb n le_rfl
  refine ⟨⟨gs, out⟩, hg, ?_⟩
  intro x
  have h := hv (List.ofFn x) (by simp)
  simp only [Circuit.eval, wires_eq, h]
  simp only [getD_ofFn]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Finset.mem_toList, Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨⟨i,j⟩, hij, hi, hj⟩
    exact ⟨i, j, (Finset.mem_filter.mp hij).2, hi, hj⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    exact ⟨(i,j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, hi, hj⟩

lemma gate_value (gs : List Gate) (w : List Bool) (k : ℕ) (g : Gate)
    (hg : gs[k]? = some g) :
    (wiresFrom gs w).getD (w.length + k) false =
      g.op.eval (g.inputs.map fun i => (wiresFrom (gs.take k) w).getD i false) := by
  induction gs generalizing w k with
  | nil => simp at hg
  | cons a gs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
      subst g
      change (wiresFrom gs (w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)])).getD
        (w.length + 0) false = _
      rw [getD_wiresFrom _ _ _ (by simp)]
      simp [wiresFrom]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hg
      have h := ih (w ++ [a.op.eval (a.inputs.map fun i => w.getD i false)]) k hg
      simpa only [wiresFrom, List.foldl_cons, List.take_succ_cons, List.length_append,
        List.length_singleton, Nat.add_assoc, Nat.add_comm 1] using h

lemma good_gate_false {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (hC : ∀ g ∈ C.gates, GateGood G g ∧ g.inputs.length ≤ 2)
    (k : ℕ) (g : Gate) (hg : C.gates[k]? = some g) (hand : g.op = GateOp.and)
    (S : Finset (Fin n)) (hS : S.card ≤ 1) :
    (C.wires (List.ofFn (fun i => decide (i ∈ S)))).getD (n + k) false = false := by
  have hmem : g ∈ C.gates := List.mem_of_getElem? hg
  rcases (hC g hmem).1 with hor | ⟨i, j, hij, hge⟩
  · rw [hand] at hor
    cases hor
  · subst g
    have h := gate_value C.gates (List.ofFn (fun i => decide (i ∈ S))) k
      ⟨GateOp.and, [i,j]⟩ hg
    simp only [List.length_ofFn] at h
    rw [wires_eq, h]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      id_eq, Bool.and_true]
    rw [show (wiresFrom (C.gates.take k) (List.ofFn (fun a => decide (a ∈ S)))).getD i false =
      decide (i ∈ S) by rw [getD_wiresFrom _ _ _ (by simp)]; simp]
    rw [show (wiresFrom (C.gates.take k) (List.ofFn (fun a => decide (a ∈ S)))).getD j false =
      decide (j ∈ S) by rw [getD_wiresFrom _ _ _ (by simp)]; simp]
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hm : decide (i ∈ S) = true ∧ decide (j ∈ S) = true := by simpa using htrue
    have hi : i ∈ S := of_decide_eq_true hm.1
    have hj : j ∈ S := of_decide_eq_true hm.2
    have heq : i = j := Finset.card_le_one.mp hS i hi j hj
    exact G.ne_of_adj hij heq


lemma safe_edge_circuit_exists (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit, Monotone2 C ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      ∀ k g, C.gates[k]? = some g → g.op = GateOp.and →
        ∀ S : Finset (Fin n), S.card ≤ 1 →
          (C.wires (List.ofFn (fun i => decide (i ∈ S)))).getD (n + k) false = false := by
  obtain ⟨C, hC, he⟩ := good_circuit_exists n G
  refine ⟨C, ?_, he, good_gate_false G C hC⟩
  intro g hg
  refine ⟨?_, (hC g hg).2⟩
  rcases (hC g hg).1 with hor | ⟨i, j, hij, hge⟩
  · simp [hor]
  · simp [hge]

lemma minimum_good_of_descent {n : ℕ} (F : (Fin n → Bool) → Bool)
    (Good : Circuit → Prop) (measure : Circuit → ℕ)
    (h : ∃ C : Circuit, Monotone2 C ∧ ∀ x, C.eval (List.ofFn x) = F x)
    (step : ∀ C : Circuit, Monotone2 C → (∀ x, C.eval (List.ofFn x) = F x) →
      ¬ Good C → ∃ D : Circuit, Monotone2 D ∧ (∀ x, D.eval (List.ofFn x) = F x) ∧
        D.size ≤ C.size ∧ measure D < measure C) :
    ∃ C : Circuit, Monotone2 C ∧ (∀ x, C.eval (List.ofFn x) = F x) ∧
      (∀ D : Circuit, Monotone2 D → (∀ x, D.eval (List.ofFn x) = F x) → C.size ≤ D.size) ∧
      Good C := by
  classical
  obtain ⟨C, hC, he, hmin⟩ := minimum_exists F h
  let Q : ℕ → Prop := fun k => ∃ D : Circuit, Monotone2 D ∧
    (∀ x, D.eval (List.ofFn x) = F x) ∧ D.size = C.size ∧ measure D = k
  have hq : ∃ k, Q k := ⟨measure C, C, hC, he, rfl, rfl⟩
  obtain ⟨B, hB, hb, hsize, hmeasure⟩ := Nat.find_spec hq
  refine ⟨B, hB, hb, ?_, ?_⟩
  · intro D hD hd
    rw [hsize]
    exact hmin D hD hd
  · by_contra hbad
    obtain ⟨D, hD, hd, hle, hlt⟩ := step B hB hb hbad
    have heq : D.size = C.size := by
      have hge := hmin D hD hd
      omega
    have hm : Nat.find hq ≤ measure D := Nat.find_min' hq ⟨D, hD, hd, heq, rfl⟩
    omega

end PEqualNP.Outside.L_meta_5282_aux
