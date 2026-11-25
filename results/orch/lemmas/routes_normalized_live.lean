import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.Norm

open PEqualNP.CircuitLowerBounds

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_len : ∀ (gs : List Gate) (l : List Bool),
    (gs.foldl stp l).length = l.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro l; simp
  | cons g gs ih =>
    intro l
    rw [List.foldl_cons, ih]
    simp [stp]
    omega

def fixG (k : ℕ) (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, (g.inputs.take 1).filter (fun i => decide (i < k))⟩
  | GateOp.and => if g.inputs.all (fun i => decide (i < k)) then g else ⟨GateOp.or, []⟩
  | GateOp.or => ⟨GateOp.or, g.inputs.filter (fun i => decide (i < k))⟩
  | _ => g

theorem fixG_eval (w : List Bool) (g : Gate) :
    (fixG w.length g).op.eval ((fixG w.length g).inputs.map fun i => w.getD i false)
      = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rcases g with ⟨op, ins⟩
  cases op with
  | not =>
    cases ins with
    | nil => simp [fixG, GateOp.eval]
    | cons a t =>
      by_cases ha : a < w.length
      · simp [fixG, GateOp.eval, ha]
      · simp [fixG, GateOp.eval, ha, List.getD_eq_default _ _ (Nat.le_of_not_lt ha)]
  | and =>
    by_cases hall : ins.all (fun i => decide (i < w.length)) = true
    · simp only [fixG, hall, if_true]
    · simp only [fixG, hall]
      simp only [Bool.false_eq_true, if_false]
      simp only [List.all_eq_true, decide_eq_true_eq, not_forall] at hall
      obtain ⟨i, hi, hlt⟩ := hall
      symm
      show (ins.map fun i => w.getD i false).all id = false
      rw [Bool.eq_false_iff]
      intro hc
      rw [List.all_eq_true] at hc
      have h2 := hc (w.getD i false) (List.mem_map.mpr ⟨i, hi, rfl⟩)
      rw [List.getD_eq_default _ _ (by omega)] at h2
      simp at h2
  | or =>
    apply Bool.eq_iff_iff.mpr
    simp only [fixG, GateOp.eval, List.any_eq_true, List.mem_map, List.mem_filter,
      decide_eq_true_eq, id_eq]
    constructor
    · rintro ⟨b, ⟨i, ⟨hi, _⟩, rfl⟩, hb⟩
      exact ⟨_, ⟨i, hi, rfl⟩, hb⟩
    · rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
      by_cases hlt : i < w.length
      · exact ⟨_, ⟨i, ⟨hi, hlt⟩, rfl⟩, hb⟩
      · rw [List.getD_eq_default _ _ (by omega)] at hb
        exact absurd hb (by simp)
  | mod m => rfl
  | maj => rfl

def S : Set GateOp := {GateOp.and, GateOp.or, GateOp.not}

theorem fixG_ok (k : ℕ) (g : Gate) (hop : g.op ∈ S) (hl : g.inputs.length ≤ 2) :
    (∀ i ∈ (fixG k g).inputs, i < k) ∧ (fixG k g).op ∈ S ∧ (fixG k g).inputs.length ≤ 2 ∧
    ((fixG k g).op = GateOp.not → (fixG k g).inputs.length ≤ 1) ∧
    (g.op = GateOp.not → (fixG k g).op = GateOp.not) := by
  rcases g with ⟨op, ins⟩
  simp only [S, Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · by_cases hall : ins.all (fun i => decide (i < k)) = true
    · simp only [fixG, hall, if_true]
      simp only [List.all_eq_true, decide_eq_true_eq] at hall
      exact ⟨hall, by simp [S], hl, by simp, by simp⟩
    · simp only [fixG, hall, Bool.false_eq_true, if_false]
      exact ⟨by simp, by simp [S], by simp, by simp, by simp⟩
  · simp only [fixG]
    refine ⟨?_, by simp [S], ?_, by simp, by simp⟩
    · intro i hi
      simp only [List.mem_filter, decide_eq_true_eq] at hi
      exact hi.2
    · exact le_trans (List.length_filter_le _ _) hl
  · simp only [fixG]
    refine ⟨?_, by simp [S], ?_, ?_, by simp⟩
    · intro i hi
      simp only [List.mem_filter, decide_eq_true_eq] at hi
      exact hi.2
    · exact le_trans (List.length_filter_le _ _) (le_trans (List.length_take_le _ _) (by omega))
    · intro _
      exact le_trans (List.length_filter_le _ _) (List.length_take_le _ _)

def fixL : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => fixG k g :: fixL (k + 1) gs

theorem fixL_foldl : ∀ (gs : List Gate) (k : ℕ) (w : List Bool), w.length = k →
    (fixL k gs).foldl stp w = gs.foldl stp w := by
  intro gs
  induction gs with
  | nil => intro k w _; rfl
  | cons g gs ih =>
    intro k w hk
    subst hk
    simp only [fixL, List.foldl_cons]
    have e : stp w (fixG w.length g) = stp w g := by
      simp only [stp, fixG_eval]
    rw [e]
    exact ih _ _ (by simp [stp])

theorem fixL_len : ∀ (gs : List Gate) (k : ℕ), (fixL k gs).length = gs.length := by
  intro gs
  induction gs with
  | nil => intro k; rfl
  | cons g gs ih => intro k; simp [fixL, ih]

theorem fixL_mem : ∀ (gs : List Gate) (k : ℕ) (g' : Gate), g' ∈ fixL k gs →
    ∃ k', ∃ g ∈ gs, g' = fixG k' g := by
  intro gs
  induction gs with
  | nil => intro k g' h; simp [fixL] at h
  | cons g gs ih =>
    intro k g' h
    simp only [fixL, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨k, g, by simp, h⟩
    · obtain ⟨k', g1, hg1, e⟩ := ih (k + 1) g' h
      exact ⟨k', g1, by simp [hg1], e⟩

theorem mem_fixL : ∀ (gs : List Gate) (k : ℕ) (g : Gate), g ∈ gs →
    ∃ k', fixG k' g ∈ fixL k gs := by
  intro gs
  induction gs with
  | nil => intro k g h; simp at h
  | cons g0 gs ih =>
    intro k g h
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨k, by simp [fixL]⟩
    · obtain ⟨k', hk'⟩ := ih (k + 1) g h
      exact ⟨k', by simp [fixL, hk']⟩

theorem fixL_getD : ∀ (gs : List Gate) (k j : ℕ), (∀ g ∈ gs, g.op ∈ S ∧ g.inputs.length ≤ 2) →
    ∀ i ∈ ((fixL k gs).getD j ⟨GateOp.or, []⟩).inputs, i < k + j := by
  intro gs
  induction gs with
  | nil => intro k j _ i hi; simp [fixL] at hi
  | cons g gs ih =>
    intro k j hall i hi
    cases j with
    | zero =>
      simp only [fixL, List.getD_cons_zero] at hi
      have h := (fixG_ok k g (hall g (by simp)).1 (hall g (by simp)).2).1 i hi
      omega
    | succ j =>
      simp only [fixL, List.getD_cons_succ] at hi
      have h := ih (k + 1) j (fun g1 hg1 => hall g1 (by simp [hg1])) i hi
      omega

theorem getD_mem_or (gs : List Gate) (j : ℕ) :
    gs.getD j ⟨GateOp.or, []⟩ ∈ gs ∨ gs.getD j ⟨GateOp.or, []⟩ = ⟨GateOp.or, []⟩ := by
  by_cases h : j < gs.length
  · left
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    simp
  · right
    exact List.getD_eq_default _ _ (by omega)

def WF (C : Circuit) : Prop :=
  ∀ (j : ℕ), (∀ i ∈ (C.gates.getD j ⟨GateOp.or, []⟩).inputs, i < 10 + j) ∧
    ((C.gates.getD j ⟨GateOp.or, []⟩).op = GateOp.not →
      (C.gates.getD j ⟨GateOp.or, []⟩).inputs.length ≤ 1)

theorem ofFn_getD (x : Fin 10 → Bool) (o : ℕ) (h : o < 10) :
    (List.ofFn x).getD o false = x ⟨o, h⟩ := by
  interval_cases o <;> rfl

theorem main (f : (Fin 10 → Bool) → Bool)
    (hf0 : ∀ o : ℕ, o < 9 → f (fun i => decide (i.val = o)) = false)
    (hf1 : f (fun _ => true) = true) :
    ∀ (n : ℕ) (C : Circuit), C.gates.length = n → PEqualNP.MetaComplexity.FanInTwo C → WF C →
      (∀ x, C.eval (List.ofFn x) = f x) →
      ∃ C' : Circuit, PEqualNP.MetaComplexity.FanInTwo C' ∧ C'.size ≤ C.size ∧
        C'.output + 1 = 10 + C'.size ∧ WF C' ∧ (C' = C ∨ C'.size < C.size) ∧
        ∀ x, C'.eval (List.ofFn x) = f x := by
  intro n
  induction n with
  | zero =>
    intro C hn hF hW hC
    have hg : C.gates = [] := List.length_eq_zero_iff.mp hn
    by_cases ho : C.output = 9
    · exact ⟨C, hF, le_rfl, by simp [Circuit.size, hn, ho], hW, Or.inl rfl, hC⟩
    · exfalso
      by_cases hlt : C.output < 9
      · have h := hC (fun i => decide (i.val = C.output))
        rw [hf0 _ hlt] at h
        simp only [Circuit.eval, Circuit.wires, hg, List.foldl_nil] at h
        rw [ofFn_getD _ _ (by omega)] at h
        simp at h
      · have h := hC (fun _ => true)
        rw [hf1] at h
        simp only [Circuit.eval, Circuit.wires, hg, List.foldl_nil] at h
        rw [List.getD_eq_default _ _ (by simp; omega)] at h
        exact absurd h (by simp)
  | succ n ih =>
    intro C hn hF hW hC
    by_cases ho : C.output + 1 = 10 + C.size
    · exact ⟨C, hF, le_rfl, ho, hW, Or.inl rfl, hC⟩
    by_cases hbig : 10 + C.size ≤ C.output
    · exfalso
      have h := hC (fun _ => true)
      rw [hf1] at h
      have hl : (C.wires (List.ofFn fun _ : Fin 10 => true)).length = 10 + C.size := by
        show (C.gates.foldl stp _).length = _
        rw [foldl_len]
        simp [Circuit.size]
      simp only [Circuit.eval] at h
      rw [List.getD_eq_default _ _ (by omega)] at h
      exact absurd h (by simp)
    rcases List.eq_nil_or_concat C.gates with h0 | ⟨gs, g, hgs⟩
    · rw [h0] at hn
      simp at hn
    rw [List.concat_eq_append] at hgs
    have hsz : C.size = gs.length + 1 := by simp [Circuit.size, hgs]
    have hDlen : gs.length = n := by
      rw [hgs] at hn
      simpa using hn
    have hDF : PEqualNP.MetaComplexity.FanInTwo ⟨gs, C.output⟩ := by
      intro g1 hg1
      exact hF g1 (by rw [hgs]; simp [hg1])
    have hDW : WF ⟨gs, C.output⟩ := by
      intro j
      by_cases hj : j < gs.length
      · have e : gs.getD j ⟨GateOp.or, []⟩ = C.gates.getD j ⟨GateOp.or, []⟩ := by
          rw [hgs, List.getD_append _ _ _ _ hj]
        show (∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < 10 + j) ∧ _
        rw [e]
        exact hW j
      · have e : gs.getD j ⟨GateOp.or, []⟩ = ⟨GateOp.or, []⟩ :=
          List.getD_eq_default _ _ (by omega)
        show (∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < 10 + j) ∧ _
        rw [e]
        simp
    have hDC : ∀ x, (Circuit.eval ⟨gs, C.output⟩ (List.ofFn x)) = f x := by
      intro x
      rw [← hC x]
      show (gs.foldl stp (List.ofFn x)).getD C.output false
        = (C.gates.foldl stp (List.ofFn x)).getD C.output false
      rw [hgs, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, stp]
      rw [List.getD_append _ _ _ _ (by rw [foldl_len]; simp; omega)]
    obtain ⟨C', h1, h2, h3, h4, _, h6⟩ := ih ⟨gs, C.output⟩ hDlen hDF hDW hDC
    have h2' : C'.size ≤ gs.length := h2
    exact ⟨C', h1, by omega, h3, h4, Or.inr (by omega), h6⟩

end PEqualNP.Outside.L_meta_2592_aux.Norm

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_2592_aux.Norm in
lemma PEqualNP.Outside.L_meta_2592_aux.Norm.normalize : have x1 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x2 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x2) = (x2 (0 : Fin (10 : ℕ)) && x2 (1 : Fin (10 : ℕ)) || x2 (1 : Fin (10 : ℕ)) && x2 (2 : Fin (10 : ℕ)) || x2 (2 : Fin (10 : ℕ)) && x2 (3 : Fin (10 : ℕ)) || x2 (3 : Fin (10 : ℕ)) && x2 (4 : Fin (10 : ℕ)) || x2 (4 : Fin (10 : ℕ)) && x2 (0 : Fin (10 : ℕ)) || x2 (0 : Fin (10 : ℕ)) && x2 (5 : Fin (10 : ℕ)) || x2 (1 : Fin (10 : ℕ)) && x2 (6 : Fin (10 : ℕ)) || x2 (2 : Fin (10 : ℕ)) && x2 (7 : Fin (10 : ℕ)) || x2 (3 : Fin (10 : ℕ)) && x2 (8 : Fin (10 : ℕ)) || x2 (4 : Fin (10 : ℕ)) && x2 (9 : Fin (10 : ℕ)) || x2 (5 : Fin (10 : ℕ)) && x2 (7 : Fin (10 : ℕ)) || x2 (7 : Fin (10 : ℕ)) && x2 (9 : Fin (10 : ℕ)) || x2 (9 : Fin (10 : ℕ)) && x2 (6 : Fin (10 : ℕ)) || x2 (6 : Fin (10 : ℕ)) && x2 (8 : Fin (10 : ℕ)) || x2 (8 : Fin (10 : ℕ)) && x2 (5 : Fin (10 : ℕ))); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) =>   ∀ (x3 : ℕ),     have x4 : PEqualNP.CircuitLowerBounds.Gate := x2.gates.getD x3 { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [] : PEqualNP.CircuitLowerBounds.Gate };     (∀ x5 ∈ x4.inputs, x5 < (10 : ℕ) + x3) ∧ (x4.op = PEqualNP.CircuitLowerBounds.GateOp.not → x4.inputs.length ≤ (1 : ℕ)); ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x3 → (∃ x5 ∈ x3.gates, x5.op = PEqualNP.CircuitLowerBounds.GateOp.not) → x1 x3 → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x7 ∧ x7.size ≤ x3.size ∧ x7.output + (1 : ℕ) = (10 : ℕ) + x7.size ∧ x2 x7 ∧ ((∃ x8 ∈ x7.gates, x8.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∨ x7.size < x3.size) ∧ x1 x7 := by
  dsimp only
  intro C hF hNot hC
  have hS : ∀ g ∈ C.gates, g.op ∈ S ∧ g.inputs.length ≤ 2 := by
    intro g hg
    exact ⟨by simpa [S] using (hF g hg).1, (hF g hg).2⟩
  let C0 : Circuit := ⟨fixL 10 C.gates, C.output⟩
  have hC0F : PEqualNP.MetaComplexity.FanInTwo C0 := by
    intro g' hg'
    obtain ⟨k', g, hg, rfl⟩ := fixL_mem C.gates 10 g' hg'
    have h := fixG_ok k' g (hS g hg).1 (hS g hg).2
    exact ⟨by simpa [S] using h.2.1, h.2.2.1⟩
  have hC0W : WF C0 := by
    intro j
    refine ⟨fixL_getD C.gates 10 j hS, ?_⟩
    rcases getD_mem_or (fixL 10 C.gates) j with h | h
    · obtain ⟨k', g, hg, e⟩ := fixL_mem C.gates 10 _ h
      show ((fixL 10 C.gates).getD j ⟨GateOp.or, []⟩).op = GateOp.not → _
      rw [e]
      exact (fixG_ok k' g (hS g hg).1 (hS g hg).2).2.2.2.1
    · show ((fixL 10 C.gates).getD j ⟨GateOp.or, []⟩).op = GateOp.not → _
      rw [h]
      simp
  have hC0C : ∀ x : Fin 10 → Bool, C0.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro x
    show (List.foldl stp (List.ofFn x) (fixL 10 C.gates)).getD C.output false
      = (C.gates.foldl stp (List.ofFn x)).getD C.output false
    rw [fixL_foldl _ _ _ (by simp)]
  obtain ⟨C', h1, h2, h3, h4, h5, h6⟩ := main _ (by intro o ho; interval_cases o <;> decide)
    (by decide) C0.gates.length C0 rfl hC0F hC0W (fun x => (hC0C x).trans (hC x))
  have hsz : C0.size = C.size := fixL_len C.gates 10
  refine ⟨C', h1, by omega, h3, h4, ?_, h6⟩
  rcases h5 with rfl | h5
  · left
    obtain ⟨g, hg, hn⟩ := hNot
    obtain ⟨k', hk'⟩ := mem_fixL C.gates 10 g hg
    exact ⟨_, hk', (fixG_ok k' g (hS g hg).1 (hS g hg).2).2.2.2.2 hn⟩
  · right
    omega

namespace PEqualNP.Outside.L_meta_2592_aux.Dead

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private lemma wiresFrom_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (by omega)]
  rw [wiresFrom_getD_lt _ _ _ (by simp [hlen])]
  exact getD_snoc_eq _ _ _ _ hlen.symm

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)


private def substWire (k a i : ℕ) : ℕ :=
  if i < k then i else if i = k then a else i - 1

private def substGate (k a : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (substWire k a)⟩

private lemma substGate_ok (k a : ℕ) (g : Gate) (h : OkGate g) : OkGate (substGate k a g) :=
  ⟨h.1, by simp [substGate]; exact h.2⟩

private lemma substGate_nok (k a : ℕ) (g : Gate) (h : NOkGate g) : NOkGate (substGate k a g) :=
  ⟨substGate_ok k a g h.1, fun hop => by simp [substGate]; exact h.2 hop⟩

private def deleteGate (m : ℕ) (C : Circuit) (j a : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a),
    substWire (m + j) a C.output⟩

private lemma deleteGate_ok (m : ℕ) (C : Circuit) (j a : ℕ)
    (hok : ∀ g ∈ C.gates, OkGate g) : ∀ g ∈ (deleteGate m C j a).gates, OkGate g := by
  intro g hg
  rcases List.mem_append.1 hg with h1 | h1
  · exact hok g (List.mem_of_mem_take h1)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
    exact substGate_ok _ _ g0 (hok g0 (List.mem_of_mem_drop hg0))

private lemma deleteGate_nok (m : ℕ) (C : Circuit) (j a : ℕ)
    (hnok : ∀ g ∈ C.gates, NOkGate g) : ∀ g ∈ (deleteGate m C j a).gates, NOkGate g := by
  intro g hg
  rcases List.mem_append.1 hg with h1 | h1
  · exact hnok g (List.mem_of_mem_take h1)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
    exact substGate_nok _ _ g0 (hnok g0 (List.mem_of_mem_drop hg0))

private lemma deleteGate_len (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length) :
    (deleteGate m C j a).gates.length = C.gates.length - 1 := by
  simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega


private lemma deleteGate_dead_wires (m : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs)
    (x : List Bool) (hx : x.length = m) :
    ∀ i < m + C.gates.length, i ≠ m + j →
      ((deleteGate m C j 0).wires x).getD (substWire (m + j) 0 i) false =
        (C.wires x).getD i false := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  show ∀ i < m + C.gates.length, i ≠ m + j →
      (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) 0)) x).getD
          (substWire (m + j) 0 i) false =
        (wiresFrom C.gates x).getD i false
  set w₂ := wiresFrom (C.gates.take j) x with hw₂
  set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
  have hw₂_len : w₂.length = m + j := by
    rw [hw₂, wiresFrom_length, hx, List.length_take, Nat.min_eq_left (by omega)]
  have hw₁_len : w₁.length = m + j + 1 := by
    rw [hw₁, wiresFrom_length, hw₂_len]; simp
  have hno_drop : ∀ g ∈ C.gates.drop (j + 1), (m + j) ∉ g.inputs := by
    intro g hg
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hg
    rw [List.getElem_drop]
    exact hno (j + 1 + t) (by rw [List.length_drop] at ht; omega) (by omega)
  have haux : ∀ (gs : List Gate) (w₁' w₂' : List Bool),
      w₁'.length = w₂'.length + 1 → m + j ≤ w₂'.length →
      (∀ g ∈ gs, (m + j) ∉ g.inputs) →
      (∀ i < w₁'.length, i ≠ m + j → w₂'.getD (substWire (m + j) 0 i) false = w₁'.getD i false) →
      ∀ i < (wiresFrom gs w₁').length, i ≠ m + j →
        (wiresFrom (gs.map (substGate (m + j) 0)) w₂').getD (substWire (m + j) 0 i) false =
          (wiresFrom gs w₁').getD i false := by
    intro gs
    induction gs with
    | nil =>
      intro w₁' w₂' _ _ _ hag i hi hne
      exact hag i hi hne
    | cons g rest ih =>
      intro w₁' w₂' hlen' hk' hnod hag'
      rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
      have hmap : ((substGate (m + j) 0 g).inputs.map fun i => w₂'.getD i false) =
          (g.inputs.map fun i => w₁'.getD i false) := by
        simp only [substGate, List.map_map]
        apply List.map_congr_left
        intro i hi
        simp only [Function.comp_apply]
        have hne : i ≠ m + j := fun h => hnod g List.mem_cons_self (h ▸ hi)
        by_cases hlt : i < w₁'.length
        · exact hag' i hlt hne
        · have hge : w₂'.length ≤ substWire (m + j) 0 i := by
            unfold substWire; split_ifs <;> omega
          rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
      rw [hmap]
      apply ih _ _ (by simp [hlen']) (by simp; omega)
        (fun g' hg' => hnod g' (List.mem_cons_of_mem _ hg'))
      intro i hi hne
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hlt : i < w₁'.length
      · have hsublt : substWire (m + j) 0 i < w₂'.length := by
          unfold substWire; split_ifs <;> omega
        rw [getD_snoc_lt _ _ _ _ hsublt, getD_snoc_lt _ _ _ _ hlt]
        exact hag' i hlt hne
      · have hieq : i = w₁'.length := by omega
        have hsubeq : substWire (m + j) 0 i = w₂'.length := by
          unfold substWire; split_ifs <;> omega
        rw [getD_snoc_eq _ _ _ _ hsubeq, getD_snoc_eq _ _ _ _ hieq]
        rfl
  intro i hi hne
  rw [wiresFrom_append, ← hw₂]
  conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
  have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = m + C.gates.length := by
    rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
  apply haux (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hno_drop _ i (by omega) hne
  intro u hu hune
  have hlt : u < m + j := by omega
  simp only [substWire, hlt, ↓reduceIte]
  rw [hw₁, wiresFrom_cons, wiresFrom_nil, getD_snoc_lt _ _ _ _ (by omega)]

private lemma deleteDeadGate {m : ℕ} (C : Circuit) (hok : ∀ g ∈ C.gates, OkGate g)
    (j : ℕ) (hj : j < C.gates.length)
    (hout : C.output ≠ m + j)
    (hno : ∀ j' : ℕ, (hj' : j' < C.gates.length) → j < j' → (m + j) ∉ C.gates[j'].inputs) :
    HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
  refine ⟨deleteGate m C j 0, deleteGate_ok m C j 0 hok,
    by show (deleteGate m C j 0).gates.length ≤ C.gates.length - 1; rw [deleteGate_len m C j 0 hj], ?_⟩
  intro x
  show ((deleteGate m C j 0).wires (List.ofFn x)).getD (substWire (m + j) 0 C.output) false =
    (C.wires (List.ofFn x)).getD C.output false
  by_cases hlt : C.output < m + C.gates.length
  · exact deleteGate_dead_wires m C j hj hno (List.ofFn x) (by simp) C.output hlt hout
  · have hge1 : (deleteGate m C j 0).gates.length + m ≤ substWire (m + j) 0 C.output := by
      rw [deleteGate_len m C j 0 hj]
      unfold substWire
      split_ifs <;> omega
    have h1 : ((deleteGate m C j 0).wires (List.ofFn x)).length =
        m + (deleteGate m C j 0).gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    have h2 : (C.wires (List.ofFn x)).length = m + C.gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

end PEqualNP.Outside.L_meta_2592_aux.Dead
