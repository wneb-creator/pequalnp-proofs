import PEqualNP.MetaComplexity.Helpers.Deg3R1

/-!
# Normal form at line-degree 3 (row L-meta-964): setup

Conjecture until the checker accepts it. The kept gates are those of line-degree at most 2; the
gates of line-degree at least 3 are pruned, then the contexts are rebuilt (see `NormalForm3b`).
-/

namespace PEqualNP.MetaComplexity.Helpers.NormalForm3
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Deg3

/-- The degrees of the input wires. -/
def nf3Init (n : ℕ) (marked : Finset ℕ) : List ℕ :=
  (List.range n).map fun i => if i ∈ marked then 1 else 0

/-- The degrees of all wires of the gate list `gs`. -/
def nf3Deg (n : ℕ) (marked : Finset ℕ) (gs : List Gate) : List ℕ :=
  d3r1Fold 0 d3r1DegOp gs (nf3Init n marked)

theorem nf3Init_length (n : ℕ) (marked : Finset ℕ) : (nf3Init n marked).length = n := by
  simp [nf3Init]

theorem nf3Deg_length (n : ℕ) (marked : Finset ℕ) (gs : List Gate) :
    (nf3Deg n marked gs).length = n + gs.length := by
  simp [nf3Deg, d3r1Fold_length, nf3Init_length]

theorem nf3Deg_input (n : ℕ) (marked : Finset ℕ) (gs : List Gate) (i : ℕ) (hi : i < n) :
    (nf3Deg n marked gs).getD i 0 ≤ 1 := by
  unfold nf3Deg
  rw [d3r1Fold_lt _ _ _ _ _ (by rw [nf3Init_length]; exact hi)]
  simp only [nf3Init]
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range]
  split_ifs <;> omega

theorem nf3Deg_gate (n : ℕ) (marked : Finset ℕ) (gs : List Gate) (t : ℕ) (ht : t < gs.length) :
    (nf3Deg n marked gs).getD (n + t) 0 =
      d3r1DegOp gs[t].op (gs[t].inputs.map fun a =>
        if a < n + t then (nf3Deg n marked gs).getD a 0 else 0) := by
  have := d3r1Fold_gate 0 d3r1DegOp gs (nf3Init n marked) t ht
  rw [nf3Init_length] at this
  exact this

theorem nf3_degop_ge (op : GateOp) (l : List ℕ) (x : ℕ) (hx : x ∈ l) : x ≤ d3r1DegOp op l := by
  unfold d3r1DegOp
  split_ifs
  · exact List.le_sum_of_mem hx
  · induction l with
    | nil => simp at hx
    | cons y ys ih =>
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hx with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

theorem nf3Deg_mono (n : ℕ) (marked : Finset ℕ) (gs : List Gate) (t : ℕ) (ht : t < gs.length)
    (a : ℕ) (ha : a ∈ gs[t].inputs) (hat : a < n + t) :
    (nf3Deg n marked gs).getD a 0 ≤ (nf3Deg n marked gs).getD (n + t) 0 := by
  rw [nf3Deg_gate n marked gs t ht]
  apply nf3_degop_ge
  exact List.mem_map.mpr ⟨a, ha, by simp [hat]⟩


/-! ## Extension of a base wire list by extra gates -/

theorem nf3F_append {α : Type} (δ : α) (Φ : GateOp → List α → α) (E E' : List Gate) (B : List α) :
    d3r1Fold δ Φ (E ++ E') B = d3r1Fold δ Φ E' (d3r1Fold δ Φ E B) := by
  simp [d3r1Fold, List.foldl_append]

theorem nf3F_ext {α : Type} (δ : α) (Φ : GateOp → List α → α) (E E' : List Gate) (B : List α)
    (i : ℕ) (hi : i < B.length + E.length) :
    (d3r1Fold δ Φ (E ++ E') B).getD i δ = (d3r1Fold δ Φ E B).getD i δ := by
  rw [nf3F_append]
  apply d3r1Fold_lt
  rw [d3r1Fold_length]; exact hi

theorem nf3F_new {α : Type} (δ : α) (Φ : GateOp → List α → α) (E : List Gate) (B : List α)
    (g : Gate) :
    (d3r1Fold δ Φ (E ++ [g]) B).getD (B.length + E.length) δ =
      Φ g.op (g.inputs.map fun i => (d3r1Fold δ Φ E B).getD i δ) := by
  rw [d3r1Fold_snoc]
  rw [List.getD_append_right _ _ _ _ (by rw [d3r1Fold_length])]
  simp [d3r1Fold_length]

/-- The base data of the extra gates: the degrees and the values of the base wires. -/
structure Env where
  L0 : ℕ
  G0 : List ℕ
  B0 : List Bool
  hG : G0.length = L0
  hB : B0.length = L0

namespace Env
variable (ev : Env)

def dG (E : List Gate) : List ℕ := d3r1Fold 0 d3r1DegOp E ev.G0
def dW (E : List Gate) : List Bool := d3r1Fold false GateOp.eval E ev.B0
def deg (E : List Gate) (i : ℕ) : ℕ := (ev.dG E).getD i 0
def val (E : List Gate) (i : ℕ) : Bool := (ev.dW E).getD i false

theorem deg_ext (E E' : List Gate) (i : ℕ) (hi : i < ev.L0 + E.length) :
    ev.deg (E ++ E') i = ev.deg E i := by
  unfold deg dG
  apply nf3F_ext; rw [ev.hG]; exact hi

theorem val_ext (E E' : List Gate) (i : ℕ) (hi : i < ev.L0 + E.length) :
    ev.val (E ++ E') i = ev.val E i := by
  unfold val dW
  apply nf3F_ext; rw [ev.hB]; exact hi

theorem deg_new (E : List Gate) (g : Gate) :
    ev.deg (E ++ [g]) (ev.L0 + E.length) = d3r1DegOp g.op (g.inputs.map fun i => ev.deg E i) := by
  unfold deg dG
  have := nf3F_new 0 d3r1DegOp E ev.G0 g
  rw [ev.hG] at this
  exact this

theorem val_new (E : List Gate) (g : Gate) :
    ev.val (E ++ [g]) (ev.L0 + E.length) = g.op.eval (g.inputs.map fun i => ev.val E i) := by
  unfold val dW
  have := nf3F_new false GateOp.eval E ev.B0 g
  rw [ev.hB] at this
  exact this

end Env


/-! ## The state machine: contexts, products, extra gates -/

/-- The state: extra gates, the context wire of each gate (if any), the accumulated OR of the
products, the list of products, and the number of gates processed with a context. -/
structure St where
  E : List Gate
  ctx : ℕ → Option ℕ
  acc : Option ℕ
  prs : List (ℕ × ℕ)
  cnt : ℕ

/-- Append one gate. -/
def St.push (st : St) (g : Gate) : St := { st with E := st.E ++ [g] }

/-- Add the wire `k` to the context of gate `c` (an OR gate if it already has one). -/
def St.merge (L0 : ℕ) (st : St) (c k : ℕ) : St :=
  match st.ctx c with
  | none => { st with ctx := Function.update st.ctx c (some k) }
  | some k0 => { st with E := st.E ++ [⟨GateOp.or, [k0, k]⟩],
                         ctx := Function.update st.ctx c (some (L0 + st.E.length)) }

/-- Add the product `AND(a, b)` to the accumulated OR. -/
def St.prod (L0 : ℕ) (st : St) (a b : ℕ) : St :=
  match st.acc with
  | none => { st with E := st.E ++ [⟨GateOp.and, [a, b]⟩], acc := some (L0 + st.E.length),
                      prs := st.prs ++ [(a, b)] }
  | some u => { st with E := st.E ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [u, L0 + st.E.length]⟩],
                        acc := some (L0 + st.E.length + 1), prs := st.prs ++ [(a, b)] }

/-- Number of gates below `k` that have a context. -/
def fcount (ctx : ℕ → Option ℕ) (k : ℕ) : ℕ :=
  ((List.range k).filter fun t => (ctx t).isSome).length

theorem fcount_succ (ctx : ℕ → Option ℕ) (k : ℕ) :
    fcount ctx (k + 1) = fcount ctx k + if (ctx k).isSome then 1 else 0 := by
  unfold fcount
  rw [List.range_succ, List.filter_append]
  by_cases h : (ctx k).isSome <;> simp [h]

theorem fcount_congr (ctx ctx' : ℕ → Option ℕ) (k : ℕ) (h : ∀ t < k, ctx t = ctx' t) :
    fcount ctx k = fcount ctx' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [fcount_succ, fcount_succ, ih (fun t ht => h t (by omega)), h k (by omega)]

theorem fcount_update (ctx : ℕ → Option ℕ) (c w : ℕ) (k : ℕ) (hck : c < k) :
    fcount (Function.update ctx c (some w)) k = fcount ctx k + if ctx c = none then 1 else 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [fcount_succ, fcount_succ]
    by_cases h : c = k
    · subst h
      have : fcount (Function.update ctx c (some w)) c = fcount ctx c :=
        fcount_congr _ _ _ (fun t ht => by simp [Function.update, show t ≠ c by omega])
      rw [this]
      cases hc : ctx c <;> simp [hc]
    · rw [ih (by omega)]
      simp [Function.update, h]
      split_ifs <;> simp_all

theorem fcount_pos (ctx : ℕ → Option ℕ) (c k : ℕ) (hck : c < k) (h : (ctx c).isSome) :
    1 ≤ fcount ctx k := by
  unfold fcount
  apply List.length_pos_of_mem (a := c)
  simp [hck, h]

/-- The context of gate `t` is true. -/
def Env.ctxV (ev : Env) (st : St) (t : ℕ) : Prop :=
  ∃ w, st.ctx t = some w ∧ ev.val st.E w = true

/-- The accumulated OR is true. -/
def Env.accV (ev : Env) (st : St) : Prop :=
  ∃ w, st.acc = some w ∧ ev.val st.E w = true

/-- The structural invariant of a state, for a base `ev` and a predicate `RC` on the gates that
may carry a context. -/
structure SI (ev : Env) (RC : ℕ → Prop) (st : St) : Prop where
  ctx : ∀ t w, st.ctx t = some w → w < ev.L0 + st.E.length ∧ ev.deg st.E w = 0 ∧ RC t
  acc : ∀ w, st.acc = some w → w < ev.L0 + st.E.length
  prs : ∀ pr ∈ st.prs, pr.1 < ev.L0 + st.E.length ∧ pr.2 < ev.L0 + st.E.length ∧
    ev.deg st.E pr.1 ≤ 2 ∧ ev.deg st.E pr.2 ≤ 1
  mono : ∀ g ∈ st.E, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2
  accprs : st.acc = none ↔ st.prs = []
  pv : ev.accV st ↔ ∃ pr ∈ st.prs, ev.val st.E pr.1 = true ∧ ev.val st.E pr.2 = true

/-- The number of gates carried by the accumulator: 0 or 1. -/
def St.flag (st : St) : ℕ := match st.acc with | none => 0 | some _ => 1


theorem pv_ext (ev : Env) (RC : ℕ → Prop) (st st' : St) (E' : List Gate)
    (hE : st'.E = st.E ++ E') (hprs : st'.prs = st.prs) (hacc : ev.accV st' ↔ ev.accV st)
    (h : SI ev RC st) :
    (ev.accV st' ↔ ∃ pr ∈ st'.prs, ev.val st'.E pr.1 = true ∧ ev.val st'.E pr.2 = true) := by
  rw [hacc, h.pv, hprs, hE]
  constructor
  · rintro ⟨pr, hpr, h1, h2⟩
    obtain ⟨a1, a2, _, _⟩ := h.prs pr hpr
    exact ⟨pr, hpr, by rw [ev.val_ext _ _ _ a1]; exact h1, by rw [ev.val_ext _ _ _ a2]; exact h2⟩
  · rintro ⟨pr, hpr, h1, h2⟩
    obtain ⟨a1, a2, _, _⟩ := h.prs pr hpr
    exact ⟨pr, hpr, by rw [← ev.val_ext _ E' _ a1]; exact h1, by rw [← ev.val_ext _ E' _ a2]; exact h2⟩

theorem merge_spec (ev : Env) (RC : ℕ → Prop) (st : St) (c k : ℕ)
    (hk : k < ev.L0 + st.E.length) (hkd : ev.deg st.E k = 0) (hc : RC c) (h : SI ev RC st) :
    SI ev RC (st.merge ev.L0 c k) ∧ (∃ E', (st.merge ev.L0 c k).E = st.E ++ E') ∧
    (st.merge ev.L0 c k).cnt = st.cnt ∧ (st.merge ev.L0 c k).acc = st.acc ∧
    (st.merge ev.L0 c k).prs = st.prs ∧
    (∀ kk, c < kk → (st.merge ev.L0 c k).E.length + fcount (st.merge ev.L0 c k).ctx kk =
      st.E.length + fcount st.ctx kk + 1) ∧
    (∀ t, t ≠ c → (st.merge ev.L0 c k).ctx t = st.ctx t) ∧
    (∃ w, (st.merge ev.L0 c k).ctx c = some w) ∧
    (ev.ctxV (st.merge ev.L0 c k) c ↔ ev.ctxV st c ∨ ev.val st.E k = true) ∧
    (∀ t, t ≠ c → (ev.ctxV (st.merge ev.L0 c k) t ↔ ev.ctxV st t)) ∧
    (ev.accV (st.merge ev.L0 c k) ↔ ev.accV st) := by
  cases h0 : st.ctx c with
  | none =>
    have e : st.merge ev.L0 c k = { st with ctx := Function.update st.ctx c (some k) } := by
      simp [St.merge, h0]
    rw [e]
    refine ⟨⟨?_, h.acc, h.prs, h.mono, h.accprs, h.pv⟩, ⟨[], by simp⟩, rfl, rfl, rfl, ?_, ?_,
      ⟨k, by simp⟩, ?_, ?_, Iff.rfl⟩
    · intro t w ht
      by_cases htc : t = c
      · subst htc
        simp at ht; subst ht
        exact ⟨hk, hkd, hc⟩
      · simp [Function.update, htc] at ht
        exact h.ctx t w ht
    · intro kk hkk
      show st.E.length + fcount (Function.update st.ctx c (some k)) kk = _
      rw [fcount_update _ _ _ _ hkk, h0]; simp; omega
    · intro t ht; simp [Function.update, ht]
    · simp [Env.ctxV, h0]
    · intro t ht
      simp [Env.ctxV, Function.update, ht]
  | some k0 =>
    obtain ⟨hk0, hk0d, _⟩ := h.ctx c k0 h0
    have e : st.merge ev.L0 c k = { st with
        E := st.E ++ [⟨GateOp.or, [k0, k]⟩],
        ctx := Function.update st.ctx c (some (ev.L0 + st.E.length)) } := by
      simp [St.merge, h0]
    rw [e]
    have hnewdeg : ev.deg (st.E ++ [⟨GateOp.or, [k0, k]⟩]) (ev.L0 + st.E.length) = 0 := by
      rw [ev.deg_new]
      simp [d3r1DegOp, ev.deg_ext, hk0d, hkd]
    have hnewval : ev.val (st.E ++ [⟨GateOp.or, [k0, k]⟩]) (ev.L0 + st.E.length) =
        (ev.val st.E k0 || ev.val st.E k) := by
      rw [ev.val_new]
      simp [GateOp.eval]
    have hlen : ∀ w, w < ev.L0 + st.E.length → w < ev.L0 + (st.E ++ [(⟨GateOp.or, [k0, k]⟩ : Gate)]).length := by
      intro w hw; simp; omega
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨[(⟨GateOp.or, [k0, k]⟩ : Gate)], rfl⟩, rfl, rfl, rfl, ?_, ?_,
      ⟨ev.L0 + st.E.length, by simp⟩, ?_, ?_, ?_⟩
    · intro t w ht
      by_cases htc : t = c
      · subst htc
        simp at ht; subst ht
        exact ⟨by simp, hnewdeg, hc⟩
      · simp [Function.update, htc] at ht
        obtain ⟨a1, a2, a3⟩ := h.ctx t w ht
        exact ⟨hlen w a1, by rw [ev.deg_ext _ _ _ a1]; exact a2, a3⟩
    · intro w hw; exact hlen w (h.acc w hw)
    · intro pr hpr
      obtain ⟨a1, a2, a3, a4⟩ := h.prs pr hpr
      exact ⟨hlen _ a1, hlen _ a2, by rw [ev.deg_ext _ _ _ a1]; exact a3,
        by rw [ev.deg_ext _ _ _ a2]; exact a4⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact h.mono g hg
      · simp at hg; subst hg; simp
    · exact h.accprs
    · exact pv_ext ev RC st _ [(⟨GateOp.or, [k0, k]⟩ : Gate)] rfl rfl (by
        simp only [Env.accV]
        constructor
        · rintro ⟨w, hw, hv⟩
          refine ⟨w, hw, ?_⟩
          rw [← ev.val_ext _ [(⟨GateOp.or, [k0, k]⟩ : Gate)] _ (h.acc w hw)]; exact hv
        · rintro ⟨w, hw, hv⟩
          refine ⟨w, hw, ?_⟩
          rw [ev.val_ext _ [(⟨GateOp.or, [k0, k]⟩ : Gate)] _ (h.acc w hw)]; exact hv) h
    · intro kk hkk
      show (st.E ++ [_]).length + fcount (Function.update st.ctx c (some _)) kk = _
      rw [fcount_update _ _ _ _ hkk, h0]; simp; omega
    · intro t ht; simp [Function.update, ht]
    · simp only [Env.ctxV]
      constructor
      · rintro ⟨w, hw, hv⟩
        simp at hw; subst hw
        rw [hnewval] at hv
        simp at hv
        rcases hv with hv | hv
        · left; exact ⟨k0, h0, hv⟩
        · right; exact hv
      · rintro (⟨w, hw, hv⟩ | hv)
        · rw [h0] at hw; simp at hw; subst hw
          refine ⟨ev.L0 + st.E.length, by simp, ?_⟩
          rw [hnewval]; simp [hv, ev.val_ext _ _ _ hk0]
        · refine ⟨ev.L0 + st.E.length, by simp, ?_⟩
          rw [hnewval]; simp [ev.val_ext _ _ _ hk, hv]
    · intro t ht
      simp only [Env.ctxV]
      simp only [Function.update, ht, dif_neg, not_false_eq_true]
      constructor
      · rintro ⟨w, hw, hv⟩
        refine ⟨w, hw, ?_⟩
        rw [← ev.val_ext _ [⟨GateOp.or, [k0, k]⟩] _ (h.ctx t w hw).1]; exact hv
      · rintro ⟨w, hw, hv⟩
        refine ⟨w, hw, ?_⟩
        rw [ev.val_ext _ [⟨GateOp.or, [k0, k]⟩] _ (h.ctx t w hw).1]; exact hv
    · simp only [Env.accV]
      constructor
      · rintro ⟨w, hw, hv⟩
        refine ⟨w, hw, ?_⟩
        rw [← ev.val_ext _ [⟨GateOp.or, [k0, k]⟩] _ (h.acc w hw)]; exact hv
      · rintro ⟨w, hw, hv⟩
        refine ⟨w, hw, ?_⟩
        rw [ev.val_ext _ [⟨GateOp.or, [k0, k]⟩] _ (h.acc w hw)]; exact hv


theorem prod_spec (ev : Env) (RC : ℕ → Prop) (st : St) (a b : ℕ)
    (ha : a < ev.L0 + st.E.length) (hb : b < ev.L0 + st.E.length)
    (hda : ev.deg st.E a ≤ 2) (hdb : ev.deg st.E b ≤ 1) (h : SI ev RC st) :
    SI ev RC (st.prod ev.L0 a b) ∧ (∃ E', (st.prod ev.L0 a b).E = st.E ++ E') ∧
    (st.prod ev.L0 a b).cnt = st.cnt ∧ (st.prod ev.L0 a b).ctx = st.ctx ∧
    (st.prod ev.L0 a b).prs = st.prs ++ [(a, b)] ∧
    (st.prod ev.L0 a b).E.length + (st.prod ev.L0 a b).flag = st.E.length + st.flag + 2 ∧
    (st.prod ev.L0 a b).flag = 1 ∧
    (ev.accV (st.prod ev.L0 a b) ↔ ev.accV st ∨ (ev.val st.E a = true ∧ ev.val st.E b = true)) ∧
    (∀ t, ev.ctxV (st.prod ev.L0 a b) t ↔ ev.ctxV st t) := by
  have hg1 : ev.deg (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]) (ev.L0 + st.E.length) ≤ 1 + 2 := by
    rw [ev.deg_new]
    simp [d3r1DegOp]
    omega
  cases h0 : st.acc with
  | none =>
    have e : st.prod ev.L0 a b = { st with
        E := st.E ++ [⟨GateOp.and, [a, b]⟩], acc := some (ev.L0 + st.E.length),
        prs := st.prs ++ [(a, b)] } := by
      simp [St.prod, h0]
    have hnv : ev.val (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]) (ev.L0 + st.E.length) =
        (ev.val st.E a && ev.val st.E b) := by
      rw [ev.val_new]; simp [GateOp.eval]
    have hnd : ev.deg (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]) (ev.L0 + st.E.length) = ev.deg st.E a + ev.deg st.E b := by
      rw [ev.deg_new]; simp [d3r1DegOp]
    have hlen : ∀ w, w < ev.L0 + st.E.length →
        w < ev.L0 + (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]).length := by
      intro w hw; simp; omega
    rw [e]
    have hpr := h.accprs.mp h0
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨[(⟨GateOp.and, [a, b]⟩ : Gate)], rfl⟩, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro t w ht
      obtain ⟨a1, a2, a3⟩ := h.ctx t w ht
      exact ⟨hlen w a1, by rw [ev.deg_ext _ _ _ a1]; exact a2, a3⟩
    · intro w hw; simp at hw; subst hw; simp
    · intro pr hpr'
      simp only [List.mem_append, List.mem_singleton] at hpr'
      rcases hpr' with hpr' | rfl
      · obtain ⟨a1, a2, a3, a4⟩ := h.prs pr hpr'
        exact ⟨hlen _ a1, hlen _ a2, by rw [ev.deg_ext _ _ _ a1]; exact a3,
          by rw [ev.deg_ext _ _ _ a2]; exact a4⟩
      · refine ⟨hlen _ ha, hlen _ hb, ?_, ?_⟩
        · rw [ev.deg_ext _ _ _ ha]; exact hda
        · rw [ev.deg_ext _ _ _ hb]; exact hdb
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact h.mono g hg
      · simp at hg; subst hg; simp
    · simp
    · constructor
      · rintro ⟨w, hw, hv⟩
        simp at hw; subst hw
        rw [hnv] at hv; simp at hv
        refine ⟨(a, b), by simp [hpr], ?_, ?_⟩
        · show ev.val (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]) a = true
          rw [ev.val_ext _ _ _ ha]; exact hv.1
        · show ev.val (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]) b = true
          rw [ev.val_ext _ _ _ hb]; exact hv.2
      · rintro ⟨pr, hmem, h1, h2⟩
        simp [hpr] at hmem; subst hmem
        refine ⟨ev.L0 + st.E.length, by simp, ?_⟩
        show ev.val (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]) (ev.L0 + st.E.length) = true
        rw [hnv]
        have h1' : ev.val (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]) a = true := h1
        have h2' : ev.val (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]) b = true := h2
        rw [ev.val_ext _ _ _ ha] at h1'
        rw [ev.val_ext _ _ _ hb] at h2'
        simp [h1', h2']
    · simp [St.flag, h0]
    · simp [St.flag]
    · simp only [Env.accV]
      constructor
      · rintro ⟨w, hw, hv⟩
        simp at hw; subst hw
        rw [hnv] at hv; simp at hv; right; exact hv
      · rintro (⟨w, hw, hv⟩ | hv)
        · rw [h0] at hw; simp at hw
        · refine ⟨ev.L0 + st.E.length, by simp, ?_⟩
          rw [hnv]; simp [hv.1, hv.2]
    · intro t
      simp only [Env.ctxV]
      constructor
      · rintro ⟨w, hw, hv⟩
        refine ⟨w, hw, ?_⟩
        rw [← ev.val_ext _ [(⟨GateOp.and, [a, b]⟩ : Gate)] _ (h.ctx t w hw).1]; exact hv
      · rintro ⟨w, hw, hv⟩
        refine ⟨w, hw, ?_⟩
        rw [ev.val_ext _ [(⟨GateOp.and, [a, b]⟩ : Gate)] _ (h.ctx t w hw).1]; exact hv
  | some u =>
    have hu := h.acc u h0
    have e : st.prod ev.L0 a b = { st with
        E := st.E ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [u, ev.L0 + st.E.length]⟩],
        acc := some (ev.L0 + st.E.length + 1), prs := st.prs ++ [(a, b)] } := by
      simp [St.prod, h0]
    have e2 : st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate), ⟨GateOp.or, [u, ev.L0 + st.E.length]⟩] =
        (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]) ++ [⟨GateOp.or, [u, ev.L0 + st.E.length]⟩] := by
      simp
    have hnv : ev.val (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]) (ev.L0 + st.E.length) =
        (ev.val st.E a && ev.val st.E b) := by
      rw [ev.val_new]; simp [GateOp.eval]
    have hnd : ev.deg (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]) (ev.L0 + st.E.length) =
        ev.deg st.E a + ev.deg st.E b := by
      rw [ev.deg_new]; simp [d3r1DegOp]
    have hnv2 : ev.val ((st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]) ++
        [(⟨GateOp.or, [u, ev.L0 + st.E.length]⟩ : Gate)]) (ev.L0 + st.E.length + 1) =
        (ev.val st.E u || (ev.val st.E a && ev.val st.E b)) := by
      have := ev.val_new (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)])
        (⟨GateOp.or, [u, ev.L0 + st.E.length]⟩ : Gate)
      simp only [List.length_append, List.length_singleton] at this
      rw [show ev.L0 + (st.E.length + 1) = ev.L0 + st.E.length + 1 by omega] at this
      rw [this]
      simp [GateOp.eval]
      rw [ev.val_ext _ _ _ hu, hnv]
    have hlen : ∀ w, w < ev.L0 + st.E.length →
        w < ev.L0 + (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate),
          ⟨GateOp.or, [u, ev.L0 + st.E.length]⟩]).length := by
      intro w hw; simp; omega
    have hst : ∀ w, w < ev.L0 + st.E.length → ev.val (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate),
          ⟨GateOp.or, [u, ev.L0 + st.E.length]⟩]) w = ev.val st.E w := by
      intro w hw
      exact ev.val_ext _ _ _ hw
    have hdt : ∀ w, w < ev.L0 + st.E.length → ev.deg (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate),
          ⟨GateOp.or, [u, ev.L0 + st.E.length]⟩]) w = ev.deg st.E w := by
      intro w hw
      exact ev.deg_ext _ _ _ hw
    rw [e]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨[(⟨GateOp.and, [a, b]⟩ : Gate),
      ⟨GateOp.or, [u, ev.L0 + st.E.length]⟩], rfl⟩, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · intro t w ht
      obtain ⟨a1, a2, a3⟩ := h.ctx t w ht
      exact ⟨hlen w a1, by rw [hdt _ a1]; exact a2, a3⟩
    · intro w hw; simp at hw; subst hw; simp; omega
    · intro pr hpr'
      simp only [List.mem_append, List.mem_singleton] at hpr'
      rcases hpr' with hpr' | rfl
      · obtain ⟨a1, a2, a3, a4⟩ := h.prs pr hpr'
        exact ⟨hlen _ a1, hlen _ a2, by rw [hdt _ a1]; exact a3, by rw [hdt _ a2]; exact a4⟩
      · refine ⟨hlen _ ha, hlen _ hb, ?_, ?_⟩
        · rw [hdt _ ha]; exact hda
        · rw [hdt _ hb]; exact hdb
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with hg | rfl | rfl
      · exact h.mono g hg
      · simp
      · simp
    · simp
    · have hpv := h.pv
      constructor
      · rintro ⟨w, hw, hv⟩
        simp at hw; subst hw
        show ∃ pr ∈ st.prs ++ [(a, b)], ev.val (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate),
          ⟨GateOp.or, [u, ev.L0 + st.E.length]⟩]) pr.1 = true ∧ ev.val (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate),
          ⟨GateOp.or, [u, ev.L0 + st.E.length]⟩]) pr.2 = true
        have hv' : ev.val (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate),
          ⟨GateOp.or, [u, ev.L0 + st.E.length]⟩]) (ev.L0 + st.E.length + 1) = true := hv
        rw [e2, hnv2] at hv'
        simp at hv'
        rcases hv' with hv' | hv'
        · obtain ⟨pr, hmem, h1, h2⟩ := hpv.mp ⟨u, h0, hv'⟩
          obtain ⟨a1, a2, _, _⟩ := h.prs pr hmem
          exact ⟨pr, by simp [hmem], by rw [hst _ a1]; exact h1, by rw [hst _ a2]; exact h2⟩
        · exact ⟨(a, b), by simp, by rw [hst _ ha]; exact hv'.1, by rw [hst _ hb]; exact hv'.2⟩
      · rintro ⟨pr, hmem, h1, h2⟩
        refine ⟨ev.L0 + st.E.length + 1, by simp, ?_⟩
        show ev.val (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate),
          ⟨GateOp.or, [u, ev.L0 + st.E.length]⟩]) (ev.L0 + st.E.length + 1) = true
        rw [e2, hnv2]
        simp only [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hmem | rfl
        · obtain ⟨a1, a2, _, _⟩ := h.prs pr hmem
          have h1' : ev.val st.E pr.1 = true := by rw [← hst _ a1]; exact h1
          have h2' : ev.val st.E pr.2 = true := by rw [← hst _ a2]; exact h2
          obtain ⟨w, hw, hwv⟩ := hpv.mpr ⟨pr, hmem, h1', h2'⟩
          rw [h0] at hw; simp at hw; subst hw
          simp [hwv]
        · have h1' : ev.val st.E a = true := by rw [← hst _ ha]; exact h1
          have h2' : ev.val st.E b = true := by rw [← hst _ hb]; exact h2
          simp [h1', h2']
    · simp [St.flag, h0]
    · simp [St.flag]
    · simp only [Env.accV]
      constructor
      · rintro ⟨w, hw, hv⟩
        simp at hw; subst hw
        rw [e2, hnv2] at hv
        simp at hv
        rcases hv with hv | hv
        · left; exact ⟨u, h0, hv⟩
        · right; exact hv
      · rintro (⟨w, hw, hv⟩ | hv)
        · rw [h0] at hw; simp at hw; subst hw
          refine ⟨ev.L0 + st.E.length + 1, by simp, ?_⟩
          rw [e2, hnv2]; simp [hv]
        · refine ⟨ev.L0 + st.E.length + 1, by simp, ?_⟩
          rw [e2, hnv2]; simp [hv.1, hv.2]
    · intro t
      simp only [Env.ctxV]
      constructor
      · rintro ⟨w, hw, hv⟩
        refine ⟨w, hw, ?_⟩
        rw [← hst _ (h.ctx t w hw).1]; exact hv
      · rintro ⟨w, hw, hv⟩
        refine ⟨w, hw, ?_⟩
        rw [hst _ (h.ctx t w hw).1]; exact hv


theorem Env.val_base (ev : Env) (E : List Gate) (i : ℕ) (hi : i < ev.L0) :
    ev.val E i = ev.B0.getD i false := by
  have := ev.val_ext ([] : List Gate) E i (by simpa using hi)
  simp only [List.nil_append] at this
  rw [this]
  simp [Env.val, Env.dW, d3r1Fold]

theorem Env.deg_base (ev : Env) (E : List Gate) (i : ℕ) (hi : i < ev.L0) :
    ev.deg E i = ev.G0.getD i 0 := by
  have := ev.deg_ext ([] : List Gate) E i (by simpa using hi)
  simp only [List.nil_append] at this
  rw [this]
  simp [Env.deg, Env.dG, d3r1Fold]

theorem merge_ctx_eq (L0 : ℕ) (st : St) (c k : ℕ) :
    ∃ w, (st.merge L0 c k).ctx = Function.update st.ctx c (some w) := by
  cases h0 : st.ctx c with
  | none => exact ⟨k, by simp [St.merge, h0]⟩
  | some k0 => exact ⟨L0 + st.E.length, by simp [St.merge, h0]⟩

theorem St.flag_le (st : St) : st.flag ≤ 1 := by
  unfold St.flag; cases st.acc <;> simp

/-- The value of the cover: the accumulated OR, or a gate below `kk` that is true with a true
context. -/
def Env.cover (ev : Env) (n : ℕ) (Wv : ℕ → Bool) (kk : ℕ) (st : St) : Prop :=
  ev.accV st ∨ ∃ t < kk, Wv (n + t) = true ∧ ev.ctxV st t

/-- A child `a` of the processed gate `k` with context wire `c`. -/
def stOrChild (L0 n : ℕ) (K : ℕ → Bool) (mp : ℕ → ℕ) (k c : ℕ) (st : St) (a : ℕ) : St :=
  if a < n + k then
    (if n ≤ a ∧ K (a - n) = false then st.merge L0 (a - n) c else st.prod L0 (mp a) c)
  else st

theorem orChild_spec (ev : Env) (RC : ℕ → Prop) (n : ℕ) (K : ℕ → Bool) (mp : ℕ → ℕ)
    (Wv : ℕ → Bool) (k c : ℕ) (st : St) (a : ℕ)
    (h : SI ev RC st) (hc : c < ev.L0 + st.E.length) (hcd : ev.deg st.E c = 0)
    (hRC : a < n + k → n ≤ a → K (a - n) = false → RC (a - n))
    (hmp : a < n + k → ¬(n ≤ a ∧ K (a - n) = false) →
      mp a < ev.L0 ∧ ev.G0.getD (mp a) 0 ≤ 2 ∧ ev.B0.getD (mp a) false = Wv a) :
    SI ev RC (stOrChild ev.L0 n K mp k c st a) ∧
    (∃ E', (stOrChild ev.L0 n K mp k c st a).E = st.E ++ E') ∧
    (stOrChild ev.L0 n K mp k c st a).cnt = st.cnt ∧
    st.flag ≤ (stOrChild ev.L0 n K mp k c st a).flag ∧
    (∀ kk, k ≤ kk → fcount st.ctx kk ≤ fcount (stOrChild ev.L0 n K mp k c st a).ctx kk) ∧
    (∀ kk, k ≤ kk → (ev.cover n Wv kk (stOrChild ev.L0 n K mp k c st a) ↔
      ev.cover n Wv kk st ∨ (a < n + k ∧ Wv a = true ∧ ev.val st.E c = true))) ∧
    (∀ kk, k ≤ kk → a < n + k → n ≤ a → K (a - n) = false →
      1 ≤ fcount (stOrChild ev.L0 n K mp k c st a).ctx kk) ∧
    (∀ kk, k ≤ kk →
      (stOrChild ev.L0 n K mp k c st a).E.length +
        fcount (stOrChild ev.L0 n K mp k c st a).ctx kk + (stOrChild ev.L0 n K mp k c st a).flag ≤
      st.E.length + fcount st.ctx kk + st.flag +
        (if a < n + k then (if n ≤ a ∧ K (a - n) = false then 1 else 2) else 0)) := by
  by_cases hak : a < n + k
  · by_cases hhi : n ≤ a ∧ K (a - n) = false
    · have e : stOrChild ev.L0 n K mp k c st a = st.merge ev.L0 (a - n) c := by
        simp [stOrChild, hak, hhi]
      obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11⟩ :=
        merge_spec ev RC st (a - n) c hc hcd (hRC hak hhi.1 hhi.2) h
      obtain ⟨w, hw⟩ := merge_ctx_eq ev.L0 st (a - n) c
      rw [e]
      refine ⟨m1, m2, m3, by simp [St.flag, m4], ?_, ?_, ?_, ?_⟩
      · intro kk hkk
        rw [hw, fcount_update _ _ _ _ (by omega)]; omega
      · intro kk hkk
        simp only [Env.cover]
        have hlt : a - n < kk := by omega
        constructor
        · rintro (hv | ⟨t, htk, hWt, hct⟩)
          · left; left; exact (m11).mp hv
          · by_cases htc : t = a - n
            · subst htc
              rcases (m9).mp hct with hct | hct
              · left; right; exact ⟨_, htk, hWt, hct⟩
              · right
                refine ⟨hak, ?_, hct⟩
                have : n + (a - n) = a := by omega
                rw [this] at hWt; exact hWt
            · left; right; exact ⟨t, htk, hWt, (m10 t htc).mp hct⟩
        · rintro ((hv | ⟨t, htk, hWt, hct⟩) | ⟨_, hW, hv⟩)
          · left; exact (m11).mpr hv
          · right
            by_cases htc : t = a - n
            · subst htc; exact ⟨_, htk, hWt, (m9).mpr (Or.inl hct)⟩
            · exact ⟨t, htk, hWt, (m10 t htc).mpr hct⟩
          · right
            refine ⟨a - n, hlt, ?_, (m9).mpr (Or.inr hv)⟩
            have : n + (a - n) = a := by omega
            rw [this]; exact hW
      · intro kk hkk _ _ _
        have hpos : (st.merge ev.L0 (a - n) c).ctx (a - n) = some w ∨ True := Or.inr trivial
        obtain ⟨w', hw'⟩ := m8
        apply fcount_pos _ (a - n) kk (by omega)
        simp [hw']
      · intro kk hkk
        have := m6 kk (by omega)
        simp [hhi, hak, St.flag, m4]
        omega
    · have e : stOrChild ev.L0 n K mp k c st a = st.prod ev.L0 (mp a) c := by
        simp [stOrChild, hak, hhi]
      obtain ⟨hm1, hm2, hm3⟩ := hmp hak hhi
      have hma : mp a < ev.L0 + st.E.length := by omega
      have hmd : ev.deg st.E (mp a) ≤ 2 := by rw [ev.deg_base _ _ hm1]; exact hm2
      have hmv : ev.val st.E (mp a) = Wv a := by rw [ev.val_base _ _ hm1]; exact hm3
      obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ :=
        prod_spec ev RC st (mp a) c hma hc hmd (by omega) h
      rw [e]
      refine ⟨p1, p2, p3, by rw [p7]; exact St.flag_le st, ?_, ?_, ?_, ?_⟩
      · intro kk hkk; rw [p4]
      · intro kk hkk
        simp only [Env.cover]
        constructor
        · rintro (hv | ⟨t, htk, hWt, hct⟩)
          · rcases (p8).mp hv with hv | ⟨hv1, hv2⟩
            · left; left; exact hv
            · right; rw [hmv] at hv1; exact ⟨hak, hv1, hv2⟩
          · left; right; exact ⟨t, htk, hWt, (p9 t).mp hct⟩
        · rintro ((hv | ⟨t, htk, hWt, hct⟩) | ⟨_, hW, hv⟩)
          · left; exact (p8).mpr (Or.inl hv)
          · right; exact ⟨t, htk, hWt, (p9 t).mpr hct⟩
          · left; exact (p8).mpr (Or.inr ⟨by rw [hmv]; exact hW, hv⟩)
      · intro kk hkk _ hn hK; exact absurd ⟨hn, hK⟩ hhi
      · intro kk hkk
        rw [p4]
        simp [hhi, hak]
        omega
  · have e : stOrChild ev.L0 n K mp k c st a = st := by simp [stOrChild, hak]
    rw [e]
    refine ⟨h, ⟨[], by simp⟩, rfl, le_refl _, fun kk _ => le_refl _, ?_, ?_, ?_⟩
    · intro kk hkk
      constructor
      · intro hv; left; exact hv
      · rintro (hv | ⟨h1, _⟩)
        · exact hv
        · exact absurd h1 hak
    · intro kk _ h1; exact absurd h1 hak
    · intro kk _; simp [hak]


theorem push_spec (ev : Env) (RC : ℕ → Prop) (st : St) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) (h : SI ev RC st) :
    SI ev RC (st.push g) ∧ (st.push g).E = st.E ++ [g] ∧ (st.push g).ctx = st.ctx ∧
    (st.push g).acc = st.acc ∧ (st.push g).prs = st.prs ∧ (st.push g).cnt = st.cnt ∧
    (∀ t, ev.ctxV (st.push g) t ↔ ev.ctxV st t) ∧ (ev.accV (st.push g) ↔ ev.accV st) := by
  have hlen : ∀ w, w < ev.L0 + st.E.length → w < ev.L0 + (st.E ++ [g]).length := by
    intro w hw; simp; omega
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro t w ht
    obtain ⟨a1, a2, a3⟩ := h.ctx t w ht
    exact ⟨hlen w a1, by show ev.deg (st.E ++ [g]) w = 0; rw [ev.deg_ext _ _ _ a1]; exact a2, a3⟩
  · intro w hw; exact hlen w (h.acc w hw)
  · intro pr hpr
    obtain ⟨a1, a2, a3, a4⟩ := h.prs pr hpr
    exact ⟨hlen _ a1, hlen _ a2, by show ev.deg (st.E ++ [g]) pr.1 ≤ 2; rw [ev.deg_ext _ _ _ a1]; exact a3,
      by show ev.deg (st.E ++ [g]) pr.2 ≤ 1; rw [ev.deg_ext _ _ _ a2]; exact a4⟩
  · intro g' hg'
    rcases List.mem_append.mp hg' with hg' | hg'
    · exact h.mono g' hg'
    · simp at hg'; subst hg'; exact hg
  · exact h.accprs
  · exact pv_ext ev RC st _ [g] rfl rfl (by
      simp only [Env.accV]
      constructor
      · rintro ⟨w, hw, hv⟩
        refine ⟨w, hw, ?_⟩
        rw [← ev.val_ext _ [g] _ (h.acc w hw)]; exact hv
      · rintro ⟨w, hw, hv⟩
        refine ⟨w, hw, ?_⟩
        show ev.val (st.E ++ [g]) w = true
        rw [ev.val_ext _ [g] _ (h.acc w hw)]; exact hv) h
  · intro t
    simp only [Env.ctxV]
    constructor
    · rintro ⟨w, hw, hv⟩
      refine ⟨w, hw, ?_⟩
      rw [← ev.val_ext _ [g] _ (h.ctx t w hw).1]; exact hv
    · rintro ⟨w, hw, hv⟩
      refine ⟨w, hw, ?_⟩
      show ev.val (st.E ++ [g]) w = true
      rw [ev.val_ext _ [g] _ (h.ctx t w hw).1]; exact hv
  · simp only [Env.accV]
    constructor
    · rintro ⟨w, hw, hv⟩
      refine ⟨w, hw, ?_⟩
      rw [← ev.val_ext _ [g] _ (h.acc w hw)]; exact hv
    · rintro ⟨w, hw, hv⟩
      refine ⟨w, hw, ?_⟩
      show ev.val (st.E ++ [g]) w = true
      rw [ev.val_ext _ [g] _ (h.acc w hw)]; exact hv

/-- The AND(3,0) case: `x` carries the degree 3 and `y'` is a point-only wire. -/
def stAnd30 (L0 n : ℕ) (st : St) (x y' c : ℕ) : St :=
  (st.push ⟨GateOp.and, [y', c]⟩).merge L0 (x - n) (L0 + st.E.length)

theorem and30_spec (ev : Env) (RC : ℕ → Prop) (n : ℕ) (Wv : ℕ → Bool) (st : St) (x y' c : ℕ)
    (k : ℕ) (h : SI ev RC st) (hc : c < ev.L0 + st.E.length) (hcd : ev.deg st.E c = 0)
    (hyd : ev.deg st.E y' = 0) (hxn : n ≤ x) (hxk : x < n + k) (hRC : RC (x - n)) :
    SI ev RC (stAnd30 ev.L0 n st x y' c) ∧ (∃ E', (stAnd30 ev.L0 n st x y' c).E = st.E ++ E') ∧
    (stAnd30 ev.L0 n st x y' c).cnt = st.cnt ∧
    st.flag ≤ (stAnd30 ev.L0 n st x y' c).flag ∧
    (∀ kk, k ≤ kk → fcount st.ctx kk ≤ fcount (stAnd30 ev.L0 n st x y' c).ctx kk) ∧
    (∀ kk, k ≤ kk → (ev.cover n Wv kk (stAnd30 ev.L0 n st x y' c) ↔
      ev.cover n Wv kk st ∨ (Wv x = true ∧ ev.val st.E y' = true ∧ ev.val st.E c = true))) ∧
    (∀ kk, k ≤ kk → 1 ≤ fcount (stAnd30 ev.L0 n st x y' c).ctx kk) ∧
    (∀ kk, k ≤ kk → (stAnd30 ev.L0 n st x y' c).E.length +
        fcount (stAnd30 ev.L0 n st x y' c).ctx kk + (stAnd30 ev.L0 n st x y' c).flag ≤
      st.E.length + fcount st.ctx kk + st.flag + 2) := by
  have hgd : ev.deg (st.E ++ [(⟨GateOp.and, [y', c]⟩ : Gate)]) (ev.L0 + st.E.length) = 0 := by
    rw [ev.deg_new]; simp [d3r1DegOp, hyd, hcd]
  have hgv : ev.val (st.E ++ [(⟨GateOp.and, [y', c]⟩ : Gate)]) (ev.L0 + st.E.length) =
      (ev.val st.E y' && ev.val st.E c) := by
    rw [ev.val_new]; simp [GateOp.eval]
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ :=
    push_spec ev RC st ⟨GateOp.and, [y', c]⟩ (by simp) h
  have hk' : ev.L0 + st.E.length < ev.L0 + (st.push ⟨GateOp.and, [y', c]⟩).E.length := by
    rw [q2]; simp
  have hkd' : ev.deg (st.push ⟨GateOp.and, [y', c]⟩).E (ev.L0 + st.E.length) = 0 := by
    rw [q2]; exact hgd
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11⟩ :=
    merge_spec ev RC (st.push ⟨GateOp.and, [y', c]⟩) (x - n) (ev.L0 + st.E.length) hk' hkd' hRC q1
  obtain ⟨w, hw⟩ := merge_ctx_eq ev.L0 (st.push ⟨GateOp.and, [y', c]⟩) (x - n) (ev.L0 + st.E.length)
  have hE2 : (st.push ⟨GateOp.and, [y', c]⟩).E.length = st.E.length + 1 := by rw [q2]; simp
  have hacc : (stAnd30 ev.L0 n st x y' c).acc = st.acc := by
    unfold stAnd30; rw [m4, q4]
  have hfl : (stAnd30 ev.L0 n st x y' c).flag = st.flag := by
    unfold St.flag; rw [hacc]
  refine ⟨m1, ?_, by unfold stAnd30; rw [m3, q6], by omega, ?_, ?_, ?_, ?_⟩
  · obtain ⟨E', hE'⟩ := m2
    exact ⟨[⟨GateOp.and, [y', c]⟩] ++ E', by unfold stAnd30; rw [hE', q2]; simp⟩
  · intro kk hkk
    unfold stAnd30
    rw [hw, fcount_update _ _ _ _ (by omega), q3]; omega
  · intro kk hkk
    have hlt : x - n < kk := by omega
    have hv1 : ev.val (st.push ⟨GateOp.and, [y', c]⟩).E (ev.L0 + st.E.length) = true ↔
        (ev.val st.E y' = true ∧ ev.val st.E c = true) := by
      rw [q2, hgv]; simp
    have e2 : stAnd30 ev.L0 n st x y' c =
        (st.push ⟨GateOp.and, [y', c]⟩).merge ev.L0 (x - n) (ev.L0 + st.E.length) := rfl
    rw [e2]
    simp only [Env.cover]
    constructor
    · rintro (hv | ⟨t, htk, hWt, hct⟩)
      · left; left; exact (q8).mp ((m11).mp hv)
      · by_cases htc : t = x - n
        · subst htc
          rcases (m9).mp hct with hct | hct
          · left; right; exact ⟨_, htk, hWt, (q7 _).mp hct⟩
          · right
            have hxx : n + (x - n) = x := by omega
            rw [hxx] at hWt
            exact ⟨hWt, (hv1.mp hct).1, (hv1.mp hct).2⟩
        · left; right; exact ⟨t, htk, hWt, (q7 t).mp ((m10 t htc).mp hct)⟩
    · rintro ((hv | ⟨t, htk, hWt, hct⟩) | ⟨hW, hy, hcv⟩)
      · left; exact (m11).mpr ((q8).mpr hv)
      · right
        by_cases htc : t = x - n
        · subst htc; exact ⟨_, htk, hWt, (m9).mpr (Or.inl ((q7 _).mpr hct))⟩
        · exact ⟨t, htk, hWt, (m10 t htc).mpr ((q7 t).mpr hct)⟩
      · right
        refine ⟨x - n, hlt, ?_, (m9).mpr (Or.inr (hv1.mpr ⟨hy, hcv⟩))⟩
        have hxx : n + (x - n) = x := by omega
        rw [hxx]; exact hW
  · intro kk hkk
    apply fcount_pos _ (x - n) kk (by omega)
    obtain ⟨w', hw'⟩ := m8
    simp [stAnd30, hw']
  · intro kk hkk
    have := m6 kk (by omega)
    rw [hfl]
    unfold stAnd30
    rw [hE2] at this
    rw [q3] at this
    omega


/-- The leaf case: `a` is the operand of degree 2, `b` the other one; the product is
`(a, AND(b, c))`. -/
def stLeaf (L0 : ℕ) (st : St) (a b c : ℕ) : St :=
  (st.push ⟨GateOp.and, [b, c]⟩).prod L0 a (L0 + st.E.length)

theorem leaf_spec (ev : Env) (RC : ℕ → Prop) (n : ℕ) (Wv : ℕ → Bool) (st : St) (a b c : ℕ)
    (k : ℕ) (h : SI ev RC st) (hc : c < ev.L0 + st.E.length) (hcd : ev.deg st.E c = 0)
    (ha : a < ev.L0 + st.E.length) (hda : ev.deg st.E a ≤ 2) (hdb : ev.deg st.E b ≤ 1) :
    SI ev RC (stLeaf ev.L0 st a b c) ∧ (∃ E', (stLeaf ev.L0 st a b c).E = st.E ++ E') ∧
    (stLeaf ev.L0 st a b c).cnt = st.cnt ∧
    st.flag ≤ (stLeaf ev.L0 st a b c).flag ∧
    (∀ kk, fcount st.ctx kk ≤ fcount (stLeaf ev.L0 st a b c).ctx kk) ∧
    (∀ kk, (ev.cover n Wv kk (stLeaf ev.L0 st a b c) ↔
      ev.cover n Wv kk st ∨ (ev.val st.E a = true ∧ ev.val st.E b = true ∧ ev.val st.E c = true))) ∧
    (∀ kk, (stLeaf ev.L0 st a b c).E.length +
        fcount (stLeaf ev.L0 st a b c).ctx kk + (stLeaf ev.L0 st a b c).flag ≤
      st.E.length + fcount st.ctx kk + st.flag + 3) ∧
    (stLeaf ev.L0 st a b c).flag = 1 := by
  have hgd : ev.deg (st.E ++ [(⟨GateOp.and, [b, c]⟩ : Gate)]) (ev.L0 + st.E.length) ≤ 1 := by
    rw [ev.deg_new]; simp [d3r1DegOp, hcd]; exact hdb
  have hgv : ev.val (st.E ++ [(⟨GateOp.and, [b, c]⟩ : Gate)]) (ev.L0 + st.E.length) =
      (ev.val st.E b && ev.val st.E c) := by
    rw [ev.val_new]; simp [GateOp.eval]
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8⟩ :=
    push_spec ev RC st ⟨GateOp.and, [b, c]⟩ (by simp) h
  have hE2 : (st.push ⟨GateOp.and, [b, c]⟩).E.length = st.E.length + 1 := by rw [q2]; simp
  have ha' : a < ev.L0 + (st.push ⟨GateOp.and, [b, c]⟩).E.length := by rw [hE2]; omega
  have hb' : ev.L0 + st.E.length < ev.L0 + (st.push ⟨GateOp.and, [b, c]⟩).E.length := by
    rw [hE2]; omega
  have hda' : ev.deg (st.push ⟨GateOp.and, [b, c]⟩).E a ≤ 2 := by
    rw [q2, ev.deg_ext _ _ _ ha]; exact hda
  have hdb' : ev.deg (st.push ⟨GateOp.and, [b, c]⟩).E (ev.L0 + st.E.length) ≤ 1 := by
    rw [q2]; exact hgd
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9⟩ :=
    prod_spec ev RC (st.push ⟨GateOp.and, [b, c]⟩) a (ev.L0 + st.E.length) ha' hb' hda' hdb' q1
  have e2 : stLeaf ev.L0 st a b c =
      (st.push ⟨GateOp.and, [b, c]⟩).prod ev.L0 a (ev.L0 + st.E.length) := rfl
  rw [e2]
  have hflag1 : st.flag ≤ 1 := St.flag_le st
  have hflag0 : (st.push ⟨GateOp.and, [b, c]⟩).flag = st.flag := by unfold St.flag; rw [q4]
  refine ⟨p1, ?_, by rw [p3, q6], by rw [p7]; exact hflag1, ?_, ?_, ?_, p7⟩
  · obtain ⟨E', hE'⟩ := p2
    exact ⟨[⟨GateOp.and, [b, c]⟩] ++ E', by rw [hE', q2]; simp⟩
  · intro kk; rw [p4, q3]
  · intro kk
    simp only [Env.cover]
    have hv1 : ev.val (st.push ⟨GateOp.and, [b, c]⟩).E (ev.L0 + st.E.length) = true ↔
        (ev.val st.E b = true ∧ ev.val st.E c = true) := by
      rw [q2, hgv]; simp
    have hv2 : ev.val (st.push ⟨GateOp.and, [b, c]⟩).E a = ev.val st.E a := by
      rw [q2, ev.val_ext _ _ _ ha]
    constructor
    · rintro (hv | ⟨t, htk, hWt, hct⟩)
      · rcases (p8).mp hv with hv | ⟨hv1', hv2'⟩
        · left; left; exact (q8).mp hv
        · right; rw [hv2] at hv1'; exact ⟨hv1', (hv1.mp hv2').1, (hv1.mp hv2').2⟩
      · left; right; exact ⟨t, htk, hWt, (q7 t).mp ((p9 t).mp hct)⟩
    · rintro ((hv | ⟨t, htk, hWt, hct⟩) | ⟨h1, h2, h3⟩)
      · left; exact (p8).mpr (Or.inl ((q8).mpr hv))
      · right; exact ⟨t, htk, hWt, (p9 t).mpr ((q7 t).mpr hct)⟩
      · left; exact (p8).mpr (Or.inr ⟨by rw [hv2]; exact h1, hv1.mpr ⟨h2, h3⟩⟩)
  · intro kk
    rw [p4, q3]
    omega


theorem Env.val_far (ev : Env) (E : List Gate) (i : ℕ) (hi : ev.L0 + E.length ≤ i) :
    ev.val E i = false := by
  unfold Env.val
  apply List.getD_eq_default
  rw [show (ev.dW E).length = ev.L0 + E.length by simp [Env.dW, d3r1Fold_length, ev.hB]]
  exact hi

theorem Env.deg_far (ev : Env) (E : List Gate) (i : ℕ) (hi : ev.L0 + E.length ≤ i) :
    ev.deg E i = 0 := by
  unfold Env.deg
  apply List.getD_eq_default
  rw [show (ev.dG E).length = ev.L0 + E.length by simp [Env.dG, d3r1Fold_length, ev.hG]]
  exact hi

/-- One step on a reached gate with operation `op` and inputs `ins`, given its context wire `c`. -/
def stStepG (L0 n : ℕ) (K : ℕ → Bool) (mp : ℕ → ℕ) (Dg : ℕ → ℕ) (BIG k c : ℕ)
    (op : GateOp) (ins : List ℕ) (st0 : St) : St :=
  match op, ins with
  | _, [a] => stOrChild L0 n K mp k c st0 a
  | GateOp.or, [a, b] => stOrChild L0 n K mp k c (stOrChild L0 n K mp k c st0 a) b
  | GateOp.and, [a, b] =>
    if (if a < n + k then Dg a else 0) = 3 then
      stAnd30 L0 n st0 a (if b < n + k then mp b else BIG) c
    else if (if b < n + k then Dg b else 0) = 3 then
      stAnd30 L0 n st0 b (if a < n + k then mp a else BIG) c
    else if (if b < n + k then Dg b else 0) ≤ 1 then stLeaf L0 st0 (mp a) (mp b) c
    else stLeaf L0 st0 (mp b) (mp a) c
  | _, _ => st0

/-- What one step needs to know about the circuit. -/
structure Dat (ev : Env) (RC : ℕ → Prop) (n : ℕ) (K : ℕ → Bool) (mp : ℕ → ℕ) (Dg : ℕ → ℕ)
    (Wv : ℕ → Bool) (k : ℕ) (op : GateOp) (ins : List ℕ) : Prop where
  mono : (op = GateOp.and ∨ op = GateOp.or) ∧ ins.length ≤ 2
  val : Wv (n + k) = op.eval (ins.map fun a => if a < n + k then Wv a else false)
  deg : Dg (n + k) = d3r1DegOp op (ins.map fun a => if a < n + k then Dg a else 0)
  deg3 : Dg (n + k) = 3
  high : ∀ a ∈ ins, a < n + k → n ≤ a → K (a - n) = false → Dg a = 3 ∧ RC (a - n)
  low : ∀ a ∈ ins, a < n + k → ¬(n ≤ a ∧ K (a - n) = false) →
    Dg a ≤ 2 ∧ mp a < ev.L0 ∧ ev.G0.getD (mp a) 0 = Dg a ∧ ev.B0.getD (mp a) false = Wv a
  d3high : ∀ a ∈ ins, a < n + k → Dg a = 3 → (n ≤ a ∧ K (a - n) = false)

/-- The result of a step, seen from the state before. -/
def Post (ev : Env) (RC : ℕ → Prop) (n : ℕ) (Wv : ℕ → Bool) (k c : ℕ) (st st' : St) : Prop :=
  SI ev RC st' ∧ st'.cnt = st.cnt ∧
  (ev.cover n Wv k st' ↔ ev.cover n Wv k st ∨ (Wv (n + k) = true ∧ ev.val st.E c = true)) ∧
  st'.E.length + fcount st'.ctx k + st'.flag ≤ st.E.length + fcount st.ctx k + st.flag + 3 ∧
  1 ≤ fcount st'.ctx k + st'.flag

theorem degop_one (op : GateOp) (x : ℕ) : d3r1DegOp op [x] = x := by
  unfold d3r1DegOp; split_ifs <;> simp

theorem stepG_one (ev : Env) (RC : ℕ → Prop) (n : ℕ) (K : ℕ → Bool) (mp : ℕ → ℕ) (Dg : ℕ → ℕ)
    (Wv : ℕ → Bool) (k c : ℕ) (op : GateOp) (a BIG : ℕ) (st0 : St)
    (d : Dat ev RC n K mp Dg Wv k op [a]) (h : SI ev RC st0)
    (hc : c < ev.L0 + st0.E.length) (hcd : ev.deg st0.E c = 0) :
    Post ev RC n Wv k c st0 (stStepG ev.L0 n K mp Dg BIG k c op [a] st0) := by
  have e : stStepG ev.L0 n K mp Dg BIG k c op [a] st0 = stOrChild ev.L0 n K mp k c st0 a := rfl
  rw [e]
  have hda : a ∈ [a] := by simp
  have h3 := d.deg3
  rw [d.deg, List.map_singleton, degop_one] at h3
  have hak : a < n + k := by
    by_contra hh; simp [hh] at h3
  simp only [hak, if_true] at h3
  obtain ⟨hn, hK⟩ := d.d3high a hda hak h3
  obtain ⟨_, hRC⟩ := d.high a hda hak hn hK
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ := orChild_spec ev RC n K mp Wv k c st0 a h hc hcd
    (fun _ _ _ => hRC)
    (fun _ hl => absurd ⟨hn, hK⟩ hl)
  have hW : Wv (n + k) = Wv a := by
    rw [d.val]
    simp only [List.map_singleton, hak, if_true]
    rcases d.mono.1 with rfl | rfl <;> simp [GateOp.eval]
  refine ⟨o1, o3, by rw [o6 k le_rfl, hW]; simp [hak], ?_, ?_⟩
  · have := o8 k le_rfl
    simp [hak, hn, hK] at this
    omega
  · have := o7 k le_rfl hak hn hK
    omega


theorem stepG_or2 (ev : Env) (RC : ℕ → Prop) (n : ℕ) (K : ℕ → Bool) (mp : ℕ → ℕ) (Dg : ℕ → ℕ)
    (Wv : ℕ → Bool) (k c : ℕ) (a b BIG : ℕ) (st0 : St)
    (d : Dat ev RC n K mp Dg Wv k GateOp.or [a, b]) (h : SI ev RC st0)
    (hc : c < ev.L0 + st0.E.length) (hcd : ev.deg st0.E c = 0) :
    Post ev RC n Wv k c st0 (stStepG ev.L0 n K mp Dg BIG k c GateOp.or [a, b] st0) := by
  have e : stStepG ev.L0 n K mp Dg BIG k c GateOp.or [a, b] st0 =
      stOrChild ev.L0 n K mp k c (stOrChild ev.L0 n K mp k c st0 a) b := rfl
  rw [e]
  have hma : a ∈ [a, b] := by simp
  have hmb : b ∈ [a, b] := by simp
  have hRCa : a < n + k → n ≤ a → K (a - n) = false → RC (a - n) :=
    fun h1 h2 h3 => (d.high a hma h1 h2 h3).2
  have hRCb : b < n + k → n ≤ b → K (b - n) = false → RC (b - n) :=
    fun h1 h2 h3 => (d.high b hmb h1 h2 h3).2
  have hmpa : a < n + k → ¬(n ≤ a ∧ K (a - n) = false) →
      mp a < ev.L0 ∧ ev.G0.getD (mp a) 0 ≤ 2 ∧ ev.B0.getD (mp a) false = Wv a :=
    fun h1 h2 => by
      obtain ⟨x1, x2, x3, x4⟩ := d.low a hma h1 h2
      exact ⟨x2, by omega, x4⟩
  have hmpb : b < n + k → ¬(n ≤ b ∧ K (b - n) = false) →
      mp b < ev.L0 ∧ ev.G0.getD (mp b) 0 ≤ 2 ∧ ev.B0.getD (mp b) false = Wv b :=
    fun h1 h2 => by
      obtain ⟨x1, x2, x3, x4⟩ := d.low b hmb h1 h2
      exact ⟨x2, by omega, x4⟩
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩ :=
    orChild_spec ev RC n K mp Wv k c st0 a h hc hcd hRCa hmpa
  obtain ⟨E1, hE1⟩ := o2
  have hc1 : c < ev.L0 + (stOrChild ev.L0 n K mp k c st0 a).E.length := by
    rw [hE1]; simp; omega
  have hcd1 : ev.deg (stOrChild ev.L0 n K mp k c st0 a).E c = 0 := by
    rw [hE1, ev.deg_ext _ _ _ hc]; exact hcd
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ :=
    orChild_spec ev RC n K mp Wv k c _ b o1 hc1 hcd1 hRCb hmpb
  have hv1 : ev.val (stOrChild ev.L0 n K mp k c st0 a).E c = ev.val st0.E c := by
    rw [hE1, ev.val_ext _ _ _ hc]
  have hW : Wv (n + k) = true ↔ (a < n + k ∧ Wv a = true) ∨ (b < n + k ∧ Wv b = true) := by
    rw [d.val]
    by_cases ha : a < n + k <;> by_cases hb : b < n + k <;> simp [GateOp.eval, ha, hb]
  have hdeg : (a < n + k ∧ Dg a = 3) ∨ (b < n + k ∧ Dg b = 3) := by
    have h3 := d.deg3
    rw [d.deg] at h3
    simp only [List.map_cons, List.map_nil] at h3
    simp only [d3r1DegOp] at h3
    by_cases ha : a < n + k <;> by_cases hb : b < n + k <;> simp [ha, hb] at h3 <;> omega
  refine ⟨p1, by rw [p3, o3], ?_, ?_, ?_⟩
  · rw [p6 k le_rfl, o6 k le_rfl, hv1]
    constructor
    · rintro ((hv | hv) | hv)
      · exact Or.inl hv
      · exact Or.inr ⟨hW.mpr (Or.inl ⟨hv.1, hv.2.1⟩), hv.2.2⟩
      · exact Or.inr ⟨hW.mpr (Or.inr ⟨hv.1, hv.2.1⟩), hv.2.2⟩
    · rintro (hv | ⟨hw, hcv⟩)
      · exact Or.inl (Or.inl hv)
      · rcases hW.mp hw with hv | hv
        · exact Or.inl (Or.inr ⟨hv.1, hv.2, hcv⟩)
        · exact Or.inr ⟨hv.1, hv.2, hcv⟩
  · have q1 := o8 k le_rfl
    have q2 := p8 k le_rfl
    have hca : (if a < n + k then (if n ≤ a ∧ K (a - n) = false then 1 else 2) else 0) ≤ 2 := by
      split_ifs <;> omega
    have hcb : (if b < n + k then (if n ≤ b ∧ K (b - n) = false then 1 else 2) else 0) ≤ 2 := by
      split_ifs <;> omega
    rcases hdeg with ⟨hak, hd3⟩ | ⟨hbk, hd3⟩
    · obtain ⟨hn, hK⟩ := d.d3high a hma hak hd3
      have : (if a < n + k then (if n ≤ a ∧ K (a - n) = false then 1 else 2) else 0) = 1 := by
        simp [hak, hn, hK]
      omega
    · obtain ⟨hn, hK⟩ := d.d3high b hmb hbk hd3
      have : (if b < n + k then (if n ≤ b ∧ K (b - n) = false then 1 else 2) else 0) = 1 := by
        simp [hbk, hn, hK]
      omega
  · rcases hdeg with ⟨hak, hd3⟩ | ⟨hbk, hd3⟩
    · obtain ⟨hn, hK⟩ := d.d3high a hma hak hd3
      have := o7 k le_rfl hak hn hK
      have := p5 k le_rfl
      omega
    · obtain ⟨hn, hK⟩ := d.d3high b hmb hbk hd3
      have := p7 k le_rfl hbk hn hK
      omega


/-- The AND(3,0) case of a step: `x` has degree 3, `y` has degree 0. -/
theorem stepG_and30 (ev : Env) (RC : ℕ → Prop) (n : ℕ) (K : ℕ → Bool) (mp : ℕ → ℕ)
    (Dg : ℕ → ℕ) (Wv : ℕ → Bool) (k c : ℕ) (x y BIG : ℕ) (st0 : St)
    (ins : List ℕ) (hx : x ∈ ins) (hy : y ∈ ins)
    (d : Dat ev RC n K mp Dg Wv k GateOp.and ins) (h : SI ev RC st0)
    (hc : c < ev.L0 + st0.E.length) (hcd : ev.deg st0.E c = 0)
    (hBIG : ev.L0 + st0.E.length ≤ BIG)
    (hxk : x < n + k) (hx3 : Dg x = 3) (hyd : (if y < n + k then Dg y else 0) = 0) :
    SI ev RC (stAnd30 ev.L0 n st0 x (if y < n + k then mp y else BIG) c) ∧
    (stAnd30 ev.L0 n st0 x (if y < n + k then mp y else BIG) c).cnt = st0.cnt ∧
    (ev.cover n Wv k (stAnd30 ev.L0 n st0 x (if y < n + k then mp y else BIG) c) ↔
      ev.cover n Wv k st0 ∨ (Wv x = true ∧ (y < n + k ∧ Wv y = true) ∧ ev.val st0.E c = true)) ∧
    (stAnd30 ev.L0 n st0 x (if y < n + k then mp y else BIG) c).E.length +
        fcount (stAnd30 ev.L0 n st0 x (if y < n + k then mp y else BIG) c).ctx k +
        (stAnd30 ev.L0 n st0 x (if y < n + k then mp y else BIG) c).flag ≤
      st0.E.length + fcount st0.ctx k + st0.flag + 2 ∧
    1 ≤ fcount (stAnd30 ev.L0 n st0 x (if y < n + k then mp y else BIG) c).ctx k := by
  obtain ⟨hn, hK⟩ := d.d3high x hx hxk hx3
  obtain ⟨_, hRC⟩ := d.high x hx hxk hn hK
  have hyD : ev.deg st0.E (if y < n + k then mp y else BIG) = 0 := by
    by_cases hyk : y < n + k
    · simp only [hyk, if_true] at hyd ⊢
      have hnh : ¬(n ≤ y ∧ K (y - n) = false) := by
        intro hh
        have := (d.high y hy hyk hh.1 hh.2).1
        omega
      obtain ⟨x1, x2, x3, x4⟩ := d.low y hy hyk hnh
      rw [ev.deg_base _ _ x2, x3]; exact hyd
    · simp only [hyk, if_false]
      exact ev.deg_far _ _ hBIG
  have hyV : ev.val st0.E (if y < n + k then mp y else BIG) = true ↔ (y < n + k ∧ Wv y = true) := by
    by_cases hyk : y < n + k
    · simp only [hyk, if_true]
      have hnh : ¬(n ≤ y ∧ K (y - n) = false) := by
        intro hh
        simp only [hyk, if_true] at hyd
        have := (d.high y hy hyk hh.1 hh.2).1
        omega
      obtain ⟨x1, x2, x3, x4⟩ := d.low y hy hyk hnh
      rw [ev.val_base _ _ x2, x4]; simp [hyk]
    · simp only [hyk, if_false]
      rw [ev.val_far _ _ hBIG]; simp [hyk]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ :=
    and30_spec ev RC n Wv st0 x _ c k h hc hcd hyD hn hxk hRC
  refine ⟨a1, a3, ?_, a8 k le_rfl, a7 k le_rfl⟩
  rw [a6 k le_rfl]
  constructor
  · rintro (hv | ⟨hw, hy', hcv⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨hw, hyV.mp hy', hcv⟩
  · rintro (hv | ⟨hw, hy', hcv⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨hw, hyV.mpr hy', hcv⟩


theorem stepG_and2 (ev : Env) (RC : ℕ → Prop) (n : ℕ) (K : ℕ → Bool) (mp : ℕ → ℕ) (Dg : ℕ → ℕ)
    (Wv : ℕ → Bool) (k c : ℕ) (a b BIG : ℕ) (st0 : St)
    (d : Dat ev RC n K mp Dg Wv k GateOp.and [a, b]) (h : SI ev RC st0)
    (hc : c < ev.L0 + st0.E.length) (hcd : ev.deg st0.E c = 0)
    (hBIG : ev.L0 + st0.E.length ≤ BIG) :
    Post ev RC n Wv k c st0 (stStepG ev.L0 n K mp Dg BIG k c GateOp.and [a, b] st0) := by
  have hma : a ∈ [a, b] := by simp
  have hmb : b ∈ [a, b] := by simp
  have hsum : (if a < n + k then Dg a else 0) + (if b < n + k then Dg b else 0) = 3 := by
    have h3 := d.deg3
    rw [d.deg] at h3
    simp only [List.map_cons, List.map_nil, d3r1DegOp] at h3
    simpa using h3
  have hW : Wv (n + k) = true ↔ (a < n + k ∧ Wv a = true) ∧ (b < n + k ∧ Wv b = true) := by
    rw [d.val]
    by_cases ha : a < n + k <;> by_cases hb : b < n + k <;> simp [GateOp.eval, ha, hb]
  unfold stStepG
  simp only []
  by_cases h1 : (if a < n + k then Dg a else 0) = 3
  · rw [if_pos h1]
    have hak : a < n + k := by
      by_contra hh; simp [hh] at h1
    simp only [hak, if_true] at h1
    have hyd : (if b < n + k then Dg b else 0) = 0 := by
      simp only [hak, if_true] at hsum; omega
    obtain ⟨s1, s2, s3, s4, s5⟩ := stepG_and30 ev RC n K mp Dg Wv k c a b BIG st0 [a, b] hma hmb d h
      hc hcd hBIG hak h1 hyd
    refine ⟨s1, s2, ?_, ?_, ?_⟩
    · rw [s3]
      constructor
      · rintro (hv | ⟨h1', h2', h3'⟩)
        · exact Or.inl hv
        · exact Or.inr ⟨hW.mpr ⟨⟨hak, h1'⟩, h2'⟩, h3'⟩
      · rintro (hv | ⟨hw, h3'⟩)
        · exact Or.inl hv
        · exact Or.inr ⟨(hW.mp hw).1.2, (hW.mp hw).2, h3'⟩
    · omega
    · omega
  · rw [if_neg h1]
    by_cases h2 : (if b < n + k then Dg b else 0) = 3
    · rw [if_pos h2]
      have hbk : b < n + k := by
        by_contra hh; simp [hh] at h2
      simp only [hbk, if_true] at h2
      have hyd : (if a < n + k then Dg a else 0) = 0 := by
        simp only [hbk, if_true] at hsum; omega
      obtain ⟨s1, s2, s3, s4, s5⟩ := stepG_and30 ev RC n K mp Dg Wv k c b a BIG st0 [a, b] hmb hma d h
        hc hcd hBIG hbk h2 hyd
      refine ⟨s1, s2, ?_, ?_, ?_⟩
      · rw [s3]
        constructor
        · rintro (hv | ⟨h1', h2', h3'⟩)
          · exact Or.inl hv
          · exact Or.inr ⟨hW.mpr ⟨h2', ⟨hbk, h1'⟩⟩, h3'⟩
        · rintro (hv | ⟨hw, h3'⟩)
          · exact Or.inl hv
          · exact Or.inr ⟨(hW.mp hw).2.2, (hW.mp hw).1, h3'⟩
      · omega
      · omega
    · rw [if_neg h2]
      -- the leaf case
      have hak : a < n + k := by
        by_contra hh; simp [hh] at hsum h1; omega
      have hbk : b < n + k := by
        by_contra hh; simp [hh] at hsum h2; omega
      simp only [hak, hbk, if_true] at hsum h1 h2
      have hnha : ¬(n ≤ a ∧ K (a - n) = false) := by
        intro hh; have := (d.high a hma hak hh.1 hh.2).1; omega
      have hnhb : ¬(n ≤ b ∧ K (b - n) = false) := by
        intro hh; have := (d.high b hmb hbk hh.1 hh.2).1; omega
      obtain ⟨xa1, xa2, xa3, xa4⟩ := d.low a hma hak hnha
      obtain ⟨xb1, xb2, xb3, xb4⟩ := d.low b hmb hbk hnhb
      have hda : ev.deg st0.E (mp a) = Dg a := by rw [ev.deg_base _ _ xa2, xa3]
      have hdb : ev.deg st0.E (mp b) = Dg b := by rw [ev.deg_base _ _ xb2, xb3]
      have hva : ev.val st0.E (mp a) = Wv a := by rw [ev.val_base _ _ xa2, xa4]
      have hvb : ev.val st0.E (mp b) = Wv b := by rw [ev.val_base _ _ xb2, xb4]
      have hwa : mp a < ev.L0 + st0.E.length := by omega
      have hwb : mp b < ev.L0 + st0.E.length := by omega
      by_cases h3 : Dg b ≤ 1
      · rw [if_pos (by simpa [hbk] using h3)]
        obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := leaf_spec ev RC n Wv st0 (mp a) (mp b) c k h hc hcd
          hwa (by omega) (by omega)
        refine ⟨l1, l3, ?_, ?_, by omega⟩
        · rw [l6 k, hva, hvb]
          constructor
          · rintro (hv | ⟨h1', h2', h3'⟩)
            · exact Or.inl hv
            · exact Or.inr ⟨hW.mpr ⟨⟨hak, by simpa [hva] using h1'⟩, ⟨hbk, by simpa [hvb] using h2'⟩⟩, h3'⟩
          · rintro (hv | ⟨hw, h3'⟩)
            · exact Or.inl hv
            · exact Or.inr ⟨(hW.mp hw).1.2, (hW.mp hw).2.2, h3'⟩
        · have := l7 k; omega
      · rw [if_neg (by simpa [hbk] using h3)]
        obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8⟩ := leaf_spec ev RC n Wv st0 (mp b) (mp a) c k h hc hcd
          hwb (by omega) (by omega)
        refine ⟨l1, l3, ?_, ?_, by omega⟩
        · rw [l6 k, hva, hvb]
          constructor
          · rintro (hv | ⟨h1', h2', h3'⟩)
            · exact Or.inl hv
            · exact Or.inr ⟨hW.mpr ⟨⟨hak, h2'⟩, ⟨hbk, h1'⟩⟩, h3'⟩
          · rintro (hv | ⟨hw, h3'⟩)
            · exact Or.inl hv
            · exact Or.inr ⟨(hW.mp hw).2.2, (hW.mp hw).1.2, h3'⟩
        · have := l7 k; omega

end PEqualNP.MetaComplexity.Helpers.NormalForm3
