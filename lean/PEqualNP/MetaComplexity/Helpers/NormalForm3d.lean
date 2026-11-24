import PEqualNP.MetaComplexity.Helpers.NormalForm3c

/-!
# Normal form at line-degree 3 with the two extra facts (row L-meta-1017)

Conjecture until the checker accepts it. The same construction as `NormalForm3c`, with two extra
invariants: the number of products is at most the number of extra gates, and the accumulated OR
has line-degree at most 3.
-/

namespace PEqualNP.MetaComplexity.Helpers.NormalForm3
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Deg3

/-- The extra invariant: fewer products than extra gates, and the accumulator has degree <= 3. -/
def nf3dXI (ev : Env) (st : St) : Prop :=
  st.prs.length ≤ st.E.length ∧
  ∀ w, st.acc = some w → w < ev.L0 + st.E.length ∧ ev.deg st.E w ≤ 3

/-- A transition keeps the invariant and only appends extra gates. -/
def nf3dOK (ev : Env) (st st' : St) : Prop :=
  nf3dXI ev st' ∧ ∃ E', st'.E = st.E ++ E'

theorem nf3d_ok_refl (ev : Env) (st : St) (h : nf3dXI ev st) : nf3dOK ev st st :=
  ⟨h, [], by simp⟩

theorem nf3d_ok_trans (ev : Env) (a b c : St) (h1 : nf3dOK ev a b) (h2 : nf3dOK ev b c) :
    nf3dOK ev a c := by
  obtain ⟨_, E1, e1⟩ := h1
  obtain ⟨x, E2, e2⟩ := h2
  exact ⟨x, E1 ++ E2, by rw [e2, e1]; simp⟩

theorem nf3d_push (ev : Env) (st : St) (g : Gate) (h : nf3dXI ev st) :
    nf3dOK ev st (st.push g) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨by simp [St.push]; omega, ?_⟩, [g], rfl⟩
  intro w hw
  obtain ⟨a, b⟩ := h2 w hw
  refine ⟨by simp [St.push]; omega, ?_⟩
  show ev.deg (st.E ++ [g]) w ≤ 3
  rw [ev.deg_ext _ _ _ a]; exact b

theorem nf3d_merge (ev : Env) (st : St) (c k : ℕ) (h : nf3dXI ev st) :
    nf3dOK ev st (st.merge ev.L0 c k) := by
  cases h0 : st.ctx c with
  | none =>
    have e : st.merge ev.L0 c k = { st with ctx := Function.update st.ctx c (some k) } := by
      simp [St.merge, h0]
    rw [e]
    exact nf3d_ok_refl ev st h
  | some k0 =>
    have e : st.merge ev.L0 c k = { st.push ⟨GateOp.or, [k0, k]⟩ with
        ctx := Function.update st.ctx c (some (ev.L0 + st.E.length)) } := by
      simp [St.merge, h0, St.push]
    rw [e]
    exact nf3d_push ev st _ h

theorem nf3d_prod (ev : Env) (st : St) (a b : ℕ) (hda : ev.deg st.E a ≤ 2)
    (hdb : ev.deg st.E b ≤ 1) (h : nf3dXI ev st) : nf3dOK ev st (st.prod ev.L0 a b) := by
  obtain ⟨h1, h2⟩ := h
  have hnd : ev.deg (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]) (ev.L0 + st.E.length) ≤ 3 := by
    rw [ev.deg_new]; simp [d3r1DegOp]; omega
  cases h0 : st.acc with
  | none =>
    have e : st.prod ev.L0 a b = { st with
        E := st.E ++ [⟨GateOp.and, [a, b]⟩], acc := some (ev.L0 + st.E.length),
        prs := st.prs ++ [(a, b)] } := by
      simp [St.prod, h0]
    rw [e]
    refine ⟨⟨?_, ?_⟩, [⟨GateOp.and, [a, b]⟩], rfl⟩
    · simp; omega
    · intro w hw
      simp at hw; subst hw
      exact ⟨by simp, hnd⟩
  | some u =>
    have hu := h2 u h0
    have e : st.prod ev.L0 a b = { st with
        E := st.E ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [u, ev.L0 + st.E.length]⟩],
        acc := some (ev.L0 + st.E.length + 1), prs := st.prs ++ [(a, b)] } := by
      simp [St.prod, h0]
    have e2 : st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate), ⟨GateOp.or, [u, ev.L0 + st.E.length]⟩] =
        (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]) ++ [⟨GateOp.or, [u, ev.L0 + st.E.length]⟩] := by
      simp
    have hnd2 : ev.deg ((st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]) ++
        [(⟨GateOp.or, [u, ev.L0 + st.E.length]⟩ : Gate)]) (ev.L0 + st.E.length + 1) ≤ 3 := by
      have := ev.deg_new (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)])
        (⟨GateOp.or, [u, ev.L0 + st.E.length]⟩ : Gate)
      simp only [List.length_append, List.length_singleton] at this
      rw [show ev.L0 + (st.E.length + 1) = ev.L0 + st.E.length + 1 by omega] at this
      rw [this]
      have h3 : ev.deg (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate)]) u = ev.deg st.E u :=
        ev.deg_ext _ _ _ hu.1
      simp [d3r1DegOp, h3]
      omega
    rw [e]
    refine ⟨⟨?_, ?_⟩, [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [u, ev.L0 + st.E.length]⟩], rfl⟩
    · simp; omega
    · intro w hw
      simp at hw; subst hw
      refine ⟨by simp; omega, ?_⟩
      show ev.deg (st.E ++ [(⟨GateOp.and, [a, b]⟩ : Gate),
        ⟨GateOp.or, [u, ev.L0 + st.E.length]⟩]) (ev.L0 + st.E.length + 1) ≤ 3
      rw [e2]; exact hnd2

theorem nf3d_orChild (ev : Env) (n : ℕ) (K : ℕ → Bool) (mp : ℕ → ℕ) (k c : ℕ) (st : St) (a : ℕ)
    (h : nf3dXI ev st) (hcd : ev.deg st.E c = 0)
    (hmp : a < n + k → ¬(n ≤ a ∧ K (a - n) = false) →
      mp a < ev.L0 ∧ ev.G0.getD (mp a) 0 ≤ 2) :
    nf3dOK ev st (stOrChild ev.L0 n K mp k c st a) := by
  unfold stOrChild
  by_cases hak : a < n + k
  · by_cases hhi : n ≤ a ∧ K (a - n) = false
    · simp only [hak, hhi, and_self, if_true]
      exact nf3d_merge ev st _ _ h
    · simp only [hak, hhi, if_true, if_false]
      obtain ⟨m1, m2⟩ := hmp hak hhi
      apply nf3d_prod ev st _ _ _ _ h
      · rw [ev.deg_base _ _ m1]; exact m2
      · omega
  · simp only [hak, if_false]
    exact nf3d_ok_refl ev st h

theorem nf3d_and30 (ev : Env) (n : ℕ) (st : St) (x y' c : ℕ) (h : nf3dXI ev st) :
    nf3dOK ev st (stAnd30 ev.L0 n st x y' c) := by
  unfold stAnd30
  exact nf3d_ok_trans ev _ _ _ (nf3d_push ev st _ h)
    (nf3d_merge ev _ _ _ (nf3d_push ev st _ h).1)

theorem nf3d_leaf (ev : Env) (st : St) (a b c : ℕ) (h : nf3dXI ev st)
    (hc : c < ev.L0 + st.E.length) (hcd : ev.deg st.E c = 0)
    (ha : a < ev.L0 + st.E.length) (hda : ev.deg st.E a ≤ 2) (hdb : ev.deg st.E b ≤ 1) :
    nf3dOK ev st (stLeaf ev.L0 st a b c) := by
  unfold stLeaf
  have hp := nf3d_push ev st ⟨GateOp.and, [b, c]⟩ h
  have hE : (st.push ⟨GateOp.and, [b, c]⟩).E = st.E ++ [⟨GateOp.and, [b, c]⟩] := rfl
  have hnd : ev.deg (st.E ++ [(⟨GateOp.and, [b, c]⟩ : Gate)]) (ev.L0 + st.E.length) ≤ 1 := by
    rw [ev.deg_new]; simp [d3r1DegOp, hcd]; exact hdb
  refine nf3d_ok_trans ev _ _ _ hp (nf3d_prod ev _ a _ ?_ ?_ hp.1)
  · rw [hE, ev.deg_ext _ _ _ ha]; exact hda
  · rw [hE]; simpa using hnd


theorem nf3d_stepG (ev : Env) (RC : ℕ → Prop) (n : ℕ) (K : ℕ → Bool) (mp : ℕ → ℕ) (Dg : ℕ → ℕ)
    (Wv : ℕ → Bool) (k c : ℕ) (op : GateOp) (ins : List ℕ) (BIG : ℕ) (st0 : St)
    (d : Dat ev RC n K mp Dg Wv k op ins) (h : nf3dXI ev st0)
    (hc : c < ev.L0 + st0.E.length) (hcd : ev.deg st0.E c = 0) :
    nf3dOK ev st0 (stStepG ev.L0 n K mp Dg BIG k c op ins st0) := by
  have hlowmp : ∀ a ∈ ins, a < n + k → ¬(n ≤ a ∧ K (a - n) = false) →
      mp a < ev.L0 ∧ ev.G0.getD (mp a) 0 ≤ 2 := by
    intro a ha h1 h2
    obtain ⟨x1, x2, x3, x4⟩ := d.low a ha h1 h2
    exact ⟨x2, by omega⟩
  obtain ⟨hop, hlen⟩ := d.mono
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨x, rest⟩⟩⟩
  · exact nf3d_ok_refl ev st0 h
  · have e : stStepG ev.L0 n K mp Dg BIG k c op [a] st0 = stOrChild ev.L0 n K mp k c st0 a := rfl
    rw [e]
    exact nf3d_orChild ev n K mp k c st0 a h hcd (hlowmp a (by simp))
  · rcases hop with rfl | rfl
    · -- AND of two
      have hma : a ∈ [a, b] := by simp
      have hmb : b ∈ [a, b] := by simp
      have hsum : (if a < n + k then Dg a else 0) + (if b < n + k then Dg b else 0) = 3 := by
        have h3 := d.deg3
        rw [d.deg] at h3
        simp only [List.map_cons, List.map_nil, d3r1DegOp] at h3
        simpa using h3
      unfold stStepG
      simp only []
      by_cases h1 : (if a < n + k then Dg a else 0) = 3
      · rw [if_pos h1]
        exact nf3d_and30 ev n st0 _ _ _ h
      · rw [if_neg h1]
        by_cases h2 : (if b < n + k then Dg b else 0) = 3
        · rw [if_pos h2]
          exact nf3d_and30 ev n st0 _ _ _ h
        · rw [if_neg h2]
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
          have hwa : mp a < ev.L0 + st0.E.length := by omega
          have hwb : mp b < ev.L0 + st0.E.length := by omega
          by_cases h3 : Dg b ≤ 1
          · rw [if_pos (by simpa [hbk] using h3)]
            exact nf3d_leaf ev st0 _ _ c h hc hcd hwa (by omega) (by omega)
          · rw [if_neg (by simpa [hbk] using h3)]
            exact nf3d_leaf ev st0 _ _ c h hc hcd hwb (by omega) (by omega)
    · -- OR of two
      have e : stStepG ev.L0 n K mp Dg BIG k c GateOp.or [a, b] st0 =
          stOrChild ev.L0 n K mp k c (stOrChild ev.L0 n K mp k c st0 a) b := rfl
      rw [e]
      have o1 := nf3d_orChild ev n K mp k c st0 a h hcd (hlowmp a (by simp))
      obtain ⟨E1, hE1⟩ := o1.2
      have hcd1 : ev.deg (stOrChild ev.L0 n K mp k c st0 a).E c = 0 := by
        rw [hE1, ev.deg_ext _ _ _ hc]; exact hcd
      exact nf3d_ok_trans ev _ _ _ o1
        (nf3d_orChild ev n K mp k c _ b o1.1 hcd1 (hlowmp b (by simp)))
  · simp at hlen


theorem nf3d_step (ev : Env) (RC : ℕ → Prop) (n s : ℕ) (K : ℕ → Bool) (mp : ℕ → ℕ)
    (Dg : ℕ → ℕ) (gs : List Gate) (Wv : ℕ → Bool) (Out : Prop) (BIG k : ℕ)
    (hdat : ∀ t, RC t → t < s → Dat ev RC n K mp Dg Wv t (gs.getD t ⟨GateOp.and, []⟩).op
      (gs.getD t ⟨GateOp.and, []⟩).inputs)
    (hks : k < s) (st : St) (h : Glob ev RC n s K Wv Out (k + 1) st) (hx : nf3dXI ev st) :
    nf3dXI ev (stStep ev.L0 n K mp Dg gs BIG k st) := by
  cases hctx : st.ctx k with
  | none =>
    have e : stStep ev.L0 n K mp Dg gs BIG k st = st := by simp [stStep, hctx]
    rw [e]; exact hx
  | some c =>
    have e : stStep ev.L0 n K mp Dg gs BIG k st =
        stStepG ev.L0 n K mp Dg BIG k c (gs.getD k ⟨GateOp.and, []⟩).op
          (gs.getD k ⟨GateOp.and, []⟩).inputs { st with cnt := st.cnt + 1 } := by
      simp [stStep, hctx]
    rw [e]
    obtain ⟨hcl, hcd, hRCk⟩ := h.si.ctx k c hctx
    exact (nf3d_stepG ev RC n K mp Dg Wv k c _ _ BIG { st with cnt := st.cnt + 1 }
      (hdat k hRCk hks) hx hcl hcd).1

theorem nf3d_run (ev : Env) (RC : ℕ → Prop) (n s : ℕ) (K : ℕ → Bool) (mp : ℕ → ℕ)
    (Dg : ℕ → ℕ) (gs : List Gate) (Wv : ℕ → Bool) (Out : Prop) (BIG : ℕ)
    (hRCs : ∀ t, RC t → t < s ∧ K t = false)
    (hdat : ∀ t, RC t → t < s → Dat ev RC n K mp Dg Wv t (gs.getD t ⟨GateOp.and, []⟩).op
      (gs.getD t ⟨GateOp.and, []⟩).inputs)
    (hBIG : ev.L0 + 2 * s + 2 ≤ BIG) :
    ∀ k, k ≤ s → ∀ st, Glob ev RC n s K Wv Out k st → nf3dXI ev st →
      nf3dXI ev (stRun ev.L0 n K mp Dg gs BIG k st) := by
  intro k
  induction k with
  | zero => intro _ st _ hx; exact hx
  | succ k ih =>
    intro hk st h hx
    exact ih (by omega) _ (glob_step ev RC n s K mp Dg gs Wv Out BIG k (by omega) hRCs hdat hBIG st h)
      (nf3d_step ev RC n s K mp Dg gs Wv Out BIG k hdat (by omega) st h hx)

theorem nf3d_init (ev : Env) (L0 t0 : ℕ) : nf3dXI ev (initSt L0 t0) := by
  refine ⟨by simp [initSt], ?_⟩
  intro w hw; simp [initSt] at hw

theorem nf3d_stF (F : Fm) (t0 : ℕ) (hRC : F.RC t0) (BIG : ℕ)
    (hBIG : F.n + F.np + 2 * F.s + 2 ≤ BIG) : nf3dXI F.ev (F.stF t0 BIG) :=
  nf3d_run F.ev F.RC F.n F.s F.K F.mp F.Dg F.gs F.Wv (F.Wv (F.n + t0) = true) BIG
    (fun t h => ⟨h.1, h.2.1⟩) (fun t h1 h2 => F.dat t h1 h2) hBIG F.s le_rfl
    (initSt F.ev.L0 t0) (init_glob F.ev F.RC F.n F.s F.K F.Wv t0 hRC hRC.1) (nf3d_init _ _ _)


/-- The assembly of `assemble`, with the two extra conclusions. -/
theorem nf3d_assemble (F0 : Fm) (out : ℕ) (E : List Gate) (prs : List (ℕ × ℕ)) (u r : ℕ)
    (hEm : ∀ g ∈ E, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hprs : ∀ pr ∈ prs, pr.1 < F0.ev.L0 + E.length ∧ pr.2 < F0.ev.L0 + E.length ∧
      F0.ev.deg E pr.1 ≤ 2 ∧ F0.ev.deg E pr.2 ≤ 1)
    (hu : u < F0.ev.L0 + E.length ∨ F0.ev.L0 + E.length + 1 ≤ u)
    (hr : (r < F0.ev.L0 + E.length ∧ F0.ev.deg E r ≤ 2) ∨ F0.ev.L0 + E.length + 1 ≤ r)
    (hsize : F0.np + E.length + 1 ≤ 2 * F0.s + 1)
    (hJ : prs.length ≤ E.length) (hud : F0.ev.deg E u ≤ 3)
    (hsem : ∀ (Z : List Bool) (hZ : Z.length = F0.n),
      (({ F0 with Z := Z, hZ := hZ } : Fm).Wc.getD out false = true ↔
        ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val E u = true ∨
          ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val E r = true) ∧
      (({ F0 with Z := Z, hZ := hZ } : Fm).ev.val E u = true ↔ ∃ pr ∈ prs,
        ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val E pr.1 = true ∧
          ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val E pr.2 = true)) :
    ∃ (D : Circuit) (J : ℕ) (a b : Fin J → ℕ) (u' r' : ℕ), Monotone2 D ∧
      D.size ≤ 2 * F0.s + 1 ∧ J ≤ D.size ∧ HasLineDegree F0.n F0.marked D 3 ∧ D.gates.getLast? = some { op := GateOp.or, inputs := [u', r'] } ∧
      D.output + 1 = F0.n + D.gates.length ∧
      (∀ j : Fin J, (D.lineDegrees F0.n F0.marked).getD (a j) 0 ≤ 2 ∧
        (D.lineDegrees F0.n F0.marked).getD (b j) 0 ≤ 1) ∧
      (D.lineDegrees F0.n F0.marked).getD r' 0 ≤ 2 ∧
      ∀ z : Fin F0.n → Bool, circuitFun F0.n D z = circuitFun F0.n ⟨F0.gs, out⟩ z ∧
        ((D.wires (List.ofFn z)).getD u' false = true ↔ ∃ i : Fin J,
          (D.wires (List.ofFn z)).getD (a i) false = true ∧
            (D.wires (List.ofFn z)).getD (b i) false = true) := by
  set fin : Gate := ⟨GateOp.or, [u, r]⟩ with hfin
  set D : Circuit := ⟨F0.P ++ (E ++ [fin]), F0.n + F0.np + E.length⟩ with hD
  have hL0 : F0.ev.L0 = F0.n + F0.np := rfl
  have hdD : D.lineDegrees F0.n F0.marked = F0.ev.dG (E ++ [fin]) := by
    rw [d3r1_lineDegrees_eq]
    show d3r1Fold 0 d3r1DegOp (F0.P ++ (E ++ [fin])) (nf3Init F0.n F0.marked) =
      d3r1Fold 0 d3r1DegOp (E ++ [fin]) (nf3Deg F0.n F0.marked F0.P)
    rw [nf3F_append]; rfl
  have hdeg : ∀ i, (D.lineDegrees F0.n F0.marked).getD i 0 = F0.ev.deg (E ++ [fin]) i := by
    intro i; rw [hdD]; rfl
  refine ⟨D, prs.length, fun j => (prs.get j).1, fun j => (prs.get j).2, u, r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [hD, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg | rfl
    · obtain ⟨h1, h2⟩ := F0.P_mono g hg
      refine ⟨?_, h2⟩
      rcases h1 with h1 | h1 <;> simp [h1]
    · obtain ⟨h1, h2⟩ := hEm g hg
      refine ⟨?_, h2⟩
      rcases h1 with h1 | h1 <;> simp [h1]
    · simp [hfin]
  · show (F0.P ++ (E ++ [fin])).length ≤ _
    simp [F0.P_length]; omega
  · show prs.length ≤ (F0.P ++ (E ++ [fin])).length
    simp [F0.P_length]; omega
  · show (D.lineDegrees F0.n F0.marked).getD D.output 0 ≤ 3
    have hout : D.output = F0.n + F0.np + E.length := rfl
    rw [hout, hdeg]
    have hrd : F0.ev.deg E r ≤ 2 := by
      rcases hr with ⟨h1, h2⟩ | h1
      · exact h2
      · rw [F0.ev.deg_far _ _ (by omega)]; omega
    have hL0 : F0.n + F0.np + E.length = F0.ev.L0 + E.length := rfl
    rw [hL0, F0.ev.deg_new]
    simp [hfin, d3r1DegOp]
    omega
  · simp [hD, hfin]
  · show F0.n + F0.np + E.length + 1 = F0.n + (F0.P ++ (E ++ [fin])).length
    simp [F0.P_length]; omega
  · intro j
    obtain ⟨a1, a2, a3, a4⟩ := hprs _ (List.get_mem prs j)
    rw [hdeg, hdeg, F0.ev.deg_ext _ _ _ a1, F0.ev.deg_ext _ _ _ a2]
    exact ⟨a3, a4⟩
  · rw [hdeg]
    rcases hr with ⟨h1, h2⟩ | h1
    · rw [F0.ev.deg_ext _ _ _ h1]; exact h2
    · rw [F0.ev.deg_far _ _ (by simp; omega)]; omega
  · intro z
    have hZ : (List.ofFn z).length = F0.n := List.length_ofFn
    obtain ⟨hs1, hs2⟩ := hsem (List.ofFn z) hZ
    set Fz : Fm := { F0 with Z := List.ofFn z, hZ := hZ } with hFz
    have hw : D.wires (List.ofFn z) = Fz.ev.dW (E ++ [fin]) := by
      rw [d3r1_wires_eq]
      show d3r1Fold false GateOp.eval (F0.P ++ (E ++ [fin])) (List.ofFn z) =
        d3r1Fold false GateOp.eval (E ++ [fin]) (d3r1Fold false GateOp.eval F0.P (List.ofFn z))
      rw [nf3F_append]
    have hval : ∀ i, (D.wires (List.ofFn z)).getD i false = Fz.ev.val (E ++ [fin]) i := by
      intro i; rw [hw]; rfl
    have hfv : Fz.ev.val (E ++ [fin]) (Fz.ev.L0 + E.length) =
        (Fz.ev.val E u || Fz.ev.val E r) := by
      rw [Fz.ev.val_new]; simp [hfin, GateOp.eval]
    have hstab : ∀ i, i < Fz.ev.L0 + E.length → Fz.ev.val (E ++ [fin]) i = Fz.ev.val E i :=
      fun i hi => Fz.ev.val_ext _ _ _ hi
    refine ⟨?_, ?_⟩
    · show (D.wires (List.ofFn z)).getD (F0.n + F0.np + E.length) false = _
      have hc : (⟨F0.gs, out⟩ : Circuit).eval (List.ofFn z) = Fz.Wc.getD out false := rfl
      show Circuit.eval D (List.ofFn z) = Circuit.eval ⟨F0.gs, out⟩ (List.ofFn z)
      rw [hc]
      unfold Circuit.eval
      show (D.wires (List.ofFn z)).getD (F0.n + F0.np + E.length) false = _
      rw [hval]
      have : F0.n + F0.np + E.length = Fz.ev.L0 + E.length := rfl
      rw [this, hfv]
      rw [Bool.eq_iff_iff]
      rw [hs1]; simp
    · rw [hval]
      have hu' : Fz.ev.val (E ++ [fin]) u = Fz.ev.val E u := by
        rcases hu with h | h
        · exact hstab u h
        · have hL : Fz.ev.L0 = F0.ev.L0 := rfl
          rw [Fz.ev.val_far E u (by omega), Fz.ev.val_far (E ++ [fin]) u (by simp; omega)]
      rw [hu', hs2]
      constructor
      · rintro ⟨pr, hpr, h1, h2⟩
        obtain ⟨i, hi⟩ := List.mem_iff_get.mp hpr
        refine ⟨i, ?_, ?_⟩
        · show (D.wires (List.ofFn z)).getD (prs.get i).1 false = true
          rw [hval, hstab _ (hprs _ (List.get_mem prs i)).1, hi]; exact h1
        · show (D.wires (List.ofFn z)).getD (prs.get i).2 false = true
          rw [hval, hstab _ (hprs _ (List.get_mem prs i)).2.1, hi]; exact h2
      · rintro ⟨i, h1, h2⟩
        refine ⟨prs.get i, List.get_mem prs i, ?_, ?_⟩
        · have := h1
          simp only [hval] at this
          rw [hstab _ (hprs _ (List.get_mem prs i)).1] at this; exact this
        · have := h2
          simp only [hval] at this
          rw [hstab _ (hprs _ (List.get_mem prs i)).2.1] at this; exact this




theorem nf3d_main : ∀ (Np Nl : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) C 3 → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (J : ℕ) (a b : Fin J → ℕ) (u r : ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ 2 * C.size + 1 ∧ J ≤ D.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) D 3 ∧ D.gates.getLast? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, r] } ∧ D.output + 1 = Np + Nl + D.gates.length ∧ (∀ j : Fin J, (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (a j) 0 ≤ 2 ∧ (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (b j) 0 ≤ 1) ∧ (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (r) 0 ≤ 2 ∧ ∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z ∧ ((D.wires (List.ofFn z)).getD u false = true ↔ ∃ i : Fin J, (D.wires (List.ofFn z)).getD (a i) false = true ∧ (D.wires (List.ofFn z)).getD (b i) false = true) := by
  intro Np Nl C hC hd
  have hmono : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨h1, h2⟩ := hC g hg
    exact ⟨by simpa using h1, h2⟩
  set n := Np + Nl with hn
  set marked := Finset.Ico Np n with hmarked
  let F0 : Fm := ⟨n, marked, C.gates, List.replicate n false, by simp, hmono⟩
  have hs : F0.s = C.size := rfl
  have hdo : F0.Dg C.output ≤ 3 := hd
  by_cases hlow : F0.Dg C.output ≤ 2
  · -- the output has line-degree at most 2: no product
    set o := C.output with ho
    have hr : (if o < n + F0.s then F0.mp o else F0.ev.L0 + 1) < F0.ev.L0 + ([] : List Gate).length ∧
        F0.ev.deg [] (if o < n + F0.s then F0.mp o else F0.ev.L0 + 1) ≤ 2 ∨
        F0.ev.L0 + ([] : List Gate).length + 1 ≤ (if o < n + F0.s then F0.mp o else F0.ev.L0 + 1) := by
      by_cases hok : o < n + F0.s
      · simp only [hok, if_true]
        left
        have hu : o < n ∨ F0.K (o - n) = true := by
          by_cases hon : o < n
          · exact Or.inl hon
          · right
            simp only [Fm.K, decide_eq_true_eq]
            refine ⟨by omega, ?_⟩
            rw [show n + (o - n) = o by omega]; exact hlow
        refine ⟨by simp only [List.length_nil, Nat.add_zero]; exact F0.mp_lt o hu, ?_⟩
        rw [F0.ev.deg_base _ _ (F0.mp_lt o hu)]
        rw [F0.deg_kept o hu]; exact hlow
      · simp only [hok, if_false]; right; simp
    have hsem : ∀ (Z : List Bool) (hZ : Z.length = F0.n),
        (({ F0 with Z := Z, hZ := hZ } : Fm).Wc.getD o false = true ↔
          ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val [] (F0.ev.L0 + 1) = true ∨
            ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val []
              (if o < n + F0.s then F0.mp o else F0.ev.L0 + 1) = true) ∧
        (({ F0 with Z := Z, hZ := hZ } : Fm).ev.val [] (F0.ev.L0 + 1) = true ↔ ∃ pr ∈
          ([] : List (ℕ × ℕ)),
          ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val [] pr.1 = true ∧
            ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val [] pr.2 = true) := by
      intro Z hZ
      have hL : ({ F0 with Z := Z, hZ := hZ } : Fm).ev.L0 = F0.ev.L0 := rfl
      have h1 : ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val [] (F0.ev.L0 + 1) = false :=
        ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val_far [] _ (by simp [hL])
      refine ⟨?_, ?_⟩
      · rw [h1]
        by_cases hok : o < n + F0.s
        · simp only [hok, if_true]
          have hu : o < n ∨ F0.K (o - n) = true := by
            by_cases hon : o < n
            · exact Or.inl hon
            · right
              simp only [Fm.K, decide_eq_true_eq]
              refine ⟨by omega, ?_⟩
              rw [show n + (o - n) = o by omega]; exact hlow
          have h2 := ({ F0 with Z := Z, hZ := hZ } : Fm).val_kept o hu
          have h3 : ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val [] (F0.mp o) =
              ({ F0 with Z := Z, hZ := hZ } : Fm).ev.B0.getD (F0.mp o) false :=
            ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val_base [] _ (F0.mp_lt o hu)
          rw [h3]
          have h4 : ({ F0 with Z := Z, hZ := hZ } : Fm).ev.B0.getD (F0.mp o) false =
              ({ F0 with Z := Z, hZ := hZ } : Fm).Wv o := h2
          rw [h4]
          simp [Fm.Wv]
        · simp only [hok, if_false]
          rw [h1]
          have hlen : ({ F0 with Z := Z, hZ := hZ } : Fm).Wc.length = n + F0.s := by
            simp only [Fm.Wc, d3r1Fold_length, hZ]; rfl
          have : ({ F0 with Z := Z, hZ := hZ } : Fm).Wc.getD o false = false :=
            List.getD_eq_default _ _ (by rw [hlen]; omega)
          rw [this]; simp
      · rw [h1]; simp
    obtain ⟨D, J, a, b, u', r', hD⟩ := nf3d_assemble F0 o [] [] (F0.ev.L0 + 1)
      (if o < n + F0.s then F0.mp o else F0.ev.L0 + 1)
      (by simp) (by simp) (Or.inr (by simp)) hr
      (by have := F0.np_le; simp only [List.length_nil]; omega) (by simp)
      (by rw [F0.ev.deg_far _ _ (by simp)]; omega) hsem
    exact ⟨D, J, a, b, u', r', hD⟩
  · -- the output has line-degree 3
    set o := C.output with ho
    have h3 : F0.Dg o = 3 := by omega
    have hon : n ≤ o := by
      by_contra hh
      have := F0.Dg_input o (by show o < n; omega)
      omega
    have hok : o < n + F0.s := by
      by_contra hh
      have : F0.Dg o = 0 := by
        unfold Fm.Dg
        apply List.getD_eq_default
        rw [nf3Deg_length]
        show n + C.gates.length ≤ o
        have : F0.s = C.gates.length := rfl
        omega
      omega
    obtain ⟨t0, hot⟩ : ∃ t0, o = n + t0 := ⟨o - n, by omega⟩
    have hRC : F0.RC t0 := by
      refine ⟨by show t0 < C.gates.length; have : F0.s = C.gates.length := rfl; omega, ?_, ?_⟩
      · simp only [Fm.K]
        have : F0.Dg (F0.n + t0) = 3 := by rw [show F0.n + t0 = o from hot.symm]; exact h3
        simp [this]
      · show F0.Dg (n + t0) = 3
        rw [← hot]; exact h3
    have hBIGle : F0.n + F0.np + 2 * F0.s + 2 ≤ F0.n + F0.np + 2 * F0.s + 2 := le_rfl
    obtain ⟨hsi, hout0, ⟨u, hu⟩, hE, hnp1, hnple⟩ := F0.run_high t0 hRC _ hBIGle
    have hu' : u < F0.ev.L0 + (F0.stF t0 (F0.n + F0.np + 2 * F0.s + 2)).E.length :=
      hsi.acc u hu
    have hsem : ∀ (Z : List Bool) (hZ : Z.length = F0.n),
        (({ F0 with Z := Z, hZ := hZ } : Fm).Wc.getD o false = true ↔
          ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val (F0.stF t0 (F0.n + F0.np + 2 * F0.s + 2)).E u = true ∨
            ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val (F0.stF t0 (F0.n + F0.np + 2 * F0.s + 2)).E
              (F0.n + F0.np + 2 * F0.s + 2) = true) ∧
        (({ F0 with Z := Z, hZ := hZ } : Fm).ev.val (F0.stF t0 (F0.n + F0.np + 2 * F0.s + 2)).E u = true ↔
          ∃ pr ∈ (F0.stF t0 (F0.n + F0.np + 2 * F0.s + 2)).prs,
            ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val (F0.stF t0 (F0.n + F0.np + 2 * F0.s + 2)).E pr.1 = true ∧
              ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val (F0.stF t0 (F0.n + F0.np + 2 * F0.s + 2)).E pr.2 = true) := by
      intro Z hZ
      have hz := ({ F0 with Z := Z, hZ := hZ } : Fm).run_high t0 hRC _ hBIGle
      obtain ⟨hsiz, houtz, _, _, _, _⟩ := hz
      have hacc : ({ F0 with Z := Z, hZ := hZ } : Fm).ev.accV
          (F0.stF t0 (F0.n + F0.np + 2 * F0.s + 2)) ↔
          ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val
            (F0.stF t0 (F0.n + F0.np + 2 * F0.s + 2)).E u = true := by
        constructor
        · rintro ⟨w, hw, hv⟩
          rw [hu] at hw; simp at hw; subst hw; exact hv
        · intro hv; exact ⟨u, hu, hv⟩
      have hfar : ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val
          (F0.stF t0 (F0.n + F0.np + 2 * F0.s + 2)).E (F0.n + F0.np + 2 * F0.s + 2) = false := by
        apply Env.val_far
        show F0.n + F0.np + (F0.stF t0 (F0.n + F0.np + 2 * F0.s + 2)).E.length ≤ _
        omega
      refine ⟨?_, ?_⟩
      · rw [hfar]
        have : ({ F0 with Z := Z, hZ := hZ } : Fm).Wc.getD o false =
            ({ F0 with Z := Z, hZ := hZ } : Fm).Wv (({ F0 with Z := Z, hZ := hZ } : Fm).n + t0) := by
          rw [show ({ F0 with Z := Z, hZ := hZ } : Fm).n + t0 = o from hot.symm]; rfl
        have houtz' : ({ F0 with Z := Z, hZ := hZ } : Fm).Wv
            (({ F0 with Z := Z, hZ := hZ } : Fm).n + t0) = true ↔
            ({ F0 with Z := Z, hZ := hZ } : Fm).ev.accV
              (F0.stF t0 (F0.n + F0.np + 2 * F0.s + 2)) := houtz
        rw [this, houtz', hacc]; simp
      · rw [← hacc]; exact hsiz.pv
    have hxi := nf3d_stF F0 t0 hRC _ hBIGle
    obtain ⟨D, J, a, b, u', r', hD⟩ := nf3d_assemble F0 o (F0.stF t0 (F0.n + F0.np + 2 * F0.s + 2)).E
      (F0.stF t0 (F0.n + F0.np + 2 * F0.s + 2)).prs u (F0.n + F0.np + 2 * F0.s + 2)
      hsi.mono hsi.prs (Or.inl hu') (Or.inr (by have hL : F0.ev.L0 = F0.n + F0.np := rfl; omega))
      (by omega) hxi.1 (hxi.2 u hu).2 hsem
    exact ⟨D, J, a, b, u', r', hD⟩


end PEqualNP.MetaComplexity.Helpers.NormalForm3
