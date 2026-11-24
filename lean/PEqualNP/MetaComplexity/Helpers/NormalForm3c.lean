import PEqualNP.MetaComplexity.Helpers.NormalForm3b

/-!
# Normal form at line-degree 3 (row L-meta-964): the start and the end of the loop

Conjecture until the checker accepts it.
-/

namespace PEqualNP.MetaComplexity.Helpers.NormalForm3
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Deg3

/-- The start: the constant `true` gate is the context of the output gate `t0`. -/
def initSt (L0 t0 : ℕ) : St :=
  { E := [⟨GateOp.and, []⟩], ctx := Function.update (fun _ => none) t0 (some L0), acc := none,
    prs := [], cnt := 0 }

theorem fcount_none (k : ℕ) : fcount (fun _ => none) k = 0 := by
  simp [fcount]

theorem init_glob (ev : Env) (RC : ℕ → Prop) (n s : ℕ) (K : ℕ → Bool) (Wv : ℕ → Bool) (t0 : ℕ)
    (hRC : RC t0) (ht0 : t0 < s) :
    Glob ev RC n s K Wv (Wv (n + t0) = true) s (initSt ev.L0 t0) := by
  have hdeg : ev.deg [(⟨GateOp.and, []⟩ : Gate)] ev.L0 = 0 := by
    have := ev.deg_new [] ⟨GateOp.and, []⟩
    simpa [d3r1DegOp] using this
  have hval : ev.val [(⟨GateOp.and, []⟩ : Gate)] ev.L0 = true := by
    have := ev.val_new [] ⟨GateOp.and, []⟩
    simpa [GateOp.eval] using this
  have hfc : fcount (initSt ev.L0 t0).ctx s = 1 := by
    show fcount (Function.update (fun _ => none) t0 (some ev.L0)) s = 1
    rw [fcount_update _ _ _ _ ht0, fcount_none]; simp
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro t w ht
    by_cases htt : t = t0
    · subst htt
      simp [initSt] at ht; subst ht
      exact ⟨by simp [initSt], hdeg, hRC⟩
    · simp [initSt, Function.update, htt] at ht
  · intro w hw; simp [initSt] at hw
  · intro pr hpr; simp [initSt] at hpr
  · intro g hg
    simp [initSt] at hg; subst hg; simp
  · simp [initSt]
  · constructor
    · rintro ⟨w, hw, _⟩; simp [initSt] at hw
    · rintro ⟨pr, hpr, _⟩; simp [initSt] at hpr
  · simp only [Env.cover]
    constructor
    · intro hW
      right
      refine ⟨t0, ht0, hW, ev.L0, by simp [initSt], hval⟩
    · rintro (⟨w, hw, _⟩ | ⟨t, _, hWt, w, hw, hv⟩)
      · simp [initSt] at hw
      · by_cases htt : t = t0
        · subst htt; exact hWt
        · simp [initSt, Function.update, htt] at hw
  · rw [hfc]; simp [initSt, St.flag]
  · rw [hfc]; omega
  · simp [initSt]


/-- The state after the whole loop. It does not depend on the point `Z`. -/
def Fm.stF (F : Fm) (t0 BIG : ℕ) : St :=
  stRun F.ev.L0 F.n F.K F.mp F.Dg F.gs BIG F.s (initSt F.ev.L0 t0)

theorem Fm.run_high (F : Fm) (t0 : ℕ) (hRC : F.RC t0) (BIG : ℕ)
    (hBIG : F.n + F.np + 2 * F.s + 2 ≤ BIG) :
    SI F.ev F.RC (F.stF t0 BIG) ∧ (F.Wv (F.n + t0) = true ↔ F.ev.accV (F.stF t0 BIG)) ∧
      (∃ u, (F.stF t0 BIG).acc = some u) ∧ (F.stF t0 BIG).E.length ≤ 2 * (F.s - F.np) + 1 ∧
      1 ≤ F.np ∧ F.np ≤ F.s := by
  have hg := glob_run F.ev F.RC F.n F.s F.K F.mp F.Dg F.gs F.Wv (F.Wv (F.n + t0) = true) BIG
    (fun t h => ⟨h.1, h.2.1⟩) (fun t h1 h2 => F.dat t h1 h2) hBIG F.s le_rfl
    (initSt F.ev.L0 t0) (init_glob F.ev F.RC F.n F.s F.K F.Wv t0 hRC hRC.1)
  have hnp := F.np_add_hcnt
  obtain ⟨g1, g2, g3, g4, g5⟩ := hg
  have hst : F.stF t0 BIG = stRun F.ev.L0 F.n F.K F.mp F.Dg F.gs BIG F.s (initSt F.ev.L0 t0) := rfl
  rw [← hst] at g1 g2 g3 g4 g5
  have hf0 : fcount (F.stF t0 BIG).ctx 0 = 0 := by simp [fcount]
  rw [hf0] at g3 g4
  have hflag : (F.stF t0 BIG).flag = 1 := by
    have := St.flag_le (F.stF t0 BIG)
    omega
  have hacc : ∃ u, (F.stF t0 BIG).acc = some u := by
    cases hh : (F.stF t0 BIG).acc with
    | none => simp [St.flag, hh] at hflag
    | some u => exact ⟨u, rfl⟩
  have h0 : 0 < F.s := by have := hRC.1; omega
  refine ⟨g1, ?_, hacc, by omega, F.np_pos h0, F.np_le⟩
  rw [g2]
  simp only [Env.cover]
  constructor
  · rintro (h | ⟨t, ht, _⟩)
    · exact h
    · omega
  · intro h; exact Or.inl h

theorem Fm.P_mono (F : Fm) : ∀ g ∈ F.P, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [Fm.P, d3r1Pruned, List.mem_map, List.mem_filter, List.mem_range] at hg
  obtain ⟨t, ⟨ht, _⟩, rfl⟩ := hg
  simp only [d3r1PGate, List.length_map]
  rw [List.getD_eq_getElem _ _ ht]
  exact F.hmono _ (List.getElem_mem ht)

/-- The assembly: the kept gates, then the extra gates, then the final OR. -/
theorem assemble (F0 : Fm) (out : ℕ) (E : List Gate) (prs : List (ℕ × ℕ)) (u r : ℕ)
    (hEm : ∀ g ∈ E, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hprs : ∀ pr ∈ prs, pr.1 < F0.ev.L0 + E.length ∧ pr.2 < F0.ev.L0 + E.length ∧
      F0.ev.deg E pr.1 ≤ 2 ∧ F0.ev.deg E pr.2 ≤ 1)
    (hu : u < F0.ev.L0 + E.length ∨ F0.ev.L0 + E.length + 1 ≤ u)
    (hr : (r < F0.ev.L0 + E.length ∧ F0.ev.deg E r ≤ 2) ∨ F0.ev.L0 + E.length + 1 ≤ r)
    (hsize : F0.np + E.length + 1 ≤ 2 * F0.s + 1)
    (hsem : ∀ (Z : List Bool) (hZ : Z.length = F0.n),
      (({ F0 with Z := Z, hZ := hZ } : Fm).Wc.getD out false = true ↔
        ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val E u = true ∨
          ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val E r = true) ∧
      (({ F0 with Z := Z, hZ := hZ } : Fm).ev.val E u = true ↔ ∃ pr ∈ prs,
        ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val E pr.1 = true ∧
          ({ F0 with Z := Z, hZ := hZ } : Fm).ev.val E pr.2 = true)) :
    ∃ (D : Circuit) (J : ℕ) (a b : Fin J → ℕ) (u' r' : ℕ), Monotone2 D ∧
      D.size ≤ 2 * F0.s + 1 ∧ D.gates.getLast? = some { op := GateOp.or, inputs := [u', r'] } ∧
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
  refine ⟨D, prs.length, fun j => (prs.get j).1, fun j => (prs.get j).2, u, r, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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


theorem nf3_main : ∀ (Np Nl : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) C 3 → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (J : ℕ) (a b : Fin J → ℕ) (u r : ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ 2 * C.size + 1 ∧ D.gates.getLast? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, r] } ∧ D.output + 1 = Np + Nl + D.gates.length ∧ (∀ j : Fin J, (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (a j) 0 ≤ 2 ∧ (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (b j) 0 ≤ 1) ∧ (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (r) 0 ≤ 2 ∧ ∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z ∧ ((D.wires (List.ofFn z)).getD u false = true ↔ ∃ i : Fin J, (D.wires (List.ofFn z)).getD (a i) false = true ∧ (D.wires (List.ofFn z)).getD (b i) false = true) := by
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
    obtain ⟨D, J, a, b, u', r', hD⟩ := assemble F0 o [] [] (F0.ev.L0 + 1)
      (if o < n + F0.s then F0.mp o else F0.ev.L0 + 1)
      (by simp) (by simp) (Or.inr (by simp)) hr
      (by have := F0.np_le; simp only [List.length_nil]; omega) hsem
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
    obtain ⟨D, J, a, b, u', r', hD⟩ := assemble F0 o (F0.stF t0 (F0.n + F0.np + 2 * F0.s + 2)).E
      (F0.stF t0 (F0.n + F0.np + 2 * F0.s + 2)).prs u (F0.n + F0.np + 2 * F0.s + 2)
      hsi.mono hsi.prs (Or.inl hu') (Or.inr (by have hL : F0.ev.L0 = F0.n + F0.np := rfl; omega))
      (by omega) hsem
    exact ⟨D, J, a, b, u', r', hD⟩

end PEqualNP.MetaComplexity.Helpers.NormalForm3
