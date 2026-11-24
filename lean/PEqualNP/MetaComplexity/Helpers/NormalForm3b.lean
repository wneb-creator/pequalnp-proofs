import PEqualNP.MetaComplexity.Helpers.NormalForm3

/-!
# Normal form at line-degree 3 (row L-meta-964): the loop

Conjecture until the checker accepts it. The step on one gate lifted to a global invariant and the
loop over the gates from the last to the first.
-/

namespace PEqualNP.MetaComplexity.Helpers.NormalForm3
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Deg3

/-- The number of gates of index at least `k` and below `s` that are not kept. -/
def hcnt (K : ℕ → Bool) (s k : ℕ) : ℕ :=
  ((List.range' k (s - k)).filter fun t => K t = false).length

theorem hcnt_succ (K : ℕ → Bool) (s k : ℕ) (hk : k < s) :
    hcnt K s k = hcnt K s (k + 1) + if K k = false then 1 else 0 := by
  unfold hcnt
  obtain ⟨m, hm⟩ : ∃ m, s - k = m + 1 := ⟨s - k - 1, by omega⟩
  rw [hm, List.range'_succ, show s - (k + 1) = m by omega]
  by_cases h : K k = false <;> simp [h, List.filter_cons]

theorem hcnt_le (K : ℕ → Bool) (s k : ℕ) : hcnt K s k ≤ s := by
  unfold hcnt
  calc _ ≤ (List.range' k (s - k)).length := List.length_filter_le _ _
    _ = s - k := by simp
    _ ≤ s := Nat.sub_le _ _

theorem SI.withCnt {ev : Env} {RC : ℕ → Prop} {st : St} (h : SI ev RC st) (m : ℕ) :
    SI ev RC { st with cnt := m } :=
  ⟨h.ctx, h.acc, h.prs, h.mono, h.accprs, h.pv⟩

/-- One step of the loop at gate `k`. -/
def stStep (L0 n : ℕ) (K : ℕ → Bool) (mp : ℕ → ℕ) (Dg : ℕ → ℕ) (gs : List Gate) (BIG k : ℕ)
    (st : St) : St :=
  match st.ctx k with
  | none => st
  | some c =>
    stStepG L0 n K mp Dg BIG k c (gs.getD k ⟨GateOp.and, []⟩).op
      (gs.getD k ⟨GateOp.and, []⟩).inputs { st with cnt := st.cnt + 1 }

/-- The loop over the gates `k - 1, ..., 0`. -/
def stRun (L0 n : ℕ) (K : ℕ → Bool) (mp : ℕ → ℕ) (Dg : ℕ → ℕ) (gs : List Gate) (BIG : ℕ) :
    ℕ → St → St
  | 0, st => st
  | k + 1, st => stRun L0 n K mp Dg gs BIG k (stStep L0 n K mp Dg gs BIG k st)

theorem stepG_post (ev : Env) (RC : ℕ → Prop) (n : ℕ) (K : ℕ → Bool) (mp : ℕ → ℕ) (Dg : ℕ → ℕ)
    (Wv : ℕ → Bool) (k c : ℕ) (op : GateOp) (ins : List ℕ) (BIG : ℕ) (st0 : St)
    (d : Dat ev RC n K mp Dg Wv k op ins) (h : SI ev RC st0)
    (hc : c < ev.L0 + st0.E.length) (hcd : ev.deg st0.E c = 0)
    (hBIG : ev.L0 + st0.E.length ≤ BIG) :
    Post ev RC n Wv k c st0 (stStepG ev.L0 n K mp Dg BIG k c op ins st0) := by
  obtain ⟨hop, hlen⟩ := d.mono
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨x, rest⟩⟩⟩
  · exfalso
    have h3 := d.deg3
    rw [d.deg] at h3
    simp [d3r1DegOp] at h3
  · exact stepG_one ev RC n K mp Dg Wv k c op a BIG st0 d h hc hcd
  · rcases hop with rfl | rfl
    · exact stepG_and2 ev RC n K mp Dg Wv k c a b BIG st0 d h hc hcd hBIG
    · exact stepG_or2 ev RC n K mp Dg Wv k c a b BIG st0 d h hc hcd
  · simp at hlen

/-- The invariant of the loop, before the gates below `k` are processed. -/
structure Glob (ev : Env) (RC : ℕ → Prop) (n s : ℕ) (K : ℕ → Bool) (Wv : ℕ → Bool) (Out : Prop)
    (k : ℕ) (st : St) : Prop where
  si : SI ev RC st
  out : Out ↔ ev.cover n Wv k st
  q : st.E.length + fcount st.ctx k + st.flag ≤ 2 * st.cnt + 2
  v6 : 1 ≤ fcount st.ctx k + st.flag
  hc : st.cnt ≤ hcnt K s k

theorem glob_step (ev : Env) (RC : ℕ → Prop) (n s : ℕ) (K : ℕ → Bool) (mp : ℕ → ℕ)
    (Dg : ℕ → ℕ) (gs : List Gate) (Wv : ℕ → Bool) (Out : Prop) (BIG k : ℕ) (hks : k < s)
    (hRCs : ∀ t, RC t → t < s ∧ K t = false)
    (hdat : ∀ t, RC t → t < s → Dat ev RC n K mp Dg Wv t (gs.getD t ⟨GateOp.and, []⟩).op
      (gs.getD t ⟨GateOp.and, []⟩).inputs)
    (hBIG : ev.L0 + 2 * s + 2 ≤ BIG) (st : St)
    (h : Glob ev RC n s K Wv Out (k + 1) st) :
    Glob ev RC n s K Wv Out k (stStep ev.L0 n K mp Dg gs BIG k st) := by
  have hhc := hcnt_succ K s k hks
  have hfc := fcount_succ st.ctx k
  cases hctx : st.ctx k with
  | none =>
    have e : stStep ev.L0 n K mp Dg gs BIG k st = st := by simp [stStep, hctx]
    rw [e]
    have hnone : (st.ctx k).isSome = false := by simp [hctx]
    rw [hnone] at hfc
    simp only [Bool.false_eq_true, if_false, add_zero] at hfc
    have hcn := h.hc
    refine ⟨h.si, ?_, by rw [← hfc]; exact h.q, by rw [← hfc]; exact h.v6, by omega⟩
    rw [h.out]
    simp only [Env.cover]
    constructor
    · rintro (hv | ⟨t, htk, hWt, hct⟩)
      · exact Or.inl hv
      · refine Or.inr ⟨t, ?_, hWt, hct⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp htk with h1 | h1
        · exact h1
        · subst h1
          obtain ⟨w, hw, _⟩ := hct
          rw [hctx] at hw; simp at hw
    · rintro (hv | ⟨t, htk, hWt, hct⟩)
      · exact Or.inl hv
      · exact Or.inr ⟨t, by omega, hWt, hct⟩
  | some c =>
    have e : stStep ev.L0 n K mp Dg gs BIG k st =
        stStepG ev.L0 n K mp Dg BIG k c (gs.getD k ⟨GateOp.and, []⟩).op
          (gs.getD k ⟨GateOp.and, []⟩).inputs { st with cnt := st.cnt + 1 } := by
      simp [stStep, hctx]
    rw [e]
    have hsome : (st.ctx k).isSome = true := by simp [hctx]
    rw [hsome] at hfc
    simp only [if_true] at hfc
    obtain ⟨hcl, hcd, hRCk⟩ := h.si.ctx k c hctx
    have hq := h.q
    have hcnt := h.hc
    have hE : st.E.length ≤ 2 * s + 2 := by
      have := hcnt_le K s (k + 1)
      omega
    have hpost := stepG_post ev RC n K mp Dg Wv k c _ _ BIG { st with cnt := st.cnt + 1 }
      (hdat k hRCk hks) (h.si.withCnt _) hcl hcd (by simp; omega)
    obtain ⟨p1, p2, p3, p4, p5⟩ := hpost
    refine ⟨p1, ?_, ?_, p5, ?_⟩
    · rw [h.out]
      simp only [Env.cover] at p3 ⊢
      rw [p3]
      constructor
      · rintro (hv | ⟨t, htk, hWt, hct⟩)
        · exact Or.inl (Or.inl hv)
        · rcases Nat.lt_succ_iff_lt_or_eq.mp htk with h1 | h1
          · exact Or.inl (Or.inr ⟨t, h1, hWt, hct⟩)
          · subst h1
            obtain ⟨w, hw, hv⟩ := hct
            rw [hctx] at hw; simp at hw; subst hw
            exact Or.inr ⟨hWt, hv⟩
      · rintro ((hv | ⟨t, htk, hWt, hct⟩) | ⟨hW, hv⟩)
        · exact Or.inl hv
        · exact Or.inr ⟨t, by omega, hWt, hct⟩
        · exact Or.inr ⟨k, by omega, hW, c, hctx, hv⟩
    · rw [p2]
      show _ ≤ 2 * (st.cnt + 1) + 2
      simp only [St.flag] at *
      omega
    · rw [p2]
      show st.cnt + 1 ≤ _
      have hKk := (hRCs k hRCk).2
      simp [hKk] at hhc
      omega


theorem glob_run (ev : Env) (RC : ℕ → Prop) (n s : ℕ) (K : ℕ → Bool) (mp : ℕ → ℕ)
    (Dg : ℕ → ℕ) (gs : List Gate) (Wv : ℕ → Bool) (Out : Prop) (BIG : ℕ)
    (hRCs : ∀ t, RC t → t < s ∧ K t = false)
    (hdat : ∀ t, RC t → t < s → Dat ev RC n K mp Dg Wv t (gs.getD t ⟨GateOp.and, []⟩).op
      (gs.getD t ⟨GateOp.and, []⟩).inputs)
    (hBIG : ev.L0 + 2 * s + 2 ≤ BIG) :
    ∀ k, k ≤ s → ∀ st, Glob ev RC n s K Wv Out k st →
      Glob ev RC n s K Wv Out 0 (stRun ev.L0 n K mp Dg gs BIG k st) := by
  intro k
  induction k with
  | zero => intro _ st h; exact h
  | succ k ih =>
    intro hk st h
    exact ih (by omega) _ (glob_step ev RC n s K mp Dg gs Wv Out BIG k (by omega) hRCs hdat hBIG st h)

/-! ## The frame of a circuit -/

/-- A circuit with its inputs: gates of AND/OR type with at most two inputs, and a point `Z`. -/
structure Fm where
  n : ℕ
  marked : Finset ℕ
  gs : List Gate
  Z : List Bool
  hZ : Z.length = n
  hmono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

namespace Fm
variable (F : Fm)

def s : ℕ := F.gs.length
def Dg (a : ℕ) : ℕ := (nf3Deg F.n F.marked F.gs).getD a 0
def K (t : ℕ) : Bool := decide (t < F.s ∧ F.Dg (F.n + t) ≤ 2)
def np : ℕ := d3r1Top F.K F.gs
def P : List Gate := d3r1Pruned F.n F.K F.gs
def mp : ℕ → ℕ := d3r1New F.n F.K F.np
def Wc : List Bool := d3r1Fold false GateOp.eval F.gs F.Z
def Wv (a : ℕ) : Bool := F.Wc.getD a false
def RC (t : ℕ) : Prop := t < F.s ∧ F.K t = false ∧ F.Dg (F.n + t) = 3

theorem K_true {t : ℕ} (h : F.K t = true) : t < F.s ∧ F.Dg (F.n + t) ≤ 2 := by
  simpa [K] using h

theorem K_false {t : ℕ} (h : F.K t = false) : ¬(t < F.s ∧ F.Dg (F.n + t) ≤ 2) := by
  simpa [K] using h

theorem P_length : F.P.length = F.np := by
  simp [P, np, d3r1_pruned_length]

theorem hκ : ∀ t, F.K t = true → t < F.gs.length := fun t h => (F.K_true h).1

theorem hcl : ∀ (t : ℕ) (ht : t < F.gs.length), F.K t = true → ∀ a ∈ F.gs[t].inputs,
    F.n ≤ a → a < F.n + t → F.K (a - F.n) = true := by
  intro t ht hk a ha han hat
  have h1 := F.K_true hk
  have h2 := nf3Deg_mono F.n F.marked F.gs t ht a ha hat
  have h3 : F.Dg a ≤ 2 := by
    have : F.Dg (F.n + t) ≤ 2 := h1.2
    unfold Dg at *; omega
  simp only [K, decide_eq_true_eq]
  refine ⟨by unfold s; omega, ?_⟩
  rw [show F.n + (a - F.n) = a by omega]; exact h3

/-- The base environment: the kept gates. -/
def ev : Env :=
  { L0 := F.n + F.np
    G0 := nf3Deg F.n F.marked F.P
    B0 := d3r1Fold false GateOp.eval F.P F.Z
    hG := by simp [nf3Deg_length, F.P_length]
    hB := by simp [d3r1Fold_length, F.hZ, F.P_length] }

theorem ev_L0 : F.ev.L0 = F.n + F.np := rfl

theorem val_kept (u : ℕ) (hu : u < F.n ∨ F.K (u - F.n) = true) :
    F.ev.B0.getD (F.mp u) false = F.Wv u := by
  have := d3r1_prune_val false GateOp.eval F.Z F.n F.hZ F.gs F.K F.hκ F.hcl u hu
  exact this

theorem deg_kept (u : ℕ) (hu : u < F.n ∨ F.K (u - F.n) = true) :
    F.ev.G0.getD (F.mp u) 0 = F.Dg u := by
  have := d3r1_prune_val 0 d3r1DegOp (nf3Init F.n F.marked) F.n (nf3Init_length _ _) F.gs F.K
    F.hκ F.hcl u hu
  exact this

theorem mp_lt (u : ℕ) (hu : u < F.n ∨ F.K (u - F.n) = true) : F.mp u < F.n + F.np := by
  rcases hu with hu | hu
  · simp only [mp, d3r1New, hu, if_true]; omega
  · by_cases hun : u < F.n
    · simp only [mp, d3r1New, hun, if_true]; omega
    · simp only [mp, d3r1New, hun, if_false, hu, if_true]
      have h1 := (F.K_true hu).1
      have := d3r1_rank_lt F.K (u - F.n) F.gs.length h1 hu
      have h2 : F.np = d3r1Rank F.K F.gs.length := rfl
      omega


theorem Dg_input (a : ℕ) (ha : a < F.n) : F.Dg a ≤ 1 := nf3Deg_input F.n F.marked F.gs a ha

theorem Dg_mono (t : ℕ) (ht : t < F.gs.length) (a : ℕ) (ha : a ∈ F.gs[t].inputs)
    (hat : a < F.n + t) : F.Dg a ≤ F.Dg (F.n + t) := nf3Deg_mono F.n F.marked F.gs t ht a ha hat

theorem dat (t : ℕ) (hRC : F.RC t) (ht : t < F.s) :
    Dat F.ev F.RC F.n F.K F.mp F.Dg F.Wv t (F.gs.getD t ⟨GateOp.and, []⟩).op
      (F.gs.getD t ⟨GateOp.and, []⟩).inputs := by
  have hgt : F.gs.getD t ⟨GateOp.and, []⟩ = F.gs[t] := List.getD_eq_getElem _ _ ht
  rw [hgt]
  have hmem : F.gs[t] ∈ F.gs := List.getElem_mem ht
  refine ⟨F.hmono _ hmem, ?_, ?_, hRC.2.2, ?_, ?_, ?_⟩
  · have := d3r1Fold_gate false GateOp.eval F.gs F.Z t ht
    rw [F.hZ] at this
    exact this
  · exact nf3Deg_gate F.n F.marked F.gs t ht
  · intro a ha hak han hK
    have h1 := F.Dg_mono t ht a ha hak
    have h2 := F.K_false hK
    have h3 : F.Dg (F.n + t) = 3 := hRC.2.2
    have h4 : ¬(a - F.n < F.s ∧ F.Dg a ≤ 2) := by
      have := h2; rw [show F.n + (a - F.n) = a by omega] at this; exact this
    have h5 : a - F.n < F.s := by unfold s at *; omega
    refine ⟨by omega, ?_, ?_, ?_⟩
    · exact h5
    · exact hK
    · rw [show F.n + (a - F.n) = a by omega]; omega
  · intro a ha hak hnh
    by_cases han : a < F.n
    · have hK : ¬(F.n ≤ a ∧ F.K (a - F.n) = false) := hnh
      have h1 := F.Dg_input a han
      have hu : a < F.n ∨ F.K (a - F.n) = true := Or.inl han
      exact ⟨by omega, F.mp_lt a hu, F.deg_kept a hu, F.val_kept a hu⟩
    · have hn : F.n ≤ a := by omega
      have hKt : F.K (a - F.n) = true := by
        by_contra hh
        exact hnh ⟨hn, by simpa using hh⟩
      have hu : a < F.n ∨ F.K (a - F.n) = true := Or.inr hKt
      have h1 := (F.K_true hKt).2
      rw [show F.n + (a - F.n) = a by omega] at h1
      exact ⟨h1, F.mp_lt a hu, F.deg_kept a hu, F.val_kept a hu⟩
  · intro a ha hak h3
    by_cases han : a < F.n
    · have := F.Dg_input a han; omega
    · have hn : F.n ≤ a := by omega
      refine ⟨hn, ?_⟩
      by_contra hh
      have hKt : F.K (a - F.n) = true := by simpa using hh
      have h1 := (F.K_true hKt).2
      rw [show F.n + (a - F.n) = a by omega] at h1
      omega


theorem filter_split (K : ℕ → Bool) (l : List ℕ) :
    (l.filter K).length + (l.filter fun t => K t = false).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : K a = true
    · simp [List.filter_cons, h] at ih ⊢; omega
    · have h' : K a = false := by simpa using h
      simp [List.filter_cons, h'] at ih ⊢; omega

theorem np_add_hcnt : F.np + hcnt F.K F.s 0 = F.s := by
  have := filter_split F.K (List.range F.gs.length)
  have h2 : hcnt F.K F.s 0 = ((List.range F.gs.length).filter fun t => F.K t = false).length := by
    unfold hcnt s
    rw [Nat.sub_zero, List.range_eq_range']
  rw [h2]
  simp only [List.length_range] at this
  unfold np d3r1Top s
  exact this

theorem np_le : F.np ≤ F.s := by have := F.np_add_hcnt; omega

theorem K_zero (h0 : 0 < F.s) : F.K 0 = true := by
  have ht : 0 < F.gs.length := h0
  have hmem : F.gs[0] ∈ F.gs := List.getElem_mem ht
  obtain ⟨_, hlen⟩ := F.hmono _ hmem
  have hd := nf3Deg_gate F.n F.marked F.gs 0 ht
  have hin : ∀ a ∈ F.gs[0].inputs, (if a < F.n + 0 then
      (nf3Deg F.n F.marked F.gs).getD a 0 else 0) ≤ 1 := by
    intro a _
    by_cases ha : a < F.n + 0
    · simp only [ha, if_true]; exact nf3Deg_input F.n F.marked F.gs a (by omega)
    · rw [if_neg ha]; omega
  simp only [K, decide_eq_true_eq]
  refine ⟨h0, ?_⟩
  show (nf3Deg F.n F.marked F.gs).getD (F.n + 0) 0 ≤ 2
  rw [hd]
  generalize F.gs[0].op = op at *
  generalize F.gs[0].inputs = ins at *
  rcases ins with _ | ⟨x, _ | ⟨y, _ | ⟨z, rest⟩⟩⟩
  · simp [d3r1DegOp]
  · have := hin x (by simp)
    simp only [List.map_cons, List.map_nil, degop_one]; omega
  · have h1 := hin x (by simp)
    have h2 := hin y (by simp)
    simp only [List.map_cons, List.map_nil]
    unfold d3r1DegOp
    by_cases hop : op = GateOp.and
    · rw [if_pos hop]; simp only [List.sum_cons, List.sum_nil]; omega
    · rw [if_neg hop]; simp only [List.foldr_cons, List.foldr_nil]; omega
  · simp at hlen

theorem np_pos (h0 : 0 < F.s) : 1 ≤ F.np := by
  unfold np d3r1Top
  apply List.length_pos_of_mem (a := 0)
  simp [F.K_zero h0, h0]
  exact h0

end Fm

end PEqualNP.MetaComplexity.Helpers.NormalForm3
