import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5106

open PEqualNP.CircuitLowerBounds

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl F x := rfl

lemma len_foldl (gs : List Gate) : ∀ w : List Bool, (gs.foldl F w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; simp only [List.foldl_cons, ih, F]; simp; omega

lemma getD_F (w : List Bool) (g : Gate) (i : ℕ) : (F w g).getD i false =
    if i < w.length then w.getD i false
    else if i = w.length then g.op.eval (g.inputs.map fun i => w.getD i false) else false := by
  unfold F
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

lemma pref (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl F w).getD i false = w.getD i false := by
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro w i h
    rw [List.foldl_cons, ih _ i (by simp [F]; omega), getD_F, if_pos h]

lemma gateval (gs : List Gate) : ∀ (w : List Bool) (k : ℕ) (hk : k < gs.length),
    (gs.foldl F w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (gs.foldl F w).getD i false else false) := by
  induction gs with
  | nil => intro w k hk; simp at hk
  | cons g gs ih =>
    intro w k hk
    cases k with
    | zero =>
      simp only [List.foldl_cons, List.getElem_cons_zero, Nat.add_zero]
      rw [pref gs (F w g) w.length (by simp [F]), getD_F, if_neg (lt_irrefl _), if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with h
      · rw [pref gs (F w g) i (by simp [F]; omega), getD_F, if_pos h]
      · rw [List.getD_eq_default _ _ (by omega)]
    | succ k =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have h1 := ih (F w g) k (by simpa using hk)
      have hl : (F w g).length = w.length + 1 := by simp [F]
      rw [hl] at h1
      rw [show w.length + (k + 1) = w.length + 1 + k by omega, h1]

def rnk (R : Finset ℕ) (j : ℕ) : ℕ := ((List.range j).filter (fun i => decide (i ∉ R))).length

lemma rnk_le (R : Finset ℕ) (j : ℕ) : rnk R j ≤ j := by
  unfold rnk; exact le_trans (List.length_filter_le _ _) (by simp)

lemma rnk_mono (R : Finset ℕ) {i j : ℕ} (h : i ≤ j) : rnk R i ≤ rnk R j := by
  unfold rnk
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.range_add, List.filter_append, List.length_append]
  omega

lemma rnk_succ_of_not_mem (R : Finset ℕ) {j : ℕ} (h : j ∉ R) : rnk R (j + 1) = rnk R j + 1 := by
  unfold rnk
  rw [List.range_succ, List.filter_append, List.length_append]
  simp [h]

lemma rnk_lt (R : Finset ℕ) {i j : ℕ} (hi : i ∉ R) (h : i < j) : rnk R i < rnk R j := by
  have := rnk_mono R (show i + 1 ≤ j by omega)
  rw [rnk_succ_of_not_mem R hi] at this
  omega

def mu (n L : ℕ) (R : Finset ℕ) (t : ℕ → ℕ) (a b : ℕ) (w : ℕ) : ℕ :=
  if w < n then (if w = a ∨ w = b then n + L else w)
  else if w < n + L then
    (if w - n ∈ R then (if t (w - n) < w then mu n L R t a b (t (w - n)) else n + L)
     else n + rnk R (w - n))
  else n + L
termination_by w

lemma mu_inv (n L : ℕ) (R : Finset ℕ) (t : ℕ → ℕ) (a b : ℕ) : ∀ w,
    mu n L R t a b w = n + L ∨ mu n L R t a b w < n ∨
      ∃ j, j ∉ R ∧ n + j ≤ w ∧ mu n L R t a b w = n + rnk R j := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  rw [mu]
  split_ifs with h1 h2 h3 h4 h5
  · left; rfl
  · right; left; exact h1
  · rcases ih _ h5 with h | h | ⟨j, hj, hle, heq⟩
    · left; rw [mu] at h ⊢; exact h
    · right; left; exact h
    · right; right; exact ⟨j, hj, by omega, heq⟩
  · left; rfl
  · right; right; exact ⟨w - n, h4, by omega, rfl⟩
  · left; rfl

lemma filt_get (R : Finset ℕ) (L j : ℕ) (hj : j < L) (hjR : j ∉ R) :
    ∃ h : rnk R j < ((List.range L).filter (fun i => decide (i ∉ R))).length,
      ((List.range L).filter (fun i => decide (i ∉ R)))[rnk R j] = j := by
  obtain ⟨m, rfl⟩ : ∃ m, L = j + (m + 1) := ⟨L - j - 1, by omega⟩
  have hsplit : (List.range (j + (m + 1))).filter (fun i => decide (i ∉ R)) =
      (List.range j).filter (fun i => decide (i ∉ R)) ++
        (j :: ((List.range m).map (fun k => j + (k + 1))).filter (fun i => decide (i ∉ R))) := by
    rw [List.range_add, List.filter_append, List.range_succ_eq_map]
    simp [hjR, List.map_map, Function.comp_def]
  have hl : rnk R j < ((List.range (j + (m + 1))).filter (fun i => decide (i ∉ R))).length := by
    rw [hsplit]; simp [rnk]
  refine ⟨hl, ?_⟩
  simp only [hsplit]
  rw [List.getElem_append_right (by simp [rnk])]
  simp [rnk]

lemma filt_len (R : Finset ℕ) (L : ℕ) (hR : ∀ r ∈ R, r < L) :
    ((List.range L).filter (fun i => decide (i ∉ R))).length = L - R.card := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _), List.toFinset_filter,
    List.toFinset_range]
  have hsub : R ⊆ Finset.range L := fun r hr => Finset.mem_range.mpr (hR r hr)
  have : (Finset.range L).filter (fun i => decide (i ∉ R) = true) = Finset.range L \ R := by
    ext i; simp
  rw [this, Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]
  simp

end PEqualNP.Outside.L_meta_5106

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_5106 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : Fin x1) (x5 : Finset ℕ),   PEqualNP.MetaComplexity.FanInTwo x2 →     (∀ x7 ∈ x5, x7 < x2.size) →       (∀ x8 ∈ x5,           ∃ (x10 : ℕ),             (x10 < x1 + x8 ∨ x1 + x2.size ≤ x10) ∧               ∀ (x11 : Fin x1 → Bool),                 have x12 : List Bool := x2.wires (List.ofFn (Function.update (Function.update x11 x3 Bool.false) x4 Bool.false));                 x12.getD (x1 + x8) Bool.false = x12.getD x10 Bool.false) →         PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x9 : Fin x1 → Bool) => x2.eval (List.ofFn (Function.update (Function.update x9 x3 Bool.false) x4 Bool.false))) (x2.size - x5.card) := by
  intro n C a b R hfan hR hyp
  classical
  open PEqualNP.Outside.L_meta_5106 in
  let L := C.gates.length
  let upd : (Fin n → Bool) → (Fin n → Bool) := fun x => Function.update (Function.update x a false) b false
  let tt : ℕ → ℕ := fun j => if h : j ∈ R then Classical.choose (hyp j h) else 0
  have ht : ∀ j ∈ R, (tt j < n + j ∨ n + C.size ≤ tt j) ∧ ∀ x : Fin n → Bool,
      (C.wires (List.ofFn (upd x))).getD (n + j) false = (C.wires (List.ofFn (upd x))).getD (tt j) false := by
    intro j hj
    have := Classical.choose_spec (hyp j hj)
    simp only [tt, dif_pos hj]
    exact this
  let μ : ℕ → ℕ := PEqualNP.Outside.L_meta_5106.mu n L R tt a.val b.val
  let mk : ℕ → Gate := fun j => ⟨(C.gates.getD j ⟨GateOp.or, []⟩).op,
    (C.gates.getD j ⟨GateOp.or, []⟩).inputs.map (fun i => if i < n + j then μ i else n + L)⟩
  let ks := (List.range L).filter (fun i => decide (i ∉ R))
  refine ⟨⟨ks.map mk, μ C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
    have hjL : j < L := List.mem_range.mp (List.mem_filter.mp hj).1
    have hmem : C.gates.getD j ⟨GateOp.or, []⟩ ∈ C.gates := by
      rw [List.getD_eq_getElem _ _ hjL]; exact List.getElem_mem hjL
    obtain ⟨h1, h2⟩ := hfan _ hmem
    exact ⟨h1, by simpa [mk] using h2⟩
  · show (ks.map mk).length ≤ C.gates.length - R.card
    rw [List.length_map, PEqualNP.Outside.L_meta_5106.filt_len R L (fun r hr => hR r hr)]
  · intro x
    let W := C.gates.foldl PEqualNP.Outside.L_meta_5106.F (List.ofFn (upd x))
    let W' := (ks.map mk).foldl PEqualNP.Outside.L_meta_5106.F (List.ofFn x)
    have hWlen : W.length = n + L := by
      simp only [W, PEqualNP.Outside.L_meta_5106.len_foldl, List.length_ofFn]; rfl
    have hW'len : W'.length ≤ n + L := by
      simp only [W', PEqualNP.Outside.L_meta_5106.len_foldl, List.length_ofFn, List.length_map]
      have h0 : ks.length ≤ L := by
        have := List.length_filter_le (fun i => decide (i ∉ R)) (List.range L)
        rw [List.length_range] at this
        exact this
      omega
    have big : W'.getD (n + L) false = false := List.getD_eq_default _ _ hW'len
    have hWout : ∀ w, n + L ≤ w → W.getD w false = false := fun w hw =>
      List.getD_eq_default _ _ (by omega)
    have claim : ∀ w, W'.getD (μ w) false = W.getD w false := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
      show W'.getD (PEqualNP.Outside.L_meta_5106.mu n L R tt a.val b.val w) false = _
      rw [PEqualNP.Outside.L_meta_5106.mu]
      split_ifs with h1 h2 h3 h4 h5
      · rw [big]
        have hp : W.getD w false = (List.ofFn (upd x)).getD w false :=
          PEqualNP.Outside.L_meta_5106.pref _ _ _ (by simp; omega)
        rw [hp, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
        have key : ∀ c : Fin n, (c = a ∨ c = b) → upd x c = false := by
          intro c hc
          by_cases hcb : c = b
          · subst hcb; simp [upd]
          · rcases hc with rfl | rfl
            · simp [upd, Function.update_of_ne hcb]
            · exact absurd rfl hcb
        refine (key _ ?_).symm
        rcases h2 with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      · have hp : W.getD w false = (List.ofFn (upd x)).getD w false :=
          PEqualNP.Outside.L_meta_5106.pref _ _ _ (by simp; omega)
        have hp' : W'.getD w false = (List.ofFn x).getD w false :=
          PEqualNP.Outside.L_meta_5106.pref _ _ _ (by simp; omega)
        rw [hp, hp', List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn,
          List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
        have ha : (⟨w, h1⟩ : Fin n) ≠ a := fun e => h2 (Or.inl (congrArg Fin.val e))
        have hb : (⟨w, h1⟩ : Fin n) ≠ b := fun e => h2 (Or.inr (congrArg Fin.val e))
        simp [upd, Function.update_of_ne ha, Function.update_of_ne hb]
      · rw [ih _ h5]
        have := (ht (w - n) h4).2 x
        rw [show n + (w - n) = w by omega] at this
        exact this.symm
      · rw [big]
        rcases (ht (w - n) h4).1 with hl | hl
        · omega
        · have := (ht (w - n) h4).2 x
          rw [show n + (w - n) = w by omega] at this
          show false = W.getD w false
          rw [show W = C.wires (List.ofFn (upd x)) from rfl, this]
          exact (List.getD_eq_default _ _ (by
            rw [show C.wires (List.ofFn (upd x)) = W from rfl, hWlen]; simp [Circuit.size] at hl; omega)).symm
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        simp only [Nat.add_sub_cancel_left] at h4 ⊢
        have hjL : j < L := by omega
        obtain ⟨hk, hkj⟩ := PEqualNP.Outside.L_meta_5106.filt_get R L j hjL h4
        have hk' : PEqualNP.Outside.L_meta_5106.rnk R j < (ks.map mk).length := by simpa [ks] using hk
        have gv' := PEqualNP.Outside.L_meta_5106.gateval (ks.map mk) (List.ofFn x) _ hk'
        have gv := PEqualNP.Outside.L_meta_5106.gateval C.gates (List.ofFn (upd x)) j hjL
        simp only [List.length_ofFn] at gv' gv
        have hmk : (ks.map mk)[PEqualNP.Outside.L_meta_5106.rnk R j] = mk j := by
          rw [List.getElem_map]; congr 1
        rw [hmk] at gv'
        show W'.getD (n + PEqualNP.Outside.L_meta_5106.rnk R j) false = W.getD (n + j) false
        rw [show W'.getD (n + PEqualNP.Outside.L_meta_5106.rnk R j) false = _ from gv',
          show W.getD (n + j) false = _ from gv]
        have hgd : C.gates.getD j ⟨GateOp.or, []⟩ = C.gates[j] := List.getD_eq_getElem _ _ hjL
        simp only [mk, hgd, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        simp only [Function.comp]
        have hrl : PEqualNP.Outside.L_meta_5106.rnk R j < L :=
          lt_of_le_of_lt (PEqualNP.Outside.L_meta_5106.rnk_le R _) hjL
        by_cases hi : i < n + j
        · rw [if_pos hi, if_pos hi]
          rcases PEqualNP.Outside.L_meta_5106.mu_inv n L R tt a.val b.val i with he | he | ⟨j', hj', hle, he⟩
          · have : ¬ (μ i < n + PEqualNP.Outside.L_meta_5106.rnk R j) := by
              show ¬ (PEqualNP.Outside.L_meta_5106.mu n L R tt a.val b.val i < _); rw [he]; omega
            rw [if_neg this, ← ih i hi]
            show false = W'.getD (PEqualNP.Outside.L_meta_5106.mu n L R tt a.val b.val i) false
            rw [he, big]
          · have : μ i < n + PEqualNP.Outside.L_meta_5106.rnk R j := by
              show PEqualNP.Outside.L_meta_5106.mu n L R tt a.val b.val i < _; omega
            rw [if_pos this, ih i hi]
          · have hlt := PEqualNP.Outside.L_meta_5106.rnk_lt R hj' (show j' < j by omega)
            have : μ i < n + PEqualNP.Outside.L_meta_5106.rnk R j := by
              show PEqualNP.Outside.L_meta_5106.mu n L R tt a.val b.val i < _; rw [he]; omega
            rw [if_pos this, ih i hi]
        · rw [if_neg hi, if_neg hi, if_neg (by omega)]
      · rw [big, hWout w (by omega)]
    exact claim C.output
