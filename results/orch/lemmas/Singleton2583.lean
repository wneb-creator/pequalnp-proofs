import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.Singleton

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C C' : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt C' k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma transfer (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool) (R : Bool → Bool → Prop)
    (hRrefl : ∀ a, R a a) (hRtrans : ∀ a b c, R a b → R b c → R a c)
    (hRand : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.and.eval (l.map f)) (GateOp.and.eval (l.map f')))
    (hRor : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.or.eval (l.map f)) (GateOp.or.eval (l.map f')))
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → R (wv n C x (n + r)) (wv n C x b)) →
      R (wv n C x w) (wv n C' x (tau n r b w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hR0
    by_cases h1 : w < n
    · have ht : tau n r b w = w := by unfold tau; rw [if_pos (by omega)]
      rw [ht, wv_input n C x w h1, wv_input n C' x w h1]
      exact hRrefl _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k = r
      · subst hk
        have ht : tau n k b (n + k) = b := by unfold tau; simp
        have htb : tau n k b b = b := by unfold tau; rw [if_pos hb]
        have h2 := ih b (by omega) (by omega) (fun h => absurd h (by omega))
        rw [htb] at h2
        rw [ht]
        exact hRtrans _ _ _ (hR0 le_rfl) h2
      · have hkm : k < C.gates.length := by omega
        obtain ⟨k', hk'1, hk'2, hk'3⟩ : ∃ k', tau n r b (n + k) = n + k' ∧ rho r k' = k ∧
            k' < C.gates.length - 1 := by
          by_cases hkr : k < r
          · refine ⟨k, ?_, ?_, by omega⟩
            · unfold tau; rw [if_pos (by omega)]
            · unfold rho; rw [if_pos hkr]
          · refine ⟨k - 1, ?_, ?_, by omega⟩
            · unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
            · unfold rho; rw [if_neg (by omega)]; omega
        have hg := hred k' hk'3
        rw [hk'2] at hg
        rw [hk'1, wv_rec n C x hC k hkm, wv_rec n C' x hC' k' (by omega), hg]
        simp only [List.map_map]
        have hin : ∀ w ∈ (gateAt C k).inputs,
            R (wv n C x w) ((wv n C' x ∘ tau n r b) w) := by
          intro w hw'
          have hlt := (hC k hkm).2 w hw'
          exact ih w hlt (by omega) (fun h => hR0 (by omega))
        rcases (hC k hkm).1 with hop | hop
        · rw [hop]; exact hRand _ _ _ hin
        · rw [hop]; exact hRor _ _ _ hin

lemma transfer_eq (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → wv n C x (n + r) = wv n C x b) →
      wv n C x w = wv n C' x (tau n r b w) := by
  refine transfer n C C' r b x (fun a b => a = b) (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2)
    ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h
    rw [List.map_congr_left h]
  · intro l f f' h
    rw [List.map_congr_left h]

lemma transfer_le (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length →
      (n + r ≤ w → (wv n C x (n + r) = true → wv n C x b = true)) →
      (wv n C x w = true → wv n C' x (tau n r b w) = true) := by
  refine transfer n C C' r b x (fun a b => a = true → b = true) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h hall
    simp only [GateOp.eval] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw (hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · intro l f f' h hany
    simp only [GateOp.eval] at hany ⊢
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨v, hv, hv2⟩ := hany
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨f' w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩


def gfun (n : ℕ) (C : Circuit) (r b : ℕ) (top : Gate) (k : ℕ) : Gate :=
  if k < C.gates.length - 1 then
    ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ else top

def V1 (n : ℕ) (C : Circuit) (r b : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (gfun n C r b ⟨GateOp.or, []⟩), tau n r b C.output⟩

def V2 (n : ℕ) (C : Circuit) (r b i : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (gfun n C r b ⟨GateOp.or, [tau n r b C.output, n + i]⟩),
    n + C.gates.length - 1⟩

lemma gateAt_range (m : ℕ) (g : ℕ → Gate) (out k : ℕ) (hk : k < m) :
    gateAt ⟨(List.range m).map g, out⟩ k = g k := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma V1_len (n : ℕ) (C : Circuit) (r b : ℕ) :
    (V1 n C r b).gates.length = C.gates.length - 1 := by simp [V1]

lemma V2_len (n : ℕ) (C : Circuit) (r b i : ℕ) :
    (V2 n C r b i).gates.length = C.gates.length := by simp [V2]

lemma V1_gate (n : ℕ) (C : Circuit) (r b k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V1 n C r b) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V1
  rw [gateAt_range _ _ _ _ hk]
  unfold gfun
  rw [if_pos hk]

lemma V2_gate (n : ℕ) (C : Circuit) (r b i k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V2 n C r b i) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_pos hk]

lemma V2_top (n : ℕ) (C : Circuit) (r b i : ℕ) (hm : 0 < C.gates.length) :
    gateAt (V2 n C r b i) (C.gates.length - 1) =
      ⟨GateOp.or, [tau n r b C.output, n + i]⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_neg (by omega)]

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma aob {n : ℕ} {C : Circuit} (h : AO2 n C) : AOB n C :=
  fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho; split_ifs <;> omega

lemma tau_lt (n r b w k : ℕ) (hb : b < n + r) (hw : w < n + rho r k) :
    tau n r b w < n + k := by
  unfold tau; unfold rho at hw; split_ifs at hw ⊢ <;> omega

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  unfold tau; rw [if_pos hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho; split_ifs <;> omega

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma V1_AO2 (n : ℕ) (C : Circuit) (r b : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) : AO2 n (V1 n C r b) := by
  intro k hk
  rw [V1_len] at hk
  rw [V1_gate n C r b k hk]
  obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk)
  refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  exact tau_lt n r b w0 k hb (h3 w0 hw0)

lemma V2_AO2 (n : ℕ) (C : Circuit) (r b i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) (hi : i < r) (hout : C.output < n + C.gates.length) :
    AO2 n (V2 n C r b i) := by
  intro k hk
  rw [V2_len] at hk
  by_cases hk1 : k < C.gates.length - 1
  · rw [V2_gate n C r b i k hk1]
    obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk1)
    refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact tau_lt n r b w0 k hb (h3 w0 hw0)
  · have hk2 : k = C.gates.length - 1 := by omega
    subst hk2
    rw [V2_top n C r b i (by omega)]
    refine ⟨Or.inr rfl, ⟨_, _, rfl⟩, ?_⟩
    intro w hw
    have hw' : w = tau n r b C.output ∨ w = n + i := by simpa using hw
    rcases hw' with rfl | rfl
    · unfold tau; split_ifs <;> omega
    · omega

lemma V1_red (n : ℕ) (C : Circuit) (r b : ℕ) : IsRedirect n C (V1 n C r b) r b :=
  fun k hk => V1_gate n C r b k hk

lemma V2_red (n : ℕ) (C : Circuit) (r b i : ℕ) : IsRedirect n C (V2 n C r b i) r b :=
  fun k hk => V2_gate n C r b i k hk

lemma V1_fun (n : ℕ) (C : Circuit) (r b : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hout : C.output < n + C.gates.length)
    (h1 : wv n C x b = true → wv n C x C.output = true)
    (h2 : wv n C x b = false → wv n C x (n + r) = false) :
    wv n (V1 n C r b) x (V1 n C r b).output = wv n C x C.output := by
  have hC' := V1_AO2 n C r b hC hr hb
  have hlen : C.gates.length - 1 ≤ (V1 n C r b).gates.length := by rw [V1_len]
  show wv n (V1 n C r b) x (tau n r b C.output) = wv n C x C.output
  cases hbv : wv n C x b with
  | true =>
    rw [h1 hbv]
    exact transfer_le n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ _ => hbv) (h1 hbv)
  | false =>
    exact (transfer_eq n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ => by rw [h2 hbv, hbv])).symm

lemma V2_low (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) :
    ∀ w, w < n + r → wv n (V2 n C r b i) x w = wv n C x w := by
  intro w hw
  have h := transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w (by omega) (fun h => absurd h (by omega))
  rw [tau_low n r b w hw] at h
  exact h.symm

lemma V2_same (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x b) :
    ∀ w, w < n + C.gates.length → wv n (V2 n C r b i) x (tau n r b w) = wv n C x w := by
  intro w hw
  exact (transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w hw (fun _ => h0)).symm

lemma V2_out (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbel : wv n C x (n + i) = true → wv n C x C.output = true)
    (h0 : wv n C x (n + i) = false → wv n C x (n + r) = wv n C x b) :
    wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output := by
  have hC' := V2_AO2 n C r b i hC hr hb hi hout
  have hm : 0 < C.gates.length := by omega
  have e : (V2 n C r b i).output = n + (C.gates.length - 1) := by
    show n + C.gates.length - 1 = _
    omega
  rw [e, wv_rec n _ x (aob hC') (C.gates.length - 1) (by rw [V2_len]; omega),
    V2_top n C r b i hm]
  have hi' := V2_low n C r b i x hC hr hb hi hout (n + i) (by omega)
  dsimp only
  rw [eval_or_pair, hi']
  cases hv : wv n C x (n + i) with
  | true => rw [hbel hv]; simp
  | false =>
    rw [V2_same n C r b i x hC hr hb hi hout (h0 hv) C.output hout]; simp


lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]
  exact List.getElem_mem hj

lemma to_real {n : ℕ} {D : Circuit} (hD : AO2 n D) : PEqualNP.TopForm.IsAO2 n D := by
  have aux : ∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    obtain ⟨hop, ⟨a, b, hin⟩, _⟩ := hD j hj
    rw [gateAt_eq hj] at hop hin
    exact ⟨hop, by rw [hin]; rfl⟩
  exact ⟨fun g hg => (aux g hg).1, fun j hj => (hD j hj).2.2,
    fun g hg => (aux g hg).2⟩

lemma of_real {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) : AO2 n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro k hk
  exact ⟨h1 _ (gateAt_mem hk), List.length_eq_two.mp (h3 _ (gateAt_mem hk)), h2 k hk⟩

lemma lift_or_implicant {n : ℕ} {C : Circuit}
    (hC : PEqualNP.TopForm.IsAO2 n C)
    (hout : C.output < n + C.size)
    (i r b : ℕ) (hr : r < C.size) (hi : i < r)
    (hop : (gateAt C r).op = GateOp.or)
    (hin : (gateAt C r).inputs = [n + i, b] ∨
      (gateAt C r).inputs = [b, n + i])
    (hbelow : ∀ x : Fin n → Bool,
      gateVal n C i x = true → PEqualNP.MetaComplexity.circuitFun n C x = true) :
    PEqualNP.TopForm.IsAO2 n (V2 n C r b i) ∧ (V2 n C r b i).size = C.size ∧
      PEqualNP.MetaComplexity.circuitFun n (V2 n C r b i) =
        PEqualNP.MetaComplexity.circuitFun n C := by
  have hc := of_real hC
  have hb : b < n + r := (hc r hr).2.2 b (by rcases hin with h | h <;> simp [h])
  refine ⟨to_real (V2_AO2 n C r b i hc hr hb hi hout),
    V2_len n C r b i, ?_⟩
  funext x
  apply V2_out n C r b i x hc hr hb hi hout
  · exact hbelow x
  · intro hzero
    rw [wv_rec n C x (aob hc) r hr, hop]
    rcases hin with h | h
    · rw [h, eval_or_pair, hzero]
      rfl
    · rw [h, eval_or_pair, hzero]
      simp

lemma delete_and_above_implicant {n : ℕ} {C : Circuit}
    (hC : PEqualNP.TopForm.IsAO2 n C)
    (hout : C.output < n + C.size)
    (i r b : ℕ) (hr : r < C.size) (hi : i < r)
    (hop : (gateAt C r).op = GateOp.and)
    (hin : (gateAt C r).inputs = [n + i, b] ∨
      (gateAt C r).inputs = [b, n + i])
    (hbelow : ∀ x : Fin n → Bool,
      gateVal n C i x = true → PEqualNP.MetaComplexity.circuitFun n C x = true) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size + 1 = C.size ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C := by
  have hc := of_real hC
  have hb : n + i < n + r := by omega
  refine ⟨V1 n C r (n + i), to_real (V1_AO2 n C r (n + i) hc hr hb), ?_, ?_⟩
  · change (V1 n C r (n + i)).gates.length + 1 = C.gates.length
    rw [V1_len]
    change r < C.gates.length at hr
    omega
  · funext x
    apply V1_fun n C r (n + i) x hc hr hb hout
    · exact hbelow x
    · intro hzero
      rw [wv_rec n C x (aob hc) r hr, hop]
      rcases hin with h | h
      · rw [h, eval_and_pair, hzero]
        rfl
      · rw [h, eval_and_pair, hzero]
        simp

lemma least_implicant_reader_is_or {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hC : PEqualNP.TopForm.IsLeastAO G C)
    (hout : C.output < n + C.size) (i r : ℕ) (hr : r < C.size)
    (hin : n + i ∈ (gateAt C r).inputs)
    (hbelow : PEqualNP.TopForm.BelowF G C i) :
    (gateAt C r).op = GateOp.or := by
  have hc := of_real hC.1
  have hi : i < r := by
    have h := (hc r hr).2.2 _ hin
    omega
  rcases (hc r hr).1 with hop | hop
  · obtain ⟨a, b, hab⟩ := (hc r hr).2.1
    have hx : n + i = a ∨ n + i = b := by simpa [hab] using hin
    have hex : ∃ b, (gateAt C r).inputs = [n + i, b] ∨
        (gateAt C r).inputs = [b, n + i] := by
      rcases hx with h | h
      · exact ⟨b, Or.inl (by simpa [h] using hab)⟩
      · exact ⟨a, Or.inr (by simpa [h] using hab)⟩
    obtain ⟨b, hb⟩ := hex
    obtain ⟨D, hao, hs, he⟩ := delete_and_above_implicant hC.1 hout i r b hr hi hop hb
      (fun x hx => by rw [hC.2.1]; exact hbelow x hx)
    have hle := hC.2.2 D hao (he.trans hC.2.1)
    omega
  · exact hop

def atomic {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n) : Circuit :=
  ⟨C.gates.set j ⟨GateOp.and, [u.val, v.val]⟩, C.output⟩

lemma atomic_size {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n) :
    (atomic C j u v).size = C.size := by simp [atomic, Circuit.size]

lemma atomic_at {n : ℕ} (C : Circuit) (j : ℕ) (u v : Fin n) (hj : j < C.size) :
    gateAt (atomic C j u v) j = ⟨GateOp.and, [u.val, v.val]⟩ := by
  change j < C.gates.length at hj
  simp [atomic, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set, hj]

lemma atomic_other {n : ℕ} (C : Circuit) (j k : ℕ) (u v : Fin n) (hne : k ≠ j) :
    gateAt (atomic C j u v) k = gateAt C k := by
  simp only [atomic, gateAt, List.getD_eq_getElem?_getD]
  rw [List.getElem?_set_ne hne.symm]

lemma atomic_AO2 {n : ℕ} {C : Circuit} (hC : AO2 n C) (j : ℕ) (u v : Fin n)
    (hj : j < C.size) : AO2 n (atomic C j u v) := by
  intro k hk
  have hkl : k < C.gates.length := by simpa [atomic] using hk
  by_cases he : k = j
  · subst k
    rw [atomic_at C j u v hj]
    refine ⟨Or.inl rfl, ⟨u.val, v.val, rfl⟩, ?_⟩
    intro a ha
    have hx : a = u.val ∨ a = v.val := by simpa using ha
    rcases hx with rfl | rfl <;> omega
  · rw [atomic_other C j k u v he]
    exact hC k hkl

lemma atomic_value {n : ℕ} {C : Circuit} (hC : AO2 n C) (j : ℕ) (u v : Fin n)
    (hj : j < C.size) (x : Fin n → Bool) :
    wv n (atomic C j u v) x (n + j) = (x u && x v) := by
  rw [wv_rec n _ x (aob (atomic_AO2 hC j u v hj)) j
    (by change j < (atomic C j u v).size; rw [atomic_size]; exact hj),
    atomic_at C j u v hj]
  change GateOp.and.eval ([u.val, v.val].map (wv n (atomic C j u v) x)) = _
  rw [eval_and_pair, wv_input n _ x u.val u.isLt, wv_input n _ x v.val v.isLt]

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f g : ℕ → Bool) (h : ∀ w ∈ l, f w = true → g w = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval]
    rw [List.all_eq_true, List.all_eq_true]
    intro hall v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact h w hw (hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · simp only [GateOp.eval]
    rw [List.any_eq_true, List.any_eq_true]
    rintro ⟨v, hv, hv2⟩
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    exact ⟨g w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩

lemma wire_mono {n : ℕ} {C : Circuit} (hC : AO2 n C) {x y : Fin n → Bool}
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ w < n + C.size, wv n C x w = true → wv n C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx
    by_cases hw0 : w < n
    · rw [wv_input n C x w hw0] at hx
      rw [wv_input n C y w hw0]
      exact hxy ⟨w, hw0⟩ hx
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.size := by omega
      rw [wv_rec n C x (aob hC) k hk] at hx
      rw [wv_rec n C y (aob hC) k hk]
      apply eval_mono _ (hC k hk).1 _ _ _ ?_ hx
      intro a ha
      exact ih a ((hC k hk).2.2 a ha) (by have := (hC k hk).2.2 a ha; omega)

lemma atomic_le {n : ℕ} {C : Circuit} (hC : AO2 n C) (j : ℕ) (u v : Fin n)
    (hj : j < C.size) (x : Fin n → Bool)
    (hgate : x u && x v = true → wv n C x (n + j) = true) :
    ∀ w < n + C.size,
      wv n (atomic C j u v) x w = true → wv n C x w = true := by
  have hD := atomic_AO2 hC j u v hj
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx
    by_cases hw0 : w < n
    · rw [wv_input n _ x w hw0] at hx
      rw [wv_input n C x w hw0]
      exact hx
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.size := by omega
      by_cases he : k = j
      · subst k
        rw [atomic_value hC j u v hj x] at hx
        exact hgate hx
      · rw [wv_rec n _ x (aob hD) k (by change k < (atomic C j u v).size; rw [atomic_size]; exact hk),
          atomic_other C j k u v he] at hx
        rw [wv_rec n C x (aob hC) k hk]
        apply eval_mono _ (hC k hk).1 _ _ _ ?_ hx
        intro a ha
        exact ih a ((hC k hk).2.2 a ha) (by have := (hC k hk).2.2 a ha; omega)

lemma atomic_eq {n : ℕ} {C : Circuit} (hC : AO2 n C) (j : ℕ) (u v : Fin n)
    (hj : j < C.size) (x : Fin n → Bool)
    (hgate : wv n C x (n + j) = (x u && x v)) :
    ∀ w < n + C.size, wv n (atomic C j u v) x w = wv n C x w := by
  have hD := atomic_AO2 hC j u v hj
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hw0 : w < n
    · rw [wv_input n _ x w hw0, wv_input n C x w hw0]
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.size := by omega
      by_cases he : k = j
      · subst k
        rw [atomic_value hC j u v hj x, hgate]
      · rw [wv_rec n _ x (aob hD) k (by change k < (atomic C j u v).size; rw [atomic_size]; exact hk),
          atomic_other C j k u v he, wv_rec n C x (aob hC) k hk]
        congr 1
        apply List.map_congr_left
        intro a ha
        exact ih a ((hC k hk).2.2 a ha) (by have := (hC k hk).2.2 a ha; omega)

lemma pair_le {n : ℕ} (u v : Fin n) (x : Fin n → Bool)
    (hu : x u = true) (hv : x v = true) :
    ∀ a, pairInput u v a = true → x a = true := by
  intro a ha
  have hx : a = u ∨ a = v := by simpa [pairInput] using ha
  rcases hx with rfl | rfl
  · exact hu
  · exact hv

lemma singleton_replacement {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : PEqualNP.TopForm.IsAO2 n C)
    (hcomp : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    (hout : C.output < n + C.size) (j : ℕ) (hj : j < C.size)
    (u v : Fin n) (huv : G.Adj u v)
    (hprofile : ∀ a b : Fin n, G.Adj a b →
      gateVal n C j (pairInput a b) = (pairInput a b u && pairInput a b v)) :
    PEqualNP.TopForm.IsAO2 n (atomic C j u v) ∧ (atomic C j u v).size = C.size ∧
      PEqualNP.MetaComplexity.circuitFun n (atomic C j u v) = graphFun G ∅ ∧
      PEqualNP.TopForm.BelowF G (atomic C j u v) j ∧
      (∀ a b : Fin n, G.Adj a b → ∀ w < n + C.size,
        wv n (atomic C j u v) (pairInput a b) w = wv n C (pairInput a b) w) ∧
      (∀ x w, w < n + C.size →
        wv n (atomic C j u v) x w = true → wv n C x w = true) := by
  have hc := of_real hC
  have hd := atomic_AO2 hc j u v hj
  have hseed : wv n C (pairInput u v) (n + j) = true := by
    have h := hprofile u v huv
    simpa [pairInput] using h
  have hle : ∀ x w, w < n + C.size →
      wv n (atomic C j u v) x w = true → wv n C x w = true := by
    intro x w hw
    apply atomic_le hc j u v hj x ?_ w hw
    intro hx
    obtain ⟨hu, hv⟩ := Bool.and_eq_true.mp hx
    exact wire_mono hc (pair_le u v x hu hv) (n + j) (by omega) hseed
  have heq : ∀ a b : Fin n, G.Adj a b → ∀ w < n + C.size,
      wv n (atomic C j u v) (pairInput a b) w = wv n C (pairInput a b) w := by
    intro a b hab
    exact atomic_eq hc j u v hj (pairInput a b) (hprofile a b hab)
  refine ⟨to_real hd, atomic_size C j u v, ?_, ?_, heq, hle⟩
  · funext x
    change wv n (atomic C j u v) x C.output = graphFun G ∅ x
    cases hf : graphFun G ∅ x with
    | false =>
      cases hdv : wv n (atomic C j u v) x C.output with
      | false => rfl
      | true =>
        have hcval := hle x C.output hout hdv
        have hce := congrFun hcomp x
        change wv n C x C.output = _ at hce
        rw [hce, hf] at hcval
        cases hcval
    | true =>
      have hfx : ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true := by
        simpa [graphFun] using hf
      obtain ⟨a, b, hab, ha, hb⟩ := hfx
      have hp : wv n C (pairInput a b) C.output = true := by
        change PEqualNP.MetaComplexity.circuitFun n C (pairInput a b) = true
        rw [hcomp]
        simp only [graphFun, Finset.notMem_empty, false_and, exists_const, decide_false,
          Bool.false_or, decide_eq_true_eq]
        exact ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
      have hpD := (heq a b hab C.output hout).trans hp
      exact wire_mono hd (pair_le a b x ha hb) C.output
        (by rw [atomic_size]; exact hout) hpD
  · intro x hx
    change wv n (atomic C j u v) x (n + j) = true at hx
    rw [atomic_value hc j u v hj x] at hx
    obtain ⟨hu, hv⟩ := Bool.and_eq_true.mp hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_const, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨u, v, huv, hu, hv⟩

end PEqualNP.Outside.L_meta_2583_aux.Singleton
