import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1506

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

def shiftDown (wOld u : ℕ) : ℕ :=
  if wOld < u then u - 1 else u

def wiresMatch (w0 : List Bool) (bOld : Bool) (wC wD : List Bool) : Prop :=
  wC.length = wD.length + 1 ∧
  w0.length ≤ wD.length ∧
  wC.getD w0.length false = bOld ∧
  (∀ u, u < w0.length → wD.getD u false = w0.getD u false) ∧
  (∀ u, u < w0.length → wC.getD u false = w0.getD u false) ∧
  (∀ u, w0.length < u → wD.getD (u - 1) false = wC.getD u false)

lemma wiresMatch_init (w0 : List Bool) (bOld : Bool) :
    wiresMatch w0 bOld (w0 ++ [bOld]) w0 := by
  refine ⟨by simp, le_rfl, ?_, fun _ _ => rfl, ?_, ?_⟩
  · simp [List.getD_eq_getElem?_getD]
  · intro u hu
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hu]
  · intro u hu
    have h1 : w0.length ≤ u - 1 := by omega
    have h2 : (w0 ++ [bOld]).length ≤ u := by simp; omega
    rw [getD_ge_length w0 (u - 1) h1, getD_ge_length (w0 ++ [bOld]) u h2]

lemma wiresMatch_step {w0 : List Bool} {bOld : Bool} {wC wD : List Bool} {b : Bool}
    (hm : wiresMatch w0 bOld wC wD) :
    wiresMatch w0 bOld (wC ++ [b]) (wD ++ [b]) := by
  obtain ⟨hlen, hle, hbold, hltD, hltC, hgt⟩ := hm
  refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_⟩
  · have hlt : w0.length < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    simpa [List.getD_eq_getElem?_getD] using hbold
  · intro u hu
    have h1 : u < wD.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    simpa [List.getD_eq_getElem?_getD] using hltD u hu
  · intro u hu
    have h2 : u < wC.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2]
    simpa [List.getD_eq_getElem?_getD] using hltC u hu
  · intro u hu
    by_cases h1 : u - 1 < wD.length
    · have h2 : u < wC.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_left h1, List.getElem?_append_left h2]
      simpa [List.getD_eq_getElem?_getD] using hgt u hu
    · by_cases heq : u - 1 = wD.length
      · have heqC : u = wC.length := by omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, heq, heqC,
            List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
        simp
      · have hg1 : (wD ++ [b]).length ≤ u - 1 := by simp; omega
        have hg2 : (wC ++ [b]).length ≤ u := by simp; omega
        rw [getD_ge_length _ _ hg1, getD_ge_length _ _ hg2]

lemma wiresMatch_getD_shiftDown {w0 : List Bool} {bOld : Bool} {wC wD : List Bool}
    (hm : wiresMatch w0 bOld wC wD) {u : ℕ} (hne : u ≠ w0.length) :
    wD.getD (shiftDown w0.length u) false = wC.getD u false := by
  unfold shiftDown
  by_cases hgt : w0.length < u
  · simp only [hgt, ↓reduceIte]; exact hm.2.2.2.2.2 u hgt
  · simp only [hgt, ↓reduceIte]
    have hlt : u < w0.length := by omega
    rw [hm.2.2.2.1 u hlt, hm.2.2.2.2.1 u hlt]

lemma foldl_wiresMatch (w0 : List Bool) (bOld : Bool) (gsC gsD : List Gate)
    (wC wD : List Bool) (hm : wiresMatch w0 bOld wC wD) (hlen : gsD.length = gsC.length)
    (hstep : ∀ (t : ℕ) (htC : t < gsC.length) (htD : t < gsD.length) (vC vD : List Bool),
      wiresMatch w0 bOld vC vD → vD.length = wD.length + t →
      (gsD[t]'htD).op.eval ((gsD[t]'htD).inputs.map fun i => vD.getD i false) =
      (gsC[t]'htC).op.eval ((gsC[t]'htC).inputs.map fun i => vC.getD i false)) :
    wiresMatch w0 bOld (gsC.foldl stepWire wC) (gsD.foldl stepWire wD) := by
  induction gsC generalizing gsD wC wD with
  | nil =>
    cases gsD with
    | nil => exact hm
    | cons => simp at hlen
  | cons gC restC ih =>
    cases gsD with
    | nil => simp at hlen
    | cons gD restD =>
      simp only [List.foldl_cons]
      have heq0 := hstep 0 (by simp) (by simp) wC wD hm (by simp)
      simp only [List.getElem_cons_zero] at heq0
      have hm1 : wiresMatch w0 bOld (stepWire wC gC) (stepWire wD gD) := by
        unfold stepWire
        rw [heq0]
        exact wiresMatch_step hm
      apply ih restD (stepWire wC gC) (stepWire wD gD) hm1 (by simp at hlen; omega)
      intro t htC htD vC vD hmv hvlen
      have h' := hstep (t + 1) (by simp; omega) (by simp; omega) vC vD hmv
        (by simp [stepWire] at hvlen ⊢; omega)
      simpa only [List.getElem_cons_succ] using h'

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

def aliasWire (wOld wNew u : ℕ) : ℕ :=
  if u = wOld then wNew else shiftDown wOld u

def aliasGate (wOld wNew : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (aliasWire wOld wNew)⟩

def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

def eraseC (n : ℕ) (C : Circuit) (j i : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (aliasGate (n + j) i),
    aliasWire (n + j) i C.output⟩

def appOr (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.or, [a, b]⟩], n + C.gates.length⟩

def truncC (C : Circuit) (m : ℕ) : Circuit :=
  ⟨C.gates.take m, C.output⟩

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma erase_wires (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (hi : i < n + j)
    (x : Fin n → Bool)
    (h : W n C x i = W n C x (n + j) ∨
      ∀ k, j < k → k < C.gates.length → n + j ∉ (gateAt C k).inputs) :
    ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
      W n (eraseC n C j i) x (aliasWire (n + j) i u) = W n C x u := by
  obtain ⟨pre, post, gj, hgs, hpre_len, _⟩ := split_gates C.gates j hj
  have hlenC : C.gates.length = pre.length + 1 + post.length := by
    have := congrArg List.length hgs; simp at this; omega
  have htake : C.gates.take j = pre := by rw [hgs, ← hpre_len]; simp
  have hdrop : C.gates.drop (j + 1) = post := by rw [hgs, ← hpre_len]; simp
  intro u hu
  simp only [W, eraseC, wires_eq_foldl, htake, hdrop]
  conv_rhs => rw [hgs, List.foldl_append, List.foldl_cons]
  rw [List.foldl_append]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + j := by
    simp [w0, foldl_stepWire_length, hpre_len]
  let bOld := gj.op.eval (gj.inputs.map fun k => w0.getD k false)
  have hCi : W n C x i = w0.getD i false := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)
  have hCj : W n C x (n + j) = bOld := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + j) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len, bOld]
  have hm0 : wiresMatch w0 bOld (stepWire w0 gj) w0 := wiresMatch_init w0 bOld
  have halias_get : ∀ (vC vD : List Bool), wiresMatch w0 bOld vC vD →
      ∀ u, (u = n + j → W n C x i = W n C x (n + j)) →
        vD.getD (aliasWire (n + j) i u) false = vC.getD u false := by
    intro vC vD hmv u hu'
    unfold aliasWire
    by_cases hu : u = n + j
    · have hval_eq : w0.getD i false = bOld := by rw [← hCi, ← hCj]; exact hu' hu
      subst hu
      simp only [↓reduceIte]
      rw [hmv.2.2.2.1 i (by omega), hval_eq, ← hw0_len, hmv.2.2.1]
    · simp only [hu, ↓reduceIte]
      rw [← hw0_len]
      exact wiresMatch_getD_shiftDown hmv (by omega)
  have hmEnd : wiresMatch w0 bOld (post.foldl stepWire (stepWire w0 gj))
      ((post.map (aliasGate (n + j) i)).foldl stepWire w0) := by
    refine foldl_wiresMatch w0 bOld post (post.map (aliasGate (n + j) i)) (stepWire w0 gj) w0 hm0
      (by simp) ?_
    intro t htC htD vC vD hmv _
    simp only [List.getElem_map, aliasGate, List.map_map]
    congr 1
    refine List.map_congr_left fun u hu => ?_
    refine halias_get vC vD hmv u ?_
    intro hun
    rcases h with h | h
    · exact h
    · exfalso
      have hget : gateAt C (j + 1 + t) = post[t] := by
        rw [gateAt_eq C (j + 1 + t) (by omega)]
        have h1 : (pre ++ gj :: post)[j + 1 + t]'(by rw [← hgs]; omega) = post[t]'htC := by
          rw [List.getElem_append_right (by omega)]
          have hsub : j + 1 + t - pre.length = t + 1 := by omega
          simp [hsub]
        simpa [hgs] using h1
      exact h (j + 1 + t) (by omega) (by omega) (by rw [hget, ← hun]; exact hu)
  exact halias_get _ _ hmEnd u hu

lemma erase_length (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) :
    (eraseC n C j i).gates.length + 1 = C.gates.length := by
  simp [eraseC]; omega

lemma erase_gateAt_lt (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : k < j) :
    gateAt (eraseC n C j i) k = gateAt C k := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp; omega)]
  simp [hk]

lemma erase_gateAt_ge (n : ℕ) (C : Circuit) (j i k : ℕ) (hj : j < C.gates.length) (hk : j ≤ k)
    (hk2 : k + 1 < C.gates.length) :
    gateAt (eraseC n C j i) k = aliasGate (n + j) i (gateAt C (k + 1)) := by
  simp only [gateAt, eraseC, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp; omega)]
  have h1 : (List.take j C.gates).length = j := by simp; omega
  have h2 : j + 1 + (k - j) = k + 1 := by omega
  rw [h1, List.getElem?_map, List.getElem?_drop, h2, List.getElem?_eq_getElem hk2]
  rfl

lemma prefix_W (n : ℕ) (pre rest1 rest2 : List Gate) (o1 o2 : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + pre.length) :
    W n ⟨pre ++ rest1, o1⟩ x u = W n ⟨pre ++ rest2, o2⟩ x u := by
  simp only [W, wires_eq_foldl, List.foldl_append]
  have h : u < (pre.foldl stepWire (List.ofFn x)).length := by
    rw [foldl_stepWire_length]; simpa using hu
  rw [foldl_stepWire_getD_lt rest1 (pre.foldl stepWire (List.ofFn x)) u h,
    foldl_stepWire_getD_lt rest2 (pre.foldl stepWire (List.ofFn x)) u h]

lemma erase_W_lt (n : ℕ) (C : Circuit) (j i : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool)
    (u : ℕ) (hu : u < n + j) : W n (eraseC n C j i) x u = W n C x u := by
  have h := prefix_W n (C.gates.take j) ((C.gates.drop (j + 1)).map (aliasGate (n + j) i))
    (C.gates.drop j) (aliasWire (n + j) i C.output) C.output x u
    (by rw [List.length_take]; omega)
  have e2 : (⟨C.gates.take j ++ C.gates.drop j, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h

lemma appOr_W_lt (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool) (u : ℕ)
    (hu : u < n + C.gates.length) : W n (appOr n C a b) x u = W n C x u := by
  have h := prefix_W n C.gates [⟨GateOp.or, [a, b]⟩] [] (n + C.gates.length) C.output x u hu
  have e2 : (⟨C.gates ++ [], C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e2] at h
  exact h

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a || W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (a b : ℕ) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    W n C x (n + k) = (W n C x a && W n C x b) := by
  rw [W_gate n C x k hk, hop, hin]
  simp [GateOp.eval, ha, hb]

lemma appOr_gateAt_lt (n : ℕ) (C : Circuit) (a b k : ℕ) (hk : k < C.gates.length) :
    gateAt (appOr n C a b) k = gateAt C k := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma appOr_gateAt_last (n : ℕ) (C : Circuit) (a b : ℕ) :
    gateAt (appOr n C a b) C.gates.length = ⟨GateOp.or, [a, b]⟩ := by
  simp [gateAt, appOr, List.getD_eq_getElem?_getD]

lemma appOr_eval (n : ℕ) (C : Circuit) (a b : ℕ) (x : Fin n → Bool)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    (appOr n C a b).eval (List.ofFn x) = (W n C x a || W n C x b) := by
  have h := W_or n (appOr n C a b) x C.gates.length (by simp [appOr]) (by rw [appOr_gateAt_last])
    a b (by rw [appOr_gateAt_last]) ha hb
  rw [appOr_W_lt n C a b x a ha, appOr_W_lt n C a b x b hb] at h
  exact h

def AO (n : ℕ) (C : Circuit) : Prop :=
  ∀ k < C.gates.length, ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
    ∃ a b, (gateAt C k).inputs = [a, b] ∧ a < n + k ∧ b < n + k

def Least (n : ℕ) (C : Circuit) : Prop :=
  AO n C ∧ ∀ D : Circuit, AO n D →
    (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
    C.gates.length ≤ D.gates.length

def Bel (n : ℕ) (C : Circuit) (j : ℕ) : Prop :=
  ∀ x : Fin n → Bool, W n C x (n + j) = true → C.eval (List.ofFn x) = true

lemma alias_lt (w i u N : ℕ) (hu : u < N + 1) (hi : i < w) (hw : w ≤ N) :
    aliasWire w i u < N := by
  unfold aliasWire shiftDown
  split_ifs <;> omega

lemma erase_AO (n : ℕ) (C : Circuit) (j i : ℕ) (hA : AO n C) (hj : j < C.gates.length)
    (hi : i < n + j) : AO n (eraseC n C j i) := by
  intro k hk
  have hlen := erase_length n C j i hj
  by_cases hkj : k < j
  · rw [erase_gateAt_lt n C j i k hj hkj]; exact hA k (by omega)
  · rw [erase_gateAt_ge n C j i k hj (by omega) (by omega)]
    obtain ⟨hop, a, b, hin, ha, hb⟩ := hA (k + 1) (by omega)
    refine ⟨hop, aliasWire (n + j) i a, aliasWire (n + j) i b, by simp [aliasGate, hin], ?_, ?_⟩
    · exact alias_lt (n + j) i a (n + k) (by omega) hi (by omega)
    · exact alias_lt (n + j) i b (n + k) (by omega) hi (by omega)

lemma appOr_AO (n : ℕ) (C : Circuit) (a b : ℕ) (hA : AO n C) (ha : a < n + C.gates.length)
    (hb : b < n + C.gates.length) : AO n (appOr n C a b) := by
  intro k hk
  have hlen : (appOr n C a b).gates.length = C.gates.length + 1 := by simp [appOr]
  by_cases hkl : k < C.gates.length
  · rw [appOr_gateAt_lt n C a b k hkl]; exact hA k hkl
  · have hke : k = C.gates.length := by omega
    subst hke
    rw [appOr_gateAt_last]
    exact ⟨Or.inr rfl, a, b, rfl, ha, hb⟩

lemma trunc_AO (n : ℕ) (C : Circuit) (m : ℕ) (hA : AO n C) (hm : m ≤ C.gates.length) :
    AO n (truncC C m) := by
  intro k hk
  have hk' : k < m := by simp [truncC] at hk; omega
  have h : gateAt (truncC C m) k = gateAt C k := by
    simp [gateAt, truncC, List.getD_eq_getElem?_getD, hk']
  rw [h]; exact hA k (by omega)

lemma trunc_W (n : ℕ) (C : Circuit) (m : ℕ) (x : Fin n → Bool) (u : ℕ) (hm : m ≤ C.gates.length)
    (hu : u < n + m) : W n (truncC C m) x u = W n C x u := by
  have h := prefix_W n (C.gates.take m) [] (C.gates.drop m) C.output C.output x u
    (by rw [List.length_take]; omega)
  have e1 : (⟨C.gates.take m ++ [], C.output⟩ : Circuit) = truncC C m := by simp [truncC]
  have e2 : (⟨C.gates.take m ++ C.gates.drop m, C.output⟩ : Circuit) = C := by
    cases C; simp
  rw [e1, e2] at h
  exact h

lemma least_out (n : ℕ) (C : Circuit) (hL : Least n C)
    (hT : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true)
    (hV : ∀ u : Fin n, ∃ x : Fin n → Bool, x u = true ∧ C.eval (List.ofFn x) = false) :
    n ≤ C.output ∧ C.output + 1 = n + C.gates.length := by
  have h1 : n ≤ C.output := by
    by_contra h
    push Not at h
    obtain ⟨x, hx, hf⟩ := hV ⟨C.output, h⟩
    have h2 : W n C x C.output = true := (W_input n C x C.output h).trans hx
    have h3 : W n C x C.output = false := hf
    rw [h2] at h3
    exact absurd h3 (by simp)
  have h2 : C.output < n + C.gates.length := by
    by_contra h
    obtain ⟨x, hx⟩ := hT
    have h3 : W n C x C.output = true := hx
    simp only [W] at h3
    rw [getD_ge_length _ _ (by rw [wires_length]; omega)] at h3
    exact absurd h3 (by simp)
  refine ⟨h1, ?_⟩
  by_contra h3
  have hm : C.output - n + 1 < C.gates.length := by omega
  have hfun : ∀ x : Fin n → Bool,
      (truncC C (C.output - n + 1)).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    trunc_W n C (C.output - n + 1) x C.output (by omega) (by omega)
  have h4 := hL.2 _ (trunc_AO n C (C.output - n + 1) hL.1 (by omega)) hfun
  simp [truncC] at h4
  omega

lemma least_read (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (j : ℕ) (hj : j + 1 < C.gates.length) :
    ∃ k, j < k ∧ k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
  by_contra hno
  push Not at hno
  obtain ⟨hop, a, b, hin, ha, hb⟩ := hL.1 j (by omega)
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j a).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j a (by omega) ha x (Or.inr hno) C.output (by intro h; omega)
  have h1 := hL.2 _ (erase_AO n C j a hL.1 (by omega) ha) hfun
  have h2 := erase_length n C j a (by omega)
  omega

lemma least_nodup (n : ℕ) (C : Circuit) (hL : Least n C) (i j : ℕ) (hij : i < n + j)
    (hj : j < C.gates.length) : ∃ x : Fin n → Bool, W n C x i ≠ W n C x (n + j) := by
  by_contra hsame
  push Not at hsame
  have hfun : ∀ x : Fin n → Bool,
      (eraseC n C j i).eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    erase_wires n C j i hj hij x (Or.inl (hsame x)) C.output (fun _ => hsame x)
  have h1 := hL.2 _ (erase_AO n C j i hL.1 hj hij) hfun
  have h2 := erase_length n C j i hj
  omega

open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h

open PEqualNP.EdgeOwnership in
lemma inCone_c1 (n : ℕ) (C : Circuit) (hA : AO n C) (i k : ℕ) (hk : k < C.gates.length)
    (hm : n + i ∈ (gateAt C k).inputs) : InCone n C i k := by
  rw [inCone_iff n C i k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  exact ⟨n + i, hm, by omega, hlt, Or.inl (by omega)⟩

open PEqualNP.EdgeOwnership in
lemma inCone_c2 (n : ℕ) (C : Circuit) (hA : AO n C) (t i k : ℕ) (hk : k < C.gates.length)
    (hc : InCone n C t i) (hm : n + i ∈ (gateAt C k).inputs) : InCone n C t k := by
  rw [inCone_iff n C t k hk]
  have hlt : n + i < n + k := by
    obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
    rw [hin] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  have he : n + i - n = i := by omega
  exact ⟨n + i, hm, by omega, hlt, Or.inr (by rw [he]; exact hc)⟩


def OrStep (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  ∃ k, u = n + k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ v ∈ (gateAt C k).inputs

def OrR (n : ℕ) (C : Circuit) : ℕ → ℕ → Prop := Relation.ReflTransGen (OrStep n C)

def Leaf (n : ℕ) (C : Circuit) (v : ℕ) : Prop :=
  v < n ∨ ∃ h, v = n + h ∧ h < C.gates.length ∧ (gateAt C h).op = GateOp.and

lemma orStep_lt (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrStep n C u v) : v < u := by
  obtain ⟨k, rfl, hk, _, hv⟩ := h
  obtain ⟨_, a, b, hin, ha, hb⟩ := hA k hk
  rw [hin] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  omega

lemma orR_le (n : ℕ) (C : Circuit) (hA : AO n C) (u v : ℕ) (h : OrR n C u v) : v ≤ u := by
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => have := orStep_lt n C hA _ _ h2; omega

lemma orStep_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrStep n C u v) (hv : W n C x v = true) : W n C x u = true := by
  obtain ⟨k, rfl, hk, hop, hin⟩ := h
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA k hk
  rw [W_or n C x k hk hop a b hab ha hb]
  rw [hab] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl
  · simp [hv]
  · simp [hv]

lemma orR_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) (u v : ℕ)
    (h : OrR n C u v) (hv : W n C x v = true) : W n C x u = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head h1 _ ih => exact orStep_mono n C hA x _ _ h1 ih

lemma orR_leaf_true (n : ℕ) (C : Circuit) (hA : AO n C) (x : Fin n → Bool) :
    ∀ u, u < n + C.gates.length → W n C x u = true →
      ∃ v, OrR n C u v ∧ Leaf n C v ∧ W n C x v = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu hx
    by_cases h1 : u < n
    · exact ⟨u, Relation.ReflTransGen.refl, Or.inl h1, hx⟩
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · exact ⟨n + k, Relation.ReflTransGen.refl, Or.inr ⟨k, rfl, hk, hop⟩, hx⟩
      · rw [W_or n C x k hk hop a b hab ha hb] at hx
        simp only [Bool.or_eq_true] at hx
        rcases hx with hx | hx
        · obtain ⟨v, hv1, hv2, hv3⟩ := ih a ha (by omega) hx
          exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2, hv3⟩
        · obtain ⟨v, hv1, hv2, hv3⟩ := ih b hb (by omega) hx
          exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2, hv3⟩

lemma orR_leaf (n : ℕ) (C : Circuit) (hA : AO n C) :
    ∀ u, u < n + C.gates.length → ∃ v, OrR n C u v ∧ Leaf n C v := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu
    by_cases h1 : u < n
    · exact ⟨u, Relation.ReflTransGen.refl, Or.inl h1⟩
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · exact ⟨n + k, Relation.ReflTransGen.refl, Or.inr ⟨k, rfl, hk, hop⟩⟩
      · obtain ⟨v, hv1, hv2⟩ := ih a ha (by omega)
        exact ⟨v, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, by rw [hab]; simp⟩ hv1, hv2⟩

open PEqualNP.EdgeOwnership in
lemma orR_cone (n : ℕ) (C : Circuit) (hA : AO n C) (h u : ℕ) (hr : OrR n C u (n + h)) :
    ∀ k, u = n + k → k < C.gates.length → h = k ∨ InCone n C h k := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => intro k hk _; left; omega
  | head h1 h2 ih =>
    rename_i u c
    intro k hk hlen
    have hle := orR_le n C hA _ _ h2
    have hlt := orStep_lt n C hA _ _ h1
    obtain ⟨k', hk', _, _, hin⟩ := h1
    have hkk : k' = k := by omega
    subst hkk
    have hc : c = n + (c - n) := by omega
    rcases ih (c - n) hc (by omega) with h3 | h3
    · right
      refine inCone_c1 n C hA h k' hlen ?_
      rw [h3, ← hc]
      exact hin
    · right
      refine inCone_c2 n C hA h (c - n) k' hlen h3 ?_
      rw [← hc]
      exact hin

lemma W_mono (n : ℕ) (C : Circuit) (hA : AO n C) (x x' : Fin n → Bool)
    (hx : ∀ i, x i = true → x' i = true) :
    ∀ u, u < n + C.gates.length → W n C x u = true → W n C x' u = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    intro hu h
    by_cases h1 : u < n
    · rw [W_input n C x' u h1]
      rw [W_input n C x u h1] at h
      exact hx _ h
    · obtain ⟨k, rfl⟩ : ∃ k, u = n + k := ⟨u - n, by omega⟩
      have hk : k < C.gates.length := by omega
      obtain ⟨hop, a, b, hab, ha, hb⟩ := hA k hk
      rcases hop with hop | hop
      · rw [W_and n C x k hk hop a b hab ha hb] at h
        rw [W_and n C x' k hk hop a b hab ha hb]
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨ih a ha (by omega) h.1, ih b hb (by omega) h.2⟩
      · rw [W_or n C x k hk hop a b hab ha hb] at h
        rw [W_or n C x' k hk hop a b hab ha hb]
        simp only [Bool.or_eq_true] at h ⊢
        rcases h with h | h
        · exact Or.inl (ih a ha (by omega) h)
        · exact Or.inr (ih b hb (by omega) h)

open PEqualNP.EdgeOwnership in
lemma leafg (n : ℕ) (C : Circuit) (hA : AO n C) (g : ℕ)
    (hT : ∀ h j, j < C.gates.length → (gateAt C j).op = GateOp.and → InCone n C h j →
      (gateAt C h).op = GateOp.and → ¬ Bel n C h)
    (hJ : ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ Bel n C h → h = g)
    (j p : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hp : p ∈ (gateAt C j).inputs) (v : ℕ) (hr : OrR n C p v) (hl : Leaf n C v) :
    v < n ∨ v = n + g := by
  rcases hl with hl | ⟨h, rfl, hh, hhop⟩
  · exact Or.inl hl
  · right
    have hle := orR_le n C hA _ _ hr
    have hplt : p < n + j := by
      obtain ⟨_, a, b, hin, ha, hb⟩ := hA j hj
      rw [hin] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      omega
    have hp' : p = n + (p - n) := by omega
    have hc : InCone n C h j := by
      rcases orR_cone n C hA h p hr (p - n) hp' (by omega) with h3 | h3
      · refine inCone_c1 n C hA h j hj ?_
        rw [h3, ← hp']
        exact hp
      · refine inCone_c2 n C hA h (p - n) j hj h3 ?_
        rw [← hp']
        exact hp
    rw [hJ h hh hhop (hT h j hj hop hc hhop)]

lemma up (n : ℕ) (C : Circuit) (hL : Least n C) (hout : C.output + 1 = n + C.gates.length)
    (g : ℕ) (hg : ¬ Bel n C g) :
    ∀ d k, k + d = C.gates.length → k < C.gates.length →
      (∀ x, W n C x (n + g) = true → W n C x (n + k) = true) →
      ∃ h p, h < C.gates.length ∧ (gateAt C h).op = GateOp.and ∧ p ∈ (gateAt C h).inputs ∧
        OrR n C p (n + k) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro k hd hk hgk
    by_cases hlast : k + 1 = C.gates.length
    · exfalso
      apply hg
      intro x hx
      have h1 := hgk x hx
      have ho : C.output = n + k := by omega
      have h2 : W n C x C.output = true := by rw [ho]; exact h1
      exact h2
    · obtain ⟨r, hkr, hr, hin⟩ := least_read n C hL hout k (by omega)
      obtain ⟨hop, _⟩ := hL.1 r hr
      rcases hop with hop | hop
      · exact ⟨r, n + k, hr, hop, hin, Relation.ReflTransGen.refl⟩
      · obtain ⟨h, p, hh, hhop, hp, hpr⟩ := ih (C.gates.length - r) (by omega) r (by omega) hr
          (fun x hx => orStep_mono n C hL.1 x _ _ ⟨r, rfl, hr, hop, hin⟩ (hgk x hx))
        exact ⟨h, p, hh, hhop, hp, Relation.ReflTransGen.tail hpr ⟨r, rfl, hr, hop, hin⟩⟩

lemma pair_le (n : ℕ) (u : Fin n) (x : Fin n → Bool) (hx : x u = true) :
    ∀ i, PEqualNP.EdgeOwnership.pairInput u u i = true → x i = true := by
  intro i hi
  simp only [PEqualNP.EdgeOwnership.pairInput, or_self, decide_eq_true_eq] at hi
  rw [hi]
  exact hx

open PEqualNP.EdgeOwnership in
theorem part1 (n : ℕ) (C : Circuit) (hL : Least n C)
    (hout : C.output + 1 = n + C.gates.length) (g m y : ℕ)
    (hT : ∀ h j, j < C.gates.length → (gateAt C j).op = GateOp.and → InCone n C h j →
      (gateAt C h).op = GateOp.and → ¬ Bel n C h)
    (hJ : ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ Bel n C h → h = g)
    (hg : ¬ Bel n C g) (hm : m < C.gates.length) (hmop : (gateAt C m).op = GateOp.or)
    (hgm : n + g ∈ (gateAt C m).inputs) (hy : y ∈ (gateAt C m).inputs) (hyg : y ≠ n + g) :
    ∃ u : Fin n, OrR n C y u.val ∧ W n C (pairInput u u) (n + g) = false := by
  have hA := hL.1
  by_contra hno
  push Not at hno
  obtain ⟨_, a, b, hab, ha, hb⟩ := hA m hm
  have hylt : y < n + m := by
    rw [hab] at hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    omega
  have hglt : n + g < n + m := by
    rw [hab] at hgm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hgm
    omega
  have hWm : ∀ x, W n C x (n + m) = (W n C x (n + g) || W n C x y) := by
    intro x
    rw [W_or n C x m hm hmop a b hab ha hb]
    rw [hab] at hy hgm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy hgm
    rcases hgm with h1 | h1 <;> rcases hy with h2 | h2
    · exact absurd (h2.trans h1.symm) hyg
    · rw [← h1, ← h2]
    · rw [← h1, ← h2, Bool.or_comm]
    · exact absurd (h2.trans h1.symm) hyg
  have hgm' : ∀ x, W n C x (n + g) = true → W n C x (n + m) = true := by
    intro x hx
    rw [hWm x, hx]
    rfl
  obtain ⟨h, p, hh, hhop, hp, hpm⟩ := up n C hL hout g hg (C.gates.length - m) m (by omega) hm hgm'
  have hmy : OrR n C (n + m) y := Relation.ReflTransGen.single ⟨m, rfl, hm, hmop, hy⟩
  have hyle : ∀ x, W n C x y = true → W n C x (n + g) = true := by
    intro x hx
    obtain ⟨v, hv1, hv2, hv3⟩ := orR_leaf_true n C hA x y (by omega) hx
    rcases leafg n C hA g hT hJ h p hh hhop hp v ((hpm.trans hmy).trans hv1) hv2 with h1 | h1
    · have h2 := hno ⟨v, h1⟩ hv1
      simp only [ne_eq, Bool.not_eq_false] at h2
      have h3 : x ⟨v, h1⟩ = true := by
        rw [← W_input n C x v h1]
        exact hv3
      exact W_mono n C hA _ x (pair_le n ⟨v, h1⟩ x h3) (n + g) (by omega) h2
    · rw [← h1]
      exact hv3
  obtain ⟨x, hx⟩ := least_nodup n C hL (n + g) m hglt hm
  apply hx
  rw [hWm x]
  cases hgx : W n C x (n + g) with
  | true => rfl
  | false =>
    cases hyx : W n C x y with
    | true => rw [hyle x hyx] at hgx; exact absurd hgx (by simp)
    | false => rfl

open PEqualNP.EdgeOwnership in
theorem part2 (n : ℕ) (C : Circuit) (hL : Least n C) (g m y a p q : ℕ)
    (hT : ∀ h j, j < C.gates.length → (gateAt C j).op = GateOp.and → InCone n C h j →
      (gateAt C h).op = GateOp.and → ¬ Bel n C h)
    (hJ : ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ Bel n C h → h = g)
    (hg : ¬ Bel n C g) (hm : m < C.gates.length) (hmop : (gateAt C m).op = GateOp.or)
    (hgm : n + g ∈ (gateAt C m).inputs) (hy : y ∈ (gateAt C m).inputs)
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (hin : (gateAt C a).inputs = [p, q] ∨ (gateAt C a).inputs = [q, p])
    (hbel : Bel n C a) (hpm : OrR n C p (n + m))
    (hV : ∀ z : Fin n, C.eval (List.ofFn (pairInput z z)) = false)
    (u : Fin n) (hu : OrR n C y u.val) :
    OrR n C p u.val ∧
    (∀ z : Fin n, OrR n C q z.val →
      C.eval (List.ofFn (pairInput u z)) = true ∧
      ∀ x : Fin n → Bool, W n C x (n + g) = true → x z = true → C.eval (List.ofFn x) = true) ∧
    (∀ v w : Fin n, W n C (pairInput v w) (n + a) = true →
      (∀ v' w' : Fin n, OrR n C p v'.val → OrR n C q w'.val →
        ¬ ((v = v' ∧ w = w') ∨ (v = w' ∧ w = v'))) →
      W n C (pairInput v w) (n + g) = true ∧ ∃ z : Fin n, OrR n C q z.val ∧ (z = v ∨ z = w)) := by
  have hA := hL.1
  obtain ⟨_, a1, b1, hab, ha1, hb1⟩ := hA a ha
  have hpq : p < n + a ∧ q < n + a := by
    rcases hin with h | h
    · rw [h] at hab
      simp only [List.cons.injEq, and_true] at hab
      omega
    · rw [h] at hab
      simp only [List.cons.injEq, and_true] at hab
      omega
  have hmem : ∀ c, c = p ∨ c = q → c ∈ (gateAt C a).inputs := by
    intro c hc
    rcases hin with h | h <;> rw [h] <;> simp <;> tauto
  have hWa : ∀ x, W n C x (n + a) = (W n C x p && W n C x q) := by
    intro x
    rcases hin with h | h
    · exact W_and n C x a ha hop p q h hpq.1 hpq.2
    · rw [W_and n C x a ha hop q p h hpq.2 hpq.1, Bool.and_comm]
  have hmy : OrR n C (n + m) y := Relation.ReflTransGen.single ⟨m, rfl, hm, hmop, hy⟩
  have hmg : OrR n C (n + m) (n + g) := Relation.ReflTransGen.single ⟨m, rfl, hm, hmop, hgm⟩
  have hpu : OrR n C p u.val := (hpm.trans hmy).trans hu
  have hpg : OrR n C p (n + g) := hpm.trans hmg
  have hqg : ¬ OrR n C q (n + g) := by
    intro hq
    apply hg
    intro x hx
    apply hbel x
    rw [hWa x, orR_mono n C hA x _ _ hpg hx, orR_mono n C hA x _ _ hq hx]
    rfl
  have hvar : ∀ (x : Fin n → Bool) (c : ℕ), c = p ∨ c = q → W n C x c = true →
      W n C x (n + g) = false ∨ c = q →
      ∃ z : Fin n, OrR n C c z.val ∧ x z = true := by
    intro x c hc hx hgc
    have hclt : c < n + a := by rcases hc with rfl | rfl <;> omega
    obtain ⟨v, hv1, hv2, hv3⟩ := orR_leaf_true n C hA x c (by omega) hx
    rcases leafg n C hA g hT hJ a c ha hop (hmem c hc) v hv1 hv2 with h1 | h1
    · refine ⟨⟨v, h1⟩, hv1, ?_⟩
      rw [← W_input n C x v h1]
      exact hv3
    · exfalso
      rcases hgc with h2 | h2
      · rw [h1, h2] at hv3
        exact absurd hv3 (by simp)
      · rw [h1, h2] at hv1
        exact hqg hv1
  have hpair : ∀ v w z : Fin n, pairInput v w z = true → z = v ∨ z = w := by
    intro v w z hz
    simpa [pairInput] using hz
  have hpair' : ∀ v w : Fin n, pairInput v w v = true ∧ pairInput v w w = true := by
    intro v w
    simp [pairInput]
  have hWin : ∀ (x : Fin n → Bool) (c : ℕ) (z : Fin n), c < n + C.gates.length →
      OrR n C c z.val → x z = true → W n C x c = true := by
    intro x c z _ hcz hz
    refine orR_mono n C hA x _ _ hcz ?_
    rw [W_input n C x z.val z.isLt]
    exact hz
  refine ⟨hpu, ?_, ?_⟩
  · intro z hz
    refine ⟨?_, ?_⟩
    · apply hbel
      rw [hWa, hWin _ p u (by omega) hpu (hpair' u z).1, hWin _ q z (by omega) hz (hpair' u z).2]
      rfl
    · intro x hx hxz
      apply hbel
      rw [hWa, orR_mono n C hA x _ _ hpg hx, hWin x q z (by omega) hz hxz]
      rfl
  · intro v w hvw hno
    rw [hWa] at hvw
    simp only [Bool.and_eq_true] at hvw
    obtain ⟨z, hz1, hz2⟩ := hvar _ q (Or.inr rfl) hvw.2 (Or.inr rfl)
    have hzvw := hpair v w z hz2
    refine ⟨?_, z, hz1, hzvw⟩
    by_contra hgf
    simp only [Bool.not_eq_true] at hgf
    obtain ⟨z', hz'1, hz'2⟩ := hvar _ p (Or.inl rfl) hvw.1 (Or.inl hgf)
    have hz'vw := hpair v w z' hz'2
    have hne : z' ≠ z := by
      rintro rfl
      have h1 : C.eval (List.ofFn (pairInput z' z')) = true := by
        apply hbel
        rw [hWa, hWin _ p z' (by omega) hz'1 (hpair' z' z').1,
          hWin _ q z' (by omega) hz1 (hpair' z' z').1]
        rfl
      rw [hV z'] at h1
      exact absurd h1 (by simp)
    apply hno z' z hz'1 hz1
    rcases hz'vw with h1 | h1 <;> rcases hzvw with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h2.symm, h1.symm⟩
    · exact absurd (h1.trans h2.symm) hne

open PEqualNP.EdgeOwnership in
lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

open PEqualNP.EdgeOwnership in
lemma graphFun_diag {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    graphFun G ∅ (pairInput u u) = false := by
  cases h : graphFun G ∅ (pairInput u u) with
  | false => rfl
  | true => exact absurd ((graphFun_pair G u u).mp h) G.irrefl

open PEqualNP.EdgeOwnership in
lemma out_last (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : Least n C) (hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x)
    (hE : G.edgeFinset.Nonempty) : C.output + 1 = n + C.gates.length := by
  refine (least_out n C hL ?_ ?_).2
  · obtain ⟨e, he⟩ := hE
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      exact ⟨pairInput u v, by rw [hF]; exact (graphFun_pair G u v).mpr he⟩
  · intro u
    refine ⟨pairInput u u, (pairInput_true u u u).mpr (Or.inl rfl), ?_⟩
    rw [hF]
    exact graphFun_diag G u

open PEqualNP.EdgeOwnership in
theorem main_abs (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : Least n C) (hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x)
    (hE : G.edgeFinset.Nonempty) (g m y : ℕ)
    (hT : ∀ h j, j < C.gates.length → (gateAt C j).op = GateOp.and → InCone n C h j →
      (gateAt C h).op = GateOp.and → ¬ Bel n C h)
    (hJ : ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ Bel n C h → h = g)
    (hg : ¬ Bel n C g) (hm : m < C.gates.length) (hmop : (gateAt C m).op = GateOp.or)
    (hgm : n + g ∈ (gateAt C m).inputs) (hy : y ∈ (gateAt C m).inputs) (hyg : y ≠ n + g) :
    (∃ u : Fin n, OrR n C y u.val ∧ gateVal n C g (pairInput u u) = false) ∧
    ∀ u : Fin n, OrR n C y u.val → ∀ a p q : ℕ, a < C.gates.length →
      (gateAt C a).op = GateOp.and →
      ((gateAt C a).inputs = [p, q] ∨ (gateAt C a).inputs = [q, p]) →
      (∀ x : Fin n → Bool, gateVal n C a x = true → graphFun G ∅ x = true) →
      OrR n C p (n + m) →
      OrR n C p u.val ∧
      (∀ z : Fin n, OrR n C q z.val → G.Adj u z ∧
        ∀ x : Fin n → Bool, gateVal n C g x = true → x z = true → graphFun G ∅ x = true) ∧
      (∀ v w : Fin n, gateVal n C a (pairInput v w) = true →
        (∀ v' w' : Fin n, OrR n C p v'.val → OrR n C q w'.val →
          ¬ ((v = v' ∧ w = w') ∨ (v = w' ∧ w = v'))) →
        gateVal n C g (pairInput v w) = true ∧
          ∃ z : Fin n, OrR n C q z.val ∧ (z = v ∨ z = w)) := by
  have hout := out_last n G C hL hF hE
  refine ⟨part1 n C hL hout g m y hT hJ hg hm hmop hgm hy hyg, ?_⟩
  intro u hu a p q ha hop hin hbelG hpm
  have hbel : Bel n C a := by
    intro x hx
    rw [hF]
    exact hbelG x hx
  have hV : ∀ z : Fin n, C.eval (List.ofFn (pairInput z z)) = false := by
    intro z
    rw [hF]
    exact graphFun_diag G z
  obtain ⟨h1, h2, h3⟩ := part2 n C hL g m y a p q hT hJ hg hm hmop hgm hy ha hop hin hbel hpm hV u hu
  refine ⟨h1, ?_, h3⟩
  intro z hz
  obtain ⟨h4, h5⟩ := h2 z hz
  refine ⟨?_, ?_⟩
  · rw [hF] at h4
    exact (graphFun_pair G u z).mp h4
  · intro x hx hxz
    rw [← hF]
    exact h5 x hx hxz

lemma not_cross {n : ℕ} (S0 S1 : Finset (Fin n)) (v w : Fin n)
    (h : s(v, w) ∉ (S0 ×ˢ S1).image (fun p => s(p.1, p.2))) :
    ∀ v' w' : Fin n, ((v' ∈ S0 ∧ w' ∈ S1) ∨ (v' ∈ S1 ∧ w' ∈ S0)) →
      ¬ ((v = v' ∧ w = w') ∨ (v = w' ∧ w = v')) := by
  intro v' w' hm he
  apply h
  rw [Finset.mem_image]
  rcases hm with ⟨h0, h1⟩ | ⟨h1, h0⟩
  · refine ⟨(v', w'), Finset.mem_product.mpr ⟨h0, h1⟩, ?_⟩
    rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
    · rw [e1, e2]
      exact Sym2.eq_swap
  · refine ⟨(w', v'), Finset.mem_product.mpr ⟨h0, h1⟩, ?_⟩
    rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
      exact Sym2.eq_swap
    · rw [e1, e2]

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) :
    ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk i hc
    rw [inCone_iff n C i k hk] at hc
    obtain ⟨w, _, hn, hlt, h | h⟩ := hc
    · omega
    · have := ih (w - n) (by omega) (by omega) i h
      omega

open PEqualNP.CleanedNonEdge in
lemma cnFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma cnStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases hop : g.op = GateOp.or
  · simp only [orStep, hop, ↓reduceIte, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_refl cs.length), Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some, List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq,
      true_and]
    constructor
    · rintro (h | ⟨w, ⟨hw, hn, hlt⟩, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w, hw, hn, hlt, h⟩
    · rintro (h | ⟨w, hw, hn, hlt, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, h⟩
  · simp only [orStep, hop, ↓reduceIte, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (le_refl cs.length), Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some, List.mem_cons, List.not_mem_nil, or_false, false_and]

open PEqualNP.CleanedNonEdge in
lemma cnStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma cnFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact cnStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_iff (n : ℕ) (C : Circuit) (g k : ℕ) (hk : k < C.gates.length) :
    g ∈ (orSets n C).getD k [] ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ g ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [cnFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, cnFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, cnFold_getD_lt n post _ m (by omega)]
    exact cnStep_getD_lt n _ gk m (by omega)
  have h3 := cnStep_mem_last n (pre.foldl (orStep n) []) gk g
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact h⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact h⟩

open PEqualNP.CleanedNonEdge in
lemma orSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp only [orSets]
  rw [cnFold_length]
  simp

open PEqualNP.CleanedNonEdge in
lemma reaches_to (n : ℕ) (C : Circuit) :
    ∀ k g, g ∈ (orSets n C).getD k [] → g < C.gates.length ∧ OrR n C (n + k) (n + g) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro g hg
    have hk : k < C.gates.length := by
      by_contra hk
      have hnone : (orSets n C)[k]? = none :=
        List.getElem?_eq_none (by rw [orSets_len]; omega)
      rw [List.getD_eq_getElem?_getD, hnone] at hg
      simp at hg
    rw [orSets_iff n C g k hk] at hg
    rcases hg with rfl | ⟨hop, w, hw, hn, hlt, h⟩
    · exact ⟨hk, Relation.ReflTransGen.refl⟩
    · obtain ⟨h4, h5⟩ := ih (w - n) (by omega) g h
      have hw' : n + (w - n) = w := by omega
      rw [hw'] at h5
      exact ⟨h4, Relation.ReflTransGen.head ⟨k, rfl, hk, hop, hw⟩ h5⟩

open PEqualNP.CleanedNonEdge in
lemma orReaches_iff (n : ℕ) (C : Circuit) (hA : AO n C) (w g : ℕ) :
    OrReaches n C w g ↔ (n ≤ w ∧ g < C.gates.length ∧ OrR n C w (n + g)) := by
  constructor
  · rintro ⟨hn, h⟩
    obtain ⟨h1, h2⟩ := reaches_to n C (w - n) g h
    have hw' : n + (w - n) = w := by omega
    rw [hw'] at h2
    exact ⟨hn, h1, h2⟩
  · rintro ⟨hn, hg, h⟩
    refine ⟨hn, ?_⟩
    clear hn
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
      have he : n + g - n = g := by omega
      rw [he, orSets_iff n C g g hg]
      exact Or.inl rfl
    | head h1 h2 ih =>
      rename_i u c
      have hle := orR_le n C hA _ _ h2
      have hlt := orStep_lt n C hA _ _ h1
      obtain ⟨k, rfl, hk, hop, hin⟩ := h1
      have he : n + k - n = k := by omega
      rw [he, orSets_iff n C g k hk]
      exact Or.inr ⟨hop, c, hin, by omega, hlt, ih⟩

lemma orIn_iff (n : ℕ) (C : Circuit) (hA : AO n C) (w : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C w ↔ OrR n C w u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, hk, hr, hop, hin⟩)
    · rw [h]
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.tail ((orReaches_iff n C hA w k).mp hr).2.2 ⟨k, rfl, hk, hop, hin⟩
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with h1 | ⟨c, h1, ⟨k, rfl, hk, hop, hin⟩⟩
    · exact Or.inl h1
    · have hle := orR_le n C hA _ _ h1
      exact Or.inr ⟨k, hk, (orReaches_iff n C hA w k).mpr ⟨by omega, hk, h1⟩, hop, hin⟩

lemma ao_of (n : ℕ) (C : Circuit) (h : PEqualNP.TopForm.IsAO2 n C) : AO n C := by
  obtain ⟨h1, h2, h3⟩ := h
  intro k hk
  have hmem : gateAt C k ∈ C.gates := by
    rw [gateAt_eq C k hk]
    exact List.getElem_mem hk
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h3 _ hmem)
  refine ⟨h1 _ hmem, a, b, hab, ?_, ?_⟩
  · exact h2 k hk a (by rw [hab]; simp)
  · exact h2 k hk b (by rw [hab]; simp)

lemma ao_to (n : ℕ) (D : Circuit) (h : AO n D) : PEqualNP.TopForm.IsAO2 n D := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    rw [← gateAt_eq D k hk]
    exact (h k hk).1
  · intro j hj i hi
    obtain ⟨_, a, b, hab, ha, hb⟩ := h j hj
    rw [hab] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
    obtain ⟨_, a, b, hab, _⟩ := h k hk
    rw [← gateAt_eq D k hk, hab]
    rfl

lemma fin2_cases (t : Fin 2) : (t = 0 ∧ 1 - t = 1) ∨ (t = 1 ∧ 1 - t = 0) := by
  revert t
  decide

lemma mem_wmax {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (z : Fin n)
    (h : ∀ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C g x = true → x z = true →
      graphFun G ∅ x = true) : z ∈ PEqualNP.TopForm.wmax G C g := by
  simp only [PEqualNP.TopForm.wmax, Finset.mem_filter, Finset.mem_univ, true_and]
  exact h

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge in
theorem final (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hE : G.edgeFinset.Nonempty) (hLeast : PEqualNP.TopForm.IsLeastAO G C)
    (hTop : PEqualNP.TopForm.TopForm G C) (g : ℕ) (hjunk : PEqualNP.TopForm.junk G C = {g})
    (m : ℕ) (hmix : m ∈ PEqualNP.TopForm.mixing G C)
    (hgm : n + g ∈ (gateAt C m).inputs) (y : ℕ) (hy : y ∈ (gateAt C m).inputs)
    (hyg : y ≠ n + g) :
    (∃ u ∈ PEqualNP.TopForm.orIn n C y, gateVal n C g (pairInput u u) = false) ∧
      ∀ u ∈ PEqualNP.TopForm.orIn n C y, ∀ a ∈ PEqualNP.TopForm.tops G C, ∀ t : Fin 2,
        OrReaches n C (PEqualNP.TopForm.opnd C a t) m →
          u ∈ PEqualNP.TopForm.side (n := n) C a t ∧
          (∀ v w : Fin n, G.Adj v w →
            gateVal n C a (pairInput v w) = true →
            s(v, w) ∉ (PEqualNP.TopForm.side (n := n) C a 0 ×ˢ
              PEqualNP.TopForm.side (n := n) C a 1).image (fun p => s(p.1, p.2)) →
            gateVal n C g (pairInput v w) = true ∧
            ∃ z ∈ PEqualNP.TopForm.wmax G C g, G.Adj u z ∧ (z = v ∨ z = w)) ∧
          (PEqualNP.TopForm.side (n := n) C a t = {u} →
            PEqualNP.TopForm.side (n := n) C a (1 - t) ⊆ PEqualNP.TopForm.wmax G C g) := by
  have hA : AO n C := ao_of n C hLeast.1
  have hF : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x :=
    fun x => congrFun hLeast.2.1 x
  have hL : Least n C := ⟨hA, fun D hD hfun =>
    hLeast.2.2 D (ao_to n D hD) (funext fun x => (hfun x).trans (hF x))⟩
  have hgj : g ∈ PEqualNP.TopForm.junk G C := by
    rw [hjunk]
    exact Finset.mem_singleton_self g
  have hgj2 : (gateAt C g).op = GateOp.and ∧ (g < C.gates.length ∧
      ∃ x : Fin n → Bool, gateVal n C g x = true ∧ graphFun G ∅ x = false) :=
    (Finset.mem_filter.mp hgj).2
  obtain ⟨hgop, hglen, x0, hx0, hx0F⟩ := hgj2
  have hg : ¬ Bel n C g := by
    intro hb
    have h1 := hb x0 hx0
    rw [hF, hx0F] at h1
    exact absurd h1 (by simp)
  have hJ : ∀ h, h < C.gates.length → (gateAt C h).op = GateOp.and → ¬ Bel n C h → h = g := by
    intro h hh hhop hnb
    have h1 : h ∈ PEqualNP.TopForm.junk G C := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, ?_⟩
      show (gateAt C h).op = GateOp.and ∧ (h < C.gates.length ∧
        ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false)
      refine ⟨hhop, hh, ?_⟩
      by_contra hno
      push Not at hno
      apply hnb
      intro x hx
      rw [hF]
      have h2 := hno x hx
      simpa using h2
    rw [hjunk] at h1
    exact Finset.mem_singleton.mp h1
  have hT : ∀ h j, j < C.gates.length → (gateAt C j).op = GateOp.and → InCone n C h j →
      (gateAt C h).op = GateOp.and → ¬ Bel n C h := by
    intro h j hj hjop hc hhop hb
    have hlt := inCone_lt n C j hj h hc
    exact hTop h (by omega) j hj hhop (fun x hx => by rw [← hF]; exact hb x hx) hjop hc
  have hmix1 : m ∈ PEqualNP.TopForm.orN G C := (Finset.mem_filter.mp hmix).1
  simp only [PEqualNP.TopForm.orN, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
    Finset.mem_range] at hmix1
  have hm : m < C.gates.length := hmix1.1
  have hmop : (gateAt C m).op = GateOp.or := hmix1.2.1
  obtain ⟨h1, h2⟩ := main_abs n G C hL hF hE g m y hT hJ hg hm hmop hgm hy hyg
  refine ⟨?_, ?_⟩
  · obtain ⟨u, hu1, hu2⟩ := h1
    exact ⟨u, (orIn_iff n C hA y u).mpr hu1, hu2⟩
  · intro u hu a ha t hreach
    simp only [PEqualNP.TopForm.tops, PEqualNP.TopForm.gatesWhere, Finset.mem_filter,
      Finset.mem_range] at ha
    have halen : a < C.gates.length := ha.1
    have haop : (gateAt C a).op = GateOp.and := ha.2.1
    have habel : ∀ x : Fin n → Bool, gateVal n C a x = true → graphFun G ∅ x = true := ha.2.2
    obtain ⟨_, a1, b1, hab, ha1, hb1⟩ := hA a halen
    have ho0 : PEqualNP.TopForm.opnd C a 0 = a1 := by simp [PEqualNP.TopForm.opnd, hab]
    have ho1 : PEqualNP.TopForm.opnd C a 1 = b1 := by simp [PEqualNP.TopForm.opnd, hab]
    have hab' : (gateAt C a).inputs =
        [PEqualNP.TopForm.opnd C a 0, PEqualNP.TopForm.opnd C a 1] := by
      rw [ho0, ho1]
      exact hab
    have hs : ∀ (s : Fin 2) (z : Fin n), z ∈ PEqualNP.TopForm.side (n := n) C a s ↔
        OrR n C (PEqualNP.TopForm.opnd C a s) z.val := fun s z => orIn_iff n C hA _ z
    have huy := (orIn_iff n C hA y u).mp hu
    rcases fin2_cases t with ⟨rfl, ht⟩ | ⟨rfl, ht⟩
    · rw [ht]
      have hpm := ((orReaches_iff n C hA _ m).mp hreach).2.2
      obtain ⟨k1, k2, k3⟩ := h2 u huy a (PEqualNP.TopForm.opnd C a 0)
        (PEqualNP.TopForm.opnd C a 1) halen haop (Or.inl hab') habel hpm
      refine ⟨(hs 0 u).mpr k1, ?_, ?_⟩
      · intro v w _ hvw hnot
        obtain ⟨k4, z, hz1, hz2⟩ := k3 v w hvw (fun v' w' hv' hw' =>
          not_cross _ _ v w hnot v' w' (Or.inl ⟨(hs 0 v').mpr hv', (hs 1 w').mpr hw'⟩))
        obtain ⟨k5, k6⟩ := k2 z hz1
        exact ⟨k4, z, mem_wmax G C g z k6, k5, hz2⟩
      · intro _ z hz
        obtain ⟨_, k6⟩ := k2 z ((hs 1 z).mp hz)
        exact mem_wmax G C g z k6
    · rw [ht]
      have hpm := ((orReaches_iff n C hA _ m).mp hreach).2.2
      obtain ⟨k1, k2, k3⟩ := h2 u huy a (PEqualNP.TopForm.opnd C a 1)
        (PEqualNP.TopForm.opnd C a 0) halen haop (Or.inr hab') habel hpm
      refine ⟨(hs 1 u).mpr k1, ?_, ?_⟩
      · intro v w _ hvw hnot
        obtain ⟨k4, z, hz1, hz2⟩ := k3 v w hvw (fun v' w' hv' hw' =>
          not_cross _ _ v w hnot v' w' (Or.inr ⟨(hs 1 v').mpr hv', (hs 0 w').mpr hw'⟩))
        obtain ⟨k5, k6⟩ := k2 z hz1
        exact ⟨k4, z, mem_wmax G C g z k6, k5, hz2⟩
      · intro _ z hz
        obtain ⟨_, k6⟩ := k2 z ((hs 0 z).mp hz)
        exact mem_wmax G C g z k6

end PEqualNP.Outside.L_meta_1506

theorem PEqualNP.Outside.L_meta_1506 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit),
  PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
  PEqualNP.TopForm.TopForm G C → ∀ (g : ℕ), PEqualNP.TopForm.junk G C = {g} →
    ∀ m ∈ PEqualNP.TopForm.mixing G C, n + g ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs →
    ∀ y ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C m).inputs, y ≠ n + g →
      (∃ u ∈ PEqualNP.TopForm.orIn n C y,
        PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput u u) = false) ∧
      ∀ u ∈ PEqualNP.TopForm.orIn n C y, ∀ a ∈ PEqualNP.TopForm.tops G C, ∀ t : Fin 2,
        PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C a t) m →
          u ∈ PEqualNP.TopForm.side (n := n) C a t ∧
          (∀ v w : Fin n, G.Adj v w →
            PEqualNP.EdgeOwnership.gateVal n C a (PEqualNP.EdgeOwnership.pairInput v w) = true →
            s(v, w) ∉ (PEqualNP.TopForm.side (n := n) C a 0 ×ˢ PEqualNP.TopForm.side (n := n) C a 1).image
              (fun p => s(p.1, p.2)) →
            PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput v w) = true ∧
            ∃ z ∈ PEqualNP.TopForm.wmax G C g, G.Adj u z ∧ (z = v ∨ z = w)) ∧
          (PEqualNP.TopForm.side (n := n) C a t = {u} →
            PEqualNP.TopForm.side (n := n) C a (1 - t) ⊆ PEqualNP.TopForm.wmax G C g) := by
  intro n G _ C _ hE hLeast hTop g hjunk m hmix hgm y hy hyg
  exact PEqualNP.Outside.L_meta_1506.final n G C hE hLeast hTop g hjunk m hmix hgm y hy hyg
