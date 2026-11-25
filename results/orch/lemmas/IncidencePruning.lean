import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.Pruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl wireStep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wireStep_prefix (gs : List Gate) (acc : List Bool) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl wireStep acc).getD w false = acc.getD w false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (wireStep acc g).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (wireStep acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_left hw]

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  exact foldl_wireStep_length C.gates x

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wireVal n C w x = x ⟨w, hw⟩ := by
  unfold wireVal Circuit.wires
  have hw' : w < (List.ofFn x).length := by simp [hw]
  have h1 := foldl_wireStep_prefix C.gates (List.ofFn x) w hw'
  change (C.gates.foldl wireStep (List.ofFn x)).getD w false = x ⟨w, hw⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw']
  simp

lemma wireVal_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hRB : ReadsBack n C) :
    wireVal n C (n + k) x =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => wireVal n C u x) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take k).foldl wireStep (List.ofFn x) with hacc
  have hacc_len : acc.length = n + k := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn, List.length_take]
    omega
  have hpref : ∀ u < n + k, wireVal n C u x = acc.getD u false := by
    intro u hu
    unfold wireVal Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD u false = acc.getD u false
    conv_lhs => rw [← List.take_append_drop k C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_wireStep_prefix (C.gates.drop k) acc u (by omega)
  have hval : wireVal n C (n + k) x =
      C.gates[k].op.eval (C.gates[k].inputs.map fun u => acc.getD u false) := by
    unfold wireVal Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD (n + k) false = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + k < (wireStep acc C.gates[k]).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_wireStep_prefix (C.gates.drop (k + 1)) (wireStep acc C.gates[k]) (n + k) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + k),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq_getElem C k hk]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq_getElem C k hk] at hu
  exact (hpref u (hRB k hk u hu)).symm

def remap (n g r w : ℕ) : ℕ :=
  if w < n + g then w
  else if w = n + g then r
  else w - 1

def origWire (n g w : ℕ) : ℕ :=
  if w < n + g then w else w + 1

def mapGate (f : ℕ → ℕ) (gt : Gate) : Gate :=
  ⟨gt.op, gt.inputs.map f⟩

def delGate (n g r : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx g).map (mapGate (remap n g r)), remap n g r C.output⟩

lemma delGate_length (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length) :
    (delGate n g r C).gates.length = C.gates.length - 1 := by
  simp [delGate, List.length_eraseIdx_of_lt hg]

lemma delGate_gateAt (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (delGate n g r C) k =
      mapGate (remap n g r) (gateAt C (if k < g then k else k + 1)) := by
  have hk' : k < (delGate n g r C).gates.length := by
    rw [delGate_length n g r C hg]; exact hk
  rw [gateAt_eq_getElem (delGate n g r C) k hk']
  have hk_e : k < (C.gates.eraseIdx g).length := by
    rw [List.length_eraseIdx_of_lt hg]; exact hk
  simp only [delGate, List.getElem_map]
  split_ifs with hkg
  · rw [List.getElem_eraseIdx_of_lt hk_e hkg, gateAt_eq_getElem C k (by omega)]
  · rw [List.getElem_eraseIdx_of_ge hk_e (by omega), gateAt_eq_getElem C (k + 1) (by omega)]

lemma delGate_isAO2 (n g r : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hg : g < C.gates.length) (hr : r < n + g) :
    IsAO2 n (delGate n g r C) := by
  rcases hAO with ⟨hAOOnly, hRB, hLen2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    simp only [delGate, List.mem_map] at hgt
    obtain ⟨gt0, hgt0, rfl⟩ := hgt
    exact hAOOnly gt0 (List.mem_of_mem_eraseIdx hgt0)
  · intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap
      split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap
      split_ifs <;> omega
  · intro gt hgt
    simp only [delGate, List.mem_map] at hgt
    obtain ⟨gt0, hgt0, rfl⟩ := hgt
    simp only [mapGate, List.length_map]
    exact hLen2 gt0 (List.mem_of_mem_eraseIdx hgt0)

lemma delGate_output_lt (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (hr : r < n + g) (hout : C.output < n + C.gates.length) :
    (delGate n g r C).output < n + (delGate n g r C).gates.length := by
  rw [delGate_length n g r C hg]
  simp only [delGate, remap]
  split_ifs <;> omega

lemma origWire_remap_ne (n g r u : ℕ) (hne : u ≠ n + g) :
    origWire n g (remap n g r u) = u := by
  unfold origWire remap
  split_ifs <;> omega

lemma origWire_remap_eq (n g r : ℕ) (hr : r < n + g) :
    origWire n g (remap n g r (n + g)) = r := by
  unfold origWire remap
  split_ifs <;> omega

lemma delGate_wireVal_eq (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g)
    (hmatch : wireVal n C (n + g) x = wireVal n C r x) :
    ∀ w < n + (delGate n g r C).gates.length,
      wireVal n (delGate n g r C) w x = wireVal n C (origWire n g w) x := by
  have hAO_rb : ReadsBack n (delGate n g r C) := by
    intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g r C) x w hwn]
      have horig : origWire n g w = w := by unfold origWire; split_ifs <;> omega
      rw [horig, wireVal_input n C x w hwn]
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by omega
      have hk_lt' : k < C.gates.length - 1 := by
        rw [← delGate_length n g r C hg]; exact hk_lt
      rw [hw_eq, wireVal_gate n (delGate n g r C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g r C hg k hk_lt']
      set k0 := if k < g then k else k + 1 with hk0_def
      have hk0_lt : k0 < C.gates.length := by
        rw [hk0_def]; split_ifs <;> omega
      have horig : origWire n g (n + k) = n + k0 := by
        unfold origWire; rw [hk0_def]; split_ifs <;> omega
      rw [horig, wireVal_gate n C x k0 hk0_lt hRB]
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hru_lt : remap n g r u < n + k := by
        have h1 : remap n g r u ∈ (gateAt (delGate n g r C) k).inputs := by
          rw [delGate_gateAt n g r C hg k hk_lt']
          simp only [mapGate, List.mem_map]
          exact ⟨u, hu, rfl⟩
        exact hAO_rb k hk_lt (remap n g r u) h1
      have hih := ih (remap n g r u) (by omega) (by omega)
      simp only [Function.comp_apply, hih]
      by_cases hug : u = n + g
      · rw [hug, origWire_remap_eq n g r hr, hmatch]
      · rw [origWire_remap_ne n g r u hug]


/-- A row set that determines the output among all monotone binary circuits. -/
def DeterminesOn (n : ℕ) (S : Set (Fin n → Bool)) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ D : Circuit, IsAO2 n D → (∀ x ∈ S, circuitFun n D x = f x) →
    circuitFun n D = f

lemma delGate_on_row {n : ℕ} (C : Circuit) (g r : ℕ)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hr : r < n + g)
    (hout : C.output < n + C.gates.length) (x : Fin n → Bool)
    (hmatch : wireVal n C (n + g) x = wireVal n C r x) :
    circuitFun n (delGate n g r C) x = circuitFun n C x := by
  have hout' := delGate_output_lt n g r C hg hr hout
  have hval := delGate_wireVal_eq n g r C x hAO.2.1 hg hr hmatch
    (delGate n g r C).output hout'
  change wireVal n (delGate n g r C) (delGate n g r C).output x =
    wireVal n C C.output x
  rw [hval]
  change wireVal n C (origWire n g (remap n g r C.output)) x = _
  by_cases he : C.output = n + g
  · rw [he, origWire_remap_eq n g r hr, hmatch]
  · rw [origWire_remap_ne n g r C.output he]

lemma no_earlier_signature {n : ℕ} (C : Circuit) (S : Set (Fin n → Bool))
    (hAO : IsAO2 n C)
    (hmin : ∀ D : Circuit, IsAO2 n D → circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (hcomplete : DeterminesOn n S (circuitFun n C))
    (hout : C.output < n + C.gates.length)
    (g r : ℕ) (hg : g < C.gates.length) (hr : r < n + g) :
    ¬ ∀ x ∈ S, wireVal n C (n + g) x = wireVal n C r x := by
  intro heq
  have hD := delGate_isAO2 n g r C hAO hg hr
  have hf : circuitFun n (delGate n g r C) = circuitFun n C :=
    hcomplete _ hD (fun x hx => delGate_on_row C g r hAO hg hr hout x (heq x hx))
  have hle := hmin _ hD hf
  have hs := delGate_length n g r C hg
  change C.gates.length ≤ (delGate n g r C).gates.length at hle
  omega

lemma operand_not_implies {n : ℕ} (C : Circuit) (S : Set (Fin n → Bool))
    (hAO : IsAO2 n C)
    (hmin : ∀ D : Circuit, IsAO2 n D → circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (hcomplete : DeterminesOn n S (circuitFun n C))
    (hout : C.output < n + C.gates.length)
    (g a b : ℕ) (hg : g < C.gates.length) (hin : (gateAt C g).inputs = [a,b]) :
    ¬ ∀ x ∈ S, wireVal n C a x = true → wireVal n C b x = true := by
  intro himp
  have ha : a < n + g := hAO.2.1 g hg a (by simp [hin])
  have hb : b < n + g := hAO.2.1 g hg b (by simp [hin])
  have hmem : gateAt C g ∈ C.gates := by
    rw [gateAt_eq_getElem C g hg]
    exact List.getElem_mem hg
  rcases hAO.1 _ hmem with hand | hor
  · apply no_earlier_signature C S hAO hmin hcomplete hout g a hg ha
    intro x hx
    rw [wireVal_gate n C x g hg hAO.2.1, hand, hin]
    have h := himp x hx
    cases ha' : wireVal n C a x <;> cases hb' : wireVal n C b x <;>
      simp_all [GateOp.eval]
  · apply no_earlier_signature C S hAO hmin hcomplete hout g b hg hb
    intro x hx
    rw [wireVal_gate n C x g hg hAO.2.1, hor, hin]
    have h := himp x hx
    cases ha' : wireVal n C a x <;> cases hb' : wireVal n C b x <;>
      simp_all [GateOp.eval]

lemma operand_separators {n : ℕ} (C : Circuit) (S : Set (Fin n → Bool))
    (hAO : IsAO2 n C)
    (hmin : ∀ D : Circuit, IsAO2 n D → circuitFun n D = circuitFun n C → C.size ≤ D.size)
    (hcomplete : DeterminesOn n S (circuitFun n C))
    (hout : C.output < n + C.gates.length)
    (g a b : ℕ) (hg : g < C.gates.length) (hin : (gateAt C g).inputs = [a,b]) :
    (∃ x ∈ S, wireVal n C a x = true ∧ wireVal n C b x = false) ∧
    (∃ x ∈ S, wireVal n C a x = false ∧ wireVal n C b x = true) := by
  classical
  have hnot := operand_not_implies C S hAO hmin hcomplete hout g a b hg hin
  have hnot' : ¬ ∀ x ∈ S, wireVal n C b x = true → wireVal n C a x = true := by
    intro himp
    have ha : a < n + g := hAO.2.1 g hg a (by simp [hin])
    have hb : b < n + g := hAO.2.1 g hg b (by simp [hin])
    have hmem : gateAt C g ∈ C.gates := by
      rw [gateAt_eq_getElem C g hg]
      exact List.getElem_mem hg
    rcases hAO.1 _ hmem with hand | hor
    · apply no_earlier_signature C S hAO hmin hcomplete hout g b hg hb
      intro x hx
      rw [wireVal_gate n C x g hg hAO.2.1, hand, hin]
      have h := himp x hx
      cases ha' : wireVal n C a x <;> cases hb' : wireVal n C b x <;>
        simp_all [GateOp.eval]
    · apply no_earlier_signature C S hAO hmin hcomplete hout g a hg ha
      intro x hx
      rw [wireVal_gate n C x g hg hAO.2.1, hor, hin]
      have h := himp x hx
      cases ha' : wireVal n C a x <;> cases hb' : wireVal n C b x <;>
        simp_all [GateOp.eval]
  push_neg at hnot hnot'
  obtain ⟨x, hx, hxa, hxb⟩ := hnot
  obtain ⟨y, hy, hyb, hya⟩ := hnot'
  exact ⟨⟨x, hx, hxa, Bool.eq_false_iff.mpr hxb⟩,
    ⟨y, hy, Bool.eq_false_iff.mpr hya, hyb⟩⟩

end PEqualNP.Outside.L_meta_2583_aux.Pruning
