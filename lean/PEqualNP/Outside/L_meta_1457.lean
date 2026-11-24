import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1457
open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen), ?_, ?_⟩
  · exact fun r hr => (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have step (r) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,h⟩)
      · simp [h]
    have form (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [form x] at hx
    rw [form y]
    rcases hop with hop|hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r,hr,rfl⟩ := hb
      exact step r hr (hx _ ⟨r,hr,rfl⟩)
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hx ⊢
      obtain ⟨b,⟨r,hr,rfl⟩,hv⟩ := hx
      exact ⟨_, ⟨r,hr,rfl⟩, step r hr hv⟩

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value C x p = true → value C y p = true
      simpa only [input_value] using hxy p
    by_cases hw : w < n + C.size
    · obtain ⟨P, _, hP, hstep⟩ := gate_inputs C hG w (by omega) hw
      exact hstep x y fun r hr => ih r (hP r hr)
    · simp [missing_value C x w (by omega)]

def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun q => decide (q = p)) w = true)

lemma mem_support {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ support C w ↔ value C (fun q => decide (q = p)) w = true := by
  simp [support]

lemma support_gate {n : ℕ} (C : Circuit) (w : ℕ) (h : 2 ≤ (support (n := n) C w).card) :
    n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p : Fin n := ⟨w, hw⟩
    have hs : support C w ⊆ {p} := by
      intro q hq
      have hv := (mem_support C w q).mp hq
      change value C (fun r => decide (r = q)) p = true at hv
      simpa [input_value, eq_comm] using hv
    have hb := Finset.card_le_card hs
    simp at hb
    omega
  · by_contra! hw
    have hs : support (n := n) C w = ∅ := by
      ext q
      simp [mem_support, missing_value C _ w hw]
    simp [hs] at h

abbrev good (C : Circuit) := ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma repl_eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ r ∈ g.inputs, f r = f' r) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rw [List.map_congr_left h]

def replC (gates : List Gate) (i0 : ℕ) : Circuit :=
  ⟨gates.set i0 ⟨GateOp.and, []⟩, 0⟩

lemma replC_size (gates : List Gate) (i0 : ℕ) : (replC gates i0).size = gates.length := by
  simp [replC, Circuit.size]

lemma replC_gates (gates : List Gate) (i0 : Fin gates.length)
    (hgate : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin gates.length, (gates.get q).op = GateOp.not → q = i0) :
    ∀ g ∈ (replC gates i0.val).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hk' : k < gates.length := by simpa [replC] using hk
  by_cases hki : i0.val = k
  · simp [replC, hki]
  · have e : (replC gates i0.val).gates[k] = gates[k] := by
      simp [replC, hki]
    rw [e]
    obtain ⟨hop, hlen⟩ := hgate gates[k] (List.getElem_mem _)
    refine ⟨?_, hlen⟩
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact absurd (congrArg Fin.val (hnot ⟨k, hk'⟩ hop)).symm hki

lemma replC_true {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (x : Fin n → Bool) :
    value (replC gates i0.val) x (n + i0.val) = true := by
  have h := gate_value (replC gates i0.val) x (n + i0.val) (by omega)
    (by rw [replC_size]; omega)
  simp only at h
  rw [h]
  simp [replC, GateOp.eval]

lemma replC_other {n : ℕ} (gates : List Gate) (i0 : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) (hne : w ≠ n + i0) :
    value (replC gates i0) x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value (replC gates i0) x r else false) := by
  have h := gate_value (replC gates i0) x w hn (by rw [replC_size]; exact hw)
  simp only at h
  rw [h]
  have e : (replC gates i0).gates[w - n]'(by simp [replC]; omega) = gates[w - n]'(by omega) := by
    simp only [replC, List.getElem_set]
    rw [ite_eq_right (by omega)]
  rw [e]

lemma orig_value {n : ℕ} (gates : List Gate) (o : ℕ) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + gates.length) :
    value ⟨gates, o⟩ x w = (gates[w - n]'(by omega)).op.eval
      ((gates[w - n]'(by omega)).inputs.map fun r =>
        if r < w then value ⟨gates, o⟩ x r else false) :=
  gate_value ⟨gates, o⟩ x w hn hw

lemma replC_eq {n : ℕ} (gates : List Gate) (i0 : Fin gates.length) (o : ℕ)
    (x : Fin n → Bool) (h0 : value ⟨gates, o⟩ x (n + i0.val) = true) (w : ℕ) :
    value (replC gates i0.val) x w = value ⟨gates, o⟩ x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value ⟨gates, o⟩ x ⟨w, hn⟩
      have h2 := input_value (replC gates i0.val) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
    by_cases hw : w < n + gates.length
    · by_cases hne : w = n + i0.val
      · rw [hne, h0]
        exact replC_true gates i0 x
      · rw [orig_value gates o x w (by omega) hw, replC_other gates i0.val x w (by omega) hw hne]
        apply repl_eval_congr
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value ⟨gates, o⟩ x w (by simp only [Circuit.size]; omega),
        missing_value (replC gates i0.val) x w (by rw [replC_size]; omega)]


def singletonInput {n : ℕ} (p : Fin n) : Fin n → Bool := fun v => decide (v = p)

def outsideSupport {n : ℕ} (C : Circuit) (R : Finset (Fin n)) (w : ℕ) :=
  support C w \ R

def liveInputs {n : ℕ} (C : Circuit) (R : Finset (Fin n)) (w : ℕ) (g : Gate) :=
  g.inputs.toFinset.filter fun r => r < w ∧ (outsideSupport C R r).Nonempty

def branches {n : ℕ} (C : Circuit) (R : Finset (Fin n)) (w : ℕ) : Prop :=
  ∃ h : w - n < C.gates.length,
    C.gates[w - n].op = GateOp.or ∧
      2 ≤ (liveInputs C R w C.gates[w - n]).card

noncomputable def charged {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (y : Fin n → Bool)
    (z : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.Ico n (n + C.size)).erase z).filter fun w =>
    outsideSupport C R w ⊆ S ∧ 2 ≤ (outsideSupport C R w).card ∧ branches C R w ∧
      value C y w = false

lemma or_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n ≤ w) (h : w - n < C.gates.length) (hop : C.gates[w - n].op = GateOp.or) :
    value C x w = true ↔ ∃ r ∈ C.gates[w - n].inputs, r < w ∧ value C x r = true := by
  have hlt : w < n + C.size := by unfold Circuit.size; omega
  rw [gate_value C x w hw hlt]
  simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨r, hr, hv⟩
    by_cases h' : r < w
    · exact ⟨r, hr, h', by simpa [h'] using hv⟩
    · simp [h'] at hv
  · rintro ⟨r, hr, h', hv⟩
    exact ⟨r, hr, by simp [h', hv]⟩

lemma and_false {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n ≤ w) (h : w - n < C.gates.length) (hop : C.gates[w - n].op = GateOp.and) :
    value C x w = false ↔ ∃ r ∈ C.gates[w - n].inputs, w ≤ r ∨ value C x r = false := by
  have hlt : w < n + C.size := by unfold Circuit.size; omega
  rw [gate_value C x w hw hlt]
  simp only [hop, GateOp.eval, List.all_map, List.all_eq_false, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨r, hr, hf⟩
    by_cases h' : r < w
    · exact ⟨r, hr, Or.inr (by simpa [h'] using hf)⟩
    · exact ⟨r, hr, Or.inl (by omega)⟩
  · rintro ⟨r, hr, hf | hf⟩
    · exact ⟨r, hr, by simp [show ¬ r < w by omega]⟩
    · exact ⟨r, hr, by simp [hf]⟩

lemma outside_mono {n : ℕ} (gates : List Gate) (j : Fin gates.length)
    (hops : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hu : ∀ k : Fin gates.length, (gates.get k).op = GateOp.not → k = j)
    (x y : Fin n → Bool) (hx : value ⟨gates, 0⟩ x (n+j.val) = true)
    (hy : value ⟨gates, 0⟩ y (n+j.val) = true)
    (hxy : ∀ p, x p = true → y p = true) (w : ℕ) :
    value ⟨gates, 0⟩ x w = true → value ⟨gates, 0⟩ y w = true := by
  rw [← replC_eq gates j 0 x hx w, ← replC_eq gates j 0 y hy w]
  exact value_mono _ (replC_gates gates j hops hu) x y hxy w

lemma outside_input_data {n : ℕ} (C : Circuit) (R : Finset (Fin n)) (y : Fin n → Bool)
    (w : ℕ) (hw : n ≤ w) (h : w - n < C.gates.length)
    (hops : C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or)
    (hlen : C.gates[w - n].inputs.length ≤ 2)
    (hy : value C y w = false) (hne : (outsideSupport C R w).Nonempty) :
    ∃ P : Finset ℕ, (∀ r ∈ P, r < w ∧ value C y r = false) ∧
      outsideSupport C R w ⊆ P.biUnion (outsideSupport C R) ∧
      P.card ≤ 2 ∧ (2 ≤ P.card → branches C R w) := by
  classical
  rcases hops with hop | hop
  · obtain ⟨r, hr, hbad⟩ := (and_false C y w hw h hop).mp hy
    have hlt : r < w := by
      by_contra! hrw
      obtain ⟨p, hp⟩ := hne
      have hp' := (mem_support C w p).mp (Finset.mem_sdiff.mp hp).1
      have hbad' := (and_false C (singletonInput p) w hw h hop).mpr ⟨r, hr, Or.inl hrw⟩
      change value C (singletonInput p) w = true at hp'
      simp [hbad'] at hp'
    refine ⟨{r}, ?_, ?_, by simp, by simp⟩
    · intro a ha
      have : a = r := Finset.mem_singleton.mp ha
      subst a
      exact ⟨hlt, hbad.resolve_left (by omega)⟩
    · intro p hp
      have hp' := (mem_support C w p).mp (Finset.mem_sdiff.mp hp).1
      have hpr : value C (singletonInput p) r = true := by
        by_contra! hr'
        have hr'' : value C (singletonInput p) r = false := by simpa using hr'
        have hn := (and_false C (singletonInput p) w hw h hop).mpr ⟨r, hr, Or.inr hr''⟩
        change value C (singletonInput p) w = true at hp'
        simp [hn] at hp'
      simpa [outsideSupport] using
        Finset.mem_sdiff.mpr ⟨(mem_support C r p).mpr hpr, (Finset.mem_sdiff.mp hp).2⟩
  · let P := liveInputs C R w C.gates[w - n]
    refine ⟨P, ?_, ?_, ?_, fun hP => ⟨h,hop,hP⟩⟩
    · intro r hr
      have ⟨hri, hlt, _⟩ := Finset.mem_filter.mp hr
      refine ⟨hlt, Bool.eq_false_iff.mpr ?_⟩
      intro hrt
      have he := (or_value C y w hw h hop).mpr ⟨r,List.mem_toFinset.mp hri,hlt,hrt⟩
      simp [hy] at he
    · intro p hp
      have hpt := (mem_support C w p).mp (Finset.mem_sdiff.mp hp).1
      obtain ⟨r, hr, hlt, hv⟩ := (or_value C (singletonInput p) w hw h hop).mp hpt
      have hpr : p ∈ outsideSupport C R r :=
        Finset.mem_sdiff.mpr ⟨(mem_support C r p).mpr hv, (Finset.mem_sdiff.mp hp).2⟩
      exact Finset.mem_biUnion.mpr ⟨r,
        Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, hlt, ⟨p,hpr⟩⟩, hpr⟩
    · exact (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen)

lemma outside_sub {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (y : Fin n → Bool)
    (hy : ∀ p, p ∉ R → p ∉ S → y p = true)
    (hm : ∀ p, p ∉ R → y p = true → ∀ w,
      value C (singletonInput p) w = true → value C y w = true)
    (w : ℕ) (hw : value C y w = false) :
    outsideSupport C R w ⊆ S := by
  intro p hp
  obtain ⟨hs, hr⟩ := Finset.mem_sdiff.mp hp
  by_contra hs'
  have := hm p hr (hy p hr hs') w ((mem_support C w p).mp hs)
  simp [hw] at this

-- Trace the outside singleton inputs backward through wires that are false on y.
lemma frontier {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (z : ℕ)
    (y : Fin n → Bool) (hz : value C y z = true)
    (hsub : ∀ w, value C y w = false → outsideSupport C R w ⊆ S)
    (hops : ∀ w, n ≤ w → (h : w - n < C.gates.length) → w ≠ z →
      (C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or) ∧
      C.gates[w - n].inputs.length ≤ 2) :
    ∀ (t : ℕ) (B : Finset ℕ), (∀ w ∈ B, value C y w = false) →
      (∀ w ∈ B, 2 ≤ (outsideSupport C R w).card → w < t) →
      ∃ F : Finset ℕ, B.biUnion (outsideSupport C R) ⊆ F.biUnion (outsideSupport C R) ∧
        (∀ w ∈ F, (outsideSupport C R w).card ≤ 1) ∧
        F.card ≤ B.card + ((charged C R S y z).filter (· < t)).card := by
  classical
  intro t
  induction t with
  | zero =>
    intro B _ hlt
    refine ⟨B, Finset.Subset.rfl, ?_, by omega⟩
    intro w hw
    have := hlt w hw
    omega
  | succ t ih =>
    intro B hfalse hlt
    by_cases hcase : t ∈ B ∧ 2 ≤ (outsideSupport C R t).card
    · obtain ⟨ht, hs⟩ := hcase
      have hs' := hs.trans (Finset.card_le_card (Finset.sdiff_subset (s := support C t) (t := R)))
      obtain ⟨hn, hC⟩ := support_gate C t hs'
      have hi : t - n < C.gates.length := by unfold Circuit.size at hC; omega
      have hne : t ≠ z := by intro e; have := hfalse t ht; simp [e, hz] at this
      obtain ⟨hop, hlen⟩ := hops t hn hi hne
      obtain ⟨P, hP, hcover, hcard, hb⟩ :=
        outside_input_data C R y t hn hi hop hlen (hfalse t ht)
          (Finset.card_pos.mp (by omega))
      let B' := B.erase t ∪ P
      have hf' (w) (hw : w ∈ B') : value C y w = false := by
        rcases Finset.mem_union.mp hw with h | h
        · exact hfalse w (Finset.mem_erase.mp h).2
        · exact (hP w h).2
      have ht' (w) (hw : w ∈ B') (hsw : 2 ≤ (outsideSupport C R w).card) : w < t := by
        rcases Finset.mem_union.mp hw with h | h
        · obtain ⟨hne, hin⟩ := Finset.mem_erase.mp h
          have := hlt w hin hsw
          omega
        · exact (hP w h).1
      obtain ⟨F, hFsub, hFs, hFc⟩ := ih B' hf' ht'
      refine ⟨F, ?_, hFs, ?_⟩
      · intro p hp
        obtain ⟨w, hw, hpw⟩ := Finset.mem_biUnion.mp hp
        apply hFsub
        by_cases he : w = t
        · subst w
          obtain ⟨r, hr, hpr⟩ := Finset.mem_biUnion.mp (hcover hpw)
          exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_right _ hr, hpr⟩
        · exact Finset.mem_biUnion.mpr
            ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hw⟩), hpw⟩
      · have hbc := Finset.card_union_le (B.erase t) P
        change B'.card ≤ _ at hbc
        have he := Finset.card_erase_add_one ht
        let G := charged C R S y z
        have hinc : G.filter (· < t) ⊆ G.filter (· < t + 1) := by
          intro w hw
          obtain ⟨hm, hw'⟩ := Finset.mem_filter.mp hw
          exact Finset.mem_filter.mpr ⟨hm, by omega⟩
        by_cases hp : 2 ≤ P.card
        · have hg : t ∈ G :=
            Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, Finset.mem_Ico.mpr ⟨hn,hC⟩⟩,
              hsub t (hfalse t ht), hs, hb hp, hfalse t ht⟩
          have hinc' : insert t (G.filter (· < t)) ⊆ G.filter (· < t + 1) := by
            intro w hw
            rcases Finset.mem_insert.mp hw with rfl | hw
            · exact Finset.mem_filter.mpr ⟨hg, by omega⟩
            · exact hinc hw
          have hfin := Finset.card_le_card hinc'
          rw [Finset.card_insert_of_notMem (by simp)] at hfin
          change F.card ≤ B.card + (G.filter (· < t + 1)).card
          change F.card ≤ B'.card + (G.filter (· < t)).card at hFc
          omega
        · have hfin := Finset.card_le_card hinc
          change F.card ≤ B.card + (G.filter (· < t + 1)).card
          change F.card ≤ B'.card + (G.filter (· < t)).card at hFc
          omega
    · have hlt' (w) (hw : w ∈ B) (hsw : 2 ≤ (outsideSupport C R w).card) : w < t := by
        have := hlt w hw hsw
        have hne : w ≠ t := by intro e; subst w; exact hcase ⟨hw,hsw⟩
        omega
      obtain ⟨F, hF, hFs, hFc⟩ := ih B hfalse hlt'
      refine ⟨F, hF, hFs, hFc.trans (Nat.add_le_add_left (Finset.card_le_card ?_) _)⟩
      intro w hw
      obtain ⟨hm, hw'⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨hm, by omega⟩

def mixed {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (y : Fin n → Bool) (w : ℕ) : Prop :=
  support C w ⊆ S ∧ (outsideSupport C R w).Nonempty ∧
    (support C w ∩ R).Nonempty ∧ value C (fun _ : Fin n => false) w = false ∧
      value C y w = false

noncomputable def entries {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (y : Fin n → Bool)
    (z : ℕ) : Finset ℕ := by
  classical
  exact ((Finset.Ico n (n + C.size)).erase z).filter fun w =>
    mixed C R S y w ∧ ¬ branches C R w

lemma mixed_card {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (y : Fin n → Bool) (w : ℕ)
    (hw : mixed C R S y w) : 2 ≤ (support (n := n) C w).card := by
  obtain ⟨p,hp⟩ := hw.2.1
  obtain ⟨r,hr⟩ := hw.2.2.1
  obtain ⟨hps,hpr⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hrs,hrr⟩ := Finset.mem_inter.mp hr
  exact Finset.one_lt_card.mpr ⟨p,hps,r,hrs,fun h => hpr (h ▸ hrr)⟩

-- The first mixed wire cannot be an OR with two outside-supporting inputs.
lemma entry_exists {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (y : Fin n → Bool) (o z : ℕ)
    (hz : value C (fun _ : Fin n => false) z = true)
    (hlen : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (ho : mixed C R S y o) :
    (entries C R S y z).Nonempty := by
  classical
  have hex : ∃ w, mixed C R S y w := ⟨o,ho⟩
  let w := Nat.find hex
  have hmix : mixed C R S y w := Nat.find_spec hex
  have ⟨hn, hC⟩ := support_gate C w (mixed_card C R S y w hmix)
  have hne : w ≠ z := by
    intro h
    have := hmix.2.2.2.1
    simp [h, hz] at this
  refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hne, Finset.mem_Ico.mpr ⟨hn,hC⟩⟩,
    hmix, ?_⟩⟩
  rintro ⟨h, hop, hb⟩
  let g := C.gates[w - n]
  obtain ⟨p,hp⟩ := hmix.2.2.1
  obtain ⟨hps,hpr⟩ := Finset.mem_inter.mp hp
  obtain ⟨r,hr,hrw,hrt⟩ := (or_value C (singletonInput p) w hn h hop).mp ((mem_support C w p).mp hps)
  have hfilter : liveInputs C R w g = g.inputs.toFinset := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    exact (List.toFinset_card_le _).trans ((hlen _ (List.getElem_mem _)).trans hb)
  have hout : (outsideSupport C R r).Nonempty :=
    (Finset.mem_filter.mp (show r ∈ liveInputs C R w g by rw [hfilter]; exact List.mem_toFinset.mpr hr)).2.2
  have hrsub : support (n := n) C r ⊆ support C w := by
    intro p' hp'
    exact (mem_support C w p').mpr ((or_value C (singletonInput p') w hn h hop).mpr
      ⟨r,hr,hrw,(mem_support C r p').mp hp'⟩)
  have hzero : value C (fun _ : Fin n => false) r = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have := (or_value C _ w hn h hop).mpr ⟨r,hr,hrw,ht⟩
    rw [hmix.2.2.2.1] at this
    contradiction
  have hyr : value C y r = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    have := (or_value C y w hn h hop).mpr ⟨r,hr,hrw,ht⟩
    rw [hmix.2.2.2.2] at this
    contradiction
  have hmr : mixed C R S y r :=
    ⟨hrsub.trans hmix.1, hout, ⟨p,Finset.mem_inter.mpr ⟨(mem_support C r p).mpr hrt,hpr⟩⟩,
      hzero, hyr⟩
  exact (Nat.find_min hex hrw) hmr

lemma charged_count {n : ℕ} (C : Circuit) (R S : Finset (Fin n)) (o z : ℕ)
    (y : Fin n → Bool) (hz : value C y z = true)
    (hout : value C y o = false) (hsupport : support C o = S)
    (hsub : ∀ w, value C y w = false → outsideSupport C R w ⊆ S)
    (hops : ∀ w, n ≤ w → (h : w - n < C.gates.length) → w ≠ z →
      (C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or) ∧
      C.gates[w - n].inputs.length ≤ 2) :
    (S \ R).card - 1 ≤ (charged C R S y z).card := by
  have hlt (w) (hw : w ∈ ({o} : Finset ℕ)) (h : 2 ≤ (outsideSupport C R w).card) :
      w < n + C.size := by
    exact (support_gate C w (h.trans (Finset.card_le_card Finset.sdiff_subset))).2
  obtain ⟨F, hFsub, hFs, hFc⟩ := frontier C R S z y hz hsub hops
    (n + C.size) {o} (by intro w hw; simpa using (Finset.mem_singleton.mp hw) ▸ hout) hlt
  have h1 := Finset.card_le_card hFsub
  simp [outsideSupport, hsupport] at h1
  have h2 := Finset.card_biUnion_le_card_mul F (outsideSupport C R) 1 hFs
  have h3 := Finset.card_filter_le (charged C R S y z) (fun w => w < n + C.size)
  simp only [Nat.mul_one] at h2
  simp only [Finset.card_singleton] at hFc
  omega

end PEqualNP.Outside.L_meta_1457

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1457 in
theorem PEqualNP.Outside.L_meta_1457 : ∀ (q n m : ℕ) (S : Fin m → Finset (Fin n)) (i0 : Fin m),
    1 ≤ q → (∀ i : Fin m, (S i).card = q + 1) →
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    (∀ (w : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
    (∀ x : Fin n → Bool, (∀ v ∈ S i0, x v = false) → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (j : ℕ)⟩ (List.ofFn x) = true) →
    ∀ i : Fin m, i ≠ i0 →
    q ≤ (Finset.univ.filter (fun g : Fin gates.length =>
      (∀ x : Fin n → Bool, (∀ v ∈ S i0, x v = false) →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn x) = true → PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out i⟩ (List.ofFn x) = true) ∧
      (((∀ p : Fin n, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v = p))) = true → p ∈ S i) ∧
          2 ≤ (Finset.univ.filter (fun p : Fin n => PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v = p))) = true)).card) ∨
       ((∃ p : Fin n, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v = p))) = true ∧ p ∉ S i) ∧
          2 ≤ (Finset.univ.filter (fun p : Fin n =>
            p ∉ S i0 ∧ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (g : ℕ)⟩ (List.ofFn (fun v : Fin n => decide (v = p))) = true)).card)))).card := by
  intro q n m S i0 _ hsize hpair gates out j hg _ hunique hcorrect hnot i hi
  classical
  let C : Circuit := ⟨gates, 0⟩
  let R := S i0
  let z := n + j.val
  have hz (x : Fin n → Bool) (hx : ∀ v ∈ R, x v = false) : value C x z = true :=
    hnot x hx
  have hop (w) (hn : n ≤ w) (hw : w - n < C.gates.length) (hne : w ≠ z) :
      (C.gates[w - n].op = GateOp.and ∨ C.gates[w - n].op = GateOp.or) ∧
      C.gates[w - n].inputs.length ≤ 2 := by
    have h := hg C.gates[w - n] (List.getElem_mem _)
    refine ⟨?_, h.2⟩
    rcases h.1 with e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · have he := congrArg Fin.val (hunique ⟨w - n, hw⟩ e)
      change w - n = j.val at he
      exact False.elim (hne (by dsimp [z]; omega))
  have ho (x : Fin n → Bool) : value C x (out i) = decide (∃ v ∈ S i, x v = true) :=
    hcorrect i x
  have hsp : support C (out i) = S i := by
    ext p
    rw [mem_support, ← show singletonInput p = (fun v => decide (v = p)) from rfl,
      ho (singletonInput p)]
    simp [singletonInput]
  let y : Fin n → Bool := fun p => decide (p ∉ R ∧ p ∉ S i)
  have hy : ∀ p ∈ R, y p = false := by intro p hp; simp [y, hp]
  have hyo : value C y (out i) = false := by
    rw [ho]
    apply decide_eq_false
    rintro ⟨p, hp, he⟩
    exact (of_decide_eq_true he).2 hp
  have counts : (S i \ R).card - 1 ≤ (charged C R (S i) y z).card := by
    apply charged_count C R (S i) (out i) z y (hz y hy) hyo hsp _ hop
    apply outside_sub C R (S i) y
    · intro p hp hr; simp [y, hp, hr]
    · intro p hp hyp w
      have hsing : ∀ r ∈ R, singletonInput p r = false := by
        intro r hr
        have hne : r ≠ p := fun e => hp (e ▸ hr)
        simp [singletonInput, hne]
      apply outside_mono gates j hg hunique (singletonInput p) y (hz _ hsing) (hz _ hy) _ w
      intro v hv
      have e : v = p := of_decide_eq_true hv
      simpa [e] using hyp
  have hentry (h1 : (S i \ R).Nonempty) (h2 : (S i ∩ R).Nonempty) :
      (entries C R (S i) y z).Nonempty := by
    apply entry_exists C R (S i) y (out i) z (hz _ (by simp)) (fun g hg' => (hg g hg').2)
    refine ⟨?_, ?_, ?_, ?_, hyo⟩
    · rw [hsp]
    · simpa only [outsideSupport, hsp] using h1
    · simpa only [hsp] using h2
    · rw [ho]
      simp
  -- A wire that is false on y is below the output of line i on inputs that vanish on R.
  have hbelow (w : ℕ) (hw : value C y w = false) (x : Fin n → Bool)
      (hx : ∀ v ∈ R, x v = false) (hxw : value C x w = true) : value C x (out i) = true := by
    by_contra hxo
    have hxo' : ∀ v ∈ S i, x v = false := by
      intro v hv
      by_contra hxv
      apply hxo
      rw [ho]
      exact decide_eq_true ⟨v, hv, by simpa using hxv⟩
    have hxy : ∀ p, x p = true → y p = true := by
      intro p hp
      have h1 : p ∉ R := fun h => by simp [hx p h] at hp
      have h2 : p ∉ S i := fun h => by simp [hxo' p h] at hp
      simp [y, h1, h2]
    have h' : value C y w = true := outside_mono gates j hg hunique x y (hz x hx) (hz y hy) hxy w hxw
    rw [hw] at h'
    exact absurd h' (by decide)
  let U := charged C R (S i) y z ∪ entries C R (S i) y z
  have hdisj : Disjoint (charged C R (S i) y z) (entries C R (S i) y z) := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    exact (Finset.mem_filter.mp hw').2.2 (Finset.mem_filter.mp hw).2.2.2.1
  have hUcard : q ≤ U.card := by
    rw [Finset.card_union_of_disjoint hdisj]
    have hs := Finset.card_sdiff_add_card_inter (S i) R
    rw [hsize i] at hs
    have hint : (S i ∩ R).card ≤ 1 := hpair i i0 hi
    by_cases h2 : (S i ∩ R).Nonempty
    · have hb := Finset.card_pos.mpr h2
      have h1 : (S i \ R).Nonempty := Finset.card_pos.mp (by omega)
      have he := Finset.card_pos.mpr (hentry h1 h2)
      omega
    · have hb : (S i ∩ R).card = 0 :=
        Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h2)
      omega
  -- Every wire of U is the wire of a gate in the posted set.
  have hdata (w : ℕ) (hw : w ∈ U) : n ≤ w ∧ w < n + gates.length ∧ value C y w = false ∧
      ((support C w ⊆ S i ∧ 2 ≤ (support (n := n) C w).card) ∨
        2 ≤ (outsideSupport C R w).card) := by
    rcases Finset.mem_union.mp hw with h | h
    · obtain ⟨hm, _, h2, _, hyw⟩ := Finset.mem_filter.mp h
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp (Finset.mem_erase.mp hm).2
      exact ⟨hlo, hhi, hyw, Or.inr h2⟩
    · obtain ⟨hm, hmix, _⟩ := Finset.mem_filter.mp h
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp (Finset.mem_erase.mp hm).2
      exact ⟨hlo, hhi, hmix.2.2.2.2, Or.inl ⟨hmix.1, mixed_card C R (S i) y w hmix⟩⟩
  refine hUcard.trans (le_trans ?_ (Finset.card_image_le (f := fun g : Fin gates.length => n + g.val)))
  apply Finset.card_le_card
  intro w hw
  obtain ⟨hlo, hhi, hyw, hsup⟩ := hdata w hw
  obtain ⟨k, hk, rfl⟩ : ∃ k, k < gates.length ∧ w = n + k := ⟨w - n, by omega, by omega⟩
  refine Finset.mem_image.mpr ⟨⟨k, hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_⟩, rfl⟩
  · intro x hx hxw
    exact hbelow (n + k) hyw x hx hxw
  · have hout_sub : outsideSupport C R (n + k) ⊆ Finset.univ.filter (fun p : Fin n =>
        p ∉ S i0 ∧ value C (fun v => decide (v = p)) (n + k) = true) := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp2, (mem_support C (n + k) p).mp hp1⟩
    rcases hsup with ⟨hsub, h2⟩ | h2
    · exact Or.inl ⟨fun p hp => hsub ((mem_support C (n + k) p).mpr hp), h2⟩
    · by_cases hsub : support C (n + k) ⊆ S i
      · exact Or.inl ⟨fun p hp => hsub ((mem_support C (n + k) p).mpr hp),
          h2.trans (Finset.card_le_card Finset.sdiff_subset)⟩
      · obtain ⟨p, hp1, hp2⟩ := Finset.not_subset.mp hsub
        exact Or.inr ⟨⟨p, (mem_support C (n + k) p).mp hp1, hp2⟩,
          h2.trans (Finset.card_le_card hout_sub)⟩
