import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_997.light

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

-- At a gate, reads of earlier wires agree with the completed run.
-- All other reads contribute false, even if the wire is produced later.
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
  classical
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, h⟩)
      · simp [h]
    have formula (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [formula x] at hx
    rw [formula y]
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hb
      exact hr r hrm (hx _ (List.mem_map.mpr ⟨r, hrm, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, hbt⟩ := hx
      obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hrm, rfl⟩, hr r hrm hbt⟩

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

-- Expand the selected gates once each, in reverse evaluation order.
-- Replacing one wire by at most two earlier wires increases the cut by at most one.
lemma cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ := gate_inputs C hG t (hGates t hex.2).1 (hGates t hex.2).2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hsize : F'.card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hlt⟩
          by_cases h : w = t
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hlt⟩)
          · exact ⟨hex.2, by omega⟩
          · exact ⟨hg, by omega⟩
      refine ⟨B, hd, ?_, ?_⟩
      · rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro x y hxy w hw
        by_cases h : w = t
        · subst w
          exact hp x y fun r hr => hi x y hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      have hle : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩

def singleSupp {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun v => decide (v = p)) w = true)

lemma mem_singleSupp {n : ℕ} (C : Circuit) (w : ℕ) (p : Fin n) :
    p ∈ singleSupp C w ↔ value C (fun v => decide (v = p)) w = true := by
  simp [singleSupp]

def charge {n : ℕ} (C : Circuit) (S : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter (fun w => singleSupp C w ⊆ S ∧
    2 ≤ (singleSupp (n := n) C w).card)

lemma mem_charge {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (w : ℕ) :
    w ∈ charge C S ↔ (n ≤ w ∧ w < n + C.size) ∧ singleSupp C w ⊆ S ∧
      2 ≤ (singleSupp (n := n) C w).card := by
  simp only [charge, Finset.mem_filter, Finset.mem_Ico]

lemma singleSupp_gate {n : ℕ} (C : Circuit) (w : ℕ)
    (h2 : 2 ≤ (singleSupp (n := n) C w).card) : n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p0 : Fin n := ⟨w, hw⟩
    have hsub : singleSupp C w ⊆ {p0} := by
      intro q hq
      have hv := (mem_singleSupp C w q).mp hq
      change value C (fun v => decide (v = q)) p0 = true at hv
      rw [input_value] at hv
      have heq : p0 = q := by simpa only [decide_eq_true_eq] using hv
      simpa only [Finset.mem_singleton] using heq.symm
    have := Finset.card_le_card hsub
    simp at this
    omega
  · by_contra! hw
    have hs0 : singleSupp (n := n) C w = ∅ := by
      ext q
      simp [mem_singleSupp, missing_value C _ w hw]
    simp [hs0] at h2

lemma light_bound {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (o k : ℕ)
    (hcorrect : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value C x o = decide (∃ p ∈ S, x p = true)) :
    min k S.card ≤ (charge C S).card + 1 := by
  classical
  let G := charge C S
  by_contra! hsmall
  have hsmallS : G.card + 1 < S.card := hsmall.trans_le (min_le_right ..)
  have hsmallK : G.card + 1 < k := hsmall.trans_le (min_le_left ..)
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size :=
    fun w hw => ((mem_charge C S w).mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C hG G hgate (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ G.card + 1 := by
    have hfilter := Finset.card_filter_le G (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    omega
  let clean (w : ℕ) : Finset (Fin n) :=
    if singleSupp C w ⊆ S then singleSupp C w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : singleSupp C w ⊆ S
    · simp only [clean, ite_eq_left hs]
      by_contra! hlarge
      exact Finset.disjoint_left.mp hd hw
        ((mem_charge C S w).mpr ⟨singleSupp_gate C w (by omega), hs, by omega⟩)
    · simp [clean, hs]
  have hcover : (B.biUnion clean).card < S.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let Dn := B.filter (fun w => ¬ singleSupp C w ⊆ S)
  have hout (w : {w // w ∈ Dn}) : ∃ q : Fin n, q ∈ singleSupp C w.val ∧ q ∉ S := by
    have hns := (Finset.mem_filter.mp w.property).2
    simpa only [Finset.not_subset] using hns
  choose qs hqs using hout
  let U : Finset (Fin n) := Dn.attach.image qs
  let z : Fin n → Bool := fun v => decide (v ∈ U)
  have hUcard : U.card < k := by
    have hi := Finset.card_image_le (s := Dn.attach) (f := qs)
    have hf := Finset.card_filter_le B (fun w => ¬ singleSupp C w ⊆ S)
    simp only [Finset.card_attach] at hi
    change U.card ≤ Dn.card at hi
    change Dn.card ≤ B.card at hf
    omega
  have hweight : (Finset.univ.filter (fun v => z v = true)).card < k := by
    simpa [z] using hUcard
  have hUS : ∀ q ∈ U, q ∉ S := by
    intro q hq
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hq
    exact (hqs w).2
  have hzfalse : value C z o = false := by
    rw [hcorrect z hweight]
    simp only [decide_eq_false_iff_not, not_exists]
    intro q hq
    exact hUS q (by simpa [z] using hq.2) hq.1
  have hfire : value C (fun v => decide (v = p)) o = true := by
    rw [hcorrect]
    · simp [hp]
    · have hsingle : Finset.univ.filter (fun v : Fin n => decide (v = p) = true) = {p} := by
        ext v
        simp
      rw [hsingle, Finset.card_singleton]
      omega
  have hztrue : value C z o = true := by
    apply hcut (fun v => decide (v = p)) z _ o (Finset.mem_singleton_self o) hfire
    intro w hw hx
    by_cases hs : singleSupp C w ⊆ S
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hw, by simp only [clean, ite_eq_left hs]; exact (mem_singleSupp C w p).mpr hx⟩))
    · let d : {w // w ∈ Dn} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
      apply value_mono C hG (fun v => decide (v = qs d)) z _ w
        ((mem_singleSupp C w (qs d)).mp (hqs d).1)
      intro v hv
      have hv' : v = qs d := by simpa using hv
      subst v
      simp only [z, decide_eq_true_eq]
      exact Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩
  rw [hzfalse] at hztrue
  exact Bool.false_ne_true hztrue

end PEqualNP.Outside.L_meta_997.light

namespace PEqualNP.Outside.L_meta_997.Heavy

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

lemma eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (f f' : ℕ → Bool) (h : ∀ r ∈ g.inputs, f r = true → f' r = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hx r hr => h r hr (hx r hr)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    exact fun ⟨r, hr, hx⟩ => ⟨r, hr, h r hr hx⟩

def fixed (C : Circuit) (t : ℕ) (b : Bool) : Circuit :=
  ⟨C.gates.set t ⟨if b then GateOp.and else GateOp.or, []⟩, C.output⟩

lemma fixed_size (C : Circuit) (t : ℕ) (b : Bool) : (fixed C t b).size = C.size := by
  simp [fixed, Circuit.size]

lemma op_other (C : Circuit) (t : ℕ)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (k : ℕ) (hk : k < C.gates.length) (hne : k ≠ t) :
    (C.gates[k]).op = GateOp.and ∨ (C.gates[k]).op = GateOp.or := by
  rcases (hgate C.gates[k] (List.getElem_mem _)).1 with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (hne (hnot ⟨k, hk⟩ h))

lemma fixed_good (C : Circuit) (t : ℕ) (b : Bool)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t) :
    ∀ g ∈ (fixed C t b).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have hk' : k < C.gates.length := by simpa [fixed] using hk
  by_cases htk : t = k
  · cases b <;> simp [fixed, htk]
  · have e : (fixed C t b).gates[k] = C.gates[k] := by simp [fixed, htk]
    rw [e]
    exact ⟨op_other C t hgate hnot k hk' (Ne.symm htk),
      (hgate C.gates[k] (List.getElem_mem _)).2⟩

lemma fixed_at {n : ℕ} (C : Circuit) (t : ℕ) (b : Bool)
    (ht : t < C.gates.length) (x : Fin n → Bool) :
    value (fixed C t b) x (n + t) = b := by
  rw [gate_value (fixed C t b) x (n + t) (by omega)
    (by rw [fixed_size]; unfold Circuit.size; omega)]
  cases b <;> simp [fixed, GateOp.eval]

lemma fixed_other {n : ℕ} (C : Circuit) (t : ℕ) (b : Bool)
    (x : Fin n → Bool) (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size)
    (hne : w ≠ n + t) :
    value (fixed C t b) x w = (C.gates[w - n]'(by unfold Circuit.size at hw; omega)).op.eval
      ((C.gates[w - n]'(by unfold Circuit.size at hw; omega)).inputs.map fun r =>
        if r < w then value (fixed C t b) x r else false) := by
  rw [gate_value (fixed C t b) x w hn (by rw [fixed_size]; exact hw)]
  have e : (fixed C t b).gates[w - n]'(by simp [fixed]; unfold Circuit.size at hw; omega) =
      C.gates[w - n]'(by unfold Circuit.size at hw; omega) := by
    simp only [fixed, List.getElem_set]
    rw [ite_eq_right (by omega)]
  rw [e]

lemma fixed_false_le {n : ℕ} (C : Circuit) (t : ℕ)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (x : Fin n → Bool) (w : ℕ) :
    value (fixed C t false) x w = true → value C x w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value C x ⟨w, hn⟩
      have h2 := input_value (fixed C t false) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
      exact id
    by_cases hw : w < n + C.size
    · by_cases hne : w = n + t
      · subst w
        rw [fixed_at C t false (by unfold Circuit.size at hw; omega) x]
        simp
      · rw [gate_value C x w (by omega) hw,
          fixed_other C t false x w (by omega) hw hne]
        apply eval_mono _ (op_other C t hgate hnot (w-n)
          (by unfold Circuit.size at hw; omega) (by omega))
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value (fixed C t false) x w (by rw [fixed_size]; omega)]
      simp

lemma fixed_eq {n : ℕ} (C : Circuit) (t : ℕ) (b : Bool) (x : Fin n → Bool)
    (h0 : value C x (n + t) = b) (w : ℕ) :
    value (fixed C t b) x w = value C x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value C x ⟨w, hn⟩
      have h2 := input_value (fixed C t b) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
    by_cases hw : w < n + C.size
    · by_cases hne : w = n + t
      · rw [hne, h0]
        exact fixed_at C t b (by unfold Circuit.size at hw; omega) x
      · rw [gate_value C x w (by omega) hw, fixed_other C t b x w (by omega) hw hne]
        rw [List.map_congr_left (fun r _ => ?_)]
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value C x w (by omega),
        missing_value (fixed C t b) x w (by rw [fixed_size]; omega)]

lemma prefix_mono {n : ℕ} (C : Circuit) (t : ℕ)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (x z : Fin n → Bool) (hxz : ∀ p, x p = true → z p = true)
    (w : ℕ) (hwt : w < n + t) : value C x w = true → value C z w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value C x ⟨w, hn⟩
      have h2 := input_value C z ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
      exact hxz ⟨w, hn⟩
    by_cases hw : w < n + C.size
    · rw [gate_value C x w (by omega) hw, gate_value C z w (by omega) hw]
      apply eval_mono _ (op_other C t hgate hnot (w-n)
        (by unfold Circuit.size at hw; omega) (by omega))
      intro r _
      by_cases hr : r < w
      · simpa [hr] using ih r hr (by omega)
      · simp [hr]
    · rw [missing_value C x w (by omega)]
      simp

lemma not_false_above {n : ℕ} (C : Circuit) (t : ℕ)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (ht : t < C.gates.length) (hop : (C.gates[t]).op = GateOp.not)
    (x z : Fin n → Bool) (hxz : ∀ p, x p = true → z p = true)
    (hx : value C x (n+t) = false) : value C z (n+t) = false := by
  have hxform := gate_value C x (n+t) (by omega) (by unfold Circuit.size; omega)
  have hzform := gate_value C z (n+t) (by omega) (by unfold Circuit.size; omega)
  simp only [Nat.add_sub_cancel_left] at hxform hzform
  rw [hop] at hxform hzform
  cases hi : (C.gates[t]).inputs with
  | nil => simp [hi, GateOp.eval, hx] at hxform
  | cons r rs =>
    have hr : r < n+t ∧ value C x r = true := by
      rw [hx] at hxform
      by_cases h : r < n+t
      · simp [hi, GateOp.eval, h] at hxform
        exact ⟨h, hxform⟩
      · simp [hi, GateOp.eval, h] at hxform
    have hz := prefix_mono C t hgate hnot x z hxz r hr.1 hr.2
    simpa [hi, GateOp.eval, hr.1, hz] using hzform

lemma fixed_false_eq_above {n : ℕ} (C : Circuit) (t : ℕ)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (ht : t < C.gates.length) (hop : (C.gates[t]).op = GateOp.not)
    (x z : Fin n → Bool) (hxz : ∀ p, x p = true → z p = true)
    (hx : value C x (n+t) = false) (w : ℕ) :
    value (fixed C t false) z w = value C z w :=
  fixed_eq C t false z (not_false_above C t hgate hnot ht hop x z hxz hx) w

lemma gate_inputs {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  classical
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let P := g.inputs.toFinset.filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen), ?_, ?_⟩
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hr : r ∈ g.inputs) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, h⟩)
      · simp [h]
    have formula (z : Fin n → Bool) :
        value C z w = g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
      gate_value C z w hn hw
    rw [formula x] at hx
    rw [formula y]
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
      intro b hb
      obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hb
      exact hr r hrm (hx _ (List.mem_map.mpr ⟨r, hrm, rfl⟩))
    · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
      obtain ⟨b, hb, hbt⟩ := hx
      obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hb
      exact ⟨_, List.mem_map.mpr ⟨r, hrm, rfl⟩, hr r hrm hbt⟩

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

-- Expand the selected gates once each, in reverse evaluation order.
-- Replacing one wire by at most two earlier wires increases the cut by at most one.
lemma cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (G : Finset ℕ) (hGates : ∀ w ∈ G, n ≤ w ∧ w < n + C.size)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t) :
    ∃ B : Finset ℕ, Disjoint B G ∧ B.card ≤ F.card + (G.filter (· < t)).card ∧
      ∀ x y : Fin n → Bool, (∀ w ∈ B, value C x w = true → value C y w = true) →
        ∀ w ∈ F, value C x w = true → value C y w = true := by
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hp⟩ := gate_inputs C hG t (hGates t hex.2).1 (hGates t hex.2).2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hsize : F'.card ≤ F.card + 1 := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : G.filter (· < t + 1) = insert t (G.filter (· < t)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hg, hlt⟩
          by_cases h : w = t
          · exact Or.inl h
          · exact Or.inr ⟨hg, by omega⟩
        · rintro (rfl | ⟨hg, hlt⟩)
          · exact ⟨hex.2, by omega⟩
          · exact ⟨hg, by omega⟩
      refine ⟨B, hd, ?_, ?_⟩
      · rw [hfilter, Finset.card_insert_of_notMem (by simp)]
        omega
      · intro x y hxy w hw
        by_cases h : w = t
        · subst w
          exact hp x y fun r hr => hi x y hxy r (Finset.mem_union_right _ hr)
        · exact hi x y hxy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      have hle : (G.filter (· < t)).card ≤ (G.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩

def sound {n : ℕ} (C : Circuit) (T : Finset (Fin n)) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, value C x w = true → ∃ p ∈ T, x p = true

def supp {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun p => value C (fun v => decide (v ∈ Y ∨ v = p)) w = true)

lemma mem_supp {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ) (p : Fin n) :
    p ∈ supp C Y w ↔ value C (fun v => decide (v ∈ Y ∨ v = p)) w = true := by
  simp [supp]

noncomputable def asg {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + C.size)).filter (fun w => sound C T w ∧ 2 ≤ (supp C Y w).card)

lemma mem_asg {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) (w : ℕ) :
    w ∈ asg C Y T ↔ (n ≤ w ∧ w < n + C.size) ∧ sound C T w ∧ 2 ≤ (supp C Y w).card := by
  classical
  unfold asg
  rw [Finset.mem_filter, Finset.mem_Ico]

lemma supp_gate {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) (w : ℕ) (hYT : Disjoint Y T)
    (hs : sound C T w) (h2 : 2 ≤ (supp C Y w).card) : n ≤ w ∧ w < n + C.size := by
  constructor
  · by_contra! hw
    let p0 : Fin n := ⟨w, hw⟩
    have hY : p0 ∉ Y := by
      intro hp0
      have hv : value C (fun v => decide (v ∈ Y)) w = true := by
        change value C (fun v => decide (v ∈ Y)) p0 = true
        rw [input_value]
        simpa using hp0
      obtain ⟨q, hqT, hqY⟩ := hs _ hv
      exact Finset.disjoint_left.mp hYT (by simpa using hqY) hqT
    have hsub : supp C Y w ⊆ {p0} := by
      intro q hq
      have hv := (mem_supp C Y w q).mp hq
      change value C (fun v => decide (v ∈ Y ∨ v = q)) p0 = true at hv
      rw [input_value] at hv
      simp only [decide_eq_true_eq] at hv
      rcases hv with hv | hv
      · exact absurd hv hY
      · simp [hv]
    have := Finset.card_le_card hsub
    simp at this
    omega
  · by_contra! hw
    have hs0 : supp (n := n) C Y w = ∅ := by
      ext q
      simp [mem_supp, missing_value C _ w hw]
    simp [hs0] at h2

lemma card_le {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y T : Finset (Fin n)) (o : ℕ) (hYT : Disjoint Y T) (hso : sound C T o)
    (hfire : ∀ p ∈ T, value C (fun v => decide (v ∈ Y ∨ v = p)) o = true) :
    T.card ≤ (asg C Y T).card + 1 := by
  classical
  let G := asg C Y T
  by_contra! hsmall
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := fun w hw => ((mem_asg C Y T w).mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C hG G hgate (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ G.card + 1 := by
    have hfilter := Finset.card_filter_le G (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    omega
  let clean (w : ℕ) : Finset (Fin n) := if sound C T w then supp C Y w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : sound C T w
    · simp only [clean, ite_eq_left hs]
      by_contra! hlarge
      have hg := supp_gate C Y T w hYT hs (by omega)
      exact Finset.disjoint_left.mp hd hw ((mem_asg C Y T w).mpr ⟨hg, hs, by omega⟩)
    · simp [clean, hs]
  have hcover : (B.biUnion clean).card < T.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    have hG' : G.card + 1 < T.card := hsmall
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let Dn := B.filter (fun w => ¬ sound C T w)
  have hout (w : {w // w ∈ Dn}) :
      ∃ x : Fin n → Bool, value C x w.val = true ∧ ∀ q ∈ T, x q = false := by
    have hns := (Finset.mem_filter.mp w.property).2
    unfold sound at hns
    push Not at hns
    obtain ⟨x, hx, hxT⟩ := hns
    exact ⟨x, hx, fun q hq => by simpa using hxT q hq⟩
  choose xs hxs using hout
  let z : Fin n → Bool := fun v => decide (v ∈ Y ∨ ∃ d : {w // w ∈ Dn}, xs d v = true)
  have hzfalse : value C z o = false := by
    by_contra hne
    have ht : value C z o = true := by simpa using hne
    obtain ⟨q, hqT, hzq⟩ := hso z ht
    simp only [z, decide_eq_true_eq] at hzq
    rcases hzq with hqY | ⟨d, hd'⟩
    · exact Finset.disjoint_left.mp hYT hqY hqT
    · rw [(hxs d).2 q hqT] at hd'
      exact Bool.false_ne_true hd'
  have hztrue : value C z o = true := by
    apply hcut (fun v => decide (v ∈ Y ∨ v = p)) z _ o (Finset.mem_singleton_self o) (hfire p hp)
    intro w hw hx
    by_cases hs : sound C T w
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hw, by simp only [clean, ite_eq_left hs]; exact (mem_supp C Y w p).mpr hx⟩))
    · let d : {w // w ∈ Dn} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
      apply value_mono C hG (xs d) z _ w (hxs d).1
      intro v hv
      simp only [z, decide_eq_true_eq]
      exact Or.inr ⟨d, hv⟩
  rw [hzfalse] at hztrue
  exact Bool.false_ne_true hztrue

lemma heavy_card_le {n : ℕ} (C : Circuit) (t : ℕ)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (ht : t < C.gates.length) (hop : (C.gates[t]).op = GateOp.not)
    (Y S : Finset (Fin n)) (o : ℕ) (hYS : Disjoint Y S)
    (hY : value C (fun v => decide (v ∈ Y)) (n+t) = false)
    (hout : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ S, x p = true)) :
    S.card ≤ (asg (fixed C t false) Y S).card + 1 := by
  apply card_le (fixed C t false) (fixed_good C t false hgate hnot) Y S o hYS
  · intro x hx
    have h := fixed_false_le C t hgate hnot x o hx
    simpa [hout] using h
  · intro p hp
    rw [fixed_false_eq_above C t hgate hnot ht hop
      (fun v => decide (v ∈ Y)) (fun v => decide (v ∈ Y ∨ v = p))
      (by intro v hv; simpa using Or.inl (of_decide_eq_true hv)) hY o, hout]
    exact decide_eq_true ⟨p, hp, by simp⟩

lemma heavy_supp_eq {n : ℕ} (C : Circuit) (t : ℕ)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (ht : t < C.gates.length) (hop : (C.gates[t]).op = GateOp.not)
    (Y : Finset (Fin n)) (hY : value C (fun v => decide (v ∈ Y)) (n+t) = false)
    (w : ℕ) : supp (fixed C t false) Y w = supp C Y w := by
  ext p
  rw [mem_supp, mem_supp]
  rw [fixed_false_eq_above C t hgate hnot ht hop
    (fun v => decide (v ∈ Y)) (fun v => decide (v ∈ Y ∨ v = p))
    (by intro v hv; simpa using Or.inl (of_decide_eq_true hv)) hY w]

lemma sound_supp_subset {n : ℕ} (C : Circuit) (Y S : Finset (Fin n))
    (hYS : Disjoint Y S) (w : ℕ) (hs : sound C S w) : supp C Y w ⊆ S := by
  intro p hp
  obtain ⟨q, hqS, hq⟩ := hs _ ((mem_supp C Y w p).mp hp)
  rcases of_decide_eq_true hq with hqY | hqp
  · exact False.elim (Finset.disjoint_left.mp hYS hqY hqS)
  · simpa [← hqp] using hqS

lemma heavy_base_false {n : ℕ} (C : Circuit) (t : ℕ)
    (Y S : Finset (Fin n)) (hYS : Disjoint Y S)
    (hY : value C (fun v => decide (v ∈ Y)) (n+t) = false)
    (w : ℕ) (hw : w ∈ asg (fixed C t false) Y S) :
    value C (fun v => decide (v ∈ Y)) w = false := by
  have hs := ((mem_asg (fixed C t false) Y S w).mp hw).2.1
  have heq := fixed_eq C t false (fun v => decide (v ∈ Y)) hY w
  by_contra! h
  have ht : value (fixed C t false) (fun v => decide (v ∈ Y)) w = true := by
    rw [heq]
    simpa using h
  obtain ⟨p, hpS, hpY⟩ := hs _ ht
  exact Finset.disjoint_left.mp hYS (of_decide_eq_true hpY) hpS

lemma heavy_disjoint {n : ℕ} (C : Circuit) (Y Si Sj : Finset (Fin n))
    (hi : Disjoint Y Si) (hj : Disjoint Y Sj) (hij : (Si ∩ Sj).card ≤ 1) :
    Disjoint (asg C Y Si) (asg C Y Sj) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hwi hwj
  have hsi := ((mem_asg C Y Si w).mp hwi).2
  have hsj := ((mem_asg C Y Sj w).mp hwj).2
  have hsub : supp C Y w ⊆ Si ∩ Sj :=
    Finset.subset_inter (sound_supp_subset C Y Si hi w hsi.1)
      (sound_supp_subset C Y Sj hj w hsj.1)
  have hc := Finset.card_le_card hsub
  omega

lemma output_supp {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (o : ℕ)
    (hout : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ S, x p = true)) :
    supp C ∅ o = S := by
  ext p
  simp [mem_supp, hout]

lemma output_gate {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (o : ℕ)
    (hS : 2 ≤ S.card)
    (hout : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ S, x p = true)) :
    n ≤ o ∧ o < n + C.size := by
  apply supp_gate C ∅ S o (by simp)
  · intro x hx
    simpa [hout] using hx
  · simpa [output_supp C S o hout] using hS

lemma output_heavy_supp {n : ℕ} (C : Circuit) (Y S : Finset (Fin n)) (o : ℕ)
    (hYS : Disjoint Y S)
    (hout : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ S, x p = true)) :
    supp C Y o = S := by
  ext p
  rw [mem_supp, hout, decide_eq_true_eq]
  constructor
  · rintro ⟨q, hqS, hq⟩
    rcases of_decide_eq_true hq with hqY | hqp
    · exact False.elim (Finset.disjoint_left.mp hYS hqY hqS)
    · simpa [← hqp] using hqS
  · intro hp
    exact ⟨p, hp, by simp⟩

lemma output_distinct {n : ℕ} (C : Circuit) (Si Sj : Finset (Fin n)) (oi oj : ℕ)
    (hSi : 2 ≤ Si.card) (hij : (Si ∩ Sj).card ≤ 1)
    (houti : ∀ x : Fin n → Bool, value C x oi = decide (∃ p ∈ Si, x p = true))
    (houtj : ∀ x : Fin n → Bool, value C x oj = decide (∃ p ∈ Sj, x p = true)) :
    oi ≠ oj := by
  intro heq
  have hsets : Si = Sj := by
    rw [← output_supp C Si oi houti, ← output_supp C Sj oj houtj, heq]
  rw [← hsets, Finset.inter_self] at hij
  omega

end PEqualNP.Outside.L_meta_997.Heavy


namespace PEqualNP.Outside.L_meta_997.light

open PEqualNP.CircuitLowerBounds

lemma light_sum_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (o : Fin m → ℕ) (k : ℕ)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    ∑ i : Fin m, min k (S i).card ≤ C.gates.length + m := by
  classical
  have hper : ∀ i : Fin m, min k (S i).card ≤ (charge C (S i)).card + 1 :=
    fun i => light_bound C hG (S i) (o i) k (hcorrect i)
  have hfiber : ∀ w ∈ Finset.Ico n (n + C.size),
      (Finset.univ.filter (fun i : Fin m => w ∈ charge C (S i))).card ≤ 1 := by
    intro w _
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hij
    have hi' := (mem_charge C (S i) w).mp (Finset.mem_filter.mp hi).2
    have hj' := (mem_charge C (S j) w).mp (Finset.mem_filter.mp hj).2
    have hsub : singleSupp C w ⊆ S i ∩ S j := fun p hp =>
      Finset.mem_inter.mpr ⟨hi'.2.1 hp, hj'.2.1 hp⟩
    have := Finset.card_le_card hsub
    have := hinter i j hij
    omega
  have hdouble : ∑ i : Fin m, (charge C (S i)).card =
      ∑ w ∈ Finset.Ico n (n + C.size),
        (Finset.univ.filter (fun i : Fin m => w ∈ charge C (S i))).card := by
    have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (Finset.univ : Finset (Fin m))) (t := Finset.Ico n (n + C.size))
      (r := fun i w => w ∈ charge C (S i))
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at key
    rw [← key]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · intro hw
      exact ⟨((mem_charge C (S i) w).mp hw).1, hw⟩
    · intro hw
      exact hw.2
  calc ∑ i : Fin m, min k (S i).card ≤ ∑ i : Fin m, ((charge C (S i)).card + 1) :=
        Finset.sum_le_sum fun i _ => hper i
    _ = ∑ i : Fin m, (charge C (S i)).card + m := by
        rw [Finset.sum_add_distrib]
        simp
    _ ≤ C.gates.length + m := by
        rw [hdouble]
        have h := Finset.sum_le_sum hfiber
        simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one] at h
        have hl : n + C.size - n = C.gates.length := by unfold Circuit.size; omega
        rw [hl] at h
        exact Nat.add_le_add_right h m

lemma truncated_sum_original {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t k : ℕ)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < k → value C x (n + t) = true) :
    ∑ i : Fin m, min k (S i).card ≤ C.gates.length + m := by
  have hgood := Heavy.fixed_good C t true hgate hnot
  have hfixed : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value (Heavy.fixed C t true) x (o i) = decide (∃ p ∈ S i, x p = true) := by
    intro i x hx
    have he := Heavy.fixed_eq C t true x (hlow x hx) (o i)
    change value (Heavy.fixed C t true) x (o i) = value C x (o i) at he
    rw [he, hcorrect]
  have h := light_sum_bound S (Heavy.fixed C t true) hgood hinter o k hfixed
  simpa [Heavy.fixed] using h

lemma all_meeting_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < y.card → value C x (n + t) = true)
    (hmeet : ∀ i : Fin m, ¬ Disjoint (S i) y) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + m := by
  simpa [hmeet] using truncated_sum_original S C o t y.card hinter hgate hnot hcorrect hlow

lemma not_exists_of_positive_window {n : ℕ} (C : Circuit) (t : ℕ) (y : Finset (Fin n))
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hlow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < y.card → value C x (n + t) = true)
    (hfalse : value C (fun v => decide (v ∈ y)) (n + t) = false)
    (hy : 0 < y.card) :
    ∃ q : Fin C.gates.length, q.val = t ∧ (C.gates.get q).op = GateOp.not := by
  by_contra! hnone
  have hmono : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hgate g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      have hn := hnot ⟨j, hj⟩ h
      exact False.elim (hnone ⟨j, hj⟩ hn h)
  have h0 : value C (fun _ : Fin n => false) (n + t) = true :=
    hlow _ (by simpa using hy)
  have h1 := value_mono C hmono (fun _ : Fin n => false) (fun v => decide (v ∈ y))
    (by simp) (n + t) h0
  rw [hfalse] at h1
  exact Bool.false_ne_true h1

lemma monotone_family_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    ∑ i : Fin m, (S i).card ≤ C.gates.length + m := by
  have h := light_sum_bound S C hgate hinter o (n + 1) (fun i x _ => hcorrect i x)
  have hcard (i : Fin m) : (S i).card ≤ n + 1 := by
    have hc := Finset.card_le_univ (S i)
    simp only [Fintype.card_fin] at hc
    omega
  simpa only [min_eq_right (hcard _)] using h

lemma monotone_mixed_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (y : Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + m := by
  apply le_trans (Finset.sum_le_sum fun i _ => ?_) (monotone_family_bound S C o hinter hgate hcorrect)
  split_ifs
  · exact le_rfl
  · exact min_le_right ..

end PEqualNP.Outside.L_meta_997.light


namespace PEqualNP.Outside.L_meta_997.Refund

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_997.light

lemma refund_output_count {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (y : Finset (Fin n))
    (hlinear : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    (Finset.univ.filter (fun i : Fin m => Disjoint (S i) y ∧ 2 ≤ (S i).card)).card ≤
      (Finset.univ.filter (fun g : Fin C.gates.length =>
        (∃ i : Fin m, ∀ p : Fin n,
          value C (fun v => decide (v = p)) (n + g) = true ↔ p ∈ S i) ∧
        (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y →
          (value C (fun v => decide (v ∈ y ∨ v = p)) (n + g) = true ↔ p ∈ S i)))).card := by
  classical
  let I := Finset.univ.filter (fun i : Fin m => Disjoint (S i) y ∧ 2 ≤ (S i).card)
  let R := Finset.univ.filter (fun g : Fin C.gates.length =>
    (∃ i : Fin m, ∀ p : Fin n,
      value C (fun v => decide (v = p)) (n + g) = true ↔ p ∈ S i) ∧
    (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y →
      (value C (fun v => decide (v ∈ y ∨ v = p)) (n + g) = true ↔ p ∈ S i)))
  have hsingle (i : Fin m) (p : Fin n) :
      value C (fun v => decide (v = p)) (o i) = true ↔ p ∈ S i := by
    rw [hcorrect]
    simp
  have hsupp (i : Fin m) : singleSupp C (o i) = S i := by
    ext p
    rw [mem_singleSupp]
    exact hsingle i p
  have hgate (i : Fin m) (hi : i ∈ I) : n ≤ o i ∧ o i < n + C.gates.length := by
    have hc := (Finset.mem_filter.mp hi).2.2
    have h := singleSupp_gate C (o i) (by rwa [hsupp])
    exact h
  have hheavy (i : Fin m) (hd : Disjoint (S i) y) (p : Fin n) :
      value C (fun v => decide (v ∈ y ∨ v = p)) (o i) = true ↔ p ∈ S i := by
    rw [hcorrect]
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨q, hq, hqy | rfl⟩
      · exact False.elim (Finset.disjoint_left.mp hd hq hqy)
      · exact hq
    · intro hp
      exact ⟨p, hp, Or.inr rfl⟩
  let f (i : {i // i ∈ I}) : Fin C.gates.length :=
    ⟨o i.val - n, by have := hgate i.val i.property; omega⟩
  have hwire (i : {i // i ∈ I}) : n + (f i).val = o i.val := by
    have := hgate i.val i.property
    dsimp [f]
    omega
  have hf (i : {i // i ∈ I}) : f i ∈ R := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · refine ⟨i.val, ?_⟩
      intro p
      rw [hwire]
      exact hsingle i.val p
    · have hd := (Finset.mem_filter.mp i.property).2.1
      refine ⟨i.val, hd, ?_⟩
      intro p _
      rw [hwire]
      exact hheavy i.val hd p
  have hinj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    by_contra hne
    have ho : o i.val = o j.val := by
      rw [← hwire i, ← hwire j, hij]
    have hs : S i.val = S j.val := by
      rw [← hsupp i.val, ← hsupp j.val, ho]
    have hcross := hlinear i.val j.val hne
    rw [← hs, Finset.inter_self] at hcross
    have hc := (Finset.mem_filter.mp i.property).2.2
    omega
  have hcard := Fintype.card_le_of_injective
    (fun i : {i // i ∈ I} => (⟨f i, hf i⟩ : {g // g ∈ R}))
    (fun i j hij => hinj (congrArg Subtype.val hij))
  simpa only [Fintype.card_coe] using hcard

end PEqualNP.Outside.L_meta_997.Refund

namespace PEqualNP.Outside.L_meta_997.light

open PEqualNP.CircuitLowerBounds

lemma small_window_with_not {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (ht : t < C.gates.length) (hop : (C.gates[t]).op = GateOp.not)
    (hfalse : value C (fun v => decide (v ∈ y)) (n + t) = false)
    (hy : y.card ≤ 2) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + m := by
  classical
  let G : Fin m → Finset ℕ := fun i =>
    if Disjoint (S i) y then Heavy.asg (Heavy.fixed C t false) y (S i)
    else if 2 ≤ (S i).card then {o i} else ∅
  have hlight : ∀ i : Fin m, ¬ Disjoint (S i) y → ∀ w ∈ G i,
      w = o i ∧ 2 ≤ (S i).card ∧ value C (fun v => decide (v ∈ y)) w = true := by
    intro i hd w hw
    by_cases hlarge : 2 ≤ (S i).card
    · have he : w = o i := by simpa [G, hd, hlarge] using hw
      refine ⟨he, hlarge, ?_⟩
      rw [he, hcorrect]
      obtain ⟨p, hpS, hpy⟩ := Finset.not_disjoint_iff.mp hd
      exact decide_eq_true ⟨p, hpS, by simpa using hpy⟩
    · simp [G, hd, hlarge] at hw
  have hrange : ∀ i : Fin m, ∀ w ∈ G i, n ≤ w ∧ w < n + C.size := by
    intro i w hw
    by_cases hd : Disjoint (S i) y
    · have hw' : w ∈ Heavy.asg (Heavy.fixed C t false) y (S i) := by simpa [G, hd] using hw
      have hr := ((Heavy.mem_asg _ _ _ w).mp hw').1
      simpa only [Heavy.fixed_size] using hr
    · obtain ⟨he, hlarge, _⟩ := hlight i hd w hw
      rw [he]
      exact Heavy.output_gate C (S i) (o i) hlarge (hcorrect i)
  have hper : ∀ i : Fin m,
      (if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ (G i).card + 1 := by
    intro i
    by_cases hd : Disjoint (S i) y
    · simpa [G, hd] using Heavy.heavy_card_le C t hgate hnot ht hop y (S i) (o i)
        hd.symm hfalse (hcorrect i)
    · by_cases hlarge : 2 ≤ (S i).card
      · simpa [G, hd, hlarge] using (min_le_left y.card (S i).card).trans hy
      · have hsmall : (S i).card ≤ 1 := by omega
        simpa [G, hd, hlarge] using (min_le_right y.card (S i).card).trans hsmall
  have hfiber : ∀ w ∈ Finset.Ico n (n + C.size),
      (Finset.univ.filter (fun i : Fin m => w ∈ G i)).card ≤ 1 := by
    intro w _
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hij
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    by_cases hdi : Disjoint (S i) y <;> by_cases hdj : Disjoint (S j) y
    · have hiw : w ∈ Heavy.asg (Heavy.fixed C t false) y (S i) := by simpa [G, hdi] using hi'
      have hjw : w ∈ Heavy.asg (Heavy.fixed C t false) y (S j) := by simpa [G, hdj] using hj'
      exact Finset.disjoint_left.mp
        (Heavy.heavy_disjoint _ y (S i) (S j) hdi.symm hdj.symm (hinter i j hij)) hiw hjw
    · have hiw : w ∈ Heavy.asg (Heavy.fixed C t false) y (S i) := by simpa [G, hdi] using hi'
      have hf := Heavy.heavy_base_false C t y (S i) hdi.symm hfalse w hiw
      have ht' := (hlight j hdj w hj').2.2
      rw [show Heavy.value C (fun v => decide (v ∈ y)) w = value C (fun v => decide (v ∈ y)) w from rfl] at hf
      rw [hf] at ht'
      exact Bool.false_ne_true ht'
    · have hjw : w ∈ Heavy.asg (Heavy.fixed C t false) y (S j) := by simpa [G, hdj] using hj'
      have hf := Heavy.heavy_base_false C t y (S j) hdj.symm hfalse w hjw
      have ht' := (hlight i hdi w hi').2.2
      rw [show Heavy.value C (fun v => decide (v ∈ y)) w = value C (fun v => decide (v ∈ y)) w from rfl] at hf
      rw [hf] at ht'
      exact Bool.false_ne_true ht'
    · obtain ⟨hei, hlarge, _⟩ := hlight i hdi w hi'
      obtain ⟨hej, _, _⟩ := hlight j hdj w hj'
      exact Heavy.output_distinct C (S i) (S j) (o i) (o j) hlarge (hinter i j hij)
        (hcorrect i) (hcorrect j) (hei.symm.trans hej)
  have hdouble : ∑ i : Fin m, (G i).card =
      ∑ w ∈ Finset.Ico n (n + C.size),
        (Finset.univ.filter (fun i : Fin m => w ∈ G i)).card := by
    have key := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (Finset.univ : Finset (Fin m))) (t := Finset.Ico n (n + C.size))
      (r := fun i w => w ∈ G i)
    simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at key
    rw [← key]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · intro hw
      exact ⟨hrange i w hw, hw⟩
    · intro hw
      exact hw.2
  have hsum : ∑ i : Fin m, (G i).card ≤ C.gates.length := by
    rw [hdouble]
    have h := Finset.sum_le_sum hfiber
    simp only [Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_one] at h
    have hl : n + C.size - n = C.gates.length := by unfold Circuit.size; omega
    simpa only [hl] using h
  calc (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card)
      ≤ ∑ i : Fin m, ((G i).card + 1) := Finset.sum_le_sum fun i _ => hper i
    _ = (∑ i : Fin m, (G i).card) + m := by simp [Finset.sum_add_distrib]
    _ ≤ C.gates.length + m := Nat.add_le_add_right hsum m

lemma small_window_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hfalse : value C (fun v => decide (v ∈ y)) (n + t) = false)
    (hy : y.card ≤ 2) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + m := by
  classical
  by_cases hex : ∃ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not
  · obtain ⟨q, hq⟩ := hex
    have he := hnot q hq
    have ht : t < C.gates.length := he ▸ q.isLt
    have hop : (C.gates[t]).op = GateOp.not := by simpa [← he] using hq
    exact small_window_with_not S C o t y hinter hgate hnot hcorrect ht hop hfalse hy
  · have hmono : ∀ g ∈ C.gates,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hgate g hg
      refine ⟨?_, hlen⟩
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
        exact False.elim (hex ⟨⟨j, hj⟩, h⟩)
    exact monotone_mixed_bound S C o y hinter hmono hcorrect


end PEqualNP.Outside.L_meta_997.light

namespace PEqualNP.Outside.L_meta_997.Heavy

open PEqualNP.CircuitLowerBounds

lemma heavy_family_sum {n m : ℕ} (C : Circuit) (S : Fin m → Finset (Fin n))
    (Y : Finset (Fin n)) (I : Finset (Fin m))
    (hdisj : ∀ i ∈ I, Disjoint Y (S i))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hcount : ∀ i ∈ I, (S i).card ≤ (asg C Y (S i)).card + 1) :
    (∑ i ∈ I, (S i).card) ≤ C.size + I.card := by
  classical
  let A := fun i => asg C Y (S i)
  have hd : (I : Set (Fin m)).PairwiseDisjoint A := by
    intro i hi j hj hij
    exact heavy_disjoint C Y (S i) (S j) (hdisj i hi) (hdisj j hj) (hinter i j hij)
  have hsub : I.biUnion A ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hw
    exact Finset.mem_Ico.mpr ((mem_asg C Y (S i) w).mp hwi).1
  have hs : (∑ i ∈ I, (A i).card) ≤ C.size := by
    rw [← Finset.card_biUnion hd]
    have hc := Finset.card_le_card hsub
    simpa only [Nat.card_Ico, Nat.add_sub_cancel_left] using hc
  calc
    (∑ i ∈ I, (S i).card) ≤ ∑ i ∈ I, ((A i).card+1) :=
      Finset.sum_le_sum hcount
    _ = (∑ i ∈ I, (A i).card) + I.card := by simp [Finset.sum_add_distrib]
    _ ≤ C.size + I.card := Nat.add_le_add_right hs I.card

lemma disjoint_family_bound {n m : ℕ} (C : Circuit) (t : ℕ)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (ht : t < C.gates.length) (hop : (C.gates[t]).op = GateOp.not)
    (Y : Finset (Fin n)) (S : Fin m → Finset (Fin n)) (o : Fin m → ℕ)
    (hYS : ∀ i, Disjoint Y (S i))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hY : value C (fun v => decide (v ∈ Y)) (n+t) = false)
    (hout : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    (∑ i : Fin m, (S i).card) ≤ C.size + m := by
  classical
  have h := heavy_family_sum (fixed C t false) S Y Finset.univ
    (fun i _ => hYS i) hinter (fun i _ =>
      heavy_card_le C t hgate hnot ht hop Y (S i) (o i) (hYS i) hY (hout i))
  simpa [fixed_size] using h

end PEqualNP.Outside.L_meta_997.Heavy

namespace PEqualNP.Outside.L_meta_997.light

open PEqualNP.CircuitLowerBounds

lemma budget_cut {n : ℕ} (C : Circuit) (H K : Finset ℕ)
    (hstep : ∀ w ∈ H, ∃ P : Finset ℕ,
      P.card ≤ (if w ∈ K then 2 else 1) ∧ (∀ r ∈ P, r < w) ∧
      ∀ (p : Fin n) (z : Fin n → Bool),
        (∀ r ∈ P, value C (fun v => decide (v = p)) r = true → value C z r = true) →
        value C (fun v => decide (v = p)) w = true → value C z w = true)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ H → w < t) :
    ∃ B : Finset ℕ, Disjoint B H ∧ B.card ≤ F.card + (K.filter (· < t)).card ∧
      ∀ (p : Fin n) (z : Fin n → Bool),
        (∀ w ∈ B, value C (fun v => decide (v = p)) w = true → value C z w = true) →
        ∀ w ∈ F, value C (fun v => decide (v = p)) w = true → value C z w = true := by
  classical
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., fun _ _ h => h⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ H
    · obtain ⟨P, hPcard, hP, hp⟩ := hstep t hex.2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ H → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      obtain ⟨B, hd, hc, hi⟩ := ih F' hF'
      have hsize : F'.card + 1 ≤ F.card + (if t ∈ K then 2 else 1) := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : (K.filter (· < t + 1)).card =
          (K.filter (· < t)).card + (if t ∈ K then 1 else 0) := by
        by_cases ht : t ∈ K
        · have he : K.filter (· < t + 1) = insert t (K.filter (· < t)) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hw, hlt⟩
              by_cases he : w = t
              · exact Or.inl he
              · exact Or.inr ⟨hw, by omega⟩
            · rintro (rfl | ⟨hw, hlt⟩)
              · exact ⟨ht, by omega⟩
              · exact ⟨hw, by omega⟩
          rw [he, Finset.card_insert_of_notMem (by simp)]
          simp only [ht, ite_true]
        · have he : K.filter (· < t + 1) = K.filter (· < t) := by
            ext w
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hw, hlt⟩
              have hne : w ≠ t := fun e => ht (e ▸ hw)
              exact ⟨hw, by omega⟩
            · rintro ⟨hw, hlt⟩
              exact ⟨hw, by omega⟩
          rw [he]
          simp only [ht, ite_false, Nat.add_zero]
      refine ⟨B, hd, ?_, ?_⟩
      · rw [hfilter]
        by_cases ht : t ∈ K <;> simp only [ht, ite_true, ite_false] at hsize ⊢ <;> omega
      · intro p z hz w hw
        by_cases he : w = t
        · subst w
          exact hp p z fun r hr => hi p z hz r (Finset.mem_union_right _ hr)
        · exact hi p z hz w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ H → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hi⟩ := ih F hF'
      have hle : (K.filter (· < t)).card ≤ (K.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
            by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hi⟩

def copyOr {n : ℕ} (C : Circuit) (w : ℕ) : Prop :=
  let g := C.gates.getD (w - n) ⟨GateOp.or, []⟩
  g.op = GateOp.or ∧ ∃ r ∈ g.inputs, r < w ∧ singleSupp (n := n) C r = singleSupp C w

noncomputable def refinedCharge {n : ℕ} (C : Circuit) (S : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (charge C S).filter (fun w => ¬ copyOr (n := n) C w)

lemma copyOr_step {n : ℕ} (C : Circuit) (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size)
    (hc : copyOr (n := n) C w) :
    ∃ r : ℕ, r < w ∧ ∀ (p : Fin n) (z : Fin n → Bool),
      (value C (fun v => decide (v = p)) r = true → value C z r = true) →
      value C (fun v => decide (v = p)) w = true → value C z w = true := by
  unfold copyOr at hc
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  rw [List.getD_eq_getElem _ _ hj] at hc
  obtain ⟨hop, r, hr, hrw, hs⟩ := hc
  refine ⟨r, hrw, ?_⟩
  intro p z htrans hp
  have hpr : value C (fun v => decide (v = p)) r = true := by
    apply (mem_singleSupp C r p).mp
    rw [hs]
    exact (mem_singleSupp C w p).mpr hp
  have hz := htrans hpr
  rw [gate_value C z w hn hw, hop]
  simp only [GateOp.eval, List.any_eq_true, id_eq]
  exact ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, by simp [hrw, hz]⟩

lemma refined_step {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (w : ℕ) (hw : w ∈ charge C S) :
    ∃ P : Finset ℕ, P.card ≤ (if w ∈ refinedCharge C S then 2 else 1) ∧
      (∀ r ∈ P, r < w) ∧ ∀ (p : Fin n) (z : Fin n → Bool),
        (∀ r ∈ P, value C (fun v => decide (v = p)) r = true → value C z r = true) →
        value C (fun v => decide (v = p)) w = true → value C z w = true := by
  classical
  have hg := ((mem_charge C S w).mp hw).1
  by_cases hc : copyOr (n := n) C w
  · obtain ⟨r, hr, ht⟩ := copyOr_step C w hg.1 hg.2 hc
    refine ⟨{r}, ?_, ?_, ?_⟩
    · simp [refinedCharge, hc]
    · intro q hq
      simpa using (Finset.mem_singleton.mp hq).symm ▸ hr
    · intro p z hz
      exact ht p z (hz r (Finset.mem_singleton_self r))
  · obtain ⟨P, hP, hlt, htrans⟩ := gate_inputs C hG w hg.1 hg.2
    refine ⟨P, ?_, hlt, ?_⟩
    · simpa [refinedCharge, hw, hc] using hP
    · intro p z hz
      exact htrans (fun v => decide (v = p)) z hz

lemma refined_light_bound {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (o k : ℕ)
    (hcorrect : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value C x o = decide (∃ p ∈ S, x p = true)) :
    min k S.card ≤ (refinedCharge C S).card + 1 := by
  classical
  let G := charge C S
  let K := refinedCharge C S
  by_contra! hsmall
  have hsmallS : K.card + 1 < S.card := hsmall.trans_le (min_le_right ..)
  have hsmallK : K.card + 1 < k := hsmall.trans_le (min_le_left ..)
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size :=
    fun w hw => ((mem_charge C S w).mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := budget_cut C G K (refined_step C hG S) (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ K.card + 1 := by
    have hfilter := Finset.card_filter_le K (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    omega
  let clean (w : ℕ) : Finset (Fin n) :=
    if singleSupp C w ⊆ S then singleSupp C w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : singleSupp C w ⊆ S
    · simp only [clean, ite_eq_left hs]
      by_contra! hlarge
      exact Finset.disjoint_left.mp hd hw
        ((mem_charge C S w).mpr ⟨singleSupp_gate C w (by omega), hs, by omega⟩)
    · simp [clean, hs]
  have hcover : (B.biUnion clean).card < S.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let Dn := B.filter (fun w => ¬ singleSupp C w ⊆ S)
  have hout (w : {w // w ∈ Dn}) : ∃ q : Fin n, q ∈ singleSupp C w.val ∧ q ∉ S := by
    have hns := (Finset.mem_filter.mp w.property).2
    simpa only [Finset.not_subset] using hns
  choose qs hqs using hout
  let U : Finset (Fin n) := Dn.attach.image qs
  let z : Fin n → Bool := fun v => decide (v ∈ U)
  have hUcard : U.card < k := by
    have hi := Finset.card_image_le (s := Dn.attach) (f := qs)
    have hf := Finset.card_filter_le B (fun w => ¬ singleSupp C w ⊆ S)
    simp only [Finset.card_attach] at hi
    change U.card ≤ Dn.card at hi
    change Dn.card ≤ B.card at hf
    omega
  have hweight : (Finset.univ.filter (fun v => z v = true)).card < k := by
    simpa [z] using hUcard
  have hUS : ∀ q ∈ U, q ∉ S := by
    intro q hq
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hq
    exact (hqs w).2
  have hzfalse : value C z o = false := by
    rw [hcorrect z hweight]
    simp only [decide_eq_false_iff_not, not_exists]
    intro q hq
    exact hUS q (by simpa [z] using hq.2) hq.1
  have hfire : value C (fun v => decide (v = p)) o = true := by
    rw [hcorrect]
    · simp [hp]
    · have hsingle : Finset.univ.filter (fun v : Fin n => decide (v = p) = true) = {p} := by
        ext v
        simp
      rw [hsingle, Finset.card_singleton]
      omega
  have hztrue : value C z o = true := by
    apply hcut p z _ o (Finset.mem_singleton_self o) hfire
    intro w hw hx
    by_cases hs : singleSupp C w ⊆ S
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hw, by simp only [clean, ite_eq_left hs]; exact (mem_singleSupp C w p).mpr hx⟩))
    · let d : {w // w ∈ Dn} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
      apply value_mono C hG (fun v => decide (v = qs d)) z _ w
        ((mem_singleSupp C w (qs d)).mp (hqs d).1)
      intro v hv
      have hv' : v = qs d := by simpa using hv
      subst v
      simp only [z, decide_eq_true_eq]
      exact Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩
  rw [hzfalse] at hztrue
  exact Bool.false_ne_true hztrue

end PEqualNP.Outside.L_meta_997.light

namespace PEqualNP.Outside.L_meta_997.HeavyOr

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Heavy

def off {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun p => decide (p ∉ S)

lemma sound_iff {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (w : ℕ) : sound C S w ↔ value C (off S) w = false := by
  constructor
  · intro hs
    by_contra! h
    obtain ⟨p, hp, hp'⟩ := hs _ (by simpa using h)
    exact of_decide_eq_true hp' hp
  · intro hf x hx
    by_contra! hn
    have hm : value C (off S) w = true := by
      apply value_mono C hG x (off S) _ w hx
      intro p hp
      apply decide_eq_true
      intro hpS
      exact hn p hpS hp
    simp [hf] at hm

def readGate (C : Circuit) (n w : ℕ) : Gate :=
  C.gates.getD (w-n) ⟨GateOp.or, []⟩

lemma readGate_eq (C : Circuit) (n w : ℕ) (hn : n ≤ w) (hw : w < n+C.size) :
    readGate C n w = C.gates[w-n]'(by unfold Circuit.size at hw; omega) := by
  exact List.getD_eq_getElem _ _ (by unfold Circuit.size at hw; omega)

lemma gate_formula {n : ℕ} (C : Circuit) (w : ℕ) (hn : n ≤ w) (hw : w < n+C.size)
    (x : Fin n → Bool) :
    value C x w = (readGate C n w).op.eval
      ((readGate C n w).inputs.map fun r => if r<w then value C x r else false) := by
  rw [readGate_eq C n w hn hw]
  exact gate_value C x w hn hw

lemma or_true {n : ℕ} (C : Circuit) (w : ℕ) (hn : n ≤ w) (hw : w < n+C.size)
    (hop : (readGate C n w).op = GateOp.or) (x : Fin n → Bool) :
    value C x w = true ↔ ∃ r ∈ (readGate C n w).inputs, r<w ∧ value C x r = true := by
  rw [gate_formula C w hn hw x, hop]
  simp [GateOp.eval, List.any_eq_true]

lemma or_supp {n : ℕ} (C : Circuit) (Y : Finset (Fin n)) (w : ℕ)
    (hn : n ≤ w) (hw : w < n+C.size) (hop : (readGate C n w).op = GateOp.or) :
    supp C Y w = ((readGate C n w).inputs.toFinset.filter (· < w)).biUnion (supp C Y) := by
  ext p
  simp only [mem_supp, or_true C w hn hw hop, Finset.mem_biUnion,
    Finset.mem_filter, List.mem_toFinset]
  aesop

lemma or_sound {n : ℕ} (C : Circuit) (S : Finset (Fin n)) (w r : ℕ)
    (hn : n ≤ w) (hw : w < n+C.size) (hop : (readGate C n w).op = GateOp.or)
    (hs : sound C S w) (hr : r ∈ (readGate C n w).inputs) (hrw : r<w) :
    sound C S r := by
  intro x hx
  apply hs x
  exact (or_true C w hn hw hop x).mpr ⟨r, hr, hrw, hx⟩

lemma and_sound_parent {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y S : Finset (Fin n)) (w : ℕ) (hn : n ≤ w) (hw : w < n+C.size)
    (hop : (readGate C n w).op = GateOp.and) (hs : sound C S w)
    (hne : (supp C Y w).Nonempty) :
    ∃ r ∈ (readGate C n w).inputs, r<w ∧ sound C S r ∧ supp C Y w ⊆ supp C Y r := by
  have hf := (sound_iff C hG S w).mp hs
  rw [gate_formula C w hn hw (off S), hop] at hf
  simp only [GateOp.eval, List.all_eq_false, List.mem_map, id_eq] at hf
  obtain ⟨b, ⟨r, hr, rfl⟩, hrf⟩ := hf
  have hcover (p : Fin n) (hp : p ∈ supp C Y w) :
      (if r<w then value C (fun v => decide (v ∈ Y ∨ v=p)) r else false) = true := by
    have hv := (mem_supp C Y w p).mp hp
    rw [gate_formula C w hn hw _, hop] at hv
    simp only [GateOp.eval, List.all_eq_true, id_eq] at hv
    exact hv _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have hrw : r<w := by
    obtain ⟨p, hp⟩ := hne
    have hv := hcover p hp
    by_contra h
    simp [h] at hv
  refine ⟨r, hr, hrw, (sound_iff C hG S r).mpr ?_, ?_⟩
  · simpa [hrw] using hrf
  · intro p hp
    exact (mem_supp C Y r p).mpr (by simpa [hrw] using hcover p hp)

noncomputable def charged {n : ℕ} (C : Circuit) (Y S : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n+C.size)).filter (fun w => sound C S w ∧
    (readGate C n w).op = GateOp.or ∧ (supp C Y w).Nonempty ∧
      ∀ r ∈ (readGate C n w).inputs, r<w → supp C Y r ≠ supp C Y w)

lemma mem_charged {n : ℕ} (C : Circuit) (Y S : Finset (Fin n)) (w : ℕ) :
    w ∈ charged C Y S ↔ (n ≤ w ∧ w<n+C.size) ∧ sound C S w ∧
      (readGate C n w).op = GateOp.or ∧ (supp C Y w).Nonempty ∧
        ∀ r ∈ (readGate C n w).inputs, r<w → supp C Y r ≠ supp C Y w := by
  classical
  simp only [charged, Finset.mem_filter, Finset.mem_Ico]

lemma branch {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y S : Finset (Fin n)) (w : ℕ) (hn : n ≤ w) (hw : w<n+C.size)
    (hs : sound C S w) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (w ∉ charged C Y S → P.card ≤ 1) ∧
      (∀ r ∈ P, r<w ∧ sound C S r) ∧ supp C Y w ⊆ P.biUnion (supp C Y) := by
  classical
  by_cases hne : (supp C Y w).Nonempty
  · have hg := hG (readGate C n w) (by rw [readGate_eq C n w hn hw]; exact List.getElem_mem _)
    rcases hg.1 with hop | hop
    · obtain ⟨r, _, hrw, hrs, hcov⟩ := and_sound_parent C hG Y S w hn hw hop hs hne
      refine ⟨{r}, by simp, by simp, ?_, ?_⟩
      · intro q hq
        have : q=r := Finset.mem_singleton.mp hq
        simpa [this] using And.intro hrw hrs
      · simpa using hcov
    · by_cases heq : ∃ r ∈ (readGate C n w).inputs, r<w ∧ supp C Y r = supp C Y w
      · obtain ⟨r, hr, hrw, hre⟩ := heq
        refine ⟨{r}, by simp, by simp, ?_, ?_⟩
        · intro q hq
          have : q=r := Finset.mem_singleton.mp hq
          subst q
          exact ⟨hrw, or_sound C S w r hn hw hop hs hr hrw⟩
        · simp [hre]
      · let P := (readGate C n w).inputs.toFinset.filter (· < w)
        refine ⟨P, (Finset.card_filter_le _ _).trans
          ((List.toFinset_card_le _).trans hg.2), ?_, ?_, ?_⟩
        · intro hnot
          apply False.elim (hnot ?_)
          apply (mem_charged C Y S w).mpr
          refine ⟨⟨hn,hw⟩,hs,hop,hne,?_⟩
          intro r hr hrw hre
          exact heq ⟨r,hr,hrw,hre⟩
        · intro r hr
          have hr' := Finset.mem_filter.mp hr
          exact ⟨hr'.2,or_sound C S w r hn hw hop hs (List.mem_toFinset.mp hr'.1) hr'.2⟩
        · exact (or_supp C Y w hn hw hop).le
  · refine ⟨∅, by simp, by simp, by simp, ?_⟩
    simp [Finset.not_nonempty_iff_eq_empty.mp hne]

lemma coverage_cut {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (Good : ℕ → Prop) (H K : Finset ℕ)
    (hstep : ∀ w ∈ H, ∃ P : Finset ℕ,
      P.card ≤ (if w ∈ K then 2 else 1) ∧ (∀ r ∈ P, r<w ∧ Good r) ∧
        support w ⊆ P.biUnion support)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ H → w<t)
    (hGood : ∀ w ∈ F, Good w) :
    ∃ B : Finset ℕ, Disjoint B H ∧ B.card ≤ F.card + (K.filter (· < t)).card ∧
      (∀ w ∈ B, Good w) ∧ F.biUnion support ⊆ B.biUnion support := by
  classical
  induction t generalizing F with
  | zero =>
    exact ⟨F, Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega),
      Nat.le_add_right .., hGood, Finset.Subset.refl _⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ H
    · obtain ⟨P, hPcard, hP, hp⟩ := hstep t hex.2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ H → w<t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact (hP w hw).1
      have hGood' : ∀ w ∈ F', Good w := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hGood w (Finset.mem_erase.mp hw).2
        · exact (hP w hw).2
      obtain ⟨B, hd, hc, hb, hi⟩ := ih F' hF' hGood'
      have hsize : F'.card + 1 ≤ F.card + (if t ∈ K then 2 else 1) := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : (K.filter (· < t+1)).card =
          (K.filter (· < t)).card + (if t ∈ K then 1 else 0) := by
        by_cases ht : t ∈ K
        · have he : K.filter (· < t+1) = insert t (K.filter (· < t)) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hw, hlt⟩
              by_cases he : w=t
              · exact Or.inl he
              · exact Or.inr ⟨hw,by omega⟩
            · rintro (rfl | ⟨hw,hlt⟩)
              · exact ⟨ht,by omega⟩
              · exact ⟨hw,by omega⟩
          rw [he, Finset.card_insert_of_notMem (by simp)]
          simp only [ht,ite_true]
        · have he : K.filter (· < t+1) = K.filter (· < t) := by
            ext w
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hw,hlt⟩
              have hne : w≠t := fun e => ht (e ▸ hw)
              exact ⟨hw,by omega⟩
            · rintro ⟨hw,hlt⟩
              exact ⟨hw,by omega⟩
          rw [he]
          simp only [ht,ite_false,Nat.add_zero]
      refine ⟨B,hd,?_,hb,?_⟩
      · rw [hfilter]
        by_cases ht : t ∈ K <;> simp only [ht,ite_true,ite_false] at hsize ⊢ <;> omega
      · intro p hpF
        apply hi
        obtain ⟨w,hw,hpw⟩ := Finset.mem_biUnion.mp hpF
        by_cases he : w=t
        · subst w
          obtain ⟨r,hr,hpr⟩ := Finset.mem_biUnion.mp (hp hpw)
          exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_union_right _ hr,hpr⟩
        · exact Finset.mem_biUnion.mpr
            ⟨w,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hw⟩),hpw⟩
    · have hF' : ∀ w ∈ F, w ∈ H → w<t := by
        intro w hw hg
        have hne : w≠t := fun e => hex ⟨e ▸ hw,e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B,hd,hc,hb,hi⟩ := ih F hF' hGood
      have hle : (K.filter (· < t)).card ≤ (K.filter (· < t+1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
            by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B,hd,by omega,hb,hi⟩

lemma charge_count {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y S : Finset (Fin n)) (o : ℕ) (hYS : Disjoint Y S) (hso : sound C S o)
    (hfire : ∀ p ∈ S, value C (fun v => decide (v ∈ Y ∨ v=p)) o = true) :
    S.card ≤ (charged C Y S).card + 1 := by
  classical
  let H := (Finset.Ico n (n+C.size)).filter (sound C S)
  have hstep : ∀ w ∈ H, ∃ P : Finset ℕ,
      P.card ≤ (if w ∈ charged C Y S then 2 else 1) ∧
        (∀ r ∈ P, r<w ∧ sound C S r) ∧ supp C Y w ⊆ P.biUnion (supp C Y) := by
    intro w hw
    have hg := Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
    obtain ⟨P,hP,hP',hp,hcover⟩ := branch C hG Y S w hg.1 hg.2 (Finset.mem_filter.mp hw).2
    refine ⟨P,?_,hp,hcover⟩
    split_ifs with hc
    · exact hP
    · exact hP' hc
  obtain ⟨B,hd,hB,hBs,hcov⟩ := coverage_cut (supp C Y) (sound C S) H (charged C Y S)
    hstep (n+C.size) {o}
      (fun w _ hw => (Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1).2)
      (fun w hw => by have : w=o := Finset.mem_singleton.mp hw; simpa [this] using hso)
  have hsmall : ∀ w ∈ B, (supp C Y w).card ≤ 1 := by
    intro w hw
    by_contra! hlarge
    have hg := supp_gate C Y S w hYS (hBs w hw) (by omega)
    exact Finset.disjoint_left.mp hd hw (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hg,hBs w hw⟩)
  have hS : S ⊆ B.biUnion (supp C Y) := by
    intro p hp
    apply hcov
    exact Finset.mem_biUnion.mpr ⟨o,Finset.mem_singleton_self o,(mem_supp C Y o p).mpr (hfire p hp)⟩
  have h1 := Finset.card_le_card hS
  have h2 := Finset.card_biUnion_le_card_mul B (supp C Y) 1 hsmall
  have h3 := Finset.card_filter_le (charged C Y S) (fun w => w<n+C.size)
  simp only [Finset.card_singleton] at hB
  simp only [mul_one] at h2
  omega

end PEqualNP.Outside.L_meta_997.HeavyOr

namespace PEqualNP.Outside.L_meta_997.HeavyOr

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Heavy

lemma charged_subset_asg {n : ℕ} (C : Circuit) (Y S : Finset (Fin n)) :
    charged C Y S ⊆ asg C Y S := by
  classical
  intro w hw
  obtain ⟨⟨hn,hW⟩,hs,hop,hne,hfresh⟩ := (mem_charged C Y S w).mp hw
  apply (mem_asg C Y S w).mpr
  refine ⟨⟨hn,hW⟩,hs,?_⟩
  by_contra! hlt
  have hsmall : (supp C Y w).card ≤ 1 := by omega
  obtain ⟨p,hp⟩ := hne
  have hp' : p ∈ ((readGate C n w).inputs.toFinset.filter (· < w)).biUnion (supp C Y) := by
    rw [← or_supp C Y w hn hW hop]
    exact hp
  obtain ⟨r,hr,hrp⟩ := Finset.mem_biUnion.mp hp'
  have hr' := Finset.mem_filter.mp hr
  apply hfresh r (List.mem_toFinset.mp hr'.1) hr'.2
  apply Finset.ext
  intro q
  constructor
  · intro hqr
    rw [or_supp C Y w hn hW hop]
    exact Finset.mem_biUnion.mpr ⟨r,hr,hqr⟩
  · intro hqw
    have hqp : q=p := Finset.card_le_one_iff.mp hsmall hqw hp
    simpa [hqp] using hrp

lemma charged_disjoint {n : ℕ} (C : Circuit) (Y Si Sj : Finset (Fin n))
    (hi : Disjoint Y Si) (hj : Disjoint Y Sj) (hij : (Si ∩ Sj).card ≤ 1) :
    Disjoint (charged C Y Si) (charged C Y Sj) :=
  (heavy_disjoint C Y Si Sj hi hj hij).mono
    (charged_subset_asg C Y Si) (charged_subset_asg C Y Sj)

lemma heavy_or_count {n : ℕ} (C : Circuit) (t : ℕ)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (ht : t < C.gates.length) (hop : (C.gates[t]).op = GateOp.not)
    (Y S : Finset (Fin n)) (o : ℕ) (hYS : Disjoint Y S)
    (hY : value C (fun v => decide (v ∈ Y)) (n+t) = false)
    (hout : ∀ x : Fin n → Bool, value C x o = decide (∃ p ∈ S, x p = true)) :
    S.card ≤ (charged (fixed C t false) Y S).card + 1 := by
  apply charge_count (fixed C t false) (fixed_good C t false hgate hnot) Y S o hYS
  · intro x hx
    have h := fixed_false_le C t hgate hnot x o hx
    simpa [hout] using h
  · intro p hp
    rw [fixed_false_eq_above C t hgate hnot ht hop
      (fun v => decide (v ∈ Y)) (fun v => decide (v ∈ Y ∨ v = p))
      (by intro v hv; simpa using Or.inl (of_decide_eq_true hv)) hY o, hout]
    exact decide_eq_true ⟨p,hp,by simp⟩

end PEqualNP.Outside.L_meta_997.HeavyOr

namespace PEqualNP.Outside.L_meta_997.HeavyOr

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Heavy

lemma charged_fixed_ne {n : ℕ} (C : Circuit) (t : ℕ) (Y S : Finset (Fin n))
    (w : ℕ) (hw : w ∈ charged (fixed C t false) Y S) : w ≠ n+t := by
  intro heq
  have h := (mem_charged (fixed C t false) Y S w).mp hw
  have ht : t < C.gates.length := by
    have hb := h.1.2
    rw [fixed_size] at hb
    unfold Circuit.size at hb
    omega
  obtain ⟨p,hp⟩ := h.2.2.2.1
  have hv := (mem_supp (fixed C t false) Y w p).mp hp
  rw [heq,fixed_at C t false ht] at hv
  exact Bool.false_ne_true hv

lemma readGate_fixed_other (C : Circuit) (n t w : ℕ) (b : Bool)
    (hn : n ≤ w) (hw : w<n+C.size) (hne : w≠n+t) :
    readGate (fixed C t b) n w = readGate C n w := by
  rw [readGate_eq (fixed C t b) n w hn (by rw [fixed_size]; exact hw),
    readGate_eq C n w hn hw]
  simp only [fixed,List.getElem_set]
  rw [ite_eq_right (by omega)]

lemma heavy_or_original {n : ℕ} (C : Circuit) (t : ℕ)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (ht : t < C.gates.length) (hop : (C.gates[t]).op = GateOp.not)
    (Y S : Finset (Fin n)) (hYS : Disjoint Y S)
    (hY : value C (fun v => decide (v ∈ Y)) (n+t) = false)
    (w : ℕ) (hw : w ∈ charged (fixed C t false) Y S) :
    n ≤ w ∧ w<n+C.size ∧ w≠n+t ∧ (readGate C n w).op = GateOp.or ∧
      value C (fun v => decide (v ∈ Y)) w = false ∧
      2 ≤ (supp C Y w).card ∧ supp C Y w ⊆ S ∧
      ∀ r ∈ (readGate C n w).inputs, r<w → supp C Y r ≠ supp C Y w := by
  have hc := (mem_charged (fixed C t false) Y S w).mp hw
  have hb : n ≤ w ∧ w<n+C.size := by simpa [fixed_size] using hc.1
  have hne := charged_fixed_ne C t Y S w hw
  have hg := readGate_fixed_other C n t w false hb.1 hb.2 hne
  have ha := charged_subset_asg (fixed C t false) Y S hw
  have has := (mem_asg (fixed C t false) Y S w).mp ha
  have heq := heavy_supp_eq C t hgate hnot ht hop Y hY
  refine ⟨hb.1,hb.2,hne,?_,heavy_base_false C t Y S hYS hY w ha,?_,?_,?_⟩
  · simpa [hg] using hc.2.2.1
  · simpa [heq w] using has.2.2
  · rw [← heq w]
    exact sound_supp_subset (fixed C t false) Y S hYS w has.2.1
  · intro r hr hrw he
    have hf := hc.2.2.2.2 r (by simpa [hg] using hr) hrw
    exact hf (by simpa only [heq] using he)

end PEqualNP.Outside.L_meta_997.HeavyOr

namespace PEqualNP.Outside.L_meta_997.Prefix

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Heavy

lemma empty_support_count {n k : ℕ} (C : Circuit) (o : ℕ) (y : Fin n → Bool)
    (hgate : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hy : value C y o = true)
    (hsmall : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun p => x p = true)).card < k → value C x o = false) :
    k ≤ ((Finset.Ico n (n + C.size)).filter
      (fun w => supp C (∅ : Finset (Fin n)) w = ∅ ∧ value C y w = true)).card + 1 := by
  classical
  let G := (Finset.Ico n (n + C.size)).filter
    (fun w => supp C (∅ : Finset (Fin n)) w = ∅ ∧ value C y w = true)
  by_contra! hbad
  have hG : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hc, hcut⟩ := cut C hgate G hG (n + C.size) {o}
    (fun w _ hw => (hG w hw).2)
  have hBc : B.card ≤ G.card + 1 := by
    have hf := Finset.card_filter_le G (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hc
    omega
  let D := B.filter (fun w => value C y w = true)
  have hnonempty (w : {w // w ∈ D}) : (supp C (∅ : Finset (Fin n)) w.val).Nonempty := by
    have hwB := (Finset.mem_filter.mp w.property).1
    have hwy := (Finset.mem_filter.mp w.property).2
    by_contra! hempty
    have hempty' : supp C (∅ : Finset (Fin n)) w.val = ∅ :=
      hempty
    by_cases hn : w.val < n
    · let p : Fin n := ⟨w.val, hn⟩
      have hp : p ∈ supp C (∅ : Finset (Fin n)) w.val := by
        rw [mem_supp]
        change value C (fun v => decide (v ∈ (∅ : Finset (Fin n)) ∨ v = p)) p = true
        simp [input_value]
      simp [hempty'] at hp
    · by_cases hW : w.val < n + C.size
      · have hwG : w.val ∈ G := Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨by omega, hW⟩, hempty', hwy⟩
        exact Finset.disjoint_left.mp hd hwB hwG
      · rw [missing_value C y w.val (by omega)] at hwy
        exact Bool.false_ne_true hwy
  choose q hq using hnonempty
  let U := D.attach.image q
  let x : Fin n → Bool := fun p => decide (p ∈ U)
  have hU : U.card < k := by
    have h1 : U.card ≤ D.attach.card := Finset.card_image_le
    have h2 := Finset.card_filter_le B (fun w => value C y w = true)
    simp only [Finset.card_attach] at h1
    change D.card ≤ B.card at h2
    change G.card + 1 < k at hbad
    omega
  have hxf : value C x o = false := by
    apply hsmall x
    have he : Finset.univ.filter (fun p => x p = true) = U := by
      ext p
      simp [x]
    rwa [he]
  have hxt : value C x o = true := by
    apply hcut y x _ o (Finset.mem_singleton_self o) hy
    intro w hw hwy
    let d : {w // w ∈ D} := ⟨w, Finset.mem_filter.mpr ⟨hw, hwy⟩⟩
    apply value_mono C hgate (fun v => decide (v ∈ (∅ : Finset (Fin n)) ∨ v = q d)) x _ w
      ((mem_supp C ∅ w (q d)).mp (hq d))
    intro p hp
    have he : p = q d := by simpa using hp
    subst p
    have hm : q d ∈ U := Finset.mem_image_of_mem q (Finset.mem_attach D d)
    simpa [x] using hm
  rw [hxf] at hxt
  exact Bool.false_ne_true hxt

end PEqualNP.Outside.L_meta_997.Prefix
namespace PEqualNP.Outside.L_meta_997.HeavySelected

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Heavy PEqualNP.Outside.L_meta_997.HeavyOr

lemma branch_edges {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y S : Finset (Fin n)) (w : ℕ) (hn : n ≤ w) (hw : w<n+C.size)
    (hs : sound C S w) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (w ∉ charged C Y S → P.card ≤ 1) ∧
      (∀ r ∈ P, r<w ∧ sound C S r ∧ r ∈ (readGate C n w).inputs) ∧
      supp C Y w ⊆ P.biUnion (supp C Y) := by
  classical
  by_cases hne : (supp C Y w).Nonempty
  · have hg := hG (readGate C n w) (by rw [readGate_eq C n w hn hw]; exact List.getElem_mem _)
    rcases hg.1 with hop | hop
    · obtain ⟨r,hr,hrw,hrs,hcov⟩ := and_sound_parent C hG Y S w hn hw hop hs hne
      refine ⟨{r},by simp,by simp,?_,?_⟩
      · intro q hq
        have : q=r := Finset.mem_singleton.mp hq
        subst q
        exact ⟨hrw,hrs,hr⟩
      · simpa using hcov
    · by_cases heq : ∃ r ∈ (readGate C n w).inputs, r<w ∧ supp C Y r = supp C Y w
      · obtain ⟨r,hr,hrw,hre⟩ := heq
        refine ⟨{r},by simp,by simp,?_,?_⟩
        · intro q hq
          have : q=r := Finset.mem_singleton.mp hq
          subst q
          exact ⟨hrw,or_sound C S w r hn hw hop hs hr hrw,hr⟩
        · simp [hre]
      · let P := (readGate C n w).inputs.toFinset.filter (· < w)
        refine ⟨P,(Finset.card_filter_le _ _).trans
          ((List.toFinset_card_le _).trans hg.2),?_,?_,?_⟩
        · intro hnot
          apply False.elim (hnot ?_)
          apply (mem_charged C Y S w).mpr
          refine ⟨⟨hn,hw⟩,hs,hop,hne,?_⟩
          intro r hr hrw hre
          exact heq ⟨r,hr,hrw,hre⟩
        · intro r hr
          have hr' := Finset.mem_filter.mp hr
          exact ⟨hr'.2,or_sound C S w r hn hw hop hs
            (List.mem_toFinset.mp hr'.1) hr'.2,List.mem_toFinset.mp hr'.1⟩
        · exact (or_supp C Y w hn hw hop).le
  · refine ⟨∅,by simp,by simp,by simp,?_⟩
    simp [Finset.not_nonempty_iff_eq_empty.mp hne]

lemma coverage_used {α : Type*} [DecidableEq α] (support : ℕ → Finset α)
    (Good : ℕ → Prop) (H K : Finset ℕ) (parents : ℕ → Finset ℕ)
    (hstep : ∀ w ∈ H,
      (parents w).card ≤ (if w ∈ K then 2 else 1) ∧
      (∀ r ∈ parents w, r<w ∧ Good r) ∧ support w ⊆ (parents w).biUnion support)
    (R : Set ℕ) (hR : ∀ w ∈ H, w ∈ R → ∀ r ∈ parents w, r ∈ R)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ H → w<t)
    (hGood : ∀ w ∈ F, Good w) (hFR : ∀ w ∈ F, w ∈ R) :
    ∃ B U : Finset ℕ, Disjoint B H ∧ B.card ≤ F.card + U.card ∧
      (∀ w ∈ B, Good w ∧ w ∈ R) ∧ F.biUnion support ⊆ B.biUnion support ∧
      ∀ w ∈ U, w ∈ H ∧ w ∈ K ∧ w<t ∧ w ∈ R := by
  classical
  induction t generalizing F with
  | zero =>
    refine ⟨F,∅,?_,by simp,?_,Finset.Subset.refl _,by simp⟩
    · exact Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega)
    · intro w hw
      exact ⟨hGood w hw,hFR w hw⟩
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ H
    · obtain ⟨hPcard,hP,hp⟩ := hstep t hex.2
      let F' := F.erase t ∪ parents t
      have hF' : ∀ w ∈ F', w ∈ H → w<t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact (hP w hw).1
      have hGood' : ∀ w ∈ F', Good w := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hGood w (Finset.mem_erase.mp hw).2
        · exact (hP w hw).2
      have hR' : ∀ w ∈ F', w ∈ R := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hFR w (Finset.mem_erase.mp hw).2
        · exact hR t hex.2 (hFR t hex.1) w hw
      obtain ⟨B,U,hd,hc,hb,hcov,hu⟩ := ih F' hF' hGood' hR'
      have hsize : F'.card + 1 ≤ F.card + (if t ∈ K then 2 else 1) := by
        have hUnion := Finset.card_union_le (F.erase t) (parents t)
        have hErase := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hUnion
        omega
      have hcov' : F.biUnion support ⊆ B.biUnion support := by
        intro p hpF
        apply hcov
        obtain ⟨w,hw,hpw⟩ := Finset.mem_biUnion.mp hpF
        by_cases he : w=t
        · subst w
          obtain ⟨r,hr,hpr⟩ := Finset.mem_biUnion.mp (hp hpw)
          exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_union_right _ hr,hpr⟩
        · exact Finset.mem_biUnion.mpr
            ⟨w,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he,hw⟩),hpw⟩
      by_cases ht : t ∈ K
      · have htu : t ∉ U := by intro h; have := (hu t h).2.2.1; omega
        refine ⟨B,insert t U,hd,?_,hb,hcov',?_⟩
        · rw [Finset.card_insert_of_notMem htu]
          simp only [ht,ite_true] at hsize
          omega
        · intro w hw
          rcases Finset.mem_insert.mp hw with he | hw
          · subst w
            exact ⟨hex.2,ht,by omega,hFR t hex.1⟩
          · obtain ⟨hwH,hwK,hwt,hwR⟩ := hu w hw
            exact ⟨hwH,hwK,by omega,hwR⟩
      · refine ⟨B,U,hd,?_,hb,hcov',?_⟩
        · simp only [ht,ite_false] at hsize
          omega
        · intro w hw
          obtain ⟨hwH,hwK,hwt,hwR⟩ := hu w hw
          exact ⟨hwH,hwK,by omega,hwR⟩
    · have hF' : ∀ w ∈ F, w ∈ H → w<t := by
        intro w hw hg
        have hne : w≠t := fun e => hex ⟨e ▸ hw,e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B,U,hd,hc,hb,hcov,hu⟩ := ih F hF' hGood hFR
      refine ⟨B,U,hd,hc,hb,hcov,?_⟩
      intro w hw
      obtain ⟨hwH,hwK,hwt,hwR⟩ := hu w hw
      exact ⟨hwH,hwK,by omega,hwR⟩

lemma selected_count {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y S : Finset (Fin n)) (o : ℕ) (hYS : Disjoint Y S) (hso : sound C S o)
    (hfire : ∀ p ∈ S, value C (fun v => decide (v ∈ Y ∨ v=p)) o = true) :
    ∃ (parents : ℕ → Finset ℕ) (U : Finset ℕ), U ⊆ charged C Y S ∧
      S.card ≤ U.card + 1 ∧
      (∀ w, (n ≤ w ∧ w<n+C.size) → sound C S w →
        (parents w).card ≤ (if w ∈ charged C Y S then 2 else 1) ∧
        (∀ r ∈ parents w, r<w ∧ sound C S r) ∧
        supp C Y w ⊆ (parents w).biUnion (supp C Y)) ∧
      (∀ w ∈ U, Relation.ReflTransGen (fun a b => b ∈ parents a) o w) ∧
      (∀ w r, r ∈ parents w → (n ≤ w ∧ w<n+C.size) ∧ sound C S w ∧
        r<w ∧ sound C S r ∧ r ∈ (readGate C n w).inputs ∧ (supp C Y r).Nonempty) := by
  classical
  let H := (Finset.Ico n (n+C.size)).filter (sound C S)
  have hbranch : ∀ w ∈ H, ∃ P : Finset ℕ,
      P.card ≤ (if w ∈ charged C Y S then 2 else 1) ∧
        (∀ r ∈ P, r<w ∧ sound C S r ∧ r ∈ (readGate C n w).inputs ∧ (supp C Y r).Nonempty) ∧
          supp C Y w ⊆ P.biUnion (supp C Y) := by
    intro w hw
    have hg := Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
    obtain ⟨P,hP,hP',hp,hcover⟩ := branch_edges C hG Y S w hg.1 hg.2 (Finset.mem_filter.mp hw).2
    let Q := P.filter (fun r => (supp C Y r).Nonempty)
    refine ⟨Q,?_,?_,?_⟩
    · have hQP : Q.card ≤ P.card := Finset.card_filter_le _ _
      split_ifs with hc
      · exact hQP.trans hP
      · exact hQP.trans (hP' hc)
    · intro r hr
      have hr' := Finset.mem_filter.mp hr
      exact ⟨(hp r hr'.1).1,(hp r hr'.1).2.1,(hp r hr'.1).2.2,hr'.2⟩
    · intro p hpw
      obtain ⟨r,hr,hpr⟩ := Finset.mem_biUnion.mp (hcover hpw)
      exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_filter.mpr ⟨hr,⟨p,hpr⟩⟩,hpr⟩
  let parents := fun w => if hw : w ∈ H then Classical.choose (hbranch w hw) else ∅
  have hpFull : ∀ w ∈ H,
      (parents w).card ≤ (if w ∈ charged C Y S then 2 else 1) ∧
        (∀ r ∈ parents w, r<w ∧ sound C S r ∧ r ∈ (readGate C n w).inputs ∧
          (supp C Y r).Nonempty) ∧
        supp C Y w ⊆ (parents w).biUnion (supp C Y) := by
    intro w hw
    simpa only [parents,dite_eq_left hw] using Classical.choose_spec (hbranch w hw)
  have hp : ∀ w ∈ H,
      (parents w).card ≤ (if w ∈ charged C Y S then 2 else 1) ∧
        (∀ r ∈ parents w, r<w ∧ sound C S r) ∧
        supp C Y w ⊆ (parents w).biUnion (supp C Y) := by
    intro w hw
    have hh := hpFull w hw
    exact ⟨hh.1,fun r hr => ⟨(hh.2.1 r hr).1,(hh.2.1 r hr).2.1⟩,hh.2.2⟩
  let R := {w | Relation.ReflTransGen (fun a b => b ∈ parents a) o w}
  have hR : ∀ w ∈ H, w ∈ R → ∀ r ∈ parents w, r ∈ R := by
    intro w _ hw r hr
    exact Relation.ReflTransGen.tail hw hr
  obtain ⟨B,U,hd,hB,hBs,hcov,hu⟩ := coverage_used (supp C Y) (sound C S)
    H (charged C Y S) parents hp R hR (n+C.size) {o}
      (fun w _ hw => (Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1).2)
      (fun w hw => by have : w=o := Finset.mem_singleton.mp hw; simpa [this] using hso)
      (fun w hw => by have : w=o := Finset.mem_singleton.mp hw; subst w; exact Relation.ReflTransGen.refl)
  refine ⟨parents,U,?_,?_,?_,?_,?_⟩
  · intro w hw
    exact (hu w hw).2.1
  · have hsmall : ∀ w ∈ B, (supp C Y w).card ≤ 1 := by
      intro w hw
      by_contra! hlarge
      have hg := supp_gate C Y S w hYS (hBs w hw).1 (by omega)
      exact Finset.disjoint_left.mp hd hw
        (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hg,(hBs w hw).1⟩)
    have hS : S ⊆ B.biUnion (supp C Y) := by
      intro p hpS
      apply hcov
      exact Finset.mem_biUnion.mpr
        ⟨o,Finset.mem_singleton_self o,(mem_supp C Y o p).mpr (hfire p hpS)⟩
    have h1 := Finset.card_le_card hS
    have h2 := Finset.card_biUnion_le_card_mul B (supp C Y) 1 hsmall
    simp only [Finset.card_singleton] at hB
    simp only [mul_one] at h2
    omega
  · intro w hg hs
    exact hp w (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hg,hs⟩)
  · intro w hw
    exact (hu w hw).2.2.2
  · intro w r hr
    by_cases hw : w ∈ H
    · exact ⟨Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1,
        (Finset.mem_filter.mp hw).2,(hpFull w hw).2.1 r hr⟩
    · simp [parents,hw] at hr

end PEqualNP.Outside.L_meta_997.HeavySelected

namespace PEqualNP.Outside.L_meta_997.BoundedDisjoint

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.light

lemma capped_disjoint_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → (i : ℕ) = t)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true))
    (hlow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card →
        (C.wires (List.ofFn x)).getD (n + t) false = true)
    (hfalse : (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD
      (n + t) false = false)
    (hcap : ∀ i : Fin m, Disjoint (S i) y → (S i).card ≤ y.card + 1) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length =>
        (∃ i : Fin m, ∀ p : Fin n,
          (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧
        (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y →
          ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD
            (n + g) false = true ↔ p ∈ S i)))).card + m := by
  classical
  by_cases hy : y.card ≤ 2
  · have h := small_window_bound S C o t y hinter hgate hnot hcorrect hfalse hy
    omega
  · let I := Finset.univ.filter (fun i : Fin m => Disjoint (S i) y ∧ 2 ≤ (S i).card)
    have hterm (i : Fin m) :
        (if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
          min y.card (S i).card + (if i ∈ I then 1 else 0) := by
      by_cases hd : Disjoint (S i) y
      · rw [if_pos hd]
        by_cases hc : (S i).card ≤ y.card
        · rw [min_eq_right hc]
          omega
        · have hi : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, by omega⟩
          rw [min_eq_left (by omega), if_pos hi]
          exact hcap i hd
      · rw [if_neg hd]
        omega
    have hs : (∑ i : Fin m, min y.card (S i).card) ≤ C.gates.length + m :=
      truncated_sum_original S C o t y.card hinter hgate hnot hcorrect hlow
    have hr := PEqualNP.Outside.L_meta_997.Refund.refund_output_count S C o y hinter hcorrect
    have hsum :
        (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
          (∑ i : Fin m, min y.card (S i).card) + I.card := by
      calc
        _ ≤ ∑ i : Fin m, (min y.card (S i).card + if i ∈ I then 1 else 0) :=
          Finset.sum_le_sum fun i _ => hterm i
        _ = _ := by simp [Finset.sum_add_distrib]
    change I.card ≤ _ at hr
    change (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length =>
        (∃ i : Fin m, ∀ p : Fin n, value C (fun v => decide (v = p)) (n + g) = true ↔ p ∈ S i) ∧
        (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y →
          (value C (fun v => decide (v ∈ y ∨ v = p)) (n + g) = true ↔ p ∈ S i)))).card + m
    omega

end PEqualNP.Outside.L_meta_997.BoundedDisjoint
namespace PEqualNP.Outside.L_meta_997.Exclusion

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.light

def within {n : ℕ} (C : Circuit) (T : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  singleSupp C w ∩ T

lemma false_branch {n : ℕ} (C : Circuit) (T : Finset (Fin n)) (q : Fin n)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not →
      value C (fun v => decide (v = q)) (n + j.val) = true)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size)
    (hq : value C (fun v => decide (v = q)) w = false)
    (hne : (within C T w).Nonempty) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧
      (∀ r ∈ P, r < w ∧ value C (fun v => decide (v = q)) r = false) ∧
      within C T w ⊆ P.biUnion (within C T) := by
  classical
  let g := PEqualNP.Outside.L_meta_997.HeavyOr.readGate C n w
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  have hge : g = C.gates[w - n] :=
    PEqualNP.Outside.L_meta_997.HeavyOr.readGate_eq C n w hn hw
  have hg := hgate g (by rw [hge]; exact List.getElem_mem _)
  have hform (x : Fin n → Bool) :
      value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) :=
    PEqualNP.Outside.L_meta_997.HeavyOr.gate_formula C w hn hw x
  rcases hg.1 with hop | hop | hop
  · have hf := hq
    rw [hform, hop] at hf
    simp only [GateOp.eval, List.all_eq_false, List.mem_map, id_eq] at hf
    obtain ⟨b, ⟨r, hr, rfl⟩, hrf⟩ := hf
    have hcover (p : Fin n) (hp : p ∈ within C T w) :
        (if r < w then value C (fun v => decide (v = p)) r else false) = true := by
      have hv := (mem_singleSupp C w p).mp (Finset.mem_inter.mp hp).1
      rw [hform, hop] at hv
      simp only [GateOp.eval, List.all_eq_true, id_eq] at hv
      exact hv _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
    have hrw : r < w := by
      obtain ⟨p, hp⟩ := hne
      have hv := hcover p hp
      by_contra h
      simp [h] at hv
    refine ⟨{r}, by simp, ?_, ?_⟩
    · intro a ha
      have he : a = r := Finset.mem_singleton.mp ha
      subst a
      exact ⟨hrw, by simpa [hrw] using hrf⟩
    · intro p hp
      have hp' : p ∈ within C T r := Finset.mem_inter.mpr
        ⟨(mem_singleSupp C r p).mpr (by simpa [hrw] using hcover p hp),
          (Finset.mem_inter.mp hp).2⟩
      exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_singleton_self r, hp'⟩
  · let P := g.inputs.toFinset.filter (· < w)
    refine ⟨P, (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hg.2), ?_, ?_⟩
    · intro r hr
      have hr' := Finset.mem_filter.mp hr
      refine ⟨hr'.2, ?_⟩
      have hf := hq
      rw [hform, hop] at hf
      simp only [GateOp.eval, List.any_eq_false, id_eq] at hf
      have h := hf _ (List.mem_map.mpr ⟨r, List.mem_toFinset.mp hr'.1, rfl⟩)
      simpa [hr'.2] using h
    · intro p hp
      have hv := (mem_singleSupp C w p).mp (Finset.mem_inter.mp hp).1
      rw [hform, hop] at hv
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hv
      obtain ⟨b, ⟨r, hr, rfl⟩, hrt⟩ := hv
      have hrw : r < w := by
        by_contra h
        simp [h] at hrt
      refine Finset.mem_biUnion.mpr ⟨r,
        Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, hrw⟩, ?_⟩
      exact Finset.mem_inter.mpr
        ⟨(mem_singleSupp C r p).mpr (by simpa [hrw] using hrt),
          (Finset.mem_inter.mp hp).2⟩
  · have hjnot : (C.gates.get ⟨w - n, hj⟩).op = GateOp.not := by simpa [hge] using hop
    have ht := hnot ⟨w - n, hj⟩ hjnot
    have he : n + (w - n) = w := by omega
    simp only [he] at ht
    rw [hq] at ht
    exact False.elim (Bool.false_ne_true ht)

lemma single_heavy_budget {n : ℕ} (C : Circuit) (T : Finset (Fin n)) (o : ℕ)
    (q : Fin n) (M : Finset ℕ)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not →
      value C (fun v => decide (v = q)) (n + j.val) = true)
    (hcorrect : ∀ x : Fin n → Bool,
      value C x o = decide (∃ p ∈ T, x p = true))
    (hqT : q ∉ T)
    (hMrange : M ⊆ Finset.Ico n (n + C.size))
    (hM : ∀ w ∈ M, (singleSupp C w ∩ T).card ≤ 1) :
    T.card ≤ ((Finset.Ico n (n + C.size)) \ M).card + 1 := by
  classical
  let E := (Finset.Ico n (n + C.size)) \ M
  let H := E.filter (fun w => value C (fun v => decide (v = q)) w = false ∧
    (within C T w).Nonempty)
  have hstep : ∀ w ∈ H, ∃ P : Finset ℕ,
      P.card ≤ (if w ∈ H then 2 else 1) ∧
      (∀ r ∈ P, r < w ∧ value C (fun v => decide (v = q)) r = false) ∧
      within C T w ⊆ P.biUnion (within C T) := by
    intro w hw
    have hw' := Finset.mem_filter.mp hw
    have hrange := Finset.mem_Ico.mp (Finset.mem_sdiff.mp hw'.1).1
    obtain ⟨P, hp, hfalse, hcover⟩ := false_branch C T q hgate hnot w
      hrange.1 hrange.2 hw'.2.1 hw'.2.2
    exact ⟨P, by simpa only [hw, ite_true] using hp, hfalse, hcover⟩
  have ho : value C (fun v => decide (v = q)) o = false := by
    rw [hcorrect]
    simp [hqT]
  obtain ⟨B, hd, hB, hGood, hcover⟩ :=
    PEqualNP.Outside.L_meta_997.HeavyOr.coverage_cut (within C T)
      (fun w => value C (fun v => decide (v = q)) w = false) H H hstep
      (n + C.size) {o}
      (fun w _ hw => (Finset.mem_Ico.mp (Finset.mem_sdiff.mp
        (Finset.mem_filter.mp hw).1).1).2)
      (fun w hw => by have he : w = o := Finset.mem_singleton.mp hw; simpa [he] using ho)
  have hsmall : ∀ w ∈ B, (within C T w).card ≤ 1 := by
    intro w hw
    by_cases hm : w ∈ M
    · exact hM w hm
    · by_contra! hc
      have hsub : within C T w ⊆ singleSupp C w := Finset.inter_subset_left
      have hg := singleSupp_gate C w (by have := Finset.card_le_card hsub; omega)
      have hwH : w ∈ H := Finset.mem_filter.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_Ico.mpr hg, hm⟩, hGood w hw,
          Finset.card_pos.mp (by omega)⟩
      exact Finset.disjoint_left.mp hd hw hwH
  have hT : T ⊆ B.biUnion (within C T) := by
    intro p hp
    apply hcover
    refine Finset.mem_biUnion.mpr ⟨o, Finset.mem_singleton_self o, ?_⟩
    apply Finset.mem_inter.mpr
    refine ⟨(mem_singleSupp C o p).mpr ?_, hp⟩
    rw [hcorrect]
    simp [hp]
  have h1 := Finset.card_le_card hT
  have h2 := Finset.card_biUnion_le_card_mul B (within C T) 1 hsmall
  have h3 : (H.filter (· < n + C.size)).card ≤ E.card :=
    (Finset.card_filter_le _ _).trans (Finset.card_filter_le _ _)
  simp only [Finset.card_singleton] at hB
  simp only [mul_one] at h2
  change T.card ≤ E.card + 1
  omega

end PEqualNP.Outside.L_meta_997.Exclusion
namespace PEqualNP.Outside.L_meta_997.LightSelected

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.light

lemma budget_used {n : ℕ} (C : Circuit) (H K : Finset ℕ) (parents : ℕ → Finset ℕ)
    (hstep : ∀ w ∈ H, (parents w).card ≤ (if w ∈ K then 2 else 1) ∧
      (∀ r ∈ parents w, r < w) ∧
      ∀ (p : Fin n) (z : Fin n → Bool),
        (∀ r ∈ parents w, value C (fun v => decide (v = p)) r = true → value C z r = true) →
        value C (fun v => decide (v = p)) w = true → value C z w = true)
    (R : Set ℕ) (hR : ∀ w ∈ H, w ∈ R → ∀ r ∈ parents w, r ∈ R)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ H → w < t)
    (hFR : ∀ w ∈ F, w ∈ R) :
    ∃ B U : Finset ℕ, Disjoint B H ∧ B.card ≤ F.card + U.card ∧
      (∀ w ∈ B, w ∈ R) ∧
      (∀ (p : Fin n) (z : Fin n → Bool),
        (∀ w ∈ B, value C (fun v => decide (v = p)) w = true → value C z w = true) →
        ∀ w ∈ F, value C (fun v => decide (v = p)) w = true → value C z w = true) ∧
      ∀ w ∈ U, w ∈ H ∧ w ∈ K ∧ w < t ∧ w ∈ R := by
  classical
  induction t generalizing F with
  | zero =>
    refine ⟨F, ∅, ?_, by simp, hFR, ?_, by simp⟩
    · exact Finset.disjoint_left.mpr (fun w hw hg => by have := hF w hw hg; omega)
    · exact fun _ _ h => h
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ H
    · obtain ⟨hPcard, hP, hp⟩ := hstep t hex.2
      let F' := F.erase t ∪ parents t
      have hF' : ∀ w ∈ F', w ∈ H → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      have hR' : ∀ w ∈ F', w ∈ R := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hFR w (Finset.mem_erase.mp hw).2
        · exact hR t hex.2 (hFR t hex.1) w hw
      obtain ⟨B, U, hd, hc, hBR, hi, hu⟩ := ih F' hF' hR'
      have hsize : F'.card + 1 ≤ F.card + (if t ∈ K then 2 else 1) := by
        have hUnion := Finset.card_union_le (F.erase t) (parents t)
        have hErase := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hUnion
        omega
      have htrans : ∀ (p : Fin n) (z : Fin n → Bool),
          (∀ w ∈ B, value C (fun v => decide (v = p)) w = true → value C z w = true) →
          ∀ w ∈ F, value C (fun v => decide (v = p)) w = true → value C z w = true := by
        intro p z hz w hw
        by_cases he : w = t
        · subst w
          exact hp p z fun r hr => hi p z hz r (Finset.mem_union_right _ hr)
        · exact hi p z hz w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hw⟩))
      by_cases ht : t ∈ K
      · have htu : t ∉ U := by intro h; have := (hu t h).2.2.1; omega
        refine ⟨B, insert t U, hd, ?_, hBR, htrans, ?_⟩
        · rw [Finset.card_insert_of_notMem htu]
          simp only [ht, ite_true] at hsize
          omega
        · intro w hw
          rcases Finset.mem_insert.mp hw with he | hw
          · subst w
            exact ⟨hex.2, ht, by omega, hFR t hex.1⟩
          · obtain ⟨hwH, hwK, hwt, hwR⟩ := hu w hw
            exact ⟨hwH, hwK, by omega, hwR⟩
      · refine ⟨B, U, hd, ?_, hBR, htrans, ?_⟩
        · simp only [ht, ite_false] at hsize
          omega
        · intro w hw
          obtain ⟨hwH, hwK, hwt, hwR⟩ := hu w hw
          exact ⟨hwH, hwK, by omega, hwR⟩
    · have hF' : ∀ w ∈ F, w ∈ H → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w (Finset.mem_erase.mp (Finset.mem_erase.mpr ⟨hne,hw⟩)).2 hg
        omega
      obtain ⟨B, U, hd, hc, hBR, hi, hu⟩ := ih F hF' hFR
      refine ⟨B, U, hd, hc, hBR, hi, ?_⟩
      intro w hw
      obtain ⟨hwH, hwK, hwt, hwR⟩ := hu w hw
      exact ⟨hwH, hwK, by omega, hwR⟩

lemma branch_edges {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (w : ℕ) (hw : w ∈ charge C S) :
    ∃ P : Finset ℕ, P.card ≤ (if w ∈ refinedCharge C S then 2 else 1) ∧
      (∀ r ∈ P, r < w ∧ r ∈ (HeavyOr.readGate C n w).inputs) ∧
      ∀ (p : Fin n) (z : Fin n → Bool),
        (∀ r ∈ P, value C (fun v => decide (v = p)) r = true → value C z r = true) →
        value C (fun v => decide (v = p)) w = true → value C z w = true := by
  classical
  have hg := ((mem_charge C S w).mp hw).1
  let g := HeavyOr.readGate C n w
  have hge : g = C.gates[w-n]'(by unfold Circuit.size at hg; omega) :=
    HeavyOr.readGate_eq C n w hg.1 hg.2
  by_cases hc : copyOr (n := n) C w
  · have hc' := hc
    change g.op = GateOp.or ∧ ∃ r ∈ g.inputs, r < w ∧ singleSupp C r = singleSupp C w at hc'
    obtain ⟨hop, r, hr, hrw, hs⟩ := hc'
    refine ⟨{r}, by simp [refinedCharge, hc], ?_, ?_⟩
    · intro q hq
      have he : q = r := Finset.mem_singleton.mp hq
      subst q
      exact ⟨hrw, hr⟩
    · intro p z hz hp
      have hpr : value C (fun v => decide (v = p)) r = true := by
        apply (mem_singleSupp C r p).mp
        rw [hs]
        exact (mem_singleSupp C w p).mpr hp
      have hzr := hz r (Finset.mem_singleton_self r) hpr
      rw [gate_value C z w hg.1 hg.2, ← hge, hop]
      simp only [GateOp.eval, List.any_eq_true, id_eq]
      exact ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, by simp [hrw, hzr]⟩
  · have hgm : g ∈ C.gates := by rw [hge]; exact List.getElem_mem _
    obtain ⟨hop, hlen⟩ := hG g hgm
    let P := g.inputs.toFinset.filter (· < w)
    refine ⟨P, ?_, ?_, ?_⟩
    · have hp := (Finset.card_filter_le g.inputs.toFinset (· < w)).trans
        ((List.toFinset_card_le g.inputs).trans hlen)
      simpa [refinedCharge, hw, hc] using hp
    · intro r hr
      exact ⟨(Finset.mem_filter.mp hr).2, List.mem_toFinset.mp (Finset.mem_filter.mp hr).1⟩
    · intro p z htrans hx
      have hr (r : ℕ) (hr : r ∈ g.inputs) :
          (if r < w then value C (fun v => decide (v = p)) r else false) = true →
          (if r < w then value C z r else false) = true := by
        by_cases h : r < w
        · simpa [h] using htrans r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, h⟩)
        · simp [h]
      have formula (x : Fin n → Bool) :
          value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
        rw [hge]
        exact gate_value C x w hg.1 hg.2
      rw [formula] at hx ⊢
      rcases hop with hop | hop
      · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hx ⊢
        intro b hb
        obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hb
        exact hr r hrm (hx _ (List.mem_map.mpr ⟨r, hrm, rfl⟩))
      · simp only [hop, GateOp.eval, List.any_eq_true, id_eq] at hx ⊢
        obtain ⟨b, hb, hbt⟩ := hx
        obtain ⟨r, hrm, rfl⟩ := List.mem_map.mp hb
        exact ⟨_, List.mem_map.mpr ⟨r, hrm, rfl⟩, hr r hrm hbt⟩

lemma selected_count {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (o k : ℕ)
    (hcorrect : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value C x o = decide (∃ p ∈ S, x p = true)) :
    ∃ (parents : ℕ → Finset ℕ) (U : Finset ℕ), U ⊆ refinedCharge C S ∧
      min k S.card ≤ U.card + 1 ∧
      (∀ w ∈ charge C S,
        (parents w).card ≤ (if w ∈ refinedCharge C S then 2 else 1) ∧
        (∀ r ∈ parents w, r < w) ∧
        ∀ (p : Fin n) (z : Fin n → Bool),
          (∀ r ∈ parents w, value C (fun v => decide (v = p)) r = true → value C z r = true) →
          value C (fun v => decide (v = p)) w = true → value C z w = true) ∧
      (∀ w ∈ U, Relation.ReflTransGen (fun a b => b ∈ parents a) o w) ∧
      (∀ w r, r ∈ parents w → w ∈ charge C S ∧ r < w ∧
        r ∈ (HeavyOr.readGate C n w).inputs ∧ (singleSupp (n := n) C r).Nonempty) := by
  classical
  let H := charge C S
  let K := refinedCharge C S
  have hbranch : ∀ w ∈ H, ∃ P : Finset ℕ,
      P.card ≤ (if w ∈ K then 2 else 1) ∧
      (∀ r ∈ P, r < w ∧ r ∈ (HeavyOr.readGate C n w).inputs ∧ (singleSupp (n := n) C r).Nonempty) ∧
      ∀ (p : Fin n) (z : Fin n → Bool),
        (∀ r ∈ P, value C (fun v => decide (v = p)) r = true → value C z r = true) →
        value C (fun v => decide (v = p)) w = true → value C z w = true := by
    intro w hw
    obtain ⟨P, hcard, hpar, htrans⟩ := branch_edges C hG S w hw
    let Q := P.filter (fun r => (singleSupp (n := n) C r).Nonempty)
    refine ⟨Q, (Finset.card_filter_le _ _).trans hcard, ?_, ?_⟩
    · intro r hr
      have hr' := Finset.mem_filter.mp hr
      exact ⟨(hpar r hr'.1).1, (hpar r hr'.1).2, hr'.2⟩
    · intro p z hq
      apply htrans p z
      intro r hr hpr
      exact hq r (Finset.mem_filter.mpr ⟨hr, ⟨p, (mem_singleSupp C r p).mpr hpr⟩⟩) hpr
  let parents := fun w => if hw : w ∈ H then Classical.choose (hbranch w hw) else ∅
  have hpFull : ∀ w ∈ H,
      (parents w).card ≤ (if w ∈ K then 2 else 1) ∧
      (∀ r ∈ parents w, r < w ∧ r ∈ (HeavyOr.readGate C n w).inputs ∧ (singleSupp (n := n) C r).Nonempty) ∧
      ∀ (p : Fin n) (z : Fin n → Bool),
        (∀ r ∈ parents w, value C (fun v => decide (v = p)) r = true → value C z r = true) →
        value C (fun v => decide (v = p)) w = true → value C z w = true := by
    intro w hw
    simpa only [parents, dite_eq_left hw] using Classical.choose_spec (hbranch w hw)
  have hp : ∀ w ∈ H,
      (parents w).card ≤ (if w ∈ K then 2 else 1) ∧
      (∀ r ∈ parents w, r < w) ∧
      ∀ (p : Fin n) (z : Fin n → Bool),
        (∀ r ∈ parents w, value C (fun v => decide (v = p)) r = true → value C z r = true) →
        value C (fun v => decide (v = p)) w = true → value C z w = true := by
    intro w hw
    have hh := hpFull w hw
    exact ⟨hh.1, fun r hr => (hh.2.1 r hr).1, hh.2.2⟩
  let R := {w | Relation.ReflTransGen (fun a b => b ∈ parents a) o w}
  have hR : ∀ w ∈ H, w ∈ R → ∀ r ∈ parents w, r ∈ R := by
    intro w _ hw r hr
    exact Relation.ReflTransGen.tail hw hr
  obtain ⟨B, U, hd, hB, hBR, hcut, hu⟩ := budget_used C H K parents hp R hR
    (n + C.size) {o}
    (fun w _ hw => ((mem_charge C S w).mp hw).1.2)
    (fun w hw => by have : w = o := Finset.mem_singleton.mp hw; subst w; exact Relation.ReflTransGen.refl)
  refine ⟨parents, U, ?_, ?_, hp, ?_, ?_⟩
  · intro w hw
    exact (hu w hw).2.1
  · by_contra! hsmall
    have hsmallS : U.card + 1 < S.card := hsmall.trans_le (min_le_right ..)
    have hsmallK : U.card + 1 < k := hsmall.trans_le (min_le_left ..)
    have hb : B.card ≤ U.card + 1 := by simpa only [Finset.card_singleton, Nat.add_comm] using hB
    let clean (w : ℕ) : Finset (Fin n) :=
      if singleSupp C w ⊆ S then singleSupp C w else ∅
    have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
      intro w hw
      by_cases hs : singleSupp C w ⊆ S
      · simp only [clean, ite_eq_left hs]
        by_contra! hlarge
        exact Finset.disjoint_left.mp hd hw
          ((mem_charge C S w).mpr ⟨singleSupp_gate C w (by omega), hs, by omega⟩)
      · simp [clean, hs]
    have hcover : (B.biUnion clean).card < S.card := by
      have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
      simp only [mul_one] at h
      omega
    obtain ⟨p, hpS, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
    let Dn := B.filter (fun w => ¬ singleSupp C w ⊆ S)
    have hout (w : {w // w ∈ Dn}) : ∃ q : Fin n, q ∈ singleSupp C w.val ∧ q ∉ S := by
      have hns := (Finset.mem_filter.mp w.property).2
      simpa only [Finset.not_subset] using hns
    choose qs hqs using hout
    let V : Finset (Fin n) := Dn.attach.image qs
    let z : Fin n → Bool := fun v => decide (v ∈ V)
    have hVcard : V.card < k := by
      have hi := Finset.card_image_le (s := Dn.attach) (f := qs)
      have hf := Finset.card_filter_le B (fun w => ¬ singleSupp C w ⊆ S)
      simp only [Finset.card_attach] at hi
      change V.card ≤ Dn.card at hi
      change Dn.card ≤ B.card at hf
      omega
    have hweight : (Finset.univ.filter (fun v => z v = true)).card < k := by
      simpa [z] using hVcard
    have hVS : ∀ q ∈ V, q ∉ S := by
      intro q hq
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hq
      exact (hqs w).2
    have hzfalse : value C z o = false := by
      rw [hcorrect z hweight]
      simp only [decide_eq_false_iff_not, not_exists]
      intro q hq
      exact hVS q (by simpa [z] using hq.2) hq.1
    have hfire : value C (fun v => decide (v = p)) o = true := by
      rw [hcorrect]
      · simp [hpS]
      · have hsingle : Finset.univ.filter (fun v : Fin n => decide (v = p) = true) = {p} := by
          ext v
          simp
        rw [hsingle, Finset.card_singleton]
        omega
    have hztrue : value C z o = true := by
      apply hcut p z _ o (Finset.mem_singleton_self o) hfire
      intro w hw hx
      by_cases hs : singleSupp C w ⊆ S
      · exact False.elim (hpnot (Finset.mem_biUnion.mpr
          ⟨w, hw, by simp only [clean, ite_eq_left hs]; exact (mem_singleSupp C w p).mpr hx⟩))
      · let d : {w // w ∈ Dn} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
        apply value_mono C hG (fun v => decide (v = qs d)) z _ w
          ((mem_singleSupp C w (qs d)).mp (hqs d).1)
        intro v hv
        have hv' : v = qs d := by simpa using hv
        subst v
        simp only [z, decide_eq_true_eq]
        exact Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩
    rw [hzfalse] at hztrue
    exact Bool.false_ne_true hztrue
  · intro w hw
    exact (hu w hw).2.2.2
  · intro w r hr
    by_cases hw : w ∈ H
    · exact ⟨hw, (hpFull w hw).2.1 r hr⟩
    · simp [parents, hw] at hr

end PEqualNP.Outside.L_meta_997.LightSelected
namespace PEqualNP.Outside.L_meta_997.LightSmart

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.light PEqualNP.Outside.L_meta_997.LightSelected

def freeAnd {n : ℕ} (C : Circuit) (w : ℕ) : Prop :=
  let g := HeavyOr.readGate C n w
  g.op = GateOp.and ∧ ∃ r ∈ g.inputs, r < w ∧ value C (fun _ : Fin n => false) r = true

noncomputable def smartCharge {n : ℕ} (C : Circuit) (S : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (refinedCharge C S).filter (fun w => ¬ freeAnd (n := n) C w)

lemma freeAnd_copy {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (w : ℕ) (hw : w ∈ charge C S) (hf : freeAnd (n := n) C w) :
    ∃ r ∈ (HeavyOr.readGate C n w).inputs, r < w ∧
      ∀ x : Fin n → Bool, value C x w = value C x r := by
  classical
  have hg := ((mem_charge C S w).mp hw).1
  have hs := ((mem_charge C S w).mp hw).2.2
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < (singleSupp (n := n) C w).card)
  have hptrue := (mem_singleSupp C w p).mp hp
  let g := HeavyOr.readGate C n w
  have hge : g = C.gates[w-n]'(by unfold Circuit.size at hg; omega) :=
    HeavyOr.readGate_eq C n w hg.1 hg.2
  have hgm : g ∈ C.gates := by rw [hge]; exact List.getElem_mem _
  have hlen := (hG g hgm).2
  change g.op = GateOp.and ∧ ∃ r ∈ g.inputs, r < w ∧ value C (fun _ : Fin n => false) r = true at hf
  obtain ⟨hop, q, hq, hqw, hqt⟩ := hf
  have formula (x : Fin n → Bool) :
      value C x w = (g.inputs.map fun r => if r < w then value C x r else false).all id := by
    rw [gate_value C x w hg.1 hg.2, ← hge, hop]
    rfl
  have hconst (x : Fin n → Bool) : value C x q = true :=
    value_mono C hG (fun _ : Fin n => false) x (by simp) q hqt
  cases hlist : g.inputs with
  | nil => simp [hlist] at hq
  | cons a tail =>
    cases tail with
    | nil =>
      have hqa : q = a := by simpa [hlist] using hq
      subst q
      refine ⟨a, by simp [g], hqw, ?_⟩
      intro x
      simp [formula, hlist, hqw]
    | cons b tail =>
      cases tail with
      | cons c rest => simp [hlist] at hlen
      | nil =>
        have hqa : q = a ∨ q = b := by simpa [hlist] using hq
        rcases hqa with hqa | hqb
        · subst q
          have hbw : b < w := by
            by_contra! hb
            have hbf : ¬ b < w := by omega
            simp [formula, hlist, hbf] at hptrue
          refine ⟨b, by simp [g], hbw, ?_⟩
          intro x
          simp [formula, hlist, hqw, hbw, hconst x]
        · subst q
          have haw : a < w := by
            by_contra! ha
            have haf : ¬ a < w := by omega
            simp [formula, hlist, haf] at hptrue
          refine ⟨a, by simp [g], haw, ?_⟩
          intro x
          simp [formula, hlist, haw, hqw, hconst x]

lemma branch_edges {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (w : ℕ) (hw : w ∈ charge C S) :
    ∃ P : Finset ℕ, P.card ≤ (if w ∈ smartCharge C S then 2 else 1) ∧
      (∀ r ∈ P, r < w ∧ r ∈ (HeavyOr.readGate C n w).inputs) ∧
      ∀ (p : Fin n) (z : Fin n → Bool),
        (∀ r ∈ P, value C (fun v => decide (v = p)) r = true → value C z r = true) →
        value C (fun v => decide (v = p)) w = true → value C z w = true := by
  classical
  by_cases hf : freeAnd (n := n) C w
  · obtain ⟨r, hr, hrw, heq⟩ := freeAnd_copy C hG S w hw hf
    refine ⟨{r}, by simp [smartCharge, hf], ?_, ?_⟩
    · intro q hq
      have he : q = r := Finset.mem_singleton.mp hq
      subst q
      exact ⟨hrw, hr⟩
    · intro p z htrans
      rw [heq, heq]
      exact htrans r (Finset.mem_singleton_self r)
  · obtain ⟨P, hP, hpar, htrans⟩ := LightSelected.branch_edges C hG S w hw
    refine ⟨P, ?_, hpar, htrans⟩
    simpa [smartCharge, hf] using hP

lemma selected_count {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (o k : ℕ)
    (hcorrect : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value C x o = decide (∃ p ∈ S, x p = true)) :
    ∃ (parents : ℕ → Finset ℕ) (U : Finset ℕ), U ⊆ smartCharge C S ∧
      min k S.card ≤ U.card + 1 ∧
      (∀ w ∈ charge C S,
        (parents w).card ≤ (if w ∈ smartCharge C S then 2 else 1) ∧
        (∀ r ∈ parents w, r < w) ∧
        ∀ (p : Fin n) (z : Fin n → Bool),
          (∀ r ∈ parents w, value C (fun v => decide (v = p)) r = true → value C z r = true) →
          value C (fun v => decide (v = p)) w = true → value C z w = true) ∧
      (∀ w ∈ U, Relation.ReflTransGen (fun a b => b ∈ parents a) o w) ∧
      (∀ w r, r ∈ parents w → w ∈ charge C S ∧ r < w ∧
        r ∈ (HeavyOr.readGate C n w).inputs ∧ (singleSupp (n := n) C r).Nonempty) := by
  classical
  let H := charge C S
  let K := smartCharge C S
  have hbranch : ∀ w ∈ H, ∃ P : Finset ℕ,
      P.card ≤ (if w ∈ K then 2 else 1) ∧
      (∀ r ∈ P, r < w ∧ r ∈ (HeavyOr.readGate C n w).inputs ∧ (singleSupp (n := n) C r).Nonempty) ∧
      ∀ (p : Fin n) (z : Fin n → Bool),
        (∀ r ∈ P, value C (fun v => decide (v = p)) r = true → value C z r = true) →
        value C (fun v => decide (v = p)) w = true → value C z w = true := by
    intro w hw
    obtain ⟨P, hcard, hpar, htrans⟩ := branch_edges C hG S w hw
    let Q := P.filter (fun r => (singleSupp (n := n) C r).Nonempty)
    refine ⟨Q, (Finset.card_filter_le _ _).trans hcard, ?_, ?_⟩
    · intro r hr
      have hr' := Finset.mem_filter.mp hr
      exact ⟨(hpar r hr'.1).1, (hpar r hr'.1).2, hr'.2⟩
    · intro p z hq
      apply htrans p z
      intro r hr hpr
      exact hq r (Finset.mem_filter.mpr ⟨hr, ⟨p, (mem_singleSupp C r p).mpr hpr⟩⟩) hpr
  let parents := fun w => if hw : w ∈ H then Classical.choose (hbranch w hw) else ∅
  have hpFull : ∀ w ∈ H,
      (parents w).card ≤ (if w ∈ K then 2 else 1) ∧
      (∀ r ∈ parents w, r < w ∧ r ∈ (HeavyOr.readGate C n w).inputs ∧ (singleSupp (n := n) C r).Nonempty) ∧
      ∀ (p : Fin n) (z : Fin n → Bool),
        (∀ r ∈ parents w, value C (fun v => decide (v = p)) r = true → value C z r = true) →
        value C (fun v => decide (v = p)) w = true → value C z w = true := by
    intro w hw
    simpa only [parents, dite_eq_left hw] using Classical.choose_spec (hbranch w hw)
  have hp : ∀ w ∈ H,
      (parents w).card ≤ (if w ∈ K then 2 else 1) ∧
      (∀ r ∈ parents w, r < w) ∧
      ∀ (p : Fin n) (z : Fin n → Bool),
        (∀ r ∈ parents w, value C (fun v => decide (v = p)) r = true → value C z r = true) →
        value C (fun v => decide (v = p)) w = true → value C z w = true := by
    intro w hw
    have hh := hpFull w hw
    exact ⟨hh.1, fun r hr => (hh.2.1 r hr).1, hh.2.2⟩
  let R := {w | Relation.ReflTransGen (fun a b => b ∈ parents a) o w}
  have hR : ∀ w ∈ H, w ∈ R → ∀ r ∈ parents w, r ∈ R := by
    intro w _ hw r hr
    exact Relation.ReflTransGen.tail hw hr
  obtain ⟨B, U, hd, hB, hBR, hcut, hu⟩ := budget_used C H K parents hp R hR
    (n + C.size) {o}
    (fun w _ hw => ((mem_charge C S w).mp hw).1.2)
    (fun w hw => by have : w = o := Finset.mem_singleton.mp hw; subst w; exact Relation.ReflTransGen.refl)
  refine ⟨parents, U, ?_, ?_, hp, ?_, ?_⟩
  · intro w hw
    exact (hu w hw).2.1
  · by_contra! hsmall
    have hsmallS : U.card + 1 < S.card := hsmall.trans_le (min_le_right ..)
    have hsmallK : U.card + 1 < k := hsmall.trans_le (min_le_left ..)
    have hb : B.card ≤ U.card + 1 := by simpa only [Finset.card_singleton, Nat.add_comm] using hB
    let clean (w : ℕ) : Finset (Fin n) :=
      if singleSupp C w ⊆ S then singleSupp C w else ∅
    have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
      intro w hw
      by_cases hs : singleSupp C w ⊆ S
      · simp only [clean, ite_eq_left hs]
        by_contra! hlarge
        exact Finset.disjoint_left.mp hd hw
          ((mem_charge C S w).mpr ⟨singleSupp_gate C w (by omega), hs, by omega⟩)
      · simp [clean, hs]
    have hcover : (B.biUnion clean).card < S.card := by
      have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
      simp only [mul_one] at h
      omega
    obtain ⟨p, hpS, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
    let Dn := B.filter (fun w => ¬ singleSupp C w ⊆ S)
    have hout (w : {w // w ∈ Dn}) : ∃ q : Fin n, q ∈ singleSupp C w.val ∧ q ∉ S := by
      have hns := (Finset.mem_filter.mp w.property).2
      simpa only [Finset.not_subset] using hns
    choose qs hqs using hout
    let V : Finset (Fin n) := Dn.attach.image qs
    let z : Fin n → Bool := fun v => decide (v ∈ V)
    have hVcard : V.card < k := by
      have hi := Finset.card_image_le (s := Dn.attach) (f := qs)
      have hf := Finset.card_filter_le B (fun w => ¬ singleSupp C w ⊆ S)
      simp only [Finset.card_attach] at hi
      change V.card ≤ Dn.card at hi
      change Dn.card ≤ B.card at hf
      omega
    have hweight : (Finset.univ.filter (fun v => z v = true)).card < k := by
      simpa [z] using hVcard
    have hVS : ∀ q ∈ V, q ∉ S := by
      intro q hq
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hq
      exact (hqs w).2
    have hzfalse : value C z o = false := by
      rw [hcorrect z hweight]
      simp only [decide_eq_false_iff_not, not_exists]
      intro q hq
      exact hVS q (by simpa [z] using hq.2) hq.1
    have hfire : value C (fun v => decide (v = p)) o = true := by
      rw [hcorrect]
      · simp [hpS]
      · have hsingle : Finset.univ.filter (fun v : Fin n => decide (v = p) = true) = {p} := by
          ext v
          simp
        rw [hsingle, Finset.card_singleton]
        omega
    have hztrue : value C z o = true := by
      apply hcut p z _ o (Finset.mem_singleton_self o) hfire
      intro w hw hx
      by_cases hs : singleSupp C w ⊆ S
      · exact False.elim (hpnot (Finset.mem_biUnion.mpr
          ⟨w, hw, by simp only [clean, ite_eq_left hs]; exact (mem_singleSupp C w p).mpr hx⟩))
      · let d : {w // w ∈ Dn} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
        apply value_mono C hG (fun v => decide (v = qs d)) z _ w
          ((mem_singleSupp C w (qs d)).mp (hqs d).1)
        intro v hv
        have hv' : v = qs d := by simpa using hv
        subst v
        simp only [z, decide_eq_true_eq]
        exact Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩
    rw [hzfalse] at hztrue
    exact Bool.false_ne_true hztrue
  · intro w hw
    exact (hu w hw).2.2.2
  · intro w r hr
    by_cases hw : w ∈ H
    · exact ⟨hw, (hpFull w hw).2.1 r hr⟩
    · simp [parents, hw] at hr

end PEqualNP.Outside.L_meta_997.LightSmart
namespace PEqualNP.Outside.L_meta_997.OneOversized

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.light

lemma single_heavy_hybrid {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n)) (a : Fin m)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not → j.val = t)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < y.card → value C x (n + t) = true)
    (ha : Disjoint (S a) y) (hy : 1 < y.card) :
    (S a).card + (∑ i ∈ Finset.univ.erase a, min y.card (S i).card) ≤ C.gates.length + m := by
  classical
  let D := PEqualNP.Outside.L_meta_997.Heavy.fixed C t true
  let I := Finset.univ.erase a
  let M := I.biUnion (fun i => charge D (S i))
  have hD : D.size = C.size := PEqualNP.Outside.L_meta_997.Heavy.fixed_size C t true
  have hgood := PEqualNP.Outside.L_meta_997.Heavy.fixed_good C t true hgate hnot
  have hfixed (i : Fin m) (x : Fin n → Bool)
      (hx : (Finset.univ.filter (fun v => x v = true)).card < y.card) :
      value D x (o i) = decide (∃ p ∈ S i, x p = true) := by
    have he := PEqualNP.Outside.L_meta_997.Heavy.fixed_eq C t true x (hlow x hx) (o i)
    change value D x (o i) = value C x (o i) at he
    rw [he, hcorrect]
  have hweight (p : Fin n) :
      (Finset.univ.filter (fun v : Fin n => decide (v = p) = true)).card < y.card := by
    have he : Finset.univ.filter (fun v : Fin n => decide (v = p) = true) = {p} := by
      ext v
      simp
    rw [he, Finset.card_singleton]
    exact hy
  have hsingle (p : Fin n) (w : ℕ) :
      value D (fun v => decide (v = p)) w = value C (fun v => decide (v = p)) w := by
    exact PEqualNP.Outside.L_meta_997.Heavy.fixed_eq C t true _ (hlow _ (hweight p)) w
  have hsupp (w : ℕ) : singleSupp (n := n) D w = singleSupp C w := by
    ext p
    rw [mem_singleSupp, mem_singleSupp, hsingle]
  have hMrange : M ⊆ Finset.Ico n (n + C.size) := by
    intro w hw
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hw
    have h := ((mem_charge D (S i) w).mp hwi).1
    rw [hD] at h
    exact Finset.mem_Ico.mpr h
  have hM : ∀ w ∈ M, (singleSupp C w ∩ S a).card ≤ 1 := by
    intro w hw
    obtain ⟨i, hi, hwi⟩ := Finset.mem_biUnion.mp hw
    have hsub : singleSupp C w ⊆ S i := by
      rw [← hsupp]
      exact ((mem_charge D (S i) w).mp hwi).2.1
    have hi' : i ≠ a := (Finset.mem_erase.mp hi).1
    have hsub' : singleSupp C w ∩ S a ⊆ S i ∩ S a := fun p hp =>
      Finset.mem_inter.mpr ⟨hsub (Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hp).2⟩
    exact (Finset.card_le_card hsub').trans (hinter i a hi')
  obtain ⟨q, hqy⟩ := Finset.card_pos.mp (show 0 < y.card by omega)
  have hq : q ∉ S a := fun hqa => Finset.disjoint_left.mp ha hqa hqy
  have hnotq : ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not →
      value C (fun v => decide (v = q)) (n + j.val) = true := by
    intro j hj
    rw [hnot j hj]
    exact hlow _ (hweight q)
  have hheavy := PEqualNP.Outside.L_meta_997.Exclusion.single_heavy_budget C (S a) (o a)
    q M hgate hnotq (hcorrect a) hq hMrange hM
  have hdisj : (I : Set (Fin m)).PairwiseDisjoint (fun i => charge D (S i)) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro w hi hj
    have hi' := ((mem_charge D (S i) w).mp hi).2
    have hj' := ((mem_charge D (S j) w).mp hj).2
    have hsub : singleSupp D w ⊆ S i ∩ S j := Finset.subset_inter hi'.1 hj'.1
    have hc := Finset.card_le_card hsub
    have hh := hinter i j hij
    omega
  have hMcard : M.card = ∑ i ∈ I, (charge D (S i)).card := Finset.card_biUnion hdisj
  have hsum : (∑ i ∈ I, min y.card (S i).card) ≤ M.card + I.card := by
    calc
      _ ≤ ∑ i ∈ I, ((charge D (S i)).card + 1) :=
        Finset.sum_le_sum fun i _ => light_bound D hgood (S i) (o i) y.card (hfixed i)
      _ = M.card + I.card := by rw [Finset.sum_add_distrib, ← hMcard]; simp
  have hI : I.card + 1 = m := by
    simpa only [I, Finset.card_univ, Fintype.card_fin] using
      Finset.card_erase_add_one (Finset.mem_univ a)
  have hcomp := Finset.card_sdiff_add_card_eq_card hMrange
  simp only [Nat.card_Ico, Nat.add_sub_cancel_left] at hcomp
  change (S a).card + (∑ i ∈ I, min y.card (S i).card) ≤ C.gates.length + m
  have hCsize : C.size = C.gates.length := rfl
  omega

lemma one_oversized_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → (i : ℕ) = t)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      (C.wires (List.ofFn x)).getD (o i) false = decide (∃ p ∈ S i, x p = true))
    (hlow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card →
        (C.wires (List.ofFn x)).getD (n + t) false = true)
    (hfalse : (C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y)))).getD
      (n + t) false = false)
    (hone : ∃ a : Fin m, ∀ i : Fin m, i ≠ a → Disjoint (S i) y → (S i).card ≤ y.card + 1) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length =>
        (∃ i : Fin m, ∀ p : Fin n,
          (C.wires (List.ofFn (fun v : Fin n => decide (v = p)))).getD (n + g) false = true ↔ p ∈ S i) ∧
        (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y →
          ((C.wires (List.ofFn (fun v : Fin n => decide (v ∈ y ∨ v = p)))).getD
            (n + g) false = true ↔ p ∈ S i)))).card + m := by
  classical
  by_cases hy : y.card ≤ 2
  · have h := small_window_bound S C o t y hinter hgate hnot hcorrect hfalse hy
    omega
  · obtain ⟨a, ha⟩ := hone
    by_cases hda : Disjoint (S a) y
    · let I := Finset.univ.erase a
      let R := Finset.univ.filter (fun i : Fin m => Disjoint (S i) y ∧ 2 ≤ (S i).card)
      let F := fun i : Fin m => if Disjoint (S i) y then (S i).card else min y.card (S i).card
      have hterm (i : Fin m) (hi : i ∈ I) :
          F i ≤ min y.card (S i).card + (if i ∈ R then 1 else 0) := by
        by_cases hd : Disjoint (S i) y
        · change (if Disjoint (S i) y then _ else _) ≤ _
          rw [ite_eq_left hd]
          by_cases hc : (S i).card ≤ y.card
          · rw [min_eq_right hc]
            omega
          · have hir : i ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, by omega⟩
            rw [min_eq_left (by omega), ite_eq_left hir]
            exact ha i (Finset.mem_erase.mp hi).1 hd
        · simp only [F, ite_eq_right hd]
          omega
      have hbonus : (∑ i ∈ I, if i ∈ R then 1 else 0) ≤ R.card := by
        calc
          _ ≤ ∑ i : Fin m, if i ∈ R then 1 else 0 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I) (by intros; omega)
          _ = R.card := by simp
      have hsum : (∑ i ∈ I, F i) ≤ (∑ i ∈ I, min y.card (S i).card) + R.card := by
        calc
          _ ≤ ∑ i ∈ I, (min y.card (S i).card + if i ∈ R then 1 else 0) :=
            Finset.sum_le_sum hterm
          _ ≤ _ := by rw [Finset.sum_add_distrib]; exact Nat.add_le_add_left hbonus _
      have hdecomp : (∑ i : Fin m, F i) = (S a).card + ∑ i ∈ I, F i := by
        rw [← Finset.add_sum_erase Finset.univ F (Finset.mem_univ a)]
        simp only [F, ite_eq_left hda]
        rfl
      have hh := single_heavy_hybrid S C o t y a hinter hgate hnot hcorrect hlow hda (by omega)
      have hr := PEqualNP.Outside.L_meta_997.Refund.refund_output_count S C o y hinter hcorrect
      change R.card ≤ _ at hr
      change (∑ i : Fin m, F i) ≤
        C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length =>
          (∃ i : Fin m, ∀ p : Fin n, value C (fun v => decide (v = p)) (n + g) = true ↔ p ∈ S i) ∧
          (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y →
            (value C (fun v => decide (v ∈ y ∨ v = p)) (n + g) = true ↔ p ∈ S i)))).card + m
      change (S a).card + (∑ i ∈ I, min y.card (S i).card) ≤ C.gates.length + m at hh
      omega
    · apply PEqualNP.Outside.L_meta_997.BoundedDisjoint.capped_disjoint_bound S C o t y
        hinter hgate hnot hcorrect hlow hfalse
      intro i hdi
      by_cases hi : i = a
      · subst i
        exact False.elim (hda hdi)
      · exact ha i hi hdi

end PEqualNP.Outside.L_meta_997.OneOversized
namespace PEqualNP.Outside.L_meta_997.GraphForest

def children (V : Finset ℕ) (o : ℕ) (up : ℕ → ℕ) (v : ℕ) : Finset ℕ :=
  V.filter (fun w => w≠o ∧ up w=v)

lemma children_euler (V : Finset ℕ) (o : ℕ) (up : ℕ → ℕ) (ho : o ∈ V)
    (hup : ∀ w ∈ V, w≠o → up w ∈ V)
    (hb : ∀ v ∈ V, (children V o up v).card ≤ 2) :
    (V.filter (fun v => (children V o up v).card=2)).card + 1 =
      (V.filter (fun v => children V o up v=∅)).card := by
  classical
  have hd : (V : Set ℕ).PairwiseDisjoint (children V o up) := by
    intro v hv u hu hne
    apply Finset.disjoint_left.mpr
    intro w hwv hwu
    have he1 := (Finset.mem_filter.mp hwv).2.2
    have he2 := (Finset.mem_filter.mp hwu).2.2
    exact hne (he1.symm.trans he2)
  have hUnion : V.biUnion (children V o up) = V.erase o := by
    ext w
    constructor
    · intro hw
      obtain ⟨v,_,hwv⟩ := Finset.mem_biUnion.mp hw
      have hh := Finset.mem_filter.mp hwv
      exact Finset.mem_erase.mpr ⟨hh.2.1,hh.1⟩
    · intro hw
      have hh := Finset.mem_erase.mp hw
      exact Finset.mem_biUnion.mpr ⟨up w,hup w hh.2 hh.1,
        Finset.mem_filter.mpr ⟨hh.2,hh.1,rfl⟩⟩
  have hEdges : (∑ v ∈ V, (children V o up v).card) + 1 = V.card := by
    rw [← Finset.card_biUnion hd,hUnion]
    exact Finset.card_erase_add_one ho
  have hLocal : ∀ v ∈ V,
      (children V o up v).card + (if children V o up v=∅ then 1 else 0) =
        1 + (if (children V o up v).card=2 then 1 else 0) := by
    intro v hv
    have h := hb v hv
    by_cases he : children V o up v=∅
    · simp [he]
    · have hp : 0 < (children V o up v).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      split_ifs <;> omega
  have hs := Finset.sum_congr rfl (fun v hv => hLocal v hv)
  simp only [Finset.sum_add_distrib] at hs
  have hLeaves : (∑ v ∈ V, if children V o up v=∅ then 1 else 0) =
      (V.filter (fun v => children V o up v=∅)).card := by simp
  have hBranches : (∑ v ∈ V, if (children V o up v).card=2 then 1 else 0) =
      (V.filter (fun v => (children V o up v).card=2)).card := by simp
  rw [hLeaves,hBranches] at hs
  simp only [Finset.sum_const,Nat.smul_one_eq_cast,Nat.cast_id] at hs
  omega

lemma children_reach (V : Finset ℕ) (o : ℕ) (up : ℕ → ℕ)
    (hbound : ∀ v ∈ V, v ≤ o)
    (hup : ∀ v ∈ V, v≠o → up v ∈ V ∧ v < up v) :
    ∀ v ∈ V, Relation.ReflTransGen (fun a b => b ∈ children V o up a) o v := by
  have h : ∀ d : ℕ, ∀ v ∈ V, o-v=d →
      Relation.ReflTransGen (fun a b => b ∈ children V o up a) o v := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro v hv hd
      by_cases he : v=o
      · subst v
        exact Relation.ReflTransGen.refl
      · have hu := hup v hv he
        have hdist : o-up v < d := by
          have := hbound (up v) hu.1
          have := hbound v hv
          omega
        have hp := ih (o-up v) hdist (up v) hu.1 rfl
        apply Relation.ReflTransGen.tail hp
        exact Finset.mem_filter.mpr ⟨hv,he,rfl⟩
  intro v hv
  exact h (o-v) v hv rfl

lemma extract_forest (P : ℕ → Finset ℕ) (V B : Finset ℕ) (o : ℕ)
    (ho : o ∈ V) (hB : B ⊆ V) (hne : B.Nonempty)
    (hstep : ∀ v ∈ V, ∀ w ∈ P v, w ∈ V ∧ w<v)
    (hreach : ∀ v ∈ V, Relation.ReflTransGen (fun a b => b ∈ P a) o v)
    (hterm : ∀ b ∈ B, P b=∅)
    (hbin : ∀ v ∈ V, (P v).card ≤ 2) :
    ∃ (W : Finset ℕ) (up : ℕ → ℕ), o ∈ W ∧ W ⊆ V ∧
      (∀ v ∈ W, children W o up v ⊆ P v) ∧
      (∀ v ∈ W, Relation.ReflTransGen (fun a b => b ∈ children W o up a) o v) ∧
      W.filter (fun v => children W o up v=∅) = B ∧
      (W.filter (fun v => (children W o up v).card=2)).card + 1 = B.card := by
  classical
  have hReachV : ∀ v, Relation.ReflTransGen (fun a b => b ∈ P a) o v → v ∈ V := by
    intro v hv
    induction hv with
    | refl => exact ho
    | @tail u v _ huv ih => exact (hstep u ih v huv).1
  have hBoundReach : ∀ v, Relation.ReflTransGen (fun a b => b ∈ P a) o v → v ≤ o := by
    intro v hh
    induction hh with
    | refl => exact le_rfl
    | @tail u v hur huv ih =>
      have ht := (hstep u (hReachV u hur) v huv).2
      omega
  have hBound : ∀ v ∈ V, v ≤ o := fun v hv => hBoundReach v (hreach v hv)
  have hPrev : ∀ v ∈ V, v≠o → ∃ u, u ∈ V ∧ v ∈ P u := by
    intro v hv hvo
    rcases (hreach v hv).cases_tail with h | ⟨u,hu,huv⟩
    · exact False.elim (hvo h)
    · exact ⟨u,hReachV u hu,huv⟩
  let up := fun v => if hv : v ∈ V ∧ v≠o then Classical.choose (hPrev v hv.1 hv.2) else o
  have hUp : ∀ v ∈ V, v≠o → up v ∈ V ∧ v ∈ P (up v) ∧ v < up v := by
    intro v hv hvo
    have he : up v = Classical.choose (hPrev v hv hvo) := by
      simp only [up,dite_eq_left (show v ∈ V ∧ v≠o from ⟨hv,hvo⟩)]
    rw [he]
    have hh := Classical.choose_spec (hPrev v hv hvo)
    exact ⟨hh.1,hh.2,(hstep _ hh.1 v hh.2).2⟩
  have hQsub : ∀ v ∈ V, children V o up v ⊆ P v := by
    intro v _ w hw
    have hh := Finset.mem_filter.mp hw
    have hp := hUp w hh.1 hh.2.1
    simpa only [hh.2.2] using hp.2.1
  have hQreach : ∀ v ∈ V,
      Relation.ReflTransGen (fun a b => b ∈ children V o up a) o v :=
    children_reach V o up hBound (fun v hv hvo => ⟨(hUp v hv hvo).1,(hUp v hv hvo).2.2⟩)
  let W := V.filter (fun v => ∃ b ∈ B,
    Relation.ReflTransGen (fun a b => b ∈ children V o up a) v b)
  have hWV : W ⊆ V := Finset.filter_subset _ _
  have hWB : B ⊆ W := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨hB hb,⟨b,hb,Relation.ReflTransGen.refl⟩⟩
  have hoW : o ∈ W := by
    obtain ⟨b,hb⟩ := hne
    exact Finset.mem_filter.mpr ⟨ho,⟨b,hb,hQreach b (hB hb)⟩⟩
  have hUpW : ∀ v ∈ W, v≠o → up v ∈ W ∧ v < up v := by
    intro v hv hvo
    have hp := hUp v (hWV hv) hvo
    obtain ⟨b,hb,hvb⟩ := (Finset.mem_filter.mp hv).2
    refine ⟨Finset.mem_filter.mpr ⟨hp.1,⟨b,hb,?_⟩⟩,hp.2.2⟩
    exact Relation.ReflTransGen.head (Finset.mem_filter.mpr ⟨hWV hv,hvo,rfl⟩) hvb
  have hWsub : ∀ v ∈ W, children W o up v ⊆ P v := by
    intro v hv w hw
    have hh := Finset.mem_filter.mp hw
    exact hQsub v (hWV hv) (Finset.mem_filter.mpr ⟨hWV hh.1,hh.2⟩)
  have hLeaves : W.filter (fun v => children W o up v=∅) = B := by
    ext v
    constructor
    · intro hv
      have hh := Finset.mem_filter.mp hv
      obtain ⟨b,hb,hvb⟩ := (Finset.mem_filter.mp hh.1).2
      rcases hvb.cases_head with he | ⟨r,hvr,hrb⟩
      · simpa only [he] using hb
      · have hr := Finset.mem_filter.mp hvr
        have hrW : r ∈ W := Finset.mem_filter.mpr ⟨hr.1,⟨b,hb,hrb⟩⟩
        have hc : r ∈ children W o up v := Finset.mem_filter.mpr ⟨hrW,hr.2⟩
        rw [hh.2] at hc
        exact False.elim (Finset.notMem_empty r hc)
    · intro hv
      refine Finset.mem_filter.mpr ⟨hWB hv,?_⟩
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hh := hWsub v (hWB hv) hw
      rw [hterm v hv] at hh
      exact Finset.notMem_empty w hh
  refine ⟨W,up,hoW,hWV,hWsub,?_,hLeaves,?_⟩
  · exact children_reach W o up (fun v hv => hBound v (hWV hv)) hUpW
  · rw [← hLeaves]
    exact children_euler W o up hoW (fun v hv hvo => (hUpW v hv hvo).1)
      (fun v hv => (Finset.card_le_card (hWsub v hv)).trans (hbin v (hWV hv)))

end PEqualNP.Outside.L_meta_997.GraphForest
namespace PEqualNP.Outside.L_meta_997.GraphForest

def forestChildren (V R : Finset ℕ) (up : ℕ → ℕ) (v : ℕ) : Finset ℕ :=
  V.filter (fun w => w ∉ R ∧ up w=v)

lemma forest_euler (V R : Finset ℕ) (up : ℕ → ℕ) (hR : R ⊆ V)
    (hup : ∀ w ∈ V, w ∉ R → up w ∈ V)
    (hb : ∀ v ∈ V, (forestChildren V R up v).card ≤ 2) :
    (V.filter (fun v => (forestChildren V R up v).card=2)).card + R.card =
      (V.filter (fun v => forestChildren V R up v=∅)).card := by
  classical
  have hd : (V : Set ℕ).PairwiseDisjoint (forestChildren V R up) := by
    intro v hv u hu hne
    apply Finset.disjoint_left.mpr
    intro w hwv hwu
    have he1 := (Finset.mem_filter.mp hwv).2.2
    have he2 := (Finset.mem_filter.mp hwu).2.2
    exact hne (he1.symm.trans he2)
  have hUnion : V.biUnion (forestChildren V R up) = V \ R := by
    ext w
    constructor
    · intro hw
      obtain ⟨v,_,hwv⟩ := Finset.mem_biUnion.mp hw
      have hh := Finset.mem_filter.mp hwv
      exact Finset.mem_sdiff.mpr ⟨hh.1,hh.2.1⟩
    · intro hw
      have hh := Finset.mem_sdiff.mp hw
      exact Finset.mem_biUnion.mpr ⟨up w,hup w hh.1 hh.2,
        Finset.mem_filter.mpr ⟨hh.1,hh.2,rfl⟩⟩
  have hEdges : (∑ v ∈ V, (forestChildren V R up v).card) + R.card = V.card := by
    rw [← Finset.card_biUnion hd,hUnion]
    exact Finset.card_sdiff_add_card_eq_card hR
  have hLocal : ∀ v ∈ V,
      (forestChildren V R up v).card + (if forestChildren V R up v=∅ then 1 else 0) =
        1 + (if (forestChildren V R up v).card=2 then 1 else 0) := by
    intro v hv
    have h := hb v hv
    by_cases he : forestChildren V R up v=∅
    · simp [he]
    · have hp : 0 < (forestChildren V R up v).card :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      split_ifs <;> omega
  have hs := Finset.sum_congr rfl (fun v hv => hLocal v hv)
  simp only [Finset.sum_add_distrib] at hs
  have hLeaves : (∑ v ∈ V, if forestChildren V R up v=∅ then 1 else 0) =
      (V.filter (fun v => forestChildren V R up v=∅)).card := by simp
  have hBranches : (∑ v ∈ V, if (forestChildren V R up v).card=2 then 1 else 0) =
      (V.filter (fun v => (forestChildren V R up v).card=2)).card := by simp
  rw [hLeaves,hBranches] at hs
  simp only [Finset.sum_const,Nat.smul_one_eq_cast,Nat.cast_id] at hs
  omega

def commonRoots (V₁ V₂ : Finset ℕ) (o₁ o₂ : ℕ) (up₁ up₂ : ℕ → ℕ) : Finset ℕ :=
  (V₁ ∩ V₂).filter (fun w => w=o₁ ∨ w=o₂ ∨ up₁ w≠up₂ w)

lemma common_children (V₁ V₂ : Finset ℕ) (o₁ o₂ : ℕ) (up₁ up₂ : ℕ → ℕ) (v : ℕ) :
    children V₁ o₁ up₁ v ∩ children V₂ o₂ up₂ v =
      forestChildren (V₁ ∩ V₂) (commonRoots V₁ V₂ o₁ o₂ up₁ up₂) up₁ v := by
  ext w
  simp only [children,forestChildren,commonRoots,Finset.mem_inter,Finset.mem_filter]
  aesop

lemma intersection_euler (V₁ V₂ : Finset ℕ) (o₁ o₂ : ℕ) (up₁ up₂ : ℕ → ℕ)
    (hup₁ : ∀ w ∈ V₁, w≠o₁ → up₁ w ∈ V₁)
    (hup₂ : ∀ w ∈ V₂, w≠o₂ → up₂ w ∈ V₂)
    (hb₁ : ∀ v ∈ V₁, (children V₁ o₁ up₁ v).card ≤ 2) :
    ((V₁ ∩ V₂).filter (fun v =>
      (children V₁ o₁ up₁ v ∩ children V₂ o₂ up₂ v).card=2)).card +
      (commonRoots V₁ V₂ o₁ o₂ up₁ up₂).card =
    ((V₁ ∩ V₂).filter (fun v =>
      children V₁ o₁ up₁ v ∩ children V₂ o₂ up₂ v=∅)).card := by
  have hR := Finset.filter_subset
    (fun w => w=o₁ ∨ w=o₂ ∨ up₁ w≠up₂ w) (V₁ ∩ V₂)
  have hUp : ∀ w ∈ V₁ ∩ V₂,
      w ∉ commonRoots V₁ V₂ o₁ o₂ up₁ up₂ → up₁ w ∈ V₁ ∩ V₂ := by
    intro w hw hwr
    have hn : w≠o₁ ∧ w≠o₂ ∧ up₁ w=up₂ w := by
      simp only [commonRoots,Finset.mem_filter,hw,true_and,not_or,not_not] at hwr
      exact ⟨hwr.1,hwr.2.1,hwr.2.2⟩
    exact Finset.mem_inter.mpr ⟨hup₁ w (Finset.mem_inter.mp hw).1 hn.1,
      by rw [hn.2.2]; exact hup₂ w (Finset.mem_inter.mp hw).2 hn.2.1⟩
  have hb : ∀ v ∈ V₁ ∩ V₂,
      (forestChildren (V₁ ∩ V₂) (commonRoots V₁ V₂ o₁ o₂ up₁ up₂) up₁ v).card ≤ 2 := by
    intro v hv
    rw [← common_children]
    exact (Finset.card_le_card Finset.inter_subset_left).trans (hb₁ v (Finset.mem_inter.mp hv).1)
  simpa only [common_children] using
    forest_euler (V₁ ∩ V₂) (commonRoots V₁ V₂ o₁ o₂ up₁ up₂) up₁ hR hUp hb

lemma double_branch_iff (A B P : Finset ℕ) (hA : A ⊆ P) (hB : B ⊆ P)
    (hP : P.card ≤ 2) : (A ∩ B).card=2 ↔ A.card=2 ∧ B.card=2 := by
  constructor
  · intro h
    have h1 := Finset.card_le_card (Finset.inter_subset_left (s₁ := A) (s₂ := B))
    have h2 := Finset.card_le_card (Finset.inter_subset_right (s₁ := A) (s₂ := B))
    have h3 := Finset.card_le_card hA
    have h4 := Finset.card_le_card hB
    omega
  · rintro ⟨ha,hb⟩
    have hAP : A=P := Finset.eq_of_subset_of_card_le hA (by omega)
    have hBP : B=P := Finset.eq_of_subset_of_card_le hB (by omega)
    rw [hAP,hBP,Finset.inter_self]
    simpa only [hAP] using ha

lemma paid_sink (A B P : Finset ℕ) (hA : A ⊆ P) (hB : B ⊆ P)
    (hP : P.card ≤ 2) (hEmpty : A ∩ B=∅) :
    (A.card=2 → B=∅) ∧ (B.card=2 → A=∅) := by
  constructor
  · intro ha
    have hAP : A=P := Finset.eq_of_subset_of_card_le hA (by omega)
    rw [hAP,Finset.inter_eq_right.mpr hB] at hEmpty
    exact hEmpty
  · intro hb
    have hBP : B=P := Finset.eq_of_subset_of_card_le hB (by omega)
    rw [hBP,Finset.inter_eq_left.mpr hA] at hEmpty
    exact hEmpty

end PEqualNP.Outside.L_meta_997.GraphForest
namespace PEqualNP.Outside.L_meta_997.OrParents

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.light

lemma or_child {n : ℕ} (C : Circuit) (w r : ℕ) (hn : n ≤ w) (hw : w < n + C.size)
    (hop : (HeavyOr.readGate C n w).op = GateOp.or)
    (hr : r ∈ (HeavyOr.readGate C n w).inputs) (hrw : r < w) (x : Fin n → Bool) :
    value C x r = true → value C x w = true := by
  intro hx
  rw [gate_value C x w hn hw, ← HeavyOr.readGate_eq C n w hn hw, hop]
  simp only [GateOp.eval, List.any_eq_true, id_eq]
  exact ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, by simp [hrw, hx]⟩

lemma support_univ_of_empty {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (h0 : value C (fun _ : Fin n => false) w = true) :
    singleSupp (n := n) C w = Finset.univ := by
  ext p
  simp only [mem_singleSupp, Finset.mem_univ, iff_true]
  exact value_mono C hG (fun _ => false) (fun v => decide (v = p)) (by simp) w h0

lemma strict_or_empty_false {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size)
    (hop : (HeavyOr.readGate C n w).op = GateOp.or) (hc : ¬ copyOr (n := n) C w) :
    value C (fun _ : Fin n => false) w = false := by
  by_contra! h0
  have h0t : value C (fun _ : Fin n => false) w = true := by simpa using h0
  have hwU := support_univ_of_empty C hG w h0t
  have hform := h0t
  rw [gate_value C _ w hn hw, ← HeavyOr.readGate_eq C n w hn hw, hop] at hform
  simp only [GateOp.eval, List.any_eq_true, id_eq] at hform
  obtain ⟨b, hb, hbt⟩ := hform
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
  have hrw : r < w := by by_contra h; simp [h] at hbt
  have hr0 : value C (fun _ : Fin n => false) r = true := by simpa [hrw] using hbt
  have hrU := support_univ_of_empty C hG r hr0
  apply hc
  change (HeavyOr.readGate C n w).op = GateOp.or ∧
    ∃ r ∈ (HeavyOr.readGate C n w).inputs, r < w ∧ singleSupp C r = singleSupp C w
  exact ⟨hop, r, hr, hrw, hrU.trans hwU.symm⟩

lemma strict_or_parents {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (w : ℕ) (hw : w ∈ refinedCharge C S)
    (hop : (HeavyOr.readGate C n w).op = GateOp.or)
    (P : Finset ℕ)
    (hP : ∀ r ∈ P, r < w ∧ r ∈ (HeavyOr.readGate C n w).inputs)
    (htrans : ∀ (p : Fin n) (z : Fin n → Bool),
      (∀ r ∈ P, value C (fun v => decide (v = p)) r = true → value C z r = true) →
      value C (fun v => decide (v = p)) w = true → value C z w = true) :
    P = (HeavyOr.readGate C n w).inputs.toFinset.filter (· < w) ∧ P.card = 2 := by
  classical
  have hh := Finset.mem_filter.mp hw
  have hg := (mem_charge C S w).mp hh.1
  have hc : ¬ copyOr (n := n) C w := hh.2
  have hzero := strict_or_empty_false C hG w hg.1.1 hg.1.2 hop hc
  have hcov : singleSupp (n := n) C w ⊆ P.biUnion (singleSupp C) := by
    intro p hp
    by_contra hn
    have hz := htrans p (fun _ => false) ?_ ((mem_singleSupp C w p).mp hp)
    · rw [hzero] at hz
      exact Bool.false_ne_true hz
    · intro r hr hpr
      exact False.elim (hn (Finset.mem_biUnion.mpr ⟨r, hr, (mem_singleSupp C r p).mpr hpr⟩))
  have hP2 : 2 ≤ P.card := by
    by_contra! hsmall
    obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < (singleSupp (n := n) C w).card)
    obtain ⟨r, hr, hpr⟩ := Finset.mem_biUnion.mp (hcov hp)
    have hsame : ∀ s ∈ P, s = r := fun s hs =>
      Finset.card_le_one.mp (show P.card ≤ 1 by omega) s hs r hr
    have hsub : singleSupp (n := n) C w ⊆ singleSupp C r := by
      intro q hq
      obtain ⟨s, hs, hqs⟩ := Finset.mem_biUnion.mp (hcov hq)
      simpa [hsame s hs] using hqs
    have hsub' : singleSupp (n := n) C r ⊆ singleSupp C w := by
      intro q hq
      exact (mem_singleSupp C w q).mpr
        (or_child C w r hg.1.1 hg.1.2 hop (hP r hr).2 (hP r hr).1 _
          ((mem_singleSupp C r q).mp hq))
    apply hc
    change (HeavyOr.readGate C n w).op = GateOp.or ∧
      ∃ r ∈ (HeavyOr.readGate C n w).inputs, r < w ∧ singleSupp C r = singleSupp C w
    exact ⟨hop, r, (hP r hr).2, (hP r hr).1, Finset.Subset.antisymm hsub' hsub⟩
  let Q := (HeavyOr.readGate C n w).inputs.toFinset.filter (· < w)
  have hPQ : P ⊆ Q := by
    intro r hr
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hP r hr).2, (hP r hr).1⟩
  have hQ2 : Q.card ≤ 2 := by
    have hgm : HeavyOr.readGate C n w ∈ C.gates := by
      rw [HeavyOr.readGate_eq C n w hg.1.1 hg.1.2]
      exact List.getElem_mem _
    exact (Finset.card_filter_le _ _).trans
      ((List.toFinset_card_le _).trans (hG _ hgm).2)
  have hcard := Finset.card_le_card hPQ
  change P = Q ∧ P.card = 2
  refine ⟨Finset.eq_of_subset_of_card_le hPQ (by omega), by omega⟩

end PEqualNP.Outside.L_meta_997.OrParents
namespace PEqualNP.Outside.L_meta_997.Restriction

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.light

def mask {n : ℕ} (U : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun p => if p ∈ U then x p else false

def wire {n : ℕ} (C : Circuit) (U : Finset (Fin n)) (r : ℕ) : ℕ :=
  if r ∈ U.image Fin.val ∨ n ≤ r then r else n + C.size

def restrict {n : ℕ} (C : Circuit) (U : Finset (Fin n)) : Circuit :=
  ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map (wire C U)⟩), wire C U C.output⟩

lemma restrict_size {n : ℕ} (C : Circuit) (U : Finset (Fin n)) :
    (restrict C U).size = C.size := by simp [restrict, Circuit.size]

lemma wire_above {n : ℕ} (C : Circuit) (U : Finset (Fin n)) (r : ℕ) (hr : n ≤ r) :
    wire C U r = r := by simp [wire, hr]

lemma wire_input {n : ℕ} (C : Circuit) (U : Finset (Fin n)) (p : Fin n) :
    wire C U p = if p ∈ U then p.val else n + C.size := by
  have he : p.val ∈ U.image Fin.val ↔ p ∈ U := by
    constructor
    · rintro hp
      obtain ⟨q, hq, he⟩ := Finset.mem_image.mp hp
      have : q = p := Fin.ext he
      simpa [this] using hq
    · exact fun hp => Finset.mem_image_of_mem Fin.val hp
  simp only [wire, he, not_le_of_gt p.isLt, or_false]

lemma wire_le {n : ℕ} (C : Circuit) (U : Finset (Fin n)) (r : ℕ) : r ≤ wire C U r := by
  unfold wire
  split_ifs with h
  · exact le_rfl
  · have hn : ¬ n ≤ r := fun hn => h (Or.inr hn)
    omega

lemma moved_false {n : ℕ} (C : Circuit) (U : Finset (Fin n)) (x : Fin n → Bool)
    (r : ℕ) (hr : wire C U r ≠ r) : value C (mask U x) r = false := by
  have hn : r < n := by
    by_contra h
    exact hr (wire_above C U r (by omega))
  let p : Fin n := ⟨r, hn⟩
  have hp : p ∉ U := by
    intro hp
    have he := wire_input C U p
    rw [ite_eq_left hp] at he
    exact hr he
  change value C (mask U x) p = false
  rw [input_value]
  simp [mask, hp]

lemma restrict_value {n : ℕ} (C : Circuit) (U : Finset (Fin n)) (x : Fin n → Bool) (w : ℕ) :
    value (restrict C U) x (wire C U w) = value C (mask U x) w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · let p : Fin n := ⟨w, hn⟩
      change value (restrict C U) x (wire C U p) = value C (mask U x) p
      rw [wire_input, input_value]
      by_cases hp : p ∈ U
      · rw [ite_eq_left hp]
        simp [input_value, mask, hp]
      · rw [ite_eq_right hp, missing_value _ _ _ (by rw [restrict_size])]
        simp [mask, hp]
    · have hn' : n ≤ w := by omega
      rw [wire_above C U w hn']
      by_cases hw : w < n + C.size
      · have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
        have hread (r : ℕ) :
            (if wire C U r < w then value (restrict C U) x (wire C U r) else false) =
              (if r < w then value C (mask U x) r else false) := by
          by_cases hr : r < w
          · rw [ite_eq_left hr]
            by_cases hm : wire C U r < w
            · rw [ite_eq_left hm, ih r hr]
            · rw [ite_eq_right hm]
              have hne : wire C U r ≠ r := fun he => hm (by rw [he]; exact hr)
              exact (moved_false C U x r hne).symm
          · have hm : ¬ wire C U r < w := by have := wire_le C U r; omega
            simp [hr, hm]
        rw [gate_value (restrict C U) x w hn' (by rwa [restrict_size]), gate_value C _ w hn' hw]
        simp only [restrict, List.getElem_map, List.map_map, Function.comp_apply]
        congr 1
        apply List.map_congr_left
        intro r _
        exact hread r
      · rw [missing_value C _ w (by omega), missing_value (restrict C U) x w
          (by rw [restrict_size]; omega)]

lemma restrict_good {n : ℕ} (C : Circuit) (U : Finset (Fin n))
    (hgate : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ (restrict C U).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
  simpa using hgate h hh

lemma restrict_supp_subset {n : ℕ} (C : Circuit) (U : Finset (Fin n))
    (hgate : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) : singleSupp (n := n) (restrict C U) w ⊆ singleSupp C w := by
  intro p hp
  have hv := (mem_singleSupp (restrict C U) w p).mp hp
  apply (mem_singleSupp C w p).mpr
  by_cases hn : w < n
  · let r : Fin n := ⟨w, hn⟩
    change value C (fun v => decide (v = p)) r = true
    change value (restrict C U) (fun v => decide (v = p)) r = true at hv
    simpa only [input_value] using hv
  · have he := restrict_value C U (fun v => decide (v = p)) w
    rw [wire_above C U w (by omega)] at he
    rw [he] at hv
    apply value_mono C hgate (mask U (fun v => decide (v = p))) (fun v => decide (v = p)) _ w hv
    intro r hr
    by_cases hu : r ∈ U
    · simpa [mask, hu] using hr
    · simp [mask, hu] at hr

end PEqualNP.Outside.L_meta_997.Restriction
namespace PEqualNP.Outside.L_meta_997.LightBoundary

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.light PEqualNP.Outside.L_meta_997.LightSelected PEqualNP.Outside.L_meta_997.LightSmart

lemma boundary_lower_bound {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (o k : ℕ) (hk : 1 < k)
    (hcorrect : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value C x o = decide (∃ p ∈ S, x p = true))
    (B : Finset ℕ) (hd : Disjoint B (charge C S))
    (hcut : ∀ (p : Fin n) (z : Fin n → Bool),
      (∀ w ∈ B, value C (fun v => decide (v = p)) w = true → value C z w = true) →
      value C (fun v => decide (v = p)) o = true → value C z o = true) :
    min k S.card ≤ B.card := by
  classical
  by_contra! hsmall
  have hsmallS : B.card < S.card := hsmall.trans_le (min_le_right ..)
  have hsmallK : B.card < k := hsmall.trans_le (min_le_left ..)
  let clean (w : ℕ) : Finset (Fin n) :=
    if singleSupp C w ⊆ S then singleSupp C w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : singleSupp C w ⊆ S
    · simp only [clean, ite_eq_left hs]
      by_contra! hlarge
      exact Finset.disjoint_left.mp hd hw
        ((mem_charge C S w).mpr ⟨singleSupp_gate C w (by omega), hs, by omega⟩)
    · simp [clean, hs]
  have hcover : (B.biUnion clean).card < S.card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨p, hpS, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let Dn := B.filter (fun w => ¬ singleSupp C w ⊆ S)
  have hout (w : {w // w ∈ Dn}) : ∃ q : Fin n, q ∈ singleSupp C w.val ∧ q ∉ S := by
    have hns := (Finset.mem_filter.mp w.property).2
    simpa only [Finset.not_subset] using hns
  choose qs hqs using hout
  let V : Finset (Fin n) := Dn.attach.image qs
  let z : Fin n → Bool := fun v => decide (v ∈ V)
  have hVcard : V.card < k := by
    have hi := Finset.card_image_le (s := Dn.attach) (f := qs)
    have hf := Finset.card_filter_le B (fun w => ¬ singleSupp C w ⊆ S)
    simp only [Finset.card_attach] at hi
    change V.card ≤ Dn.card at hi
    change Dn.card ≤ B.card at hf
    omega
  have hweight : (Finset.univ.filter (fun v => z v = true)).card < k := by
    simpa [z] using hVcard
  have hVS : ∀ q ∈ V, q ∉ S := by
    intro q hq
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hq
    exact (hqs w).2
  have hzfalse : value C z o = false := by
    rw [hcorrect z hweight]
    simp only [decide_eq_false_iff_not, not_exists]
    intro q hq
    exact hVS q (by simpa [z] using hq.2) hq.1
  have hfire : value C (fun v => decide (v = p)) o = true := by
    rw [hcorrect]
    · simp [hpS]
    · have hsingle : Finset.univ.filter (fun v : Fin n => decide (v = p) = true) = {p} := by
        ext v
        simp
      rw [hsingle, Finset.card_singleton]
      exact hk
  have hztrue : value C z o = true := by
    apply hcut p z _ hfire
    intro w hw hx
    by_cases hs : singleSupp C w ⊆ S
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hw, by simp only [clean, ite_eq_left hs]; exact (mem_singleSupp C w p).mpr hx⟩))
    · let d : {w // w ∈ Dn} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
      apply value_mono C hG (fun v => decide (v = qs d)) z _ w
        ((mem_singleSupp C w (qs d)).mp (hqs d).1)
      intro v hv
      have hv' : v = qs d := by simpa using hv
      subst v
      simp only [z, decide_eq_true_eq]
      exact Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩
  rw [hzfalse] at hztrue
  exact Bool.false_ne_true hztrue

lemma selected_boundary {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (o k : ℕ) (hk : 1 < k)
    (hcorrect : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value C x o = decide (∃ p ∈ S, x p = true)) :
    ∃ (parents : ℕ → Finset ℕ) (B : Finset ℕ), Disjoint B (charge C S) ∧
      min k S.card ≤ B.card ∧
      (∀ w ∈ charge C S,
        (parents w).card ≤ (if w ∈ smartCharge C S then 2 else 1) ∧
        (∀ r ∈ parents w, r < w) ∧
        ∀ (p : Fin n) (z : Fin n → Bool),
          (∀ r ∈ parents w, value C (fun v => decide (v = p)) r = true → value C z r = true) →
          value C (fun v => decide (v = p)) w = true → value C z w = true) ∧
      (∀ w ∈ B, Relation.ReflTransGen (fun a b => b ∈ parents a) o w) ∧
      (∀ w ∈ B, parents w = ∅) ∧
      (∀ w r, r ∈ parents w → w ∈ charge C S ∧ r < w ∧
        r ∈ (HeavyOr.readGate C n w).inputs ∧ (singleSupp (n := n) C r).Nonempty) := by
  classical
  let H := charge C S
  let K := smartCharge C S
  have hbranch : ∀ w ∈ H, ∃ P : Finset ℕ,
      P.card ≤ (if w ∈ K then 2 else 1) ∧
      (∀ r ∈ P, r < w ∧ r ∈ (HeavyOr.readGate C n w).inputs ∧ (singleSupp (n := n) C r).Nonempty) ∧
      ∀ (p : Fin n) (z : Fin n → Bool),
        (∀ r ∈ P, value C (fun v => decide (v = p)) r = true → value C z r = true) →
        value C (fun v => decide (v = p)) w = true → value C z w = true := by
    intro w hw
    obtain ⟨P, hcard, hpar, htrans⟩ := LightSmart.branch_edges C hG S w hw
    let Q := P.filter (fun r => (singleSupp (n := n) C r).Nonempty)
    refine ⟨Q, (Finset.card_filter_le _ _).trans hcard, ?_, ?_⟩
    · intro r hr
      have hr' := Finset.mem_filter.mp hr
      exact ⟨(hpar r hr'.1).1, (hpar r hr'.1).2, hr'.2⟩
    · intro p z hq
      apply htrans p z
      intro r hr hpr
      exact hq r (Finset.mem_filter.mpr ⟨hr, ⟨p, (mem_singleSupp C r p).mpr hpr⟩⟩) hpr
  let parents := fun w => if hw : w ∈ H then Classical.choose (hbranch w hw) else ∅
  have hpFull : ∀ w ∈ H,
      (parents w).card ≤ (if w ∈ K then 2 else 1) ∧
      (∀ r ∈ parents w, r < w ∧ r ∈ (HeavyOr.readGate C n w).inputs ∧ (singleSupp (n := n) C r).Nonempty) ∧
      ∀ (p : Fin n) (z : Fin n → Bool),
        (∀ r ∈ parents w, value C (fun v => decide (v = p)) r = true → value C z r = true) →
        value C (fun v => decide (v = p)) w = true → value C z w = true := by
    intro w hw
    simpa only [parents, dite_eq_left hw] using Classical.choose_spec (hbranch w hw)
  have hp : ∀ w ∈ H,
      (parents w).card ≤ (if w ∈ K then 2 else 1) ∧
      (∀ r ∈ parents w, r < w) ∧
      ∀ (p : Fin n) (z : Fin n → Bool),
        (∀ r ∈ parents w, value C (fun v => decide (v = p)) r = true → value C z r = true) →
        value C (fun v => decide (v = p)) w = true → value C z w = true := by
    intro w hw
    have hh := hpFull w hw
    exact ⟨hh.1, fun r hr => (hh.2.1 r hr).1, hh.2.2⟩
  let R := {w | Relation.ReflTransGen (fun a b => b ∈ parents a) o w}
  have hR : ∀ w ∈ H, w ∈ R → ∀ r ∈ parents w, r ∈ R := by
    intro w _ hw r hr
    exact Relation.ReflTransGen.tail hw hr
  obtain ⟨B, U, hd, hB, hBR, hcut, hu⟩ := budget_used C H K parents hp R hR
    (n + C.size) {o}
    (fun w _ hw => ((mem_charge C S w).mp hw).1.2)
    (fun w hw => by have : w = o := Finset.mem_singleton.mp hw; subst w; exact Relation.ReflTransGen.refl)
  refine ⟨parents, B, hd, ?_, hp, hBR, ?_, ?_⟩
  · apply boundary_lower_bound C hG S o k hk hcorrect B hd
    intro p z hz hfire
    exact hcut p z hz o (Finset.mem_singleton_self o) hfire
  · intro w hw
    have hwH : w ∉ H := fun h => Finset.disjoint_left.mp hd hw h
    simp [parents, hwH]
  · intro w r hr
    by_cases hw : w ∈ H
    · exact ⟨hw, (hpFull w hw).2.1 r hr⟩
    · simp [parents, hw] at hr

end PEqualNP.Outside.L_meta_997.LightBoundary
namespace PEqualNP.Outside.L_meta_997.HeavyForest

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Heavy PEqualNP.Outside.L_meta_997.HeavyOr PEqualNP.Outside.L_meta_997.HeavySelected PEqualNP.Outside.L_meta_997.GraphForest

lemma heavy_forest {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y S : Finset (Fin n)) (o : ℕ) (hYS : Disjoint Y S) (hne : S.Nonempty)
    (hso : sound C S o)
    (hfire : ∀ p ∈ S, value C (fun v => decide (v ∈ Y ∨ v=p)) o = true) :
    ∃ (W : Finset ℕ) (up : ℕ → ℕ), o ∈ W ∧
      (∀ v ∈ W, ∀ r ∈ children W o up v,
        r<v ∧ r ∈ (readGate C n v).inputs) ∧
      (∀ v ∈ W, sound C S v ∧ (supp C Y v).Nonempty) ∧
      (∀ v ∈ W, Relation.ReflTransGen (fun a b => b ∈ children W o up a) o v) ∧
      W.filter (fun v => children W o up v=∅) = S.image Fin.val ∧
      (W.filter (fun v => (children W o up v).card=2)).card + 1 = S.card ∧
      W.filter (fun v => (children W o up v).card=2) ⊆ charged C Y S := by
  classical
  obtain ⟨P,U,_,_,hStep,_,hEdge⟩ := selected_count C hG Y S o hYS hso hfire
  have hRootSupp : (supp C Y o).Nonempty := by
    obtain ⟨p,hp⟩ := hne
    exact ⟨p,(mem_supp C Y o p).mpr (hfire p hp)⟩
  have hReach : ∀ v, Relation.ReflTransGen (fun a b => b ∈ P a) o v →
      v ≤ o ∧ sound C S v ∧ (supp C Y v).Nonempty := by
    intro v hv
    induction hv with
    | refl => exact ⟨le_rfl,hso,hRootSupp⟩
    | @tail u v _ huv ih =>
      have he := hEdge u v huv
      exact ⟨(he.2.2.1.le).trans ih.1,he.2.2.2.1,he.2.2.2.2.2⟩
  let V := (Finset.range (o+1)).filter
    (fun v => Relation.ReflTransGen (fun a b => b ∈ P a) o v)
  have hVreach : ∀ v ∈ V, Relation.ReflTransGen (fun a b => b ∈ P a) o v := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have ho : o ∈ V := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),Relation.ReflTransGen.refl⟩
  have hVstep : ∀ v ∈ V, ∀ r ∈ P v, r ∈ V ∧ r<v := by
    intro v hv r hr
    have he := hEdge v r hr
    have hrv := Relation.ReflTransGen.tail (hVreach v hv) hr
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := (hReach r hrv).1; omega),hrv⟩,
      he.2.2.1⟩
  let B := V.filter (fun v => P v=∅)
  have hBV : B ⊆ V := Finset.filter_subset _ _
  have hLeaf : ∀ w ∈ V, ∀ p ∈ supp C Y w,
      ∃ b ∈ B, p ∈ supp C Y b := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw p hp
      by_cases hz : P w=∅
      · exact ⟨w,Finset.mem_filter.mpr ⟨hw,hz⟩,hp⟩
      · obtain ⟨r,hr⟩ := Finset.nonempty_iff_ne_empty.mpr hz
        have he := hEdge w r hr
        have hc := (hStep w he.1 he.2.1).2.2 hp
        obtain ⟨r',hr',hp'⟩ := Finset.mem_biUnion.mp hc
        have hh := hVstep w hw r' hr'
        exact ih r' hh.2 hh.1 p hp'
  have hBinput : ∀ b ∈ B, ∃ p : Fin n, b=p.val ∧ p ∈ S := by
    intro b hb
    have hv := hBV hb
    have hs := hReach b (hVreach b hv)
    have hz := (Finset.mem_filter.mp hb).2
    have hn : b<n := by
      by_contra! hge
      have hupper : b<n+C.size := by
        by_contra! hout
        obtain ⟨p,hp⟩ := hs.2.2
        have hh := (mem_supp C Y b p).mp hp
        rw [missing_value C _ b hout] at hh
        exact Bool.false_ne_true hh
      have hc := (hStep b ⟨hge,hupper⟩ hs.2.1).2.2
      obtain ⟨p,hp⟩ := hs.2.2
      have hh := hc hp
      simp [hz] at hh
    let p : Fin n := ⟨b,hn⟩
    have hval : value C (fun q : Fin n => decide (q=p)) b = true := by
      change value C (fun q : Fin n => decide (q=p)) p = true
      simp only [input_value,decide_true]
    obtain ⟨q,hqS,hq⟩ := hs.2.1 _ hval
    have hqp : q=p := of_decide_eq_true hq
    exact ⟨p,rfl,by simpa only [hqp] using hqS⟩
  have hBsupp : ∀ b ∈ B, (supp C Y b).card ≤ 1 := by
    intro b hb
    obtain ⟨p,hbp,hpS⟩ := hBinput b hb
    have hpn : p ∉ Y := fun hpY => Finset.disjoint_left.mp hYS hpY hpS
    have he : supp C Y b = {p} := by
      ext q
      rw [hbp,mem_supp,input_value]
      simp [hpn,eq_comm]
    simp [he]
  have hCover : S ⊆ B.biUnion (supp C Y) := by
    intro p hp
    obtain ⟨b,hb,hpb⟩ := hLeaf o ho p ((mem_supp C Y o p).mpr (hfire p hp))
    exact Finset.mem_biUnion.mpr ⟨b,hb,hpb⟩
  have hCardLower : S.card ≤ B.card := by
    have h1 := Finset.card_le_card hCover
    have h2 := Finset.card_biUnion_le_card_mul B (supp C Y) 1 hBsupp
    simp only [mul_one] at h2
    omega
  have hBsub : B ⊆ S.image Fin.val := by
    intro b hb
    obtain ⟨p,hbp,hpS⟩ := hBinput b hb
    exact Finset.mem_image.mpr ⟨p,hpS,hbp.symm⟩
  have hImage : (S.image Fin.val).card=S.card := Finset.card_image_of_injective S Fin.val_injective
  have hBeq : B=S.image Fin.val :=
    Finset.eq_of_subset_of_card_le hBsub (by omega)
  have hBne : B.Nonempty := by
    rw [hBeq]
    exact hne.image _
  have hBinary : ∀ v ∈ V, (P v).card ≤ 2 := by
    intro v hv
    by_cases hz : P v=∅
    · simp [hz]
    · obtain ⟨r,hr⟩ := Finset.nonempty_iff_ne_empty.mpr hz
      have he := hEdge v r hr
      have hc := (hStep v he.1 he.2.1).1
      split_ifs at hc <;> omega
  obtain ⟨W,up,how,hWV,hWsub,hWr,hWleaf,hWcount⟩ :=
    extract_forest P V B o ho hBV hBne hVstep hVreach
      (fun b hb => (Finset.mem_filter.mp hb).2) hBinary
  refine ⟨W,up,how,?_,?_,hWr,hWleaf.trans hBeq,?_,?_⟩
  · intro v hv r hr
    have he := hEdge v r (hWsub v hv hr)
    exact ⟨he.2.2.1,he.2.2.2.2.1⟩
  · intro v hv
    exact (hReach v (hVreach v (hWV hv))).2
  · simpa only [hBeq,hImage] using hWcount
  · intro v hv
    have hv' := Finset.mem_filter.mp hv
    have hc := Finset.card_le_card (hWsub v hv'.1)
    have hPne : (P v).Nonempty := by
      apply Finset.card_pos.mp
      omega
    obtain ⟨r,hr⟩ := hPne
    have he := hEdge v r hr
    have hb := (hStep v he.1 he.2.1).1
    by_contra hn
    simp only [hn,ite_false] at hb
    omega

end PEqualNP.Outside.L_meta_997.HeavyForest

namespace PEqualNP.Outside.L_meta_997.LightForest

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.light PEqualNP.Outside.L_meta_997.LightSmart PEqualNP.Outside.L_meta_997.LightBoundary PEqualNP.Outside.L_meta_997.GraphForest

lemma light_forest {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (o k : ℕ) (hk : 1 < k) (hne : S.Nonempty)
    (hcorrect : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value C x o = decide (∃ p ∈ S, x p = true)) :
    ∃ (W : Finset ℕ) (up : ℕ → ℕ), o ∈ W ∧
      (∀ v ∈ W, ∀ r ∈ children W o up v,
        r<v ∧ r ∈ (HeavyOr.readGate C n v).inputs) ∧
      (∀ v ∈ W, (singleSupp (n := n) C v).Nonempty) ∧
      (∀ v ∈ W, Relation.ReflTransGen (fun a b => b ∈ children W o up a) o v) ∧
      Disjoint (W.filter (fun v => children W o up v=∅)) (charge C S) ∧
      (W.filter (fun v => children W o up v=∅)).card = min k S.card ∧
      (W.filter (fun v => (children W o up v).card=2)).card + 1 = min k S.card ∧
      W.filter (fun v => (children W o up v).card=2) ⊆ smartCharge C S := by
  classical
  obtain ⟨P,B,hBdis,hBcard,hStep,hBR,hTerm,hEdge⟩ :=
    selected_boundary C hG S o k hk hcorrect
  have hRootSupp : (singleSupp (n := n) C o).Nonempty := by
    obtain ⟨p,hp⟩ := hne
    refine ⟨p,(mem_singleSupp C o p).mpr ?_⟩
    rw [hcorrect]
    · simp [hp]
    · have hh : Finset.univ.filter (fun v : Fin n => decide (v=p)=true)={p} := by
        ext v
        simp
      simpa only [hh,Finset.card_singleton] using hk
  have hReach : ∀ v, Relation.ReflTransGen (fun a b => b ∈ P a) o v →
      v≤o ∧ (singleSupp (n := n) C v).Nonempty := by
    intro v hv
    induction hv with
    | refl => exact ⟨le_rfl,hRootSupp⟩
    | @tail u v _ huv ih =>
      have he := hEdge u v huv
      exact ⟨he.2.1.le.trans ih.1,he.2.2.2⟩
  let V := (Finset.range (o+1)).filter
    (fun v => Relation.ReflTransGen (fun a b => b ∈ P a) o v)
  have hVreach : ∀ v ∈ V, Relation.ReflTransGen (fun a b => b ∈ P a) o v := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have ho : o ∈ V := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega),Relation.ReflTransGen.refl⟩
  have hVstep : ∀ v ∈ V, ∀ r ∈ P v, r ∈ V ∧ r<v := by
    intro v hv r hr
    have he := hEdge v r hr
    have hrv := Relation.ReflTransGen.tail (hVreach v hv) hr
    exact ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by have := (hReach r hrv).1; omega),hrv⟩,he.2.1⟩
  have hBV : B ⊆ V := by
    intro b hb
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by have := (hReach b (hBR b hb)).1; omega),hBR b hb⟩
  obtain ⟨D,hDB,hDcard⟩ := Finset.exists_subset_card_eq hBcard
  have hDne : D.Nonempty := by
    apply Finset.card_pos.mp
    rw [hDcard]
    exact lt_min (by omega) (Finset.card_pos.mpr hne)
  have hBinary : ∀ v ∈ V, (P v).card ≤ 2 := by
    intro v _
    by_cases hz : P v=∅
    · simp [hz]
    · obtain ⟨r,hr⟩ := Finset.nonempty_iff_ne_empty.mpr hz
      have hc := (hStep v (hEdge v r hr).1).1
      split_ifs at hc <;> omega
  obtain ⟨W,up,how,hWV,hWsub,hWr,hWleaf,hWcount⟩ :=
    extract_forest P V D o ho (hDB.trans hBV) hDne hVstep hVreach
      (fun b hb => hTerm b (hDB hb)) hBinary
  refine ⟨W,up,how,?_,?_,hWr,?_,?_,?_,?_⟩
  · intro v hv r hr
    have he := hEdge v r (hWsub v hv hr)
    exact ⟨he.2.1,he.2.2.1⟩
  · intro v hv
    exact (hReach v (hVreach v (hWV hv))).2
  · rw [hWleaf]
    exact Finset.disjoint_left.mpr (fun v hv hc =>
      Finset.disjoint_left.mp hBdis (hDB hv) hc)
  · simpa only [hWleaf] using hDcard
  · simpa only [hDcard] using hWcount
  · intro v hv
    have hv' := Finset.mem_filter.mp hv
    have hc := Finset.card_le_card (hWsub v hv'.1)
    have hPne : (P v).Nonempty := by
      apply Finset.card_pos.mp
      omega
    obtain ⟨r,hr⟩ := hPne
    have hb := (hStep v (hEdge v r hr).1).1
    by_contra hn
    simp only [hn,ite_false] at hb
    omega

end PEqualNP.Outside.L_meta_997.LightForest

namespace PEqualNP.Outside.L_meta_997.PrefixBudget

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Heavy

lemma fixed_before {n : ℕ} (C : Circuit) (t : ℕ) (b : Bool) (x : Fin n → Bool)
    (w : ℕ) (hwt : w < n + t) :
    value (fixed C t b) x w = value C x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value C x ⟨w, hn⟩
      have h2 := input_value (fixed C t b) x ⟨w, hn⟩
      simp only at h1 h2
      rw [h1, h2]
    by_cases hw : w < n + C.size
    · rw [gate_value C x w (by omega) hw,
          fixed_other C t b x w (by omega) hw (by omega)]
      rw [List.map_congr_left (fun r _ => ?_)]
      by_cases hr : r < w
      · simpa [hr] using ih r hr (by omega)
      · simp [hr]
    · rw [missing_value C x w (by omega),
        missing_value (fixed C t b) x w (by rw [fixed_size]; omega)]

lemma predecessor {n : ℕ} (C : Circuit) (t : ℕ) (y : Finset (Fin n))
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hlow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < y.card → value C x (n+t) = true)
    (hfalse : value C (fun v => decide (v ∈ y)) (n+t) = false)
    (hy : 0 < y.card) :
    ∃ r : ℕ, value (fixed C t true) (fun v => decide (v ∈ y)) r = true ∧
      ∀ x : Fin n → Bool,
        (Finset.univ.filter (fun v => x v = true)).card < y.card →
          value (fixed C t true) x r = false := by
  obtain ⟨q, hq, hqn⟩ := light.not_exists_of_positive_window C t y hgate hnot hlow hfalse hy
  have ht : t < C.gates.length := hq ▸ q.isLt
  have hop : (C.gates[t]).op = GateOp.not := by simpa [← hq] using hqn
  have hf := gate_value C (fun v => decide (v ∈ y)) (n+t)
    (by omega) (by unfold Circuit.size; omega)
  simp only [Nat.add_sub_cancel_left] at hf
  rw [hop, hfalse] at hf
  cases hi : (C.gates[t]).inputs with
  | nil => simp [hi, GateOp.eval] at hf
  | cons r rs =>
    have hr : r < n+t ∧ value C (fun v => decide (v ∈ y)) r = true := by
      by_cases h : r < n+t
      · simp [hi, GateOp.eval, h] at hf
        exact ⟨h, hf⟩
      · simp [hi, GateOp.eval, h] at hf
    refine ⟨r, ?_, ?_⟩
    · rw [fixed_before C t true _ r hr.1]
      exact hr.2
    · intro x hx
      rw [fixed_before C t true x r hr.1]
      have hf' := gate_value C x (n+t) (by omega) (by unfold Circuit.size; omega)
      simp only [Nat.add_sub_cancel_left] at hf'
      rw [hop, hlow x hx] at hf'
      simpa [hi, GateOp.eval, hr.1] using hf'

lemma light_sum_with_empty {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (o : Fin m → ℕ) (k : ℕ)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun v => x v = true)).card < k →
      light.value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (E : Finset ℕ) (hE : E ⊆ Finset.Ico n (n+C.size))
    (hempty : ∀ w ∈ E, light.singleSupp (n:=n) C w = ∅) :
    (∑ i : Fin m, min k (S i).card) + E.card ≤ C.gates.length + m := by
  classical
  let A := fun i => light.charge C (S i)
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint A := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro w hi hj
    have hwi := (light.mem_charge C (S i) w).mp hi
    have hwj := (light.mem_charge C (S j) w).mp hj
    have hs : light.singleSupp C w ⊆ S i ∩ S j := Finset.subset_inter hwi.2.1 hwj.2.1
    have := Finset.card_le_card hs
    have := hinter i j hij
    omega
  let U := Finset.univ.biUnion A
  have hU : U ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hw
    exact Finset.mem_Ico.mpr ((light.mem_charge C (S i) w).mp hwi).1
  have hUE : Disjoint U E := by
    apply Finset.disjoint_left.mpr
    intro w hw he
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hw
    have hc := ((light.mem_charge C (S i) w).mp hwi).2.2
    rw [hempty w he] at hc
    simp at hc
  have hb : U.card + E.card ≤ C.gates.length := by
    rw [← Finset.card_union_of_disjoint hUE]
    have h := Finset.card_le_card (Finset.union_subset hU hE)
    simpa only [Nat.card_Ico, Nat.add_sub_cancel_left, Circuit.size] using h
  have hs : (∑ i : Fin m, min k (S i).card) ≤ U.card + m := by
    calc
      _ ≤ ∑ i : Fin m, ((A i).card + 1) :=
        Finset.sum_le_sum fun i _ => light.light_bound C hG (S i) (o i) k (hcorrect i)
      _ = U.card + m := by rw [Finset.sum_add_distrib, ← Finset.card_biUnion hd]; simp [U]
  omega

lemma truncated_sum_prefix_budget {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < y.card → value C x (n+t) = true)
    (hfalse : value C (fun v => decide (v ∈ y)) (n+t) = false) :
    (∑ i : Fin m, min y.card (S i).card) + (y.card - 1) ≤ C.gates.length + m := by
  classical
  by_cases hy : 0 < y.card
  · let D := fixed C t true
    have hg := fixed_good C t true hgate hnot
    obtain ⟨r, hry, hrlow⟩ := predecessor C t y hgate hnot hlow hfalse hy
    let E := (Finset.Ico n (n+D.size)).filter
      (fun w => supp D (∅ : Finset (Fin n)) w = ∅ ∧ value D (fun v => decide (v ∈ y)) w = true)
    have hpre : y.card ≤ E.card + 1 := Prefix.empty_support_count D r _ hg hry hrlow
    have hout : ∀ (i : Fin m) (x : Fin n → Bool),
        (Finset.univ.filter (fun v => x v = true)).card < y.card →
        light.value D x (o i) = decide (∃ p ∈ S i, x p = true) := by
      intro i x hx
      change value D x (o i) = _
      rw [fixed_eq C t true x (hlow x hx) (o i), hcorrect]
    have he := light_sum_with_empty S D hg hinter o y.card hout E
      (fun w hw => (Finset.mem_filter.mp hw).1) (by
        intro w hw
        have hs := (Finset.mem_filter.mp hw).2.1
        simpa [supp, light.singleSupp, value, light.value] using hs)
    have hsize : D.gates.length = C.gates.length := by simp [D, fixed]
    rw [hsize] at he
    omega
  · have hy0 : y.card = 0 := by omega
    simp [hy0]

lemma total_excess_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → (i : ℕ) = t)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card →
        value C x (n+t) = true)
    (hfalse : value C (fun v : Fin n => decide (v ∈ y)) (n+t) = false)
    (hexcess : (∑ i : Fin m, if Disjoint (S i) y then (S i).card - (y.card+1) else 0)
      ≤ y.card - 1) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length =>
        (∃ i : Fin m, ∀ p : Fin n,
          value C (fun v : Fin n => decide (v = p)) (n + g) = true ↔ p ∈ S i) ∧
        (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y →
          (value C (fun v : Fin n => decide (v ∈ y ∨ v = p))
            (n + g) = true ↔ p ∈ S i)))).card + m := by
  classical
  by_cases hy : y.card ≤ 2
  · have h := light.small_window_bound S C o t y hinter hgate hnot hcorrect hfalse hy
    omega
  · let I := Finset.univ.filter (fun i : Fin m => Disjoint (S i) y ∧ 2 ≤ (S i).card)
    have hterm (i : Fin m) :
        (if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
          min y.card (S i).card + (if i ∈ I then 1 else 0) +
            (if Disjoint (S i) y then (S i).card - (y.card+1) else 0) := by
      by_cases hd : Disjoint (S i) y
      · simp only [ite_eq_left hd]
        by_cases hc : (S i).card ≤ y.card
        · rw [min_eq_right hc]
          omega
        · have hi : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, by omega⟩
          rw [min_eq_left (by omega), if_pos hi]
          omega
      · simp only [ite_eq_right hd]
        omega
    have hs := truncated_sum_prefix_budget S C o t y hinter hgate hnot hcorrect hlow hfalse
    have hr := Refund.refund_output_count S C o y hinter hcorrect
    have hsum :
        (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
          (∑ i : Fin m, min y.card (S i).card) + I.card +
          (∑ i : Fin m, if Disjoint (S i) y then (S i).card - (y.card+1) else 0) := by
      calc
        _ ≤ ∑ i : Fin m, (min y.card (S i).card + (if i ∈ I then 1 else 0) +
          (if Disjoint (S i) y then (S i).card - (y.card+1) else 0)) :=
            Finset.sum_le_sum fun i _ => hterm i
        _ = _ := by simp [Finset.sum_add_distrib]
    let R := Finset.univ.filter (fun g : Fin C.gates.length =>
        (∃ i : Fin m, ∀ p : Fin n,
          value C (fun v : Fin n => decide (v = p)) (n + g) = true ↔ p ∈ S i) ∧
        (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y →
          (value C (fun v : Fin n => decide (v ∈ y ∨ v = p))
            (n + g) = true ↔ p ∈ S i)))
    have hr' : I.card ≤ R.card := hr
    change _ ≤ C.gates.length + R.card + m
    omega

end PEqualNP.Outside.L_meta_997.PrefixBudget

namespace PEqualNP.Outside.L_meta_997.PrefixBudget

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Heavy

lemma light_sum_with_unused {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (o : Fin m → ℕ) (k : ℕ)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      (Finset.univ.filter (fun v => x v = true)).card < k →
      light.value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (E : Finset ℕ) (hE : E ⊆ Finset.Ico n (n+C.size))
    (hunused : ∀ w ∈ E, ∀ i, w ∉ light.charge C (S i)) :
    (∑ i : Fin m, min k (S i).card) + E.card ≤ C.gates.length + m := by
  classical
  let A := fun i => light.charge C (S i)
  have hd : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint A := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro w hi hj
    have hwi := (light.mem_charge C (S i) w).mp hi
    have hwj := (light.mem_charge C (S j) w).mp hj
    have hs : light.singleSupp C w ⊆ S i ∩ S j := Finset.subset_inter hwi.2.1 hwj.2.1
    have := Finset.card_le_card hs
    have := hinter i j hij
    omega
  let U := Finset.univ.biUnion A
  have hU : U ⊆ Finset.Ico n (n+C.size) := by
    intro w hw
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hw
    exact Finset.mem_Ico.mpr ((light.mem_charge C (S i) w).mp hwi).1
  have hUE : Disjoint U E := by
    apply Finset.disjoint_left.mpr
    intro w hw he
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hw
    exact hunused w he i hwi
  have hb : U.card + E.card ≤ C.gates.length := by
    rw [← Finset.card_union_of_disjoint hUE]
    have h := Finset.card_le_card (Finset.union_subset hU hE)
    simpa only [Nat.card_Ico, Nat.add_sub_cancel_left, Circuit.size] using h
  have hs : (∑ i : Fin m, min k (S i).card) ≤ U.card + m := by
    calc
      _ ≤ ∑ i : Fin m, ((A i).card + 1) :=
        Finset.sum_le_sum fun i _ => light.light_bound C hG (S i) (o i) k (hcorrect i)
      _ = U.card + m := by rw [Finset.sum_add_distrib, ← Finset.card_biUnion hd]; simp [U]
  omega

lemma proper_family_of_disjoint {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hy : 0 < y.card) (j : Fin m) (hd : Disjoint (S j) y) (hj : 2 ≤ (S j).card) :
    ∀ i, S i ≠ Finset.univ := by
  intro i heq
  by_cases hij : i = j
  · subst i
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hy
    exact Finset.disjoint_left.mp hd (by rw [heq]; simp) hp
  · have h := hinter i j hij
    rw [heq, Finset.univ_inter] at h
    omega

lemma truncated_sum_prefix_not_budget {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ q : Fin C.gates.length, (C.gates.get q).op = GateOp.not → q.val = t)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < y.card → value C x (n+t) = true)
    (hfalse : value C (fun v => decide (v ∈ y)) (n+t) = false)
    (hproper : ∀ i, S i ≠ Finset.univ) :
    (∑ i : Fin m, min y.card (S i).card) + y.card ≤ C.gates.length + m := by
  classical
  by_cases hy : 0 < y.card
  · let D := fixed C t true
    have hg := fixed_good C t true hgate hnot
    obtain ⟨q, hq, _⟩ := light.not_exists_of_positive_window C t y hgate hnot hlow hfalse hy
    have ht : t < C.gates.length := hq ▸ q.isLt
    obtain ⟨r, hry, hrlow⟩ := predecessor C t y hgate hnot hlow hfalse hy
    let E := (Finset.Ico n (n+D.size)).filter
      (fun w => supp D (∅ : Finset (Fin n)) w = ∅ ∧ value D (fun v => decide (v ∈ y)) w = true)
    have hpre : y.card ≤ E.card + 1 := Prefix.empty_support_count D r _ hg hry hrlow
    have hempty : ∀ w ∈ E, light.singleSupp (n:=n) D w = ∅ := by
      intro w hw
      have hs := (Finset.mem_filter.mp hw).2.1
      simpa [supp, light.singleSupp, value, light.value] using hs
    have hnotvalue (x : Fin n → Bool) : light.value D x (n+t) = true := fixed_at C t true ht x
    have hnotSupp : light.singleSupp (n:=n) D (n+t) = Finset.univ := by
      ext p
      simp [light.singleSupp, hnotvalue]
    have hnotE : n+t ∉ E := by
      intro hn
      have hh := hempty (n+t) hn
      rw [hnotSupp] at hh
      obtain ⟨p, _⟩ := Finset.card_pos.mp hy
      have hp : p ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ _
      rw [hh] at hp
      simp at hp
    have hout : ∀ (i : Fin m) (x : Fin n → Bool),
        (Finset.univ.filter (fun v => x v = true)).card < y.card →
        light.value D x (o i) = decide (∃ p ∈ S i, x p = true) := by
      intro i x hx
      change value D x (o i) = _
      rw [fixed_eq C t true x (hlow x hx) (o i), hcorrect]
    have he := light_sum_with_unused S D hg hinter o y.card hout (insert (n+t) E)
      (by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · apply Finset.mem_Ico.mpr
          simpa [D, fixed, Circuit.size] using
            (show n ≤ n+t ∧ n+t < n+C.gates.length by omega)
        · exact (Finset.mem_filter.mp hw).1)
      (by
        intro w hw i hc
        have hs := (light.mem_charge D (S i) w).mp hc
        rcases Finset.mem_insert.mp hw with rfl | hw
        · rw [hnotSupp] at hs
          exact hproper i (Finset.Subset.antisymm (Finset.subset_univ _) hs.2.1)
        · rw [hempty w hw] at hs
          simp at hs)
    have hsize : D.gates.length = C.gates.length := by simp [D, fixed]
    rw [hsize, Finset.card_insert_of_notMem hnotE] at he
    omega
  · have hy0 : y.card = 0 := by omega
    simp [hy0]

end PEqualNP.Outside.L_meta_997.PrefixBudget
namespace PEqualNP.Outside.L_meta_997.PrefixBudget

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Heavy

lemma total_excess_not_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → (i : ℕ) = t)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card →
        value C x (n+t) = true)
    (hfalse : value C (fun v : Fin n => decide (v ∈ y)) (n+t) = false)
    (hexcess : (∑ i : Fin m, if Disjoint (S i) y then (S i).card - (y.card+1) else 0)
      ≤ y.card) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length =>
        (∃ i : Fin m, ∀ p : Fin n,
          value C (fun v : Fin n => decide (v = p)) (n + g) = true ↔ p ∈ S i) ∧
        (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y →
          (value C (fun v : Fin n => decide (v ∈ y ∨ v = p))
            (n + g) = true ↔ p ∈ S i)))).card + m := by
  classical
  by_cases hy : y.card ≤ 2
  · have h := light.small_window_bound S C o t y hinter hgate hnot hcorrect hfalse hy
    omega
  · by_cases hex : ∃ j : Fin m, Disjoint (S j) y ∧ 2 ≤ (S j).card
    · obtain ⟨j, hjd, hjc⟩ := hex
      have hproper := proper_family_of_disjoint S y hinter (by omega) j hjd hjc
      let I := Finset.univ.filter (fun i : Fin m => Disjoint (S i) y ∧ 2 ≤ (S i).card)
      have hterm (i : Fin m) :
          (if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
            min y.card (S i).card + (if i ∈ I then 1 else 0) +
              (if Disjoint (S i) y then (S i).card - (y.card+1) else 0) := by
        by_cases hd : Disjoint (S i) y
        · simp only [ite_eq_left hd]
          by_cases hc : (S i).card ≤ y.card
          · rw [min_eq_right hc]
            omega
          · have hi : i ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd, by omega⟩
            rw [min_eq_left (by omega), if_pos hi]
            omega
        · simp only [ite_eq_right hd]
          omega
      have hs := truncated_sum_prefix_not_budget S C o t y hinter hgate hnot hcorrect hlow hfalse hproper
      have hr := Refund.refund_output_count S C o y hinter hcorrect
      have hsum :
          (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
            (∑ i : Fin m, min y.card (S i).card) + I.card +
            (∑ i : Fin m, if Disjoint (S i) y then (S i).card - (y.card+1) else 0) := by
        calc
          _ ≤ ∑ i : Fin m, (min y.card (S i).card + (if i ∈ I then 1 else 0) +
            (if Disjoint (S i) y then (S i).card - (y.card+1) else 0)) :=
              Finset.sum_le_sum fun i _ => hterm i
          _ = _ := by simp [Finset.sum_add_distrib]
      let R := Finset.univ.filter (fun g : Fin C.gates.length =>
          (∃ i : Fin m, ∀ p : Fin n,
            value C (fun v : Fin n => decide (v = p)) (n + g) = true ↔ p ∈ S i) ∧
          (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y →
            (value C (fun v : Fin n => decide (v ∈ y ∨ v = p))
              (n + g) = true ↔ p ∈ S i)))
      have hr' : I.card ≤ R.card := hr
      change _ ≤ C.gates.length + R.card + m
      omega

    · exact BoundedDisjoint.capped_disjoint_bound S C o t y hinter hgate hnot hcorrect hlow hfalse
        (by
          intro i hd
          have hc : (S i).card < 2 := by
            by_contra! hc
            exact hex ⟨i, hd, hc⟩
          omega)

end PEqualNP.Outside.L_meta_997.PrefixBudget
namespace PEqualNP.Outside.L_meta_997.UnionTrue

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.light
open PEqualNP.Outside.L_meta_997.Restriction

lemma covering_true_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y U : Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not → j.val = t)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < y.card → value C x (n + t) = true)
    (hcover : ∀ i : Fin m, Disjoint (S i) y → S i ⊆ U)
    (htrue : value C (fun v => decide (v ∈ U)) (n + t) = true) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + m := by
  classical
  by_cases hex : ∃ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not
  · obtain ⟨j, hj⟩ := hex
    have hejt := hnot j hj
    have ht : t < C.gates.length := hejt ▸ j.isLt
    have hop : (C.gates[t]).op = GateOp.not := by simpa [← hejt] using hj
    let D := PEqualNP.Outside.L_meta_997.Heavy.fixed C t true
    let E := restrict D U
    have hD : D.size = C.size := PEqualNP.Outside.L_meta_997.Heavy.fixed_size C t true
    have hE : E.size = C.size := (restrict_size D U).trans hD
    have hgoodD := PEqualNP.Outside.L_meta_997.Heavy.fixed_good C t true hgate hnot
    have hgoodE := restrict_good D U hgoodD
    have hbelow (x : Fin n → Bool) : value C (mask U x) (n + t) = true := by
      by_contra h
      have hf : value C (mask U x) (n + t) = false := by simpa using h
      have hle : ∀ p, mask U x p = true → decide (p ∈ U) = true := by
        intro p hp
        by_cases hu : p ∈ U
        · simp [hu]
        · simp [mask, hu] at hp
      have hc := PEqualNP.Outside.L_meta_997.Heavy.not_false_above C t hgate hnot ht hop
        (mask U x) (fun p => decide (p ∈ U)) hle hf
      change value C (fun p => decide (p ∈ U)) (n + t) = false at hc
      rw [htrue] at hc
      exact Bool.false_ne_true hc.symm
    have hcorrectE (i : Fin m) (hi : Disjoint (S i) y) (x : Fin n → Bool) :
        value E x (wire D U (o i)) = decide (∃ p ∈ S i, x p = true) := by
      rw [restrict_value]
      have he := PEqualNP.Outside.L_meta_997.Heavy.fixed_eq C t true (mask U x) (hbelow x) (o i)
      change value D (mask U x) (o i) = value C (mask U x) (o i) at he
      rw [he, hcorrect]
      apply Bool.decide_congr
      constructor
      · rintro ⟨p, hp, hx⟩
        exact ⟨p, hp, by simpa [mask, hcover i hi hp] using hx⟩
      · rintro ⟨p, hp, hx⟩
        exact ⟨p, hp, by simpa [mask, hcover i hi hp] using hx⟩
    have hcorrectD (i : Fin m) (x : Fin n → Bool)
        (hx : (Finset.univ.filter (fun v => x v = true)).card < y.card) :
        value D x (o i) = decide (∃ p ∈ S i, x p = true) := by
      have he := PEqualNP.Outside.L_meta_997.Heavy.fixed_eq C t true x (hlow x hx) (o i)
      change value D x (o i) = value C x (o i) at he
      rw [he, hcorrect]
    let G := fun i : Fin m => if Disjoint (S i) y then charge E (S i) else charge D (S i)
    have hper (i : Fin m) :
        (if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤ (G i).card + 1 := by
      by_cases hi : Disjoint (S i) y
      · have hc : (S i).card ≤ n + 1 := by
          have h := Finset.card_le_univ (S i)
          simp only [Fintype.card_fin] at h
          omega
        have h := light_bound E hgoodE (S i) (wire D U (o i)) (n + 1)
          (fun x _ => hcorrectE i hi x)
        simpa only [G, ite_eq_left hi, min_eq_right hc] using h
      · simpa only [G, ite_eq_right hi] using light_bound D hgoodD (S i) (o i) y.card (hcorrectD i)
    have hrange (i : Fin m) (w : ℕ) (hw : w ∈ G i) : n ≤ w ∧ w < n + C.size := by
      by_cases hi : Disjoint (S i) y
      · have hw' : w ∈ charge E (S i) := by simpa only [G, ite_eq_left hi] using hw
        have h := ((mem_charge E (S i) w).mp hw').1
        simpa only [hE] using h
      · have hw' : w ∈ charge D (S i) := by simpa only [G, ite_eq_right hi] using hw
        have h := ((mem_charge D (S i) w).mp hw').1
        simpa only [hD] using h
    have hsub (i : Fin m) (w : ℕ) (hw : w ∈ G i) : singleSupp E w ⊆ S i := by
      by_cases hi : Disjoint (S i) y
      · have hw' : w ∈ charge E (S i) := by simpa only [G, ite_eq_left hi] using hw
        exact ((mem_charge E (S i) w).mp hw').2.1
      · have hw' : w ∈ charge D (S i) := by simpa only [G, ite_eq_right hi] using hw
        exact (restrict_supp_subset D U hgoodD w).trans ((mem_charge D (S i) w).mp hw').2.1
    have hdisj : ((Finset.univ : Finset (Fin m)) : Set (Fin m)).PairwiseDisjoint G := by
      intro i _ j _ hij
      apply Finset.disjoint_left.mpr
      intro w hi hj
      by_cases hdi : Disjoint (S i) y
      · have hi' : w ∈ charge E (S i) := by simpa only [G, ite_eq_left hdi] using hi
        have hc := ((mem_charge E (S i) w).mp hi').2.2
        have hs := Finset.card_le_card (Finset.subset_inter (hsub i w hi) (hsub j w hj))
        have hh := hinter i j hij
        omega
      · by_cases hdj : Disjoint (S j) y
        · have hj' : w ∈ charge E (S j) := by simpa only [G, ite_eq_left hdj] using hj
          have hc := ((mem_charge E (S j) w).mp hj').2.2
          have hs := Finset.card_le_card (Finset.subset_inter (hsub i w hi) (hsub j w hj))
          have hh := hinter i j hij
          omega
        · have hi' : w ∈ charge D (S i) := by simpa only [G, ite_eq_right hdi] using hi
          have hj' : w ∈ charge D (S j) := by simpa only [G, ite_eq_right hdj] using hj
          have hsi := ((mem_charge D (S i) w).mp hi').2
          have hsj := ((mem_charge D (S j) w).mp hj').2
          have hs := Finset.card_le_card (Finset.subset_inter hsi.1 hsj.1)
          have hh := hinter i j hij
          omega
    have hsum : (∑ i : Fin m, (G i).card) ≤ C.gates.length := by
      rw [← Finset.card_biUnion hdisj]
      have hs : Finset.univ.biUnion G ⊆ Finset.Ico n (n + C.size) := by
        intro w hw
        obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
        exact Finset.mem_Ico.mpr (hrange i w hi)
      have h := Finset.card_le_card hs
      simpa only [Nat.card_Ico, Nat.add_sub_cancel_left, Circuit.size] using h
    calc
      _ ≤ ∑ i : Fin m, ((G i).card + 1) := Finset.sum_le_sum fun i _ => hper i
      _ = (∑ i : Fin m, (G i).card) + m := by simp [Finset.sum_add_distrib]
      _ ≤ C.gates.length + m := Nat.add_le_add_right hsum m
  · have hmono : ∀ g ∈ C.gates,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hgate g hg
      refine ⟨?_, hlen⟩
      rcases hop with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
        exact False.elim (hex ⟨⟨j, hj⟩, h⟩)
    exact monotone_mixed_bound S C o y hinter hmono hcorrect

def heavyUnion {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n)) : Finset (Fin n) :=
  (Finset.univ.filter (fun i : Fin m => Disjoint (S i) y)).biUnion S

lemma union_true_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not → j.val = t)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < y.card → value C x (n + t) = true)
    (hfalse : value C (fun v => decide (v ∈ y)) (n + t) = false)
    (htrue : value C (fun v => decide (v ∈ heavyUnion S y)) (n + t) = true) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + m := by
  apply covering_true_bound S C o t y (heavyUnion S y) hinter hgate hnot hcorrect hlow
  · intro i hi p hp
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, hp⟩
  · exact htrue

end PEqualNP.Outside.L_meta_997.UnionTrue

namespace PEqualNP.Outside.L_meta_997.SmallDimension

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Heavy

lemma pair_budget {n : ℕ} (A B Y : Finset (Fin n))
    (hAY : Disjoint A Y) (hBY : Disjoint B Y) (hAB : (A ∩ B).card ≤ 1) :
    A.card + B.card + Y.card ≤ n+1 := by
  have hd : Disjoint (A ∪ B) Y := Finset.disjoint_union_left.mpr ⟨hAY, hBY⟩
  have hc := Finset.card_le_card (Finset.subset_univ ((A ∪ B) ∪ Y))
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  rw [Finset.card_union_of_disjoint hd] at hc
  have hi := Finset.card_union_add_card_inter A B
  omega

lemma triple_budget {n : ℕ} (A B D Y : Finset (Fin n))
    (hAY : Disjoint A Y) (hBY : Disjoint B Y) (hDY : Disjoint D Y)
    (hAB : (A ∩ B).card ≤ 1) (hAD : (A ∩ D).card ≤ 1) (hBD : (B ∩ D).card ≤ 1) :
    A.card + B.card + D.card + Y.card ≤ n+3 := by
  have hd : Disjoint ((A ∪ B) ∪ D) Y :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hAY, hBY⟩, hDY⟩
  have hc := Finset.card_le_card (Finset.subset_univ (((A ∪ B) ∪ D) ∪ Y))
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  rw [Finset.card_union_of_disjoint hd] at hc
  have hi := Finset.card_union_add_card_inter A B
  have hj := Finset.card_union_add_card_inter (A ∪ B) D
  have hs : (A ∪ B) ∩ D ⊆ (A ∩ D) ∪ (B ∩ D) := by
    intro p hp
    obtain ⟨hpAB, hpD⟩ := Finset.mem_inter.mp hp
    rcases Finset.mem_union.mp hpAB with hpA | hpB
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hpA, hpD⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hpB, hpD⟩)
  have hk := Finset.card_le_card hs
  have hl := Finset.card_union_le (A ∩ D) (B ∩ D)
  omega

lemma excess_of_two {n m : ℕ} (S : Fin m → Finset (Fin n)) (y : Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hdim : n ≤ 4*y.card+1) (a b : Fin m) (hab : a ≠ b)
    (had : Disjoint (S a) y) (hbd : Disjoint (S b) y)
    (hac : y.card+2 ≤ (S a).card) (hbc : y.card+2 ≤ (S b).card) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card - (y.card+1) else 0) ≤ y.card := by
  classical
  let f := fun i : Fin m => if Disjoint (S i) y then (S i).card - (y.card+1) else 0
  have hzero (i : Fin m) (hia : i ≠ a) (hib : i ≠ b) : f i = 0 := by
    by_cases hd : Disjoint (S i) y
    · have hcap : (S i).card ≤ y.card+1 := by
        have ht := triple_budget (S a) (S b) (S i) y had hbd hd
          (hinter a b hab) (hinter a i (Ne.symm hia)) (hinter b i (Ne.symm hib))
        omega
      simp [f, hd, Nat.sub_eq_zero_of_le hcap]
    · simp [f, hd]
  have hsum : (∑ i : Fin m, f i) = f a + f b := by
    have h := Finset.sum_subset (Finset.subset_univ ({a,b} : Finset (Fin m)))
      (fun i _ hi => hzero i (by simpa using fun hia => hi (by simp [hia]))
        (by simpa using fun hib => hi (by simp [hib])))
    change (∑ i ∈ ({a,b} : Finset (Fin m)), f i) = ∑ i : Fin m, f i at h
    rw [← h]
    simp [hab]
  have hp := pair_budget (S a) (S b) y had hbd (hinter a b hab)
  change (∑ i : Fin m, f i) ≤ y.card
  rw [hsum]
  simp only [f, ite_eq_left had, ite_eq_left hbd]
  omega

lemma dimension_window_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → (i : ℕ) = t)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card →
        value C x (n+t) = true)
    (hfalse : value C (fun v : Fin n => decide (v ∈ y)) (n+t) = false)
    (hdim : n ≤ 4*y.card+1) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length =>
        (∃ i : Fin m, ∀ p : Fin n,
          value C (fun v : Fin n => decide (v = p)) (n + g) = true ↔ p ∈ S i) ∧
        (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y →
          (value C (fun v : Fin n => decide (v ∈ y ∨ v = p))
            (n + g) = true ↔ p ∈ S i)))).card + m := by
  classical
  by_cases hcap : ∀ i : Fin m, Disjoint (S i) y → (S i).card ≤ y.card+1
  · exact BoundedDisjoint.capped_disjoint_bound S C o t y hinter hgate hnot hcorrect hlow hfalse hcap
  push_neg at hcap
  obtain ⟨a, had, hac⟩ := hcap
  by_cases hone : ∀ i : Fin m, i ≠ a → Disjoint (S i) y → (S i).card ≤ y.card+1
  · exact OneOversized.one_oversized_bound S C o t y hinter hgate hnot hcorrect hlow hfalse ⟨a, hone⟩
  push_neg at hone
  obtain ⟨b, hba, hbd, hbc⟩ := hone
  apply PrefixBudget.total_excess_not_bound S C o t y hinter hgate hnot hcorrect hlow hfalse
  exact excess_of_two S y hinter hdim a b (Ne.symm hba) had hbd (by omega) (by omega)

lemma inputs_thirteen_bound {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n))
    (hinter : ∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hgate : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → (i : ℕ) = t)
    (hcorrect : ∀ (i : Fin m) (x : Fin n → Bool),
      value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hlow : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v : Fin n => x v = true)).card < y.card →
        value C x (n+t) = true)
    (hfalse : value C (fun v : Fin n => decide (v ∈ y)) (n+t) = false)
    (hn : n ≤ 13) :
    (∑ i : Fin m, if Disjoint (S i) y then (S i).card else min y.card (S i).card) ≤
      C.gates.length + (Finset.univ.filter (fun g : Fin C.gates.length =>
        (∃ i : Fin m, ∀ p : Fin n,
          value C (fun v : Fin n => decide (v = p)) (n + g) = true ↔ p ∈ S i) ∧
        (∃ i : Fin m, Disjoint (S i) y ∧ ∀ p : Fin n, p ∉ y →
          (value C (fun v : Fin n => decide (v ∈ y ∨ v = p))
            (n + g) = true ↔ p ∈ S i)))).card + m := by
  by_cases hy : y.card ≤ 2
  · have h := light.small_window_bound S C o t y hinter hgate hnot hcorrect hfalse hy
    omega
  · exact dimension_window_bound S C o t y hinter hgate hnot hcorrect hlow hfalse (by omega)

end PEqualNP.Outside.L_meta_997.SmallDimension
namespace PEqualNP.Outside.L_meta_997.LightMatching

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.light

lemma boundary_subset_bound {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (o k : ℕ) (hk : 1 < k)
    (hcorrect : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value C x o = decide (∃ p ∈ S, x p = true))
    (B : Finset ℕ) (hd : Disjoint B (charge C S))
    (hcut : ∀ (p : Fin n) (z : Fin n → Bool),
      (∀ w ∈ B, value C (fun v => decide (v = p)) w = true → value C z w = true) →
      value C (fun v => decide (v = p)) o = true → value C z o = true)
    (X : Finset (Fin n)) (hXS : X ⊆ S) :
    min k X.card ≤ (B.filter (fun w => ∃ p ∈ X, p ∈ singleSupp C w)).card := by
  classical
  let N := B.filter (fun w => ∃ p ∈ X, p ∈ singleSupp C w)
  by_contra! hsmall
  have hsmallS : N.card < X.card := hsmall.trans_le (min_le_right ..)
  have hsmallK : N.card < k := hsmall.trans_le (min_le_left ..)
  let clean (w : ℕ) : Finset (Fin n) :=
    if singleSupp C w ⊆ S then singleSupp C w else ∅
  have hclean : ∀ w ∈ N, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : singleSupp C w ⊆ S
    · simp only [clean, ite_eq_left hs]
      by_contra! hlarge
      exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp hw).1
        ((mem_charge C S w).mpr ⟨singleSupp_gate C w (by omega), hs, by omega⟩)
    · simp [clean, hs]
  have hcover : (N.biUnion clean).card < X.card := by
    have h := Finset.card_biUnion_le_card_mul N clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨p, hpX, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  have hpS := hXS hpX
  let Dn := N.filter (fun w => ¬ singleSupp C w ⊆ S)
  have hout (w : {w // w ∈ Dn}) : ∃ q : Fin n, q ∈ singleSupp C w.val ∧ q ∉ S := by
    have hns := (Finset.mem_filter.mp w.property).2
    simpa only [Finset.not_subset] using hns
  choose qs hqs using hout
  let V : Finset (Fin n) := Dn.attach.image qs
  let z : Fin n → Bool := fun v => decide (v ∈ V)
  have hVcard : V.card < k := by
    have hi := Finset.card_image_le (s := Dn.attach) (f := qs)
    have hf := Finset.card_filter_le N (fun w => ¬ singleSupp C w ⊆ S)
    simp only [Finset.card_attach] at hi
    change V.card ≤ Dn.card at hi
    change Dn.card ≤ N.card at hf
    omega
  have hweight : (Finset.univ.filter (fun v => z v = true)).card < k := by
    simpa [z] using hVcard
  have hVS : ∀ q ∈ V, q ∉ S := by
    intro q hq
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hq
    exact (hqs w).2
  have hzfalse : value C z o = false := by
    rw [hcorrect z hweight]
    simp only [decide_eq_false_iff_not, not_exists]
    intro q hq
    exact hVS q (by simpa [z] using hq.2) hq.1
  have hfire : value C (fun v => decide (v = p)) o = true := by
    rw [hcorrect]
    · simp [hpS]
    · have hsingle : Finset.univ.filter (fun v : Fin n => decide (v = p) = true) = {p} := by
        ext v
        simp
      rw [hsingle, Finset.card_singleton]
      exact hk
  have hztrue : value C z o = true := by
    apply hcut p z _ hfire
    intro w hw hx
    have hwN : w ∈ N := Finset.mem_filter.mpr ⟨hw, p, hpX, (mem_singleSupp C w p).mpr hx⟩
    by_cases hs : singleSupp C w ⊆ S
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hwN, by simp only [clean, ite_eq_left hs]; exact (mem_singleSupp C w p).mpr hx⟩))
    · let d : {w // w ∈ Dn} := ⟨w, Finset.mem_filter.mpr ⟨hwN, hs⟩⟩
      apply value_mono C hG (fun v => decide (v = qs d)) z _ w
        ((mem_singleSupp C w (qs d)).mp (hqs d).1)
      intro v hv
      have hv' : v = qs d := by simpa using hv
      subst v
      simp only [z, decide_eq_true_eq]
      exact Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩
  rw [hzfalse] at hztrue
  exact Bool.false_ne_true hztrue

lemma boundary_matching {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (o k : ℕ) (hk : 1 < k)
    (hcorrect : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value C x o = decide (∃ p ∈ S, x p = true))
    (B : Finset ℕ) (hd : Disjoint B (charge C S))
    (hcut : ∀ (p : Fin n) (z : Fin n → Bool),
      (∀ w ∈ B, value C (fun v => decide (v = p)) w = true → value C z w = true) →
      value C (fun v => decide (v = p)) o = true → value C z o = true)
    (T : Finset (Fin n)) (hTS : T ⊆ S) (hTk : T.card ≤ k) :
    ∃ f : {p // p ∈ T} → ℕ, Function.Injective f ∧
      ∀ p, f p ∈ B ∧ p.val ∈ singleSupp C (f p) := by
  classical
  let candidates : {p // p ∈ T} → Finset ℕ := fun p => B.filter (fun w => p.val ∈ singleSupp C w)
  have hHall : ∀ J : Finset {p // p ∈ T}, J.card ≤ (J.biUnion candidates).card := by
    intro J
    let X : Finset (Fin n) := J.image Subtype.val
    have hXT : X ⊆ T := by
      intro p hp
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
      exact q.property
    have hXk : X.card ≤ k := (Finset.card_le_card hXT).trans hTk
    have hXcard : X.card = J.card := Finset.card_image_of_injective J Subtype.val_injective
    have hN : B.filter (fun w => ∃ p ∈ X, p ∈ singleSupp C w) = J.biUnion candidates := by
      ext w
      simp only [candidates, Finset.mem_filter, Finset.mem_biUnion]
      constructor
      · rintro ⟨hwB, p, hpX, hpw⟩
        obtain ⟨q, hqJ, rfl⟩ := Finset.mem_image.mp hpX
        exact ⟨q, hqJ, hwB, hpw⟩
      · rintro ⟨q, hqJ, hwB, hqw⟩
        exact ⟨hwB, q.val, Finset.mem_image.mpr ⟨q, hqJ, rfl⟩, hqw⟩
    have h := boundary_subset_bound C hG S o k hk hcorrect B hd hcut X (hXT.trans hTS)
    rw [min_eq_right hXk, hN, hXcard] at h
    exact h
  obtain ⟨f, hf, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' candidates).mp hHall
  exact ⟨f, hf, fun p => Finset.mem_filter.mp (hmem p)⟩

end PEqualNP.Outside.L_meta_997.LightMatching
namespace PEqualNP.Outside.L_meta_997.EligibleLight

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.light

lemma boundary_subset_bound {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (o k : ℕ)
    (hcorrect : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value C x o = decide (∃ p ∈ S, x p = true))
    (B : Finset ℕ) (hd : Disjoint B (charge C S))
    (E : Fin n → ℕ → Prop) [DecidableRel E]
    (hE : ∀ p w, E p w → p ∈ singleSupp C w)
    (hcut : ∀ (p : Fin n), p ∈ S → ∀ z : Fin n → Bool,
      (∀ w ∈ B, E p w → value C z w = true) → value C z o = true)
    (X : Finset (Fin n)) (hXS : X ⊆ S) :
    min k X.card ≤ (B.filter (fun w => ∃ p ∈ X, E p w)).card := by
  classical
  let N := B.filter (fun w => ∃ p ∈ X, E p w)
  by_contra! hsmall
  have hsmallS : N.card < X.card := hsmall.trans_le (min_le_right ..)
  have hsmallK : N.card < k := hsmall.trans_le (min_le_left ..)
  let clean (w : ℕ) : Finset (Fin n) :=
    if singleSupp C w ⊆ S then singleSupp C w else ∅
  have hclean : ∀ w ∈ N, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : singleSupp C w ⊆ S
    · simp only [clean, ite_eq_left hs]
      by_contra! hlarge
      exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp hw).1
        ((mem_charge C S w).mpr ⟨singleSupp_gate C w (by omega), hs, by omega⟩)
    · simp [clean, hs]
  have hcover : (N.biUnion clean).card < X.card := by
    have h := Finset.card_biUnion_le_card_mul N clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨p, hpX, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  have hpS := hXS hpX
  let Dn := N.filter (fun w => ¬ singleSupp C w ⊆ S)
  have hout (w : {w // w ∈ Dn}) : ∃ q : Fin n, q ∈ singleSupp C w.val ∧ q ∉ S := by
    have hns := (Finset.mem_filter.mp w.property).2
    simpa only [Finset.not_subset] using hns
  choose qs hqs using hout
  let V : Finset (Fin n) := Dn.attach.image qs
  let z : Fin n → Bool := fun v => decide (v ∈ V)
  have hVcard : V.card < k := by
    have hi := Finset.card_image_le (s := Dn.attach) (f := qs)
    have hf := Finset.card_filter_le N (fun w => ¬ singleSupp C w ⊆ S)
    simp only [Finset.card_attach] at hi
    change V.card ≤ Dn.card at hi
    change Dn.card ≤ N.card at hf
    omega
  have hweight : (Finset.univ.filter (fun v => z v = true)).card < k := by
    simpa [z] using hVcard
  have hVS : ∀ q ∈ V, q ∉ S := by
    intro q hq
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hq
    exact (hqs w).2
  have hzfalse : value C z o = false := by
    rw [hcorrect z hweight]
    simp only [decide_eq_false_iff_not, not_exists]
    intro q hq
    exact hVS q (by simpa [z] using hq.2) hq.1
  have hztrue : value C z o = true := by
    apply hcut p hpS z
    intro w hw hx
    have hwN : w ∈ N := Finset.mem_filter.mpr ⟨hw, p, hpX, hx⟩
    by_cases hs : singleSupp C w ⊆ S
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hwN, by simp only [clean, ite_eq_left hs]; exact hE p w hx⟩))
    · let d : {w // w ∈ Dn} := ⟨w, Finset.mem_filter.mpr ⟨hwN, hs⟩⟩
      apply value_mono C hG (fun v => decide (v = qs d)) z _ w
        ((mem_singleSupp C w (qs d)).mp (hqs d).1)
      intro v hv
      have hv' : v = qs d := by simpa using hv
      subst v
      simp only [z, decide_eq_true_eq]
      exact Finset.mem_image.mpr ⟨d, Finset.mem_attach _ _, rfl⟩
  rw [hzfalse] at hztrue
  exact Bool.false_ne_true hztrue

lemma boundary_matching {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (o k : ℕ)
    (hcorrect : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value C x o = decide (∃ p ∈ S, x p = true))
    (B : Finset ℕ) (hd : Disjoint B (charge C S))
    (E : Fin n → ℕ → Prop) [DecidableRel E]
    (hE : ∀ p w, E p w → p ∈ singleSupp C w)
    (hcut : ∀ (p : Fin n), p ∈ S → ∀ z : Fin n → Bool,
      (∀ w ∈ B, E p w → value C z w = true) → value C z o = true)
    (T : Finset (Fin n)) (hTS : T ⊆ S) (hTk : T.card ≤ k) :
    ∃ f : {p // p ∈ T} → ℕ, Function.Injective f ∧
      ∀ p, f p ∈ B ∧ E p.val (f p) := by
  classical
  let candidates : {p // p ∈ T} → Finset ℕ := fun p => B.filter (fun w => E p.val w)
  have hHall : ∀ J : Finset {p // p ∈ T}, J.card ≤ (J.biUnion candidates).card := by
    intro J
    let X : Finset (Fin n) := J.image Subtype.val
    have hXT : X ⊆ T := by
      intro p hp
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
      exact q.property
    have hXk : X.card ≤ k := (Finset.card_le_card hXT).trans hTk
    have hXcard : X.card = J.card := Finset.card_image_of_injective J Subtype.val_injective
    have hN : B.filter (fun w => ∃ p ∈ X, E p w) = J.biUnion candidates := by
      ext w
      simp only [candidates, Finset.mem_filter, Finset.mem_biUnion]
      constructor
      · rintro ⟨hwB, p, hpX, hpw⟩
        obtain ⟨q, hqJ, rfl⟩ := Finset.mem_image.mp hpX
        exact ⟨q, hqJ, hwB, hpw⟩
      · rintro ⟨q, hqJ, hwB, hqw⟩
        exact ⟨hwB, q.val, Finset.mem_image.mpr ⟨q, hqJ, rfl⟩, hqw⟩
    have h := boundary_subset_bound C hG S o k hcorrect B hd E hE hcut X (hXT.trans hTS)
    rw [min_eq_right hXk, hN, hXcard] at h
    exact h
  obtain ⟨f, hf, hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' candidates).mp hHall
  exact ⟨f, hf, fun p => Finset.mem_filter.mp (hmem p)⟩

end PEqualNP.Outside.L_meta_997.EligibleLight

namespace PEqualNP.Outside.L_meta_997.ActiveLight

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.light

def active {n : ℕ} (C : Circuit) (parents : ℕ → Finset ℕ) (p : Fin n) (o w : ℕ) : Prop :=
  value C (fun v => decide (v = p)) o = true ∧
    Relation.ReflTransGen (fun a b => b ∈ parents a ∧ value C (fun v => decide (v = p)) b = true) o w

lemma active_value {n : ℕ} (C : Circuit) (parents : ℕ → Finset ℕ) (p : Fin n) (o w : ℕ)
    (h : active C parents p o w) : value C (fun v => decide (v = p)) w = true := by
  obtain ⟨h0, hpath⟩ := h
  induction hpath with
  | refl => exact h0
  | tail _ hlast _ => exact hlast.2

lemma active_tail {n : ℕ} (C : Circuit) (parents : ℕ → Finset ℕ) (p : Fin n) (o w r : ℕ)
    (h : active C parents p o w) (hr : r ∈ parents w)
    (hrt : value C (fun v => decide (v = p)) r = true) : active C parents p o r :=
  ⟨h.1, Relation.ReflTransGen.tail h.2 ⟨hr, hrt⟩⟩

lemma active_reachable {n : ℕ} (C : Circuit) (parents : ℕ → Finset ℕ) (p : Fin n) (o w : ℕ)
    (h : active C parents p o w) : Relation.ReflTransGen (fun a b => b ∈ parents a) o w := by
  obtain ⟨_, hpath⟩ := h
  induction hpath with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hlast ih => exact Relation.ReflTransGen.tail ih hlast.1

lemma reachable_le (parents : ℕ → Finset ℕ)
    (hdesc : ∀ w r, r ∈ parents w → r < w) (o w : ℕ)
    (h : Relation.ReflTransGen (fun a b => b ∈ parents a) o w) : w ≤ o := by
  induction h with
  | refl => exact le_rfl
  | tail _ hlast ih => exact (hdesc _ _ hlast).le.trans ih

noncomputable def frontier (parents : ℕ → Finset ℕ) (H : Finset ℕ) (o : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Iic o).filter (fun w => Relation.ReflTransGen (fun a b => b ∈ parents a) o w ∧ w ∉ H)

lemma mem_frontier (parents : ℕ → Finset ℕ) (H : Finset ℕ) (o w : ℕ) :
    w ∈ frontier parents H o ↔ w ≤ o ∧
      Relation.ReflTransGen (fun a b => b ∈ parents a) o w ∧ w ∉ H := by
  classical
  simp [frontier]

lemma frontier_cut {n : ℕ} (C : Circuit) (parents : ℕ → Finset ℕ) (H : Finset ℕ)
    (hdesc : ∀ w r, r ∈ parents w → r < w)
    (hstep : ∀ w ∈ H, ∀ (p : Fin n) (z : Fin n → Bool),
      (∀ r ∈ parents w, value C (fun v => decide (v = p)) r = true → value C z r = true) →
      value C (fun v => decide (v = p)) w = true → value C z w = true)
    (o : ℕ) (p : Fin n) (z : Fin n → Bool)
    (hfire : value C (fun v => decide (v = p)) o = true)
    (hforce : ∀ w ∈ frontier parents H o, active C parents p o w → value C z w = true) :
    value C z o = true := by
  have hprove : ∀ w : ℕ, active C parents p o w → value C z w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro ha
      by_cases hw : w ∈ H
      · apply hstep w hw p z _ (active_value C parents p o w ha)
        intro r hr hrt
        exact ih r (hdesc w r hr) (active_tail C parents p o w r ha hr hrt)
      · have hre := active_reachable C parents p o w ha
        exact hforce w ((mem_frontier parents H o w).mpr
          ⟨reachable_le parents hdesc o w hre, hre, hw⟩) ha
  exact hprove o ⟨hfire, Relation.ReflTransGen.refl⟩

lemma active_matching {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (S : Finset (Fin n)) (o k : ℕ) (hk : 1 < k)
    (hcorrect : ∀ x : Fin n → Bool,
      (Finset.univ.filter (fun v => x v = true)).card < k →
      value C x o = decide (∃ p ∈ S, x p = true))
    (T : Finset (Fin n)) (hTS : T ⊆ S) (hTk : T.card ≤ k) :
    ∃ (parents : ℕ → Finset ℕ) (B : Finset ℕ) (f : {p // p ∈ T} → ℕ),
      Function.Injective f ∧
      (∀ p, f p ∈ B ∧ active C parents p.val o (f p)) ∧
      Disjoint B (charge C S) ∧ (∀ w ∈ B, parents w = ∅) ∧
      (∀ w ∈ charge C S, (parents w).card ≤ (if w ∈ LightSmart.smartCharge C S then 2 else 1)) ∧
      (∀ w r, r ∈ parents w → w ∈ charge C S ∧ r < w ∧
        r ∈ (HeavyOr.readGate C n w).inputs ∧ (singleSupp (n := n) C r).Nonempty) := by
  classical
  obtain ⟨parents, U, _, _, hstep, _, hedges⟩ := LightSmart.selected_count C hG S o k hcorrect
  let H := charge C S
  let B := frontier parents H o
  have hdesc : ∀ w r, r ∈ parents w → r < w := fun w r hr => (hedges w r hr).2.1
  have hd : Disjoint B H := by
    apply Finset.disjoint_left.mpr
    intro w hw hH
    exact ((mem_frontier parents H o w).mp hw).2.2 hH
  have hE : ∀ (p : Fin n) (w : ℕ), active C parents p o w → p ∈ singleSupp C w :=
    fun p w h => (mem_singleSupp C w p).mpr (active_value C parents p o w h)
  have hcut : ∀ (p : Fin n), p ∈ S → ∀ z : Fin n → Bool,
      (∀ w ∈ B, active C parents p o w → value C z w = true) → value C z o = true := by
    intro p hp z hz
    apply frontier_cut C parents H hdesc (fun w hw => (hstep w hw).2.2) o p z ?_ hz
    rw [hcorrect]
    · simp [hp]
    · have hsingle : Finset.univ.filter (fun v : Fin n => decide (v = p) = true) = {p} := by
        ext v
        simp
      rw [hsingle, Finset.card_singleton]
      exact hk
  obtain ⟨f, hf, hmatch⟩ := EligibleLight.boundary_matching C hG S o k hcorrect B hd
    (fun p w => active C parents p o w) hE hcut T hTS hTk
  refine ⟨parents, B, f, hf, hmatch, hd, ?_, ?_, hedges⟩
  · intro w hw
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    exact ((mem_frontier parents H o w).mp hw).2.2 (hedges w r hr).1
  · intro w hw
    exact (hstep w hw).1

end PEqualNP.Outside.L_meta_997.ActiveLight
namespace PEqualNP.Outside.L_meta_997.HeavyActive

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Heavy PEqualNP.Outside.L_meta_997.HeavyOr PEqualNP.Outside.L_meta_997.HeavySelected

lemma active_paths {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y S : Finset (Fin n)) (o : ℕ) (hYS : Disjoint Y S)
    (hso : sound C S o)
    (hfire : ∀ p ∈ S, value C (fun v => decide (v ∈ Y ∨ v=p)) o = true) :
    ∃ P : ℕ → Finset ℕ,
      (∀ p ∈ S, Relation.ReflTransGen
        (fun a b => b ∈ P a ∧ p ∈ supp C Y b) o p.val) ∧
      (∀ w r, r ∈ P w → (n≤w ∧ w<n+C.size) ∧ sound C S w ∧
        r<w ∧ sound C S r ∧ r ∈ (readGate C n w).inputs ∧
        (supp C Y r).Nonempty) ∧
      (∀ w, (n≤w ∧ w<n+C.size) → sound C S w →
        (P w).card ≤ (if w ∈ charged C Y S then 2 else 1)) := by
  classical
  obtain ⟨P,U,_,_,hStep,_,hEdge⟩ := selected_count C hG Y S o hYS hso hfire
  refine ⟨P,?_,hEdge,fun w hw hs => (hStep w hw hs).1⟩
  have hPath : ∀ w, sound C S w → ∀ p ∈ supp C Y w,
      Relation.ReflTransGen (fun a b => b ∈ P a ∧ p ∈ supp C Y b) w p.val := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hs p hp
      by_cases hn : w<n
      · let q : Fin n := ⟨w,hn⟩
        have hqS : q ∈ S := by
          have hv : value C (fun v : Fin n => decide (v=q)) w=true := by
            change value C (fun v : Fin n => decide (v=q)) q=true
            simp only [input_value,decide_true]
          obtain ⟨v,hvS,hv⟩ := hs _ hv
          have hvq : v=q := of_decide_eq_true hv
          simpa only [hvq] using hvS
        have hqY : q ∉ Y := fun hq => Finset.disjoint_left.mp hYS hq hqS
        have hqp : q=p := by
          have hv := (mem_supp C Y w p).mp hp
          change value C (fun v : Fin n => decide (v∈Y ∨ v=p)) q=true at hv
          simpa only [input_value,decide_eq_true_eq,hqY,false_or] using hv
        have hwp : w=p.val := congrArg Fin.val hqp
        rw [hwp]
      · have hupper : w<n+C.size := by
          by_contra! hout
          have hv := (mem_supp C Y w p).mp hp
          rw [missing_value C _ w hout] at hv
          exact Bool.false_ne_true hv
        have hc := (hStep w ⟨by omega,hupper⟩ hs).2.2 hp
        obtain ⟨r,hr,hpr⟩ := Finset.mem_biUnion.mp hc
        have he := hEdge w r hr
        exact Relation.ReflTransGen.head ⟨hr,hpr⟩
          (ih r he.2.2.1 he.2.2.2.1 p hpr)
  intro p hp
  exact hPath o hso p ((mem_supp C Y o p).mpr (hfire p hp))

end PEqualNP.Outside.L_meta_997.HeavyActive

namespace PEqualNP.Outside.L_meta_997.HeavyExit

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_997.Heavy PEqualNP.Outside.L_meta_997.HeavyOr PEqualNP.Outside.L_meta_997.HeavySelected

lemma strict_parents {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y S : Finset (Fin n)) (w : ℕ) (P : Finset ℕ)
    (hc : w ∈ charged C Y S)
    (hP : ∀ r ∈ P, r ∈ (readGate C n w).inputs ∧ r<w)
    (hcov : supp C Y w ⊆ P.biUnion (supp C Y)) :
    P=(readGate C n w).inputs.toFinset.filter (· < w) ∧ P.card=2 := by
  classical
  obtain ⟨hwr,_,hop,hne,hstrict⟩ := (mem_charged C Y S w).mp hc
  let A := (readGate C n w).inputs.toFinset.filter (· < w)
  have hsub : P ⊆ A := by
    intro r hr
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hP r hr).1,(hP r hr).2⟩
  have hAcard : A.card ≤ 2 := by
    apply (Finset.card_filter_le _ _).trans
    apply (List.toFinset_card_le _).trans
    exact (hG (readGate C n w) (by
      rw [readGate_eq C n w hwr.1 hwr.2]
      exact List.getElem_mem _)).2
  have hPcard := Finset.card_le_card hsub
  have hPne : P.Nonempty := by
    obtain ⟨p,hp⟩ := hne
    obtain ⟨r,hr,_⟩ := Finset.mem_biUnion.mp (hcov hp)
    exact ⟨r,hr⟩
  have htwo : P.card=2 := by
    by_contra hn
    have hone : P.card=1 := by have := Finset.card_pos.mpr hPne; omega
    obtain ⟨r,hr⟩ := Finset.card_eq_one.mp hone
    have hrP : r ∈ P := by simp [hr]
    apply hstrict r (hP r hrP).1 (hP r hrP).2
    apply Finset.Subset.antisymm
    · intro p hp
      rw [or_supp C Y w hwr.1 hwr.2 hop]
      exact Finset.mem_biUnion.mpr ⟨r,hsub hrP,hp⟩
    · simpa [hr] using hcov
  exact ⟨Finset.eq_of_subset_of_card_le hsub (by change A.card ≤ P.card; omega),htwo⟩

lemma marker_exit {n : ℕ} (C D : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsize : D.size=C.size) (Y S : Finset (Fin n))
    (hmatch : ∀ w, (n≤w ∧ w<n+C.size) → sound C S w →
      (supp C Y w).Nonempty → readGate D n w=readGate C n w)
    (P : ℕ → Finset ℕ)
    (hcover : ∀ w, (n≤w ∧ w<n+C.size) → sound C S w →
      supp C Y w ⊆ (P w).biUnion (supp C Y))
    (hedge : ∀ w r, r ∈ P w → (n≤w ∧ w<n+C.size) ∧ sound C S w ∧
      r<w ∧ sound C S r ∧ r ∈ (readGate C n w).inputs ∧ (supp C Y r).Nonempty)
    (p : Fin n) (hpS : p ∉ S) (w : ℕ)
    (hwS : sound C S w) (hwne : (supp C Y w).Nonempty)
    (hwp : value D (fun v => decide (v=p)) w=true) :
    ∃ v, Relation.ReflTransGen
      (fun a b => b ∈ P a ∧ value D (fun q => decide (q=p)) b=true) w v ∧
      value D (fun q => decide (q=p)) v=true ∧
      (n≤v ∧ v<n+C.size) ∧ sound C S v ∧ (supp C Y v).Nonempty ∧
      (readGate C n v).op=GateOp.or ∧ v ∉ charged C Y S ∧
      (P v).Nonempty ∧ (∀ r ∈ P v, value D (fun q => decide (q=p)) r=false) ∧
      ∃ r ∈ (readGate C n v).inputs, r<v ∧
        value D (fun q => decide (q=p)) r=true ∧ r ∉ P v := by
  classical
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hex : ∃ r ∈ P w, value D (fun q => decide (q=p)) r=true
    · obtain ⟨r,hr,hrp⟩ := hex
      have he := hedge w r hr
      obtain ⟨v,hpath,hrest⟩ := ih r he.2.2.1 he.2.2.2.1 he.2.2.2.2.2 hrp
      exact ⟨v,Relation.ReflTransGen.head ⟨hr,hrp⟩ hpath,hrest⟩
    · have hfalse : ∀ r ∈ P w, value D (fun q => decide (q=p)) r=false := by
        intro r hr
        exact Bool.eq_false_iff.mpr (fun ht => hex ⟨r,hr,ht⟩)
      have hn : n≤w := by
        by_contra! hn
        let q : Fin n := ⟨w,hn⟩
        have hqS : q ∈ S := by
          have hq : value C (fun v : Fin n => decide (v=q)) w=true := by
            change value C (fun v : Fin n => decide (v=q)) q=true
            simp only [input_value,decide_true]
          obtain ⟨v,hvS,hv⟩ := hwS _ hq
          have hvq : v=q := of_decide_eq_true hv
          simpa only [hvq] using hvS
        change value D (fun v : Fin n => decide (v=p)) q=true at hwp
        have hqp : q=p := by simpa only [input_value,decide_eq_true_eq] using hwp
        exact hpS (hqp ▸ hqS)
      have hw : w<n+C.size := by
        by_contra! hout
        obtain ⟨q,hq⟩ := hwne
        have hv := (mem_supp C Y w q).mp hq
        rw [missing_value C _ w hout] at hv
        exact Bool.false_ne_true hv
      have hcov := hcover w ⟨hn,hw⟩ hwS
      have hPne : (P w).Nonempty := by
        obtain ⟨q,hq⟩ := hwne
        obtain ⟨r,hr,_⟩ := Finset.mem_biUnion.mp (hcov hq)
        exact ⟨r,hr⟩
      have hgate := hmatch w ⟨hn,hw⟩ hwS hwne
      have hDw : w<n+D.size := by omega
      have hformula := hwp
      rw [gate_formula D w hn hDw _,hgate] at hformula
      have hg := (hG (readGate C n w) (by
        rw [readGate_eq C n w hn hw]
        exact List.getElem_mem _)).1
      have hop : (readGate C n w).op=GateOp.or := by
        rcases hg with ha | ho
        · rw [ha] at hformula
          simp only [GateOp.eval,List.all_eq_true,id_eq] at hformula
          obtain ⟨r,hr⟩ := hPne
          have he := hedge w r hr
          have hh := hformula _ (List.mem_map.mpr ⟨r,he.2.2.2.2.1,rfl⟩)
          simp only [ite_eq_left he.2.2.1,hfalse r hr] at hh
          exact False.elim (Bool.false_ne_true hh)
        · exact ho
      have hDop : (readGate D n w).op=GateOp.or := by simpa only [hgate] using hop
      obtain ⟨r,hr,hrw,hrp⟩ := (or_true D w hn hDw hDop _).mp hwp
      rw [hgate] at hr
      have hrnot : r ∉ P w := by intro hrP; rw [hfalse r hrP] at hrp; exact Bool.false_ne_true hrp
      have hnc : w ∉ charged C Y S := by
        intro hc
        have heq := (strict_parents C hG Y S w (P w) hc
          (fun s hs => ⟨(hedge w s hs).2.2.2.2.1,(hedge w s hs).2.2.1⟩) hcov).1
        exact hrnot (by rw [heq]; exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr,hrw⟩)
      exact ⟨w,Relation.ReflTransGen.refl,hwp,⟨hn,hw⟩,hwS,hwne,hop,hnc,hPne,hfalse,
        r,hr,hrw,hrp,hrnot⟩

lemma fixed_match {n : ℕ} (C : Circuit) (t : ℕ) (Y : Finset (Fin n))
    (w : ℕ) (hwr : n≤w ∧ w<n+(fixed C t false).size)
    (hne : (supp (fixed C t false) Y w).Nonempty) :
    readGate (fixed C t true) n w=readGate (fixed C t false) n w := by
  have hb : w<n+C.size := by simpa only [fixed_size] using hwr.2
  have hneq : w≠n+t := by
    intro heq
    have ht : t<C.gates.length := by unfold Circuit.size at hb; omega
    obtain ⟨p,hp⟩ := hne
    have hv := (mem_supp (fixed C t false) Y w p).mp hp
    rw [heq,fixed_at C t false ht] at hv
    exact Bool.false_ne_true hv
  rw [readGate_fixed_other C n t w true hwr.1 hb hneq,
    readGate_fixed_other C n t w false hwr.1 hb hneq]

end PEqualNP.Outside.L_meta_997.HeavyExit

