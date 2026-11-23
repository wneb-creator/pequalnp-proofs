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

end PEqualNP.Outside.L_meta_997.Heavy

