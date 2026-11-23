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
        r<w ∧ sound C S r ∧ r ∈ (readGate C n w).inputs) := by
  classical
  let H := (Finset.Ico n (n+C.size)).filter (sound C S)
  have hbranch : ∀ w ∈ H, ∃ P : Finset ℕ,
      P.card ≤ (if w ∈ charged C Y S then 2 else 1) ∧
        (∀ r ∈ P, r<w ∧ sound C S r ∧ r ∈ (readGate C n w).inputs) ∧
          supp C Y w ⊆ P.biUnion (supp C Y) := by
    intro w hw
    have hg := Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
    obtain ⟨P,hP,hP',hp,hcover⟩ := branch_edges C hG Y S w hg.1 hg.2 (Finset.mem_filter.mp hw).2
    refine ⟨P,?_,hp,hcover⟩
    split_ifs with hc
    · exact hP
    · exact hP' hc
  let parents := fun w => if hw : w ∈ H then Classical.choose (hbranch w hw) else ∅
  have hpFull : ∀ w ∈ H,
      (parents w).card ≤ (if w ∈ charged C Y S then 2 else 1) ∧
        (∀ r ∈ parents w, r<w ∧ sound C S r ∧ r ∈ (readGate C n w).inputs) ∧
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

