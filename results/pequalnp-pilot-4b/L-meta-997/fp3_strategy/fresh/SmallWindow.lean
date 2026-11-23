import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_997.SmallBase

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
    · simp only [clean, if_pos hs]
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
    push_neg at hns
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
        ⟨w, hw, by simp only [clean, if_pos hs]; exact (mem_supp C Y w p).mpr hx⟩))
    · let d : {w // w ∈ Dn} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
      apply value_mono C hG (xs d) z _ w (hxs d).1
      intro v hv
      simp only [z, decide_eq_true_eq]
      exact Or.inr ⟨d, hv⟩
  rw [hzfalse] at hztrue
  exact Bool.false_ne_true hztrue

lemma meet {n : ℕ} (C : Circuit) (Yi Ti Tj : Finset (Fin n)) (w : ℕ) (hdi : Disjoint Yi Ti)
    (hsi : sound C Ti w) (hsj : sound C Tj w) (h2 : 2 ≤ (supp C Yi w).card)
    (hint : (Ti ∩ Tj).card ≤ 1) : ¬ Disjoint Yi Tj := by
  intro hdj
  have hsub : supp C Yi w ⊆ Ti ∩ Tj := by
    intro p hp
    have hv := (mem_supp C Yi w p).mp hp
    obtain ⟨q, hqT, hqv⟩ := hsi _ hv
    obtain ⟨r, hrT, hrv⟩ := hsj _ hv
    simp only [decide_eq_true_eq] at hqv hrv
    rcases hqv with hqv | hqv
    · exact absurd hqT (Finset.disjoint_left.mp hdi hqv)
    rcases hrv with hrv | hrv
    · exact absurd hrT (Finset.disjoint_left.mp hdj hrv)
    rw [hqv] at hqT
    rw [hrv] at hrT
    exact Finset.mem_inter.mpr ⟨hqT, hrT⟩
  have := Finset.card_le_card hsub
  omega

end PEqualNP.Outside.L_meta_997.SmallBase
namespace PEqualNP.Outside.L_meta_997.Window
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

lemma repl_eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ r ∈ g.inputs, f r = true → f' r = true) :
    g.op.eval (g.inputs.map f) = true → g.op.eval (g.inputs.map f') = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hx r hr => h r hr (hx r hr)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    exact fun ⟨r, hr, hx⟩ => ⟨r, hr, h r hr hx⟩

lemma repl_eval_congr (g : Gate) (f f' : ℕ → Bool) (h : ∀ r ∈ g.inputs, f r = f' r) :
    g.op.eval (g.inputs.map f) = g.op.eval (g.inputs.map f') := by
  rw [List.map_congr_left h]


def freeze (C : Circuit) (t : ℕ) (b : Bool) : Circuit :=
  ⟨C.gates.set t ⟨if b then GateOp.and else GateOp.or, []⟩, C.output⟩

lemma freeze_size (C : Circuit) (t : ℕ) (b : Bool) :
    (freeze C t b).size = C.size := by simp [freeze, Circuit.size]

lemma freeze_value {n : ℕ} (C : Circuit) (t : Fin C.gates.length)
    (b : Bool) (x : Fin n → Bool) : value (freeze C t b) x (n + t) = b := by
  rw [gate_value _ _ _ (by omega) (by rw [freeze_size]; simp only [Circuit.size]; omega)]
  cases b <;> simp [freeze, GateOp.eval]

lemma freeze_other {n : ℕ} (C : Circuit) (t : ℕ) (b : Bool)
    (x : Fin n → Bool) (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size)
    (hne : w ≠ n + t) :
    value (freeze C t b) x w = (C.gates[w-n]'(by unfold Circuit.size at hw; omega)).op.eval
      ((C.gates[w-n]'(by unfold Circuit.size at hw; omega)).inputs.map fun r =>
        if r < w then value (freeze C t b) x r else false) := by
  rw [gate_value _ _ _ hn (by rw [freeze_size]; exact hw)]
  have h : t ≠ w - n := by omega
  simp [freeze, h]

lemma freeze_eq {n : ℕ} (C : Circuit) (t : Fin C.gates.length)
    (b : Bool) (x : Fin n → Bool) (ht : value C x (n+t) = b) (w : ℕ) :
    value (freeze C t b) x w = value C x w := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value C x ⟨w, hn⟩
      have h2 := input_value (freeze C t b) x ⟨w, hn⟩
      simpa only using h2.trans h1.symm
    by_cases hw : w < n + C.size
    · by_cases he : w = n + t
      · rw [he, freeze_value, ht]
      · rw [freeze_other _ _ _ _ _ (by omega) hw he,
          gate_value C x w (by omega) hw]
        apply repl_eval_congr
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value C x w (by omega),
        missing_value (freeze C t b) x w (by rw [freeze_size]; omega)]

lemma before_mono {n : ℕ} (C : Circuit) (t : ℕ)
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → (i : ℕ) = t)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true)
    (w : ℕ) (hw : w < n + t) : value C x w = true → value C y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value C x ⟨w, hn⟩
      have h2 := input_value C y ⟨w, hn⟩
      simp only at h1 h2
      rw [h1,h2]
      exact hxy _
    by_cases hl : w < n + C.size
    · rw [gate_value C x w (by omega) hl, gate_value C y w (by omega) hl]
      have hi : w - n < C.gates.length := by unfold Circuit.size at hl; omega
      have hop : (C.gates[w-n]'hi).op = GateOp.and ∨ (C.gates[w-n]'hi).op = GateOp.or := by
        have hne : (C.gates[w-n]'hi).op ≠ GateOp.not := by
          intro he
          have hh := hnot ⟨w-n,hi⟩ he
          simp only at hh
          omega
        rcases hg C.gates[w-n] (List.getElem_mem _) with ha | ho | ht
        · exact Or.inl ha
        · exact Or.inr ho
        · exact (hne ht).elim
      apply repl_eval_mono _ hop
      intro r _
      by_cases hr : r < w
      · simpa [hr] using ih r hr (by omega)
      · simp [hr]
    · rw [missing_value C x w (by omega)]
      simp

lemma not_of_drop {n : ℕ} (C : Circuit) (t : Fin C.gates.length)
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → i.val = t.val)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true)
    (hx : value C x (n+t) = true) (hy : value C y (n+t) = false) :
    (C.gates.get t).op = GateOp.not := by
  by_contra hn
  have hop : (C.gates.get t).op = GateOp.and ∨ (C.gates.get t).op = GateOp.or := by
    rcases hg (C.gates.get t) (List.get_mem C.gates t) with ha | ho | ht
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (hn ht).elim
  rw [gate_value C x (n+t) (by omega) (by simp only [Circuit.size]; omega)] at hx
  rw [gate_value C y (n+t) (by omega) (by simp only [Circuit.size]; omega)] at hy
  simp only [Nat.add_sub_cancel_left, List.get_eq_getElem] at hx hy hop
  have ht := repl_eval_mono (C.gates.get t) hop
    (fun r => if r < n+t then value C x r else false)
    (fun r => if r < n+t then value C y r else false) (by
      intro r _
      by_cases hr : r < n+t
      · simpa [hr] using before_mono C t hg hnot x y hxy r hr
      · simp [hr]) hx
  simp only [List.get_eq_getElem] at ht
  rw [hy] at ht
  simp at ht

lemma not_false_above {n : ℕ} (C : Circuit) (t : Fin C.gates.length)
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → i.val = t.val)
    (ht : (C.gates.get t).op = GateOp.not)
    (x y : Fin n → Bool) (hxy : ∀ p, x p = true → y p = true)
    (hx : value C x (n+t) = false) : value C y (n+t) = false := by
  rw [gate_value C x (n+t) (by omega) (by simp only [Circuit.size]; omega)] at hx
  rw [gate_value C y (n+t) (by omega) (by simp only [Circuit.size]; omega)]
  simp only [Nat.add_sub_cancel_left] at hx ⊢
  have ht2 : C.gates[t.val].op = GateOp.not := by simpa only [List.get_eq_getElem] using ht
  rw [ht2] at hx ⊢
  simp only [GateOp.eval] at hx ⊢
  cases hs : C.gates[t.val].inputs with
  | nil => simp [hs] at hx
  | cons r rs =>
    simp only [hs, List.map_cons, List.headD_cons] at hx ⊢
    by_cases hr : r < n+t
    · simpa [hr] using before_mono C t hg hnot x y hxy r hr (by simpa [hr] using hx)
    · simp [hr] at hx

lemma freeze_good (C : Circuit) (t : Fin C.gates.length) (b : Bool)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → i.val = t.val) :
    ∀ g ∈ (freeze C t b).gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hmem
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hmem
  have hj0 : j < C.gates.length := by simpa [freeze] using hj
  by_cases he : t.val = j
  · cases b <;> simp [freeze, he]
  · have eq : (freeze C t b).gates[j] = C.gates[j] := by simp [freeze, he]
    rw [eq]
    obtain ⟨hop, har⟩ := hg C.gates[j] (List.getElem_mem _)
    refine ⟨?_, har⟩
    rcases hop with ha | ho | hn
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (he (hnot ⟨j,hj0⟩ hn).symm).elim

lemma freeze_false_le {n : ℕ} (C : Circuit) (t : Fin C.gates.length)
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → i.val = t.val)
    (x : Fin n → Bool) (w : ℕ) :
    value (freeze C t false) x w = true → value C x w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · have h1 := input_value C x ⟨w,hn⟩
      have h2 := input_value (freeze C t false) x ⟨w,hn⟩
      simp only at h1 h2
      rw [h1,h2]
      exact id
    by_cases hw : w < n+C.size
    · by_cases he : w = n+t
      · rw [he, freeze_value]
        simp
      · rw [freeze_other _ _ _ _ _ (by omega) hw he, gate_value C x w (by omega) hw]
        have hj : w-n < C.gates.length := by unfold Circuit.size at hw; omega
        have hop : (C.gates[w-n]'hj).op = GateOp.and ∨ (C.gates[w-n]'hj).op = GateOp.or := by
          rcases hg C.gates[w-n] (List.getElem_mem _) with ha | ho | ht
          · exact Or.inl ha
          · exact Or.inr ho
          · have hh := hnot ⟨w-n,hj⟩ ht
            simp only at hh
            omega
        apply repl_eval_mono _ hop
        intro r _
        by_cases hr : r < w
        · simpa [hr] using ih r hr
        · simp [hr]
    · rw [missing_value (freeze C t false) x w (by rw [freeze_size]; omega)]
      simp

lemma positive_window_not {n : ℕ} (C : Circuit) (t : ℕ) (Y : Finset (Fin n))
    (hg : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → i.val = t)
    (hk : 0 < Y.card)
    (hsmall : ∀ x : Fin n → Bool, (Finset.univ.filter fun v => x v = true).card < Y.card →
      value C x (n+t) = true)
    (hY : value C (fun v => decide (v ∈ Y)) (n+t) = false) :
    ∃ ht : t < C.gates.length, (C.gates.get ⟨t,ht⟩).op = GateOp.not ∧
      ∀ x : Fin n → Bool, (∀ p ∈ Y, x p = true) → value C x (n+t) = false := by
  have hempty : value C (fun _ => false) (n+t) = true := hsmall _ (by simpa using hk)
  have ht : t < C.gates.length := by
    by_contra h
    have hf := missing_value C (fun _ : Fin n => false) (n+t) (by unfold Circuit.size; omega)
    rw [hf] at hempty
    simp at hempty
  have hn : (C.gates.get ⟨t,ht⟩).op = GateOp.not :=
    not_of_drop C ⟨t,ht⟩ hg hnot (fun _ => false) (fun v => decide (v ∈ Y))
      (by simp) hempty hY
  refine ⟨ht, hn, ?_⟩
  intro x hx
  exact not_false_above C ⟨t,ht⟩ hg hnot hn _ x
    (fun p hp => hx p (of_decide_eq_true hp)) hY

end PEqualNP.Outside.L_meta_997.Window

namespace PEqualNP.Outside.L_meta_997.Small
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_997.SmallBase

lemma output_bounds {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ)
    (hc : ∀ i x, value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (i : Fin m) (hi : 2 ≤ (S i).card) : n ≤ o i ∧ o i < n + C.size := by
  classical
  have hp (p : Fin n) (hp : p ∈ S i) :
      value C (fun q => decide (q = p)) (o i) = true := by
    rw [hc]
    simp only [decide_eq_true_eq]
    exact ⟨p, hp, by simp⟩
  constructor
  · by_contra! hn
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (S i).card)
    have h1 := hp a ha
    have h2 := hp b hb
    have hv (p : Fin n) := input_value C (fun q => decide (q = p)) (⟨o i, hn⟩ : Fin n)
    simp only at hv
    rw [hv] at h1 h2
    simp only [decide_eq_true_eq] at h1 h2
    exact hab (h1.symm.trans h2)
  · by_contra! hn
    obtain ⟨p, hp'⟩ := Finset.card_pos.mp (by omega : 0 < (S i).card)
    have hv := hp p hp'
    rw [missing_value C _ _ hn] at hv
    contradiction

lemma output_ne {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (o : Fin m → ℕ)
    (hc : ∀ i x, value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (i j : Fin m) (hij : i ≠ j) (hi : 2 ≤ (S i).card) : o i ≠ o j := by
  classical
  intro he
  have hsub : S i ⊆ S j := by
    intro p hp
    have hv : value C (fun q => decide (q = p)) (o i) = true := by
      rw [hc]
      simp only [decide_eq_true_eq]
      exact ⟨p, hp, by simp⟩
    rw [he, hc] at hv
    simpa using hv
  have hh : S i ∩ S j = S i := Finset.inter_eq_left.mpr hsub
  have ht := hinter i j hij
  rw [hh] at ht
  omega

theorem small_of_monotone_window {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C M : Circuit) (o : Fin m → ℕ) (y : Finset (Fin n))
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ M.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsz : M.size = C.size)
    (hc : ∀ i x, value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hsound : ∀ i, Disjoint (S i) y → sound M (S i) (o i))
    (hfire : ∀ i, Disjoint (S i) y → ∀ p ∈ S i,
      value M (fun v => decide (v ∈ y ∨ v = p)) (o i) = true)
    (hy : ∀ w, value M (fun v => decide (v ∈ y)) w =
      value C (fun v => decide (v ∈ y)) w)
    (hsmall : y.card ≤ 2) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card)
      ≤ C.gates.length + m := by
  classical
  let A : Fin m → Finset ℕ := fun i =>
    if Disjoint (S i) y then asg M y (S i)
    else if 2 ≤ (S i).card then {o i} else ∅
  have hfalse (i : Fin m) (hd : Disjoint (S i) y) (w : ℕ) (hw : w ∈ asg M y (S i)) :
      value M (fun v => decide (v ∈ y)) w = false := by
    apply Bool.eq_false_iff.mpr
    intro hv
    obtain ⟨p, hp, hpy⟩ := (mem_asg M y (S i) w).mp hw |>.2.1 _ hv
    exact Finset.disjoint_left.mp hd hp (by simpa using hpy)
  have htrue (i : Fin m) (hd : ¬Disjoint (S i) y) :
      value M (fun v => decide (v ∈ y)) (o i) = true := by
    rw [hy, hc]
    simp only [decide_eq_true_eq]
    obtain ⟨p, hp, hpy⟩ := Finset.not_disjoint_iff.mp hd
    exact ⟨p, hp, by simpa using hpy⟩
  have hab : ∀ i, A i ⊆ Finset.Ico n (n + C.size) := by
    intro i w hw
    by_cases hd : Disjoint (S i) y
    · simp only [A, hd, if_true] at hw
      have hh := ((mem_asg M y (S i) w).mp hw).1
      simpa only [Finset.mem_Ico, hsz] using hh
    · simp only [A, hd, if_false] at hw
      split_ifs at hw with hi
      · have he : w = o i := Finset.mem_singleton.mp hw
        subst w
        exact Finset.mem_Ico.mpr (output_bounds S C o hc i hi)
      · simp at hw
  have hdis : ∀ i j, i ≠ j → Disjoint (A i) (A j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro w hwi hwj
    by_cases hi : Disjoint (S i) y <;> by_cases hj : Disjoint (S j) y
    · simp only [A, hi, hj, if_true] at hwi hwj
      have ai := (mem_asg M y (S i) w).mp hwi
      have aj := (mem_asg M y (S j) w).mp hwj
      exact (meet M y (S i) (S j) w hi.symm ai.2.1 aj.2.1 ai.2.2 (hinter i j hij)) hj.symm
    · simp only [A, hj, if_false] at hwj
      split_ifs at hwj with hs
      · have he := Finset.mem_singleton.mp hwj
        have hf := hfalse i hi w (by simpa only [A, hi, if_true] using hwi)
        have ht := htrue j hj
        rw [he, ht] at hf
        contradiction
      · simp at hwj
    · simp only [A, hi, if_false] at hwi
      split_ifs at hwi with hs
      · have he := Finset.mem_singleton.mp hwi
        have hf := hfalse j hj w (by simpa only [A, hj, if_true] using hwj)
        have ht := htrue i hi
        rw [he, ht] at hf
        contradiction
      · simp at hwi
    · simp only [A, hi, hj, if_false] at hwi hwj
      split_ifs at hwi with hsi
      · split_ifs at hwj with hsj
        · have hei := Finset.mem_singleton.mp hwi
          have hej := Finset.mem_singleton.mp hwj
          exact output_ne S C o hc hinter i j hij hsi (hei.symm.trans hej)
        · simp at hwj
      · simp at hwi
  have hper : ∀ i, (if Disjoint (S i) y then (S i).card else min y.card (S i).card)
      ≤ (A i).card + 1 := by
    intro i
    by_cases hd : Disjoint (S i) y
    · simp only [A, hd, if_true]
      exact card_le M hg y (S i) (o i) hd.symm (hsound i hd) (hfire i hd)
    · simp only [A, hd, if_false]
      split_ifs with hi
      · simp only [Finset.card_singleton]
        omega
      · simp only [Finset.card_empty, zero_add]
        omega
  have hcard : (∑ i, (A i).card) ≤ C.size := by
    have hu : (Finset.univ.biUnion A) ⊆ Finset.Ico n (n+C.size) := by
      intro w hw
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
      exact hab i hi
    have hd : (Finset.univ.biUnion A).card = ∑ i, (A i).card := by
      apply Finset.card_biUnion
      intro i _ j _ hij
      exact hdis i j hij
    have hh := Finset.card_le_card hu
    rw [hd] at hh
    simpa using hh
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hper i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at hh
  simpa only [Circuit.size] using hh.trans (Nat.add_le_add_right hcard m)

end PEqualNP.Outside.L_meta_997.Small

#print axioms PEqualNP.Outside.L_meta_997.Small.small_of_monotone_window

namespace PEqualNP.Outside.L_meta_997.Small
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_997.SmallBase

theorem small_one_not {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (t : ℕ) (y : Finset (Fin n))
    (hinter : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hnot : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → i.val = t)
    (hc : ∀ i x, value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hY : value C (fun v => decide (v ∈ y)) (n+t) = false)
    (hsmall : y.card ≤ 2) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card)
      ≤ C.gates.length + m := by
  classical
  by_cases hex : ∃ j : Fin C.gates.length, (C.gates.get j).op = GateOp.not
  · obtain ⟨j, hj⟩ := hex
    have hjt := hnot j hj
    have hnotj : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.not → i.val = j.val := by
      intro i hi
      exact (hnot i hi).trans hjt.symm
    have hYj : Window.value C (fun v => decide (v ∈ y)) (n+j) = false := by
      simpa only [hjt, Window.value, value] using hY
    have habove (x : Fin n → Bool) (hx : ∀ p ∈ y, x p = true) :
        Window.value C x (n+j) = false := by
      exact Window.not_false_above C j (fun g h => (hg g h).1) hnotj hj _ x
        (fun p hp => hx p (of_decide_eq_true hp)) hYj
    apply small_of_monotone_window S C (Window.freeze C j false) o y hinter
      (Window.freeze_good C j false hg hnotj) (Window.freeze_size C j false) hc
    · intro i _ x hx
      have hv := Window.freeze_false_le C j (fun g h => (hg g h).1) hnotj x (o i) hx
      change value C x (o i) = true at hv
      rw [hc] at hv
      exact of_decide_eq_true hv
    · intro i _ p hp
      have hz := habove (fun v => decide (v ∈ y ∨ v = p)) (by
        intro v hv
        simp [hv])
      have he := Window.freeze_eq C j false (fun v => decide (v ∈ y ∨ v = p)) hz (o i)
      change value (Window.freeze C j false) _ (o i) = value C _ (o i) at he
      rw [he, hc]
      simp only [decide_eq_true_eq]
      exact ⟨p, hp, by simp⟩
    · intro w
      exact Window.freeze_eq C j false _ hYj w
    · exact hsmall
  · have hmono : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        g.inputs.length ≤ 2 := by
      intro g hmem
      obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hmem
      obtain ⟨hop, hlen⟩ := hg C.gates[r] (List.getElem_mem _)
      refine ⟨?_, hlen⟩
      rcases hop with ha | ho | hn
      · exact Or.inl ha
      · exact Or.inr ho
      · exact (hex ⟨⟨r,hr⟩,hn⟩).elim
    apply small_of_monotone_window S C C o y hinter hmono rfl hc
    · intro i _ x hx
      rw [hc] at hx
      exact of_decide_eq_true hx
    · intro i _ p hp
      rw [hc]
      simp only [decide_eq_true_eq]
      exact ⟨p, hp, by simp⟩
    · exact fun _ => rfl
    · exact hsmall

end PEqualNP.Outside.L_meta_997.Small

#print axioms PEqualNP.Outside.L_meta_997.Small.small_one_not
