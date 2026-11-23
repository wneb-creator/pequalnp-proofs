import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_997.WeightedFrontier

variable {α : Type*} [DecidableEq α]

lemma paid_succ (A : Finset ℕ) (t : ℕ) :
    (A.filter (fun w => w < t + 1)).card =
      (A.filter (fun w => w < t)).card + (if t ∈ A then 1 else 0) := by
  by_cases ht : t ∈ A
  · have he : A.filter (fun w => w < t + 1) = insert t (A.filter (fun w => w < t)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hwA, hw⟩
        by_cases hwt : w = t
        · exact Or.inl hwt
        · exact Or.inr ⟨hwA, by omega⟩
      · rintro (rfl | ⟨hwA, hw⟩)
        · exact ⟨ht, by omega⟩
        · exact ⟨hwA, by omega⟩
    rw [he]
    simp [ht]
  · have he : A.filter (fun w => w < t + 1) = A.filter (fun w => w < t) := by
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hwA, hw⟩
        have hwt : w ≠ t := by rintro rfl; exact ht hwA
        exact ⟨hwA, by omega⟩
      · rintro ⟨hwA, hw⟩
        exact ⟨hwA, by omega⟩
    rw [he]
    simp [ht]

theorem frontier_cut
    (Sup : ℕ → Finset α) (Good : ℕ → Prop) (A : Finset ℕ)
    (step : ∀ w, Good w → 2 ≤ (Sup w).card →
      ∃ P : Finset ℕ,
        P.card ≤ 1 + (if w ∈ A then 1 else 0) ∧
        (∀ r ∈ P, r < w ∧ Good r) ∧ Sup w ⊆ P.biUnion Sup) :
    ∀ t (F : Finset ℕ),
      (∀ w ∈ F, Good w) →
      (∀ w ∈ F, 2 ≤ (Sup w).card → w < t) →
      ∃ B : Finset ℕ,
        (∀ w ∈ B, Good w) ∧ (∀ w ∈ B, (Sup w).card ≤ 1) ∧
        F.biUnion Sup ⊆ B.biUnion Sup ∧
        B.card ≤ F.card + (A.filter (fun w => w < t)).card := by
  intro t
  induction t with
  | zero =>
    intro F hgood hbound
    refine ⟨F, hgood, ?_, Finset.Subset.refl _, ?_⟩
    · intro w hw
      by_contra! hlarge
      have := hbound w hw (by omega)
      omega
    · simp
  | succ t ih =>
    intro F hgood hbound
    by_cases htF : t ∈ F
    · by_cases htlarge : 2 ≤ (Sup t).card
      · obtain ⟨P, hPcard, hPgood, hPcover⟩ := step t (hgood t htF) htlarge
        let F' := F.erase t ∪ P
        have hgood' : ∀ w ∈ F', Good w := by
          intro w hw
          rcases Finset.mem_union.mp hw with hw | hw
          · exact hgood w (Finset.mem_of_mem_erase hw)
          · exact (hPgood w hw).2
        have hbound' : ∀ w ∈ F', 2 ≤ (Sup w).card → w < t := by
          intro w hw hlarge
          rcases Finset.mem_union.mp hw with hw | hw
          · have hwF := Finset.mem_of_mem_erase hw
            have hne := (Finset.mem_erase.mp hw).1
            have hb := hbound w hwF hlarge
            omega
          · exact (hPgood w hw).1
        obtain ⟨B, hBg, hBs, hBcover, hBcard⟩ := ih F' hgood' hbound'
        refine ⟨B, hBg, hBs, ?_, ?_⟩
        · apply Finset.Subset.trans ?_ hBcover
          intro a ha
          obtain ⟨w, hw, ha⟩ := Finset.mem_biUnion.mp ha
          by_cases hwt : w = t
          · subst w
            obtain ⟨r, hr, har⟩ := Finset.mem_biUnion.mp (hPcover ha)
            exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_union_right _ hr, har⟩
          · exact Finset.mem_biUnion.mpr
              ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwt, hw⟩), ha⟩
        · have hFcard : F'.card ≤ (F.erase t).card + P.card := Finset.card_union_le _ _
          have herase := Finset.card_erase_add_one htF
          have hpaid := paid_succ A t
          change B.card ≤ F.card + (A.filter (fun w => w < t + 1)).card
          omega
      · have hbound' : ∀ w ∈ F, 2 ≤ (Sup w).card → w < t := by
          intro w hw hlarge
          have hne : w ≠ t := by rintro rfl; exact htlarge hlarge
          have hb := hbound w hw hlarge
          omega
        obtain ⟨B, hBg, hBs, hBc, hBcard⟩ := ih F hgood hbound'
        refine ⟨B, hBg, hBs, hBc, ?_⟩
        have hpaid := paid_succ A t
        change B.card ≤ F.card + (A.filter (fun w => w < t + 1)).card
        omega
    · have hbound' : ∀ w ∈ F, 2 ≤ (Sup w).card → w < t := by
        intro w hw hlarge
        have hne : w ≠ t := by rintro rfl; exact htF hw
        have hb := hbound w hw hlarge
        omega
      obtain ⟨B, hBg, hBs, hBc, hBcard⟩ := ih F hgood hbound'
      refine ⟨B, hBg, hBs, hBc, ?_⟩
      have hpaid := paid_succ A t
      change B.card ≤ F.card + (A.filter (fun w => w < t + 1)).card
      omega

theorem support_card_le_paid_add_one
    (Sup : ℕ → Finset α) (Good : ℕ → Prop) (A : Finset ℕ)
    (step : ∀ w, Good w → 2 ≤ (Sup w).card →
      ∃ P : Finset ℕ,
        P.card ≤ 1 + (if w ∈ A then 1 else 0) ∧
        (∀ r ∈ P, r < w ∧ Good r) ∧ Sup w ⊆ P.biUnion Sup)
    (o : ℕ) (ho : Good o) : (Sup o).card ≤ A.card + 1 := by
  obtain ⟨B, _, hsmall, hcover, hcard⟩ := frontier_cut Sup Good A step (o + 1) {o}
    (by intro w hw; simpa using (Finset.mem_singleton.mp hw) ▸ ho)
    (by intro w hw _; simp only [Finset.mem_singleton] at hw; omega)
  have hcov : Sup o ⊆ B.biUnion Sup := by simpa using hcover
  have h1 := Finset.card_le_card hcov
  have h2 := Finset.card_biUnion_le_card_mul B Sup 1 hsmall
  have h3 := Finset.card_filter_le A (fun w => w < o + 1)
  simp only [Finset.card_singleton] at hcard
  simp only [mul_one] at h2
  omega

end PEqualNP.Outside.L_meta_997.WeightedFrontier

namespace PEqualNP.Outside.L_meta_997.HeavyOrCount

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


def outside {n : ℕ} (T : Finset (Fin n)) : Fin n → Bool := fun p => decide (p ∉ T)

lemma false_outside_sound {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (T : Finset (Fin n)) (w : ℕ) (hz : value C (outside T) w = false) : sound C T w := by
  intro x hx
  by_contra hn
  have hxy : ∀ p, x p = true → outside T p = true := by
    intro p hp
    simp only [outside, decide_eq_true_eq]
    intro hpT
    exact hn ⟨p, hpT, hp⟩
  have := value_mono C hG x (outside T) hxy w hx
  simp [hz] at this

open Classical in
lemma gate_choice {X : Type} (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (f : X → ℕ → Bool) (z : X)
    (hz : g.op.eval (g.inputs.map (f z)) = false) :
    ∃ P : Finset ℕ, P.card ≤ 1 + (if g.op = GateOp.or then 1 else 0) ∧
      (∀ r ∈ P, f z r = false) ∧
      ∀ x, g.op.eval (g.inputs.map (f x)) = true → ∃ r ∈ P, f x r = true := by
  classical
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen hz ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · simp [GateOp.eval] at hz
    · exact ⟨∅, by simp, by simp, by simp [GateOp.eval]⟩
  | [a], _ =>
    refine ⟨{a}, by simp, ?_, ?_⟩
    · intro r hr
      have : r = a := by simpa using hr
      subst r
      rcases hop with rfl | rfl <;> simpa [GateOp.eval] using hz
    · intro x hx
      refine ⟨a, by simp, ?_⟩
      rcases hop with rfl | rfl <;> simpa [GateOp.eval] using hx
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · by_cases ha : f z a = false
      · refine ⟨{a}, by simp, by simpa using ha, ?_⟩
        intro x hx
        have h : f x a = true ∧ f x b = true := by simpa [GateOp.eval] using hx
        exact ⟨a, by simp, h.1⟩
      · have hb : f z b = false := by
          cases hza : f z a <;> cases hzb : f z b <;> simp_all [GateOp.eval]
        refine ⟨{b}, by simp, by simpa using hb, ?_⟩
        intro x hx
        have h : f x a = true ∧ f x b = true := by simpa [GateOp.eval] using hx
        exact ⟨b, by simp, h.2⟩
    · refine ⟨{a,b}, ?_, ?_, ?_⟩
      · have := Finset.card_insert_le a ({b} : Finset ℕ)
        simpa using this
      · have h : f z a = false ∧ f z b = false := by simpa [GateOp.eval] using hz
        intro r hr
        simp only [Finset.mem_insert, Finset.mem_singleton] at hr
        rcases hr with rfl | rfl
        · exact h.1
        · exact h.2
      · intro x hx
        have h : f x a = true ∨ f x b = true := by simpa [GateOp.eval] using hx
        rcases h with ha | hb
        · exact ⟨a, by simp, ha⟩
        · exact ⟨b, by simp, hb⟩
  | _ :: _ :: _ :: _, h => simp at h

noncomputable def charged {n : ℕ} (C : Circuit) (Y T : Finset (Fin n)) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n+C.size)).filter fun w =>
    value C (outside T) w = false ∧ 2 ≤ (supp C Y w).card ∧
      ∃ h : w-n < C.gates.length, (C.gates[w-n]'h).op = GateOp.or

lemma decompose {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y T : Finset (Fin n)) (hYT : Disjoint Y T) (w : ℕ)
    (hz : value C (outside T) w = false) (hs : 2 ≤ (supp C Y w).card) :
    ∃ P : Finset ℕ, P.card ≤ 1 + (if w ∈ charged C Y T then 1 else 0) ∧
      (∀ r ∈ P, r < w ∧ value C (outside T) r = false) ∧
      supp C Y w ⊆ P.biUnion (supp C Y) := by
  classical
  obtain ⟨hn, hw⟩ := supp_gate C Y T w hYT (false_outside_sound C hG T w hz) hs
  let g := C.gates[w-n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  let f (x : Fin n → Bool) (r : ℕ) := if r < w then value C x r else false
  have formula (x : Fin n → Bool) : value C x w = g.op.eval (g.inputs.map (f x)) :=
    gate_value C x w hn hw
  obtain ⟨R, hR, hzero, hcover⟩ := gate_choice g hop hlen f (outside T) (by rw [← formula]; exact hz)
  refine ⟨R.filter (· < w), ?_, ?_, ?_⟩
  · have hcard := Finset.card_filter_le R (· < w)
    by_cases hg : g.op = GateOp.or
    · have hc : w ∈ charged C Y T := by
        simp only [charged, Finset.mem_filter, Finset.mem_Ico]
        exact ⟨⟨hn, hw⟩, hz, hs, ⟨by unfold Circuit.size at hw; omega, hg⟩⟩
      simp only [ite_eq_left hg] at hR
      simp only [ite_eq_left hc]
      omega
    · simp only [ite_eq_right hg] at hR
      split_ifs <;> omega
  · intro r hr
    obtain ⟨hr, hlt⟩ := Finset.mem_filter.mp hr
    exact ⟨hlt, by simpa [f, hlt] using hzero r hr⟩
  · intro p hp
    have hv := (mem_supp C Y w p).mp hp
    rw [formula] at hv
    obtain ⟨r, hr, hrtrue⟩ := hcover _ hv
    have hlt : r < w := by
      by_contra h
      simp [f, h] at hrtrue
    exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hlt⟩,
      (mem_supp C Y r p).mpr (by simpa [f, hlt] using hrtrue)⟩


lemma supp_subset {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y T : Finset (Fin n)) (hYT : Disjoint Y T) (w : ℕ)
    (hz : value C (outside T) w = false) : supp C Y w ⊆ T := by
  intro q hq
  obtain ⟨p, hp, hv⟩ := false_outside_sound C hG T w hz _ ((mem_supp C Y w q).mp hq)
  have hh : p ∈ Y ∨ p = q := of_decide_eq_true hv
  rcases hh with hy | rfl
  · exact (Finset.disjoint_left.mp hYT hy hp).elim
  · exact hp

lemma charged_disjoint {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y T U : Finset (Fin n)) (hYT : Disjoint Y T) (hYU : Disjoint Y U)
    (hTU : (T ∩ U).card ≤ 1) : Disjoint (charged C Y T) (charged C Y U) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w hT hU
  have ht := (Finset.mem_filter.mp hT).2
  have hu := (Finset.mem_filter.mp hU).2
  have hsub : supp C Y w ⊆ T ∩ U := fun q hq =>
    Finset.mem_inter.mpr ⟨supp_subset C hG Y T hYT w ht.1 hq,
      supp_subset C hG Y U hYU w hu.1 hq⟩
  have hc := Finset.card_le_card hsub
  have hl := ht.2.1
  omega

lemma charged_false_background {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y T : Finset (Fin n)) (hYT : Disjoint Y T) (w : ℕ)
    (hw : w ∈ charged C Y T) : value C (fun p => decide (p ∈ Y)) w = false := by
  classical
  have hz := (Finset.mem_filter.mp hw).2.1
  by_contra hn
  have hv : value C (fun p => decide (p ∈ Y)) w = true := by simpa using hn
  have hm := value_mono C hG (fun p => decide (p ∈ Y)) (outside T)
    (fun p hp => by
      simp only [outside, decide_eq_true_eq]
      exact fun hpT => Finset.disjoint_left.mp hYT (of_decide_eq_true hp) hpT) w hv
  simp [hz] at hm


lemma card_le_or {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (Y T : Finset (Fin n)) (o : ℕ) (hYT : Disjoint Y T)
    (hso : sound C T o)
    (hfire : ∀ p ∈ T, value C (fun v => decide (v ∈ Y ∨ v = p)) o = true) :
    T.card ≤ (charged C Y T).card + 1 := by
  classical
  have hz : value C (outside T) o = false := by
    by_contra hn
    have hv : value C (outside T) o = true := by simpa using hn
    obtain ⟨p, hp, hvp⟩ := hso _ hv
    exact (of_decide_eq_true hvp) hp
  have hc := PEqualNP.Outside.L_meta_997.WeightedFrontier.support_card_le_paid_add_one
    (supp C Y) (fun w => value C (outside T) w = false) (charged C Y T)
    (fun w hw hs => decompose C hG Y T hYT w hw hs) o hz
  have hsub : T ⊆ supp C Y o := fun p hp => (mem_supp C Y o p).mpr (hfire p hp)
  exact (Finset.card_le_card hsub).trans hc

end PEqualNP.Outside.L_meta_997.HeavyOrCount
