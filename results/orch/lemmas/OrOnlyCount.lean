import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970.OrCount
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

def orFlag (n : ℕ) (C : Circuit) (w : ℕ) : Bool :=
  match (PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n)).op with
  | .or => true
  | _ => false

lemma split_false {n : ℕ} (C : Circuit) (hG : good C) (y : Fin n → Bool)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) (hy : value C y w = false) :
    ∃ P : Finset ℕ, P.card ≤ 1 + (if orFlag n C w then 1 else 0) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, value C y r = false) ∧
      ∀ a ∈ support (n := n) C w, ∃ r ∈ P, a ∈ support C r := by
  classical
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  let g := C.gates[w - n]
  have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C (w - n) = g := by
    rw [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem _ _ hj]
  have hgval : ∀ x : Fin n → Bool,
      value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) :=
    fun x => gate_value C x w hn hw
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  rcases hop with hop | hop
  · have hgy : (g.inputs.map fun r => if r < w then value C y r else false).all id = false := by
      have h := (hgval y).symm
      rw [hy, hop] at h
      exact h
    have hgy' : ¬ ((g.inputs.map fun r => if r < w then value C y r else false).all id = true) :=
      fun h => Bool.false_ne_true (hgy.symm.trans h)
    simp only [List.all_eq_true, List.mem_map, id_eq, not_forall] at hgy'
    obtain ⟨_, ⟨u, hu, rfl⟩, huf⟩ := hgy'
    have hsupport : ∀ a ∈ support (n := n) C w,
        (if u < w then value C (fun q => decide (q = a)) u else false) = true := by
      intro a ha
      have hgp : (g.inputs.map fun r =>
          if r < w then value C (fun q => decide (q = a)) r else false).all id = true := by
        have h := (hgval (fun q => decide (q = a))).symm
        rw [(mem_support C w a).mp ha, hop] at h
        exact h
      simp only [List.all_eq_true, List.mem_map, id_eq] at hgp
      exact hgp _ ⟨u, hu, rfl⟩
    by_cases hut : u < w
    · have huy : value C y u = false := by
        simp only [hut, ↓reduceIte] at huf
        exact Bool.eq_false_iff.mpr huf
      refine ⟨{u}, by simp, ?_, ?_, ?_⟩
      · intro r hr
        obtain rfl := Finset.mem_singleton.mp hr
        exact hut
      · intro r hr
        obtain rfl := Finset.mem_singleton.mp hr
        exact huy
      · intro a ha
        refine ⟨u, Finset.mem_singleton_self _, (mem_support C u a).mpr ?_⟩
        simpa [hut] using hsupport a ha
    · refine ⟨∅, by simp, by simp, by simp, ?_⟩
      intro a ha
      have := hsupport a ha
      simp [hut] at this
  · let P := g.inputs.toFinset.filter (· < w)
    have hor : orFlag n C w = true := by
      simp only [orFlag, hgate, hop]
    have hPc : P.card ≤ 2 :=
      (Finset.card_filter_le _ _).trans ((List.toFinset_card_le g.inputs).trans hlen)
    refine ⟨P, by simpa [hor] using hPc, ?_, ?_, ?_⟩
    · intro r hr
      exact (Finset.mem_filter.mp hr).2
    · intro r hr
      have hmem := List.mem_toFinset.mp (Finset.mem_filter.mp hr).1
      have hlt := (Finset.mem_filter.mp hr).2
      have hgy : (g.inputs.map fun s => if s < w then value C y s else false).any id = false := by
        have h := (hgval y).symm
        rw [hy, hop] at h
        exact h
      have hgy' : ¬ ((g.inputs.map fun s => if s < w then value C y s else false).any id = true) :=
        fun h => Bool.false_ne_true (hgy.symm.trans h)
      simp only [List.any_eq_true, List.mem_map, id_eq] at hgy'
      rw [Bool.eq_false_iff]
      intro hv
      exact hgy' ⟨true, ⟨r, hmem, by simp [hlt, hv]⟩, rfl⟩
    · intro a ha
      have hgp : (g.inputs.map fun r =>
          if r < w then value C (fun q => decide (q = a)) r else false).any id = true := by
        have h := (hgval (fun q => decide (q = a))).symm
        rw [(mem_support C w a).mp ha, hop] at h
        exact h
      simp only [List.any_eq_true, List.mem_map, id_eq] at hgp
      obtain ⟨_, ⟨u, hu, rfl⟩, huv⟩ := hgp
      by_cases hut : u < w
      · exact ⟨u, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hu, hut⟩,
          (mem_support C u a).mpr (by simpa [hut] using huv)⟩
      · simp [hut] at huv

lemma frontier_cut {α : Type*} [DecidableEq α]
    (supp : ℕ → Finset α) (neg : ℕ → Prop) (G K : Finset ℕ)
    (hstep : ∀ w ∈ G, neg w → ∃ P : Finset ℕ,
      P.card ≤ 1 + (if w ∈ K then 1 else 0) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, neg r) ∧
      ∀ a ∈ supp w, ∃ r ∈ P, a ∈ supp r)
    (t : ℕ) (F : Finset ℕ)
    (hFt : ∀ w ∈ F, w ∈ G → w < t) (hFn : ∀ w ∈ F, neg w) :
    ∃ B : Finset ℕ, Disjoint B G ∧ (∀ w ∈ B, neg w) ∧
      B.card ≤ F.card + (K.filter (· < t)).card ∧
      ∀ a, (∃ w ∈ F, a ∈ supp w) → ∃ w ∈ B, a ∈ supp w := by
  classical
  induction t generalizing F with
  | zero =>
    refine ⟨F, Finset.disjoint_left.mpr ?_, hFn, by simp, fun _ h => h⟩
    intro w hw hg
    have := hFt w hw hg
    omega
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPc, hPt, hPn, hPs⟩ := hstep t hex.2 (hFn t hex.1)
      let F' := F.erase t ∪ P
      have hF't : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hFt w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hPt w hw
      have hF'n : ∀ w ∈ F', neg w := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hFn w (Finset.mem_erase.mp hw).2
        · exact hPn w hw
      obtain ⟨B, hd, hn, hc, hs⟩ := ih F' hF't hF'n
      have hsize : F'.card ≤ F.card + (if t ∈ K then 1 else 0) := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : (K.filter (· < t + 1)).card =
          (K.filter (· < t)).card + (if t ∈ K then 1 else 0) := by
        by_cases ht : t ∈ K
        · have heq : K.filter (· < t + 1) = insert t (K.filter (· < t)) := by
            ext w
            simp only [Finset.mem_filter, Finset.mem_insert]
            constructor
            · rintro ⟨hw, hlt⟩
              by_cases h : w = t
              · exact Or.inl h
              · exact Or.inr ⟨hw, by omega⟩
            · rintro (rfl | ⟨hw, hlt⟩)
              · exact ⟨ht, by omega⟩
              · exact ⟨hw, by omega⟩
          rw [heq, Finset.card_insert_of_notMem (by simp)]
          simp [ht]
        · have heq : K.filter (· < t + 1) = K.filter (· < t) := by
            ext w
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hw, hlt⟩
              have hne : w ≠ t := fun h => ht (h ▸ hw)
              exact ⟨hw, by omega⟩
            · rintro ⟨hw, hlt⟩
              exact ⟨hw, by omega⟩
          rw [heq]
          simp [ht]
      refine ⟨B, hd, hn, by omega, ?_⟩
      intro a ⟨w, hw, ha⟩
      apply hs a
      by_cases hwt : w = t
      · subst w
        obtain ⟨r, hr, har⟩ := hPs a ha
        exact ⟨r, Finset.mem_union_right _ hr, har⟩
      · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hwt, hw⟩), ha⟩
    · have hF't : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun h => hex ⟨h ▸ hw, h ▸ hg⟩
        have hlt := hFt w hw hg
        omega
      obtain ⟨B, hd, hn, hc, hs⟩ := ih F hF't hFn
      have hle : (K.filter (· < t)).card ≤ (K.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw => Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hw).1, by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, hn, by omega, hs⟩

def owned {n : ℕ} (C : Circuit) (S : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w =>
    support C w ⊆ S ∧ 2 ≤ (support (n := n) C w).card

def ownedOr {n : ℕ} (C : Circuit) (S : Finset (Fin n)) : Finset ℕ :=
  (owned C S).filter fun w => orFlag n C w

lemma count_or {n : ℕ} (C : Circuit) (hG : good C) (S : Finset (Fin n))
    (F : Finset ℕ)
    (hpos : ∀ p ∈ S, ∃ w ∈ F, p ∈ support C w)
    (hneg : ∀ w ∈ F, value C (fun p => decide (p ∉ S)) w = false) :
    S.card ≤ F.card + (ownedOr C S).card := by
  classical
  let y : Fin n → Bool := fun p => decide (p ∉ S)
  let G := owned C S
  let K := ownedOr C S
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  have hstep : ∀ w ∈ G, value C y w = false → ∃ P : Finset ℕ,
      P.card ≤ 1 + (if w ∈ K then 1 else 0) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, value C y r = false) ∧
      ∀ a ∈ support (n := n) C w, ∃ r ∈ P, a ∈ support C r := by
    intro w hw hy
    obtain ⟨P, hc, ht, hn, hs⟩ := split_false C hG y w (hgate w hw).1 (hgate w hw).2 hy
    have hmem : w ∈ K ↔ orFlag n C w = true := by
      simp only [K, ownedOr, Finset.mem_filter]
      change w ∈ G ∧ orFlag n C w = true ↔ orFlag n C w = true
      simp [hw]
    exact ⟨P, by simpa only [hmem] using hc, ht, hn, hs⟩
  obtain ⟨B, hd, hn, hc, hs⟩ :=
    frontier_cut (support (n := n) C) (fun w => value C y w = false) G K hstep
      (n + C.size) F (fun w _ hw => (hgate w hw).2) hneg
  have hsmall : ∀ w ∈ B, (support (n := n) C w).card ≤ 1 := by
    intro w hw
    have hsub : support (n := n) C w ⊆ S := by
      intro p hp
      by_contra hpS
      have hpt := (mem_support C w p).mp hp
      have hmono := value_mono C hG (fun q => decide (q = p)) y (by
        intro q hq
        have hqp : q = p := of_decide_eq_true hq
        subst q
        simp [y, hpS]) w hpt
      rw [hn w hw] at hmono
      exact Bool.false_ne_true hmono
    by_contra! hlarge
    have hreal := support_gate C w (by omega)
    have hwG : w ∈ G := Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr hreal, hsub, by omega⟩
    exact Finset.disjoint_left.mp hd hw hwG
  have hcovered : S ⊆ B.biUnion (support C) := by
    intro p hp
    obtain ⟨w, hw, hwp⟩ := hs p (hpos p hp)
    exact Finset.mem_biUnion.mpr ⟨w, hw, hwp⟩
  have h1 := Finset.card_le_card hcovered
  have h2 := Finset.card_biUnion_le_card_mul B (support C) 1 hsmall
  have h3 := Finset.card_filter_le K (fun w => w < n + C.size)
  change S.card ≤ F.card + K.card
  omega

lemma count_or_one {n : ℕ} (C : Circuit) (hG : good C) (S : Finset (Fin n))
    (o : ℕ) (hpos : ∀ p ∈ S, p ∈ support C o)
    (hneg : value C (fun p => decide (p ∉ S)) o = false) :
    S.card - 1 ≤ (ownedOr C S).card := by
  have h := count_or C hG S {o}
    (fun p hp => ⟨o, Finset.mem_singleton_self _, hpos p hp⟩)
    (by intro w hw; obtain rfl := Finset.mem_singleton.mp hw; exact hneg)
  simp only [Finset.card_singleton] at h
  omega

end PEqualNP.Outside.L_meta_4970.OrCount
