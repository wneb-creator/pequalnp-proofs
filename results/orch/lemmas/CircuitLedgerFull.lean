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


namespace PEqualNP.Outside.L_meta_4970.Components

def Joined {α : Type*} (H : SimpleGraph α) (A : Finset α) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, H.Reachable a b

lemma joined_small {α : Type*} (H : SimpleGraph α) (A : Finset α)
    (hA : A.card ≤ 1) : Joined H A := by
  intro a ha b hb
  have hab := Finset.card_le_one.mp hA a ha b hb
  subst b
  exact SimpleGraph.Reachable.refl _

lemma joined_subset {α : Type*} (H : SimpleGraph α) {A B : Finset α}
    (hA : A ⊆ B) (hB : Joined H B) : Joined H A := by
  intro a ha b hb
  exact hB a (hA ha) b (hA hb)

lemma joined_mono {α : Type*} {H H' : SimpleGraph α} (hH : H ≤ H')
    {A : Finset α} (hA : Joined H A) : Joined H' A := by
  intro a ha b hb
  exact (hA a ha b hb).mono hH

lemma join_two {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) (A B : Finset α) (hA : Joined H A) (hB : Joined H B) :
    ∃ H' : SimpleGraph α, H ≤ H' ∧
      H'.edgeSet.ncard ≤ H.edgeSet.ncard + 1 ∧ Joined H' (A ∪ B) := by
  classical
  by_cases ha : A.Nonempty
  · by_cases hb : B.Nonempty
    · obtain ⟨a, ha⟩ := ha
      obtain ⟨b, hb⟩ := hb
      let J : SimpleGraph α := SimpleGraph.fromEdgeSet {s(a, b)}
      have hJsub : J.edgeFinset ⊆ {s(a, b)} := by
        intro e he
        have he' : e ∈ J.edgeSet := by simpa using he
        dsimp only [J] at he'
        rw [SimpleGraph.edgeSet_fromEdgeSet] at he'
        simpa using he'.1
      have hJcard : J.edgeFinset.card ≤ 1 := by
        simpa using Finset.card_le_card hJsub
      have hab : (H ⊔ J).Reachable a b := by
        by_cases h : a = b
        · subst b
          exact SimpleGraph.Reachable.refl _
        · apply SimpleGraph.Adj.reachable
          exact Or.inr ((SimpleGraph.fromEdgeSet_adj
            (s := ({s(a, b)} : Set (Sym2 α)))).mpr ⟨by simp, h⟩)
      refine ⟨H ⊔ J, le_sup_left, ?_, ?_⟩
      · simp only [Set.ncard_eq_toFinset_card']
        change (H ⊔ J).edgeFinset.card ≤ H.edgeFinset.card + 1
        rw [SimpleGraph.edgeFinset_sup]
        exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left hJcard _)
      · intro u hu v hv
        rcases Finset.mem_union.mp hu with hu | hu
        · rcases Finset.mem_union.mp hv with hv | hv
          · exact (hA u hu v hv).mono le_sup_left
          · exact ((hA u hu a ha).mono le_sup_left).trans
              (hab.trans ((hB b hb v hv).mono le_sup_left))
        · rcases Finset.mem_union.mp hv with hv | hv
          · exact ((hB u hu b hb).mono le_sup_left).trans
              (hab.symm.trans ((hA a ha v hv).mono le_sup_left))
          · exact (hB u hu v hv).mono le_sup_left
    · have hb : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
      refine ⟨H, le_rfl, Nat.le_add_right .., ?_⟩
      simpa [hb] using hA
  · have ha : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    refine ⟨H, le_rfl, Nat.le_add_right .., ?_⟩
    simpa [ha] using hB

lemma joined_biUnion_one {α : Type*} [DecidableEq α]
    (H : SimpleGraph α) (P : Finset ℕ) (supp : ℕ → Finset α)
    (hP : P.card ≤ 1) (hj : ∀ w ∈ P, Joined H (supp w)) :
    Joined H (P.biUnion supp) := by
  intro a ha b hb
  obtain ⟨u, hu, hau⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨v, hv, hbv⟩ := Finset.mem_biUnion.mp hb
  have huv := Finset.card_le_one.mp hP u hu v hv
  subst v
  exact hj u hu a hau b hbv

lemma join_family {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) (P : Finset ℕ) (supp : ℕ → Finset α) (charge : Bool)
    (hP : P.card ≤ 1 + (if charge then 1 else 0))
    (hj : ∀ w ∈ P, Joined H (supp w)) :
    ∃ H' : SimpleGraph α, H ≤ H' ∧
      H'.edgeSet.ncard ≤ H.edgeSet.ncard + (if charge then 1 else 0) ∧
      Joined H' (P.biUnion supp) := by
  classical
  by_cases hP1 : P.card ≤ 1
  · exact ⟨H, le_rfl, Nat.le_add_right .., joined_biUnion_one H P supp hP1 hj⟩
  · have hcharge : charge = true := by
      cases charge
      · exact False.elim (hP1 (by simpa using hP))
      · rfl
    have hP2 : P.card = 2 := by simp [hcharge] at hP; omega
    obtain ⟨u, v, _, hPuv⟩ := Finset.card_eq_two.mp hP2
    have hu : u ∈ P := by simp [hPuv]
    have hv : v ∈ P := by simp [hPuv]
    obtain ⟨H', hle, hc, hjoin⟩ := join_two H (supp u) (supp v) (hj u hu) (hj v hv)
    refine ⟨H', hle, by simpa [hcharge] using hc, ?_⟩
    simpa [hPuv] using hjoin

lemma filter_lt_succ_card (K : Finset ℕ) (t : ℕ) :
    (K.filter (· < t + 1)).card = (K.filter (· < t)).card +
      (if t ∈ K then 1 else 0) := by
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

lemma build_support_graph {α : Type*} [Fintype α] [DecidableEq α]
    (supp : ℕ → Finset α) (neg : ℕ → Prop) (K : Finset ℕ)
    (hstep : ∀ w, neg w → 2 ≤ (supp w).card → ∃ P : Finset ℕ,
      P.card ≤ 1 + (if w ∈ K then 1 else 0) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, neg r) ∧
      supp w ⊆ P.biUnion supp)
    (t : ℕ) :
    ∃ H : SimpleGraph α, H.edgeSet.ncard ≤ (K.filter (· < t)).card ∧
      ∀ w < t, neg w → Joined H (supp w) := by
  classical
  induction t with
  | zero =>
    refine ⟨⊥, by simp, ?_⟩
    intro w hw
    omega
  | succ t ih =>
    obtain ⟨H, hHcard, hHjoin⟩ := ih
    have hfilter := filter_lt_succ_card K t
    by_cases ht : neg t ∧ 2 ≤ (supp t).card
    · obtain ⟨P, hPc, hPt, hPn, hPs⟩ := hstep t ht.1 ht.2
      have hj : ∀ w ∈ P, Joined H (supp w) :=
        fun w hw => hHjoin w (hPt w hw) (hPn w hw)
      obtain ⟨H', hle, hc, hjoin⟩ := join_family H P supp (decide (t ∈ K))
        (by simpa only [decide_eq_true_eq] using hPc) hj
      simp only [decide_eq_true_eq] at hc
      refine ⟨H', by omega, ?_⟩
      intro w hw hn
      by_cases hwt : w = t
      · subst w
        exact joined_subset H' hPs hjoin
      · exact joined_mono hle (hHjoin w (by omega) hn)
    · refine ⟨H, by omega, ?_⟩
      intro w hw hn
      by_cases hwt : w = t
      · subst w
        have hsmall : (supp t).card ≤ 1 := by
          have : ¬ 2 ≤ (supp t).card := fun h => ht ⟨hn, h⟩
          omega
        exact joined_small H (supp t) hsmall
      · exact hHjoin w (by omega) hn

lemma component_card_antitone {α : Type*} [Finite α] (G H : SimpleGraph α)
    (hreach : ∀ a b, G.Reachable a b → H.Reachable a b) :
    Nat.card H.ConnectedComponent ≤ Nat.card G.ConnectedComponent := by
  let f : G.ConnectedComponent → H.ConnectedComponent :=
    Quot.map id (fun a b hab => hreach a b hab)
  have hf : Function.Surjective f := by
    intro c
    refine Quot.inductionOn c ?_
    intro a
    exact ⟨G.connectedComponentMk a, rfl⟩
  exact Nat.card_le_card_of_surjective f hf

lemma vertex_card_le_edges_components {α : Type*} [Finite α] (G : SimpleGraph α) :
    Nat.card α ≤ G.edgeSet.ncard + Nat.card G.ConnectedComponent := by
  obtain ⟨T, hTG, hT, hreach⟩ := G.exists_isAcyclic_reachable_eq_le
  have heq := hT.ncard_edgeSet_add_card_connectedComponent
  have he : T.edgeSet.ncard ≤ G.edgeSet.ncard :=
    Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hTG)
  have hc := component_card_antitone G T (by intro a b hab; rwa [hreach])
  omega

def familyGraph {α : Type*} (supp : ℕ → Finset α) (F : Finset ℕ) : SimpleGraph α where
  Adj a b := a ≠ b ∧ ∃ w ∈ F, a ∈ supp w ∧ b ∈ supp w
  symm := ⟨by
    intro a b hab
    obtain ⟨hne, w, hw, ha, hb⟩ := hab
    exact ⟨hne.symm, w, hw, hb, ha⟩⟩
  loopless := ⟨by
    intro a ha
    exact ha.1 rfl⟩

lemma family_reachable {α : Type*} (H : SimpleGraph α)
    (supp : ℕ → Finset α) (F : Finset ℕ) (hj : ∀ w ∈ F, Joined H (supp w)) :
    ∀ a b, (familyGraph supp F).Reachable a b → H.Reachable a b := by
  intro a b hab
  obtain ⟨walk⟩ := hab
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hab _ ih =>
    obtain ⟨_, w, hw, ha, hb⟩ := hab
    exact (hj w hw _ ha _ hb).trans ih

lemma frontier_component_bound {α : Type*} [Fintype α] [DecidableEq α]
    (supp : ℕ → Finset α) (neg : ℕ → Prop) (K : Finset ℕ)
    (hstep : ∀ w, neg w → 2 ≤ (supp w).card → ∃ P : Finset ℕ,
      P.card ≤ 1 + (if w ∈ K then 1 else 0) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, neg r) ∧ supp w ⊆ P.biUnion supp)
    (t : ℕ) (F : Finset ℕ) (hFt : ∀ w ∈ F, w < t) (hFn : ∀ w ∈ F, neg w) :
    Nat.card α ≤ (K.filter (· < t)).card +
      Nat.card (familyGraph supp F).ConnectedComponent := by
  obtain ⟨H, hHc, hHj⟩ := build_support_graph supp neg K hstep t
  have hj : ∀ w ∈ F, Joined H (supp w) := fun w hw => hHj w (hFt w hw) (hFn w hw)
  have hcc := component_card_antitone (familyGraph supp F) H (family_reachable H supp F hj)
  have hv := vertex_card_le_edges_components H
  omega

end PEqualNP.Outside.L_meta_4970.Components

namespace PEqualNP.Outside.L_meta_4970.OrCount

open PEqualNP.CircuitLowerBounds

def restrictedSupport {n : ℕ} (S : Finset (Fin n)) (C : Circuit) (w : ℕ) : Finset S :=
  Finset.univ.filter fun p => p.val ∈ support (n := n) C w

lemma restrictedSupport_card_le {n : ℕ} (S : Finset (Fin n)) (C : Circuit) (w : ℕ) :
    (restrictedSupport S C w).card ≤ (support (n := n) C w).card := by
  have hsub : (restrictedSupport S C w).image Subtype.val ⊆ support C w := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hq).2
  calc
    (restrictedSupport S C w).card = ((restrictedSupport S C w).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (support (n := n) C w).card := Finset.card_le_card hsub

lemma count_or_components {n : ℕ} (C : Circuit) (hG : good C)
    (S : Finset (Fin n)) (F : Finset ℕ)
    (hFt : ∀ w ∈ F, w < n + C.size)
    (hneg : ∀ w ∈ F, value C (fun p => decide (p ∉ S)) w = false) :
    S.card ≤ (ownedOr C S).card +
      Nat.card (PEqualNP.Outside.L_meta_4970.Components.familyGraph
        (restrictedSupport S C) F).ConnectedComponent := by
  classical
  let y : Fin n → Bool := fun p => decide (p ∉ S)
  let K := ownedOr C S
  have hstep : ∀ w, value C y w = false →
      2 ≤ (restrictedSupport S C w).card → ∃ P : Finset ℕ,
      P.card ≤ 1 + (if w ∈ K then 1 else 0) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, value C y r = false) ∧
      restrictedSupport S C w ⊆ P.biUnion (restrictedSupport S C) := by
    intro w hw hlarge
    have hlarge' : 2 ≤ (support (n := n) C w).card :=
      hlarge.trans (restrictedSupport_card_le S C w)
    have hreal := support_gate C w hlarge'
    have hsub : support (n := n) C w ⊆ S := by
      intro p hp
      by_contra hpS
      have hpt := (mem_support C w p).mp hp
      have hmono := value_mono C hG (fun q => decide (q = p)) y (by
        intro q hq
        have hqp : q = p := of_decide_eq_true hq
        subst q
        simp [y, hpS]) w hpt
      rw [hw] at hmono
      exact Bool.false_ne_true hmono
    have howned : w ∈ owned C S := Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr hreal, hsub, hlarge'⟩
    have hmem : w ∈ K ↔ orFlag n C w = true := by
      simp only [K, ownedOr, Finset.mem_filter, howned, true_and]
    obtain ⟨P, hPc, hPt, hPn, hPs⟩ := split_false C hG y w hreal.1 hreal.2 hw
    refine ⟨P, by simpa only [hmem] using hPc, hPt, hPn, ?_⟩
    intro p hp
    obtain ⟨r, hr, hpr⟩ := hPs p.val (Finset.mem_filter.mp hp).2
    exact Finset.mem_biUnion.mpr
      ⟨r, hr, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpr⟩⟩
  have h := PEqualNP.Outside.L_meta_4970.Components.frontier_component_bound
    (restrictedSupport S C) (fun w => value C y w = false) K hstep
    (n + C.size) F hFt hneg
  have hS : Nat.card S = S.card := by simp
  rw [hS] at h
  have hK := Finset.card_filter_le K (fun w => w < n + C.size)
  change S.card ≤ K.card + _
  omega

lemma pure_support_eq {n : ℕ} (C : Circuit) (w : ℕ) (Q : Finset (Fin n))
    (hpure : ∀ x : Fin n → Bool, value C x w = decide (∃ p ∈ Q, x p = true)) :
    support (n := n) C w = Q := by
  ext p
  rw [mem_support, hpure]
  simp

lemma sum_count_or_components {n : ℕ} {ι : Type*} [DecidableEq ι]
    (C : Circuit) (hG : good C) (I : Finset ι)
    (S : ι → Finset (Fin n)) (F : ι → Finset ℕ)
    (hFt : ∀ i ∈ I, ∀ w ∈ F i, w < n + C.size)
    (hneg : ∀ i ∈ I, ∀ w ∈ F i,
      value C (fun p => decide (p ∉ S i)) w = false)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ∑ i ∈ I, (S i).card ≤
      ((Finset.Ico n (n + C.size)).filter fun w => orFlag n C w).card +
      ∑ i ∈ I, Nat.card (PEqualNP.Outside.L_meta_4970.Components.familyGraph
        (restrictedSupport (S i) C) (F i)).ConnectedComponent := by
  classical
  have hc := Finset.sum_le_sum (fun i hi => count_or_components C hG (S i) (F i)
    (hFt i hi) (hneg i hi))
  have hd : (I : Set ι).PairwiseDisjoint (fun i => ownedOr C (S i)) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro w hwi hwj
    have hsi := (Finset.mem_filter.mp (Finset.mem_filter.mp hwi).1).2
    have hsj := (Finset.mem_filter.mp (Finset.mem_filter.mp hwj).1).2
    have hcard := Finset.card_le_card (Finset.subset_inter hsi.1 hsj.1)
    have hsep' := hsep i hi j hj hij
    omega
  have hs : (I.biUnion fun i => ownedOr C (S i)) ⊆
      (Finset.Ico n (n + C.size)).filter (fun w => orFlag n C w) := by
    intro w hw
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨howned, hor⟩ := Finset.mem_filter.mp hwi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp howned).1, hor⟩
  rw [Finset.sum_add_distrib, ← Finset.card_biUnion hd] at hc
  exact hc.trans (Nat.add_le_add_right (Finset.card_le_card hs) _)

end PEqualNP.Outside.L_meta_4970.OrCount


namespace PEqualNP.Outside.L_meta_4970

lemma right_stars_inter_card_le_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} (haa' : a ≠ a') (Q Q' : Finset (Fin l))
    (hQ : ∀ b ∈ Q, (a, b) ∈ E) (hQ' : ∀ b ∈ Q', (a', b) ∈ E) :
    (Q ∩ Q').card ≤ 1 := by
  by_contra hlarge
  obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp (by omega : 1 < (Q ∩ Q').card)
  obtain ⟨hbQ, hbQ'⟩ := Finset.mem_inter.mp hb
  obtain ⟨hb'Q, hb'Q'⟩ := Finset.mem_inter.mp hb'
  exact hC4 a a' b b' haa' hbb' ⟨hQ b hbQ, hQ b' hb'Q, hQ' b hbQ', hQ' b' hb'Q'⟩

lemma left_stars_inter_card_le_one {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {b b' : Fin l} (hbb' : b ≠ b') (P P' : Finset (Fin p))
    (hP : ∀ a ∈ P, (a, b) ∈ E) (hP' : ∀ a ∈ P', (a, b') ∈ E) :
    (P ∩ P').card ≤ 1 := by
  by_contra hlarge
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp (by omega : 1 < (P ∩ P').card)
  obtain ⟨haP, haP'⟩ := Finset.mem_inter.mp ha
  obtain ⟨ha'P, ha'P'⟩ := Finset.mem_inter.mp ha'
  exact hC4 a a' b b' haa' hbb' ⟨hP a haP, hP' a haP', hP a' ha'P, hP' a' ha'P'⟩

def starLeafFamily {p l : ℕ} (Q : Fin p → Finset (Fin l))
    (P : Fin l → Finset (Fin p)) : Fin p ⊕ Fin l → Finset (Fin (p + l))
  | .inl a => (Q a).image (Fin.natAdd p)
  | .inr b => (P b).image (Fin.castAdd l)

lemma starLeafFamily_separated {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (Q : Fin p → Finset (Fin l)) (P : Fin l → Finset (Fin p))
    (hQ : ∀ a b, b ∈ Q a → (a, b) ∈ E)
    (hP : ∀ b a, a ∈ P b → (a, b) ∈ E) :
    ∀ c d, c ≠ d → (starLeafFamily Q P c ∩ starLeafFamily Q P d).card ≤ 1 := by
  have hinjR : Function.Injective (Fin.natAdd p : Fin l → Fin (p + l)) := by
    intro a b h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa using hv
  have hinjL : Function.Injective (Fin.castAdd l : Fin p → Fin (p + l)) := by
    intro a b h
    exact Fin.castAdd_inj.mp h
  have hcross : ∀ (a : Fin p) (b : Fin l),
      Disjoint ((Q a).image (Fin.natAdd p)) ((P b).image (Fin.castAdd l)) := by
    intro a b
    apply Finset.disjoint_left.mpr
    intro i hiR hiL
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hiR
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hiL
    have heq := congrArg Fin.val (hv.trans hu.symm)
    have huLt := u.isLt
    simp only [Fin.val_natAdd, Fin.val_castAdd] at heq
    omega
  intro c d hcd
  cases c with
  | inl a =>
    cases d with
    | inl a' =>
      change ((Q a).image (Fin.natAdd p) ∩ (Q a').image (Fin.natAdd p)).card ≤ 1
      rw [← Finset.image_inter _ _ hinjR, Finset.card_image_of_injective _ hinjR]
      exact right_stars_inter_card_le_one E hC4 (fun h => hcd (congrArg Sum.inl h))
        (Q a) (Q a') (hQ a) (hQ a')
    | inr b =>
      change ((Q a).image (Fin.natAdd p) ∩ (P b).image (Fin.castAdd l)).card ≤ 1
      rw [Finset.disjoint_iff_inter_eq_empty.mp (hcross a b)]
      simp
  | inr b =>
    cases d with
    | inl a =>
      change ((P b).image (Fin.castAdd l) ∩ (Q a).image (Fin.natAdd p)).card ≤ 1
      rw [Finset.disjoint_iff_inter_eq_empty.mp (hcross a b).symm]
      simp
    | inr b' =>
      change ((P b).image (Fin.castAdd l) ∩ (P b').image (Fin.castAdd l)).card ≤ 1
      rw [← Finset.image_inter _ _ hinjL, Finset.card_image_of_injective _ hinjL]
      exact left_stars_inter_card_le_one E hC4 (fun h => hcd (congrArg Sum.inr h))
        (P b) (P b') (hP b) (hP b')

lemma star_families_from_witnesses {p l : ℕ} (E : Finset (Fin p × Fin l))
    (J : Finset ℕ) (f : ℕ → (Fin (p + l) → Bool) → Bool)
    (hwitness : ∀ a b, (a, b) ∈ E →
      (∃ j ∈ J, ∃ Q : Finset (Fin l), 2 ≤ Q.card ∧ b ∈ Q ∧
        (∀ b' ∈ Q, (a, b') ∈ E) ∧
        ∀ x, f j x = decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨
      (∃ j ∈ J, ∃ P : Finset (Fin p), 2 ≤ P.card ∧ a ∈ P ∧
        (∀ a' ∈ P, (a', b) ∈ E) ∧
        ∀ x, f j x = decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))) :
    ∃ (Q : Fin p → Finset (Fin l)) (P : Fin l → Finset (Fin p))
      (F : Fin p ⊕ Fin l → Finset ℕ),
      (∀ a b, b ∈ Q a → (a, b) ∈ E) ∧
      (∀ b a, a ∈ P b → (a, b) ∈ E) ∧
      (∀ a b, (a, b) ∈ E → b ∈ Q a ∨ a ∈ P b) ∧
      (∀ c, F c ⊆ J) ∧
      (∀ c j, j ∈ F c →
        f j (fun u => decide (u ∉ starLeafFamily Q P c)) = false) ∧
      (∀ c u, u ∈ starLeafFamily Q P c →
        ∃ j ∈ F c, f j (fun v => decide (v = u)) = true) := by
  classical
  let R := fun a : Fin p => J.filter fun j =>
    ∃ Q : Finset (Fin l), 2 ≤ Q.card ∧ (∀ b ∈ Q, (a, b) ∈ E) ∧
      ∀ x, f j x = decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)
  let L := fun b : Fin l => J.filter fun j =>
    ∃ P : Finset (Fin p), 2 ≤ P.card ∧ (∀ a ∈ P, (a, b) ∈ E) ∧
      ∀ x, f j x = decide (∃ a ∈ P, x (Fin.castAdd l a) = true)
  let Q := fun a : Fin p => Finset.univ.filter fun b : Fin l =>
    ∃ j ∈ R a, f j (fun v => decide (v = Fin.natAdd p b)) = true
  let P := fun b : Fin l => Finset.univ.filter fun a : Fin p =>
    ∃ j ∈ L b, f j (fun v => decide (v = Fin.castAdd l a)) = true
  let F : Fin p ⊕ Fin l → Finset ℕ := Sum.elim R L
  have hQa : ∀ a b, b ∈ Q a → (a, b) ∈ E := by
    intro a b hb
    obtain ⟨j, hj, hjb⟩ := (Finset.mem_filter.mp hb).2
    obtain ⟨Qj, _, hQj, hfun⟩ := (Finset.mem_filter.mp hj).2
    have hbQ : b ∈ Qj := by
      have ht := (hfun _).symm.trans hjb
      simpa using ht
    exact hQj b hbQ
  have hPb : ∀ b a, a ∈ P b → (a, b) ∈ E := by
    intro b a ha
    obtain ⟨j, hj, hja⟩ := (Finset.mem_filter.mp ha).2
    obtain ⟨Pj, _, hPj, hfun⟩ := (Finset.mem_filter.mp hj).2
    have haP : a ∈ Pj := by
      have ht := (hfun _).symm.trans hja
      simpa using ht
    exact hPj a haP
  refine ⟨Q, P, F, hQa, hPb, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    rcases hwitness a b hab with ⟨j, hj, Qj, hcard, hb, hadj, hfun⟩ |
      ⟨j, hj, Pj, hcard, ha, hadj, hfun⟩
    · apply Or.inl
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hj, Qj, hcard, hadj, hfun⟩
      · rw [hfun]
        simpa using hb
    · apply Or.inr
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hj, Pj, hcard, hadj, hfun⟩
      · rw [hfun]
        simpa using ha
  · intro c j hj
    cases c <;> exact (Finset.mem_filter.mp hj).1
  · intro c j hj
    cases c with
    | inl a =>
      obtain ⟨Qj, _, _, hfun⟩ := (Finset.mem_filter.mp hj).2
      rw [hfun]
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨b, hb, hnot⟩ := of_decide_eq_true ht
      have hbQ : b ∈ Q a := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj, ?_⟩
        rw [hfun]
        simpa using hb
      exact (of_decide_eq_true hnot) (Finset.mem_image.mpr ⟨b, hbQ, rfl⟩)
    | inr b =>
      obtain ⟨Pj, _, _, hfun⟩ := (Finset.mem_filter.mp hj).2
      rw [hfun]
      apply Bool.eq_false_iff.mpr
      intro ht
      obtain ⟨a, ha, hnot⟩ := of_decide_eq_true ht
      have haP : a ∈ P b := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hj, ?_⟩
        rw [hfun]
        simpa using ha
      exact (of_decide_eq_true hnot) (Finset.mem_image.mpr ⟨a, haP, rfl⟩)
  · intro c u hu
    cases c with
    | inl a =>
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hu
      exact (Finset.mem_filter.mp hb).2
    | inr b =>
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hu
      exact (Finset.mem_filter.mp ha).2

end PEqualNP.Outside.L_meta_4970

namespace PEqualNP.Outside.L_meta_4970

def starEdgeFamily {p l : ℕ} (Q : Fin p → Finset (Fin l))
    (P : Fin l → Finset (Fin p)) : Fin p ⊕ Fin l → Finset (Fin p × Fin l)
  | .inl a => (Q a).image (fun b => (a, b))
  | .inr b => (P b).image (fun a => (a, b))

lemma starEdgeFamily_card {p l : ℕ} (Q : Fin p → Finset (Fin l))
    (P : Fin l → Finset (Fin p)) (c : Fin p ⊕ Fin l) :
    (starEdgeFamily Q P c).card = (starLeafFamily Q P c).card := by
  cases c with
  | inl a =>
    have hpair : Function.Injective (fun b : Fin l => (a, b)) := by
      intro b b' h
      exact congrArg Prod.snd h
    have hinj : Function.Injective (Fin.natAdd p : Fin l → Fin (p + l)) := by
      intro b b' h
      apply Fin.ext
      have hv := congrArg Fin.val h
      simpa using hv
    simp only [starEdgeFamily, starLeafFamily,
      Finset.card_image_of_injective _ hpair, Finset.card_image_of_injective _ hinj]
  | inr b =>
    have hpair : Function.Injective (fun a : Fin p => (a, b)) := by
      intro a a' h
      exact congrArg Prod.fst h
    have hinj : Function.Injective (Fin.castAdd l : Fin p → Fin (p + l)) := by
      intro a a' h
      exact Fin.castAdd_inj.mp h
    simp only [starEdgeFamily, starLeafFamily,
      Finset.card_image_of_injective _ hpair, Finset.card_image_of_injective _ hinj]

lemma edge_card_le_star_leaves {p l : ℕ} (E : Finset (Fin p × Fin l))
    (Q : Fin p → Finset (Fin l)) (P : Fin l → Finset (Fin p))
    (hcover : ∀ a b, (a, b) ∈ E → b ∈ Q a ∨ a ∈ P b) :
    E.card ≤ ∑ c : Fin p ⊕ Fin l, (starLeafFamily Q P c).card := by
  have hsub : E ⊆ Finset.univ.biUnion (starEdgeFamily Q P) := by
    rintro ⟨a, b⟩ hab
    rcases hcover a b hab with hb | ha
    · exact Finset.mem_biUnion.mpr ⟨Sum.inl a, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
    · exact Finset.mem_biUnion.mpr ⟨Sum.inr b, Finset.mem_univ _,
        Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
  calc
    E.card ≤ (Finset.univ.biUnion (starEdgeFamily Q P)).card := Finset.card_le_card hsub
    _ ≤ ∑ c : Fin p ⊕ Fin l, (starEdgeFamily Q P c).card := Finset.card_biUnion_le
    _ = ∑ c : Fin p ⊕ Fin l, (starLeafFamily Q P c).card := by
      apply Finset.sum_congr rfl
      intro c _
      exact starEdgeFamily_card Q P c

end PEqualNP.Outside.L_meta_4970

namespace PEqualNP.Outside.L_meta_4970.OrCount

open PEqualNP.CircuitLowerBounds

lemma sum_count_or_components_owned {n : ℕ} {ι : Type*} [DecidableEq ι]
    (C : Circuit) (hG : good C) (I : Finset ι)
    (S : ι → Finset (Fin n)) (F : ι → Finset ℕ)
    (hFt : ∀ i ∈ I, ∀ w ∈ F i, w < n + C.size)
    (hneg : ∀ i ∈ I, ∀ w ∈ F i,
      value C (fun p => decide (p ∉ S i)) w = false)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (S i ∩ S j).card ≤ 1) :
    ∑ i ∈ I, (S i).card ≤
      (I.biUnion fun i => ownedOr C (S i)).card +
      ∑ i ∈ I, Nat.card (PEqualNP.Outside.L_meta_4970.Components.familyGraph
        (restrictedSupport (S i) C) (F i)).ConnectedComponent := by
  classical
  have hc := Finset.sum_le_sum (fun i hi => count_or_components C hG (S i) (F i)
    (hFt i hi) (hneg i hi))
  have hd : (I : Set ι).PairwiseDisjoint (fun i => ownedOr C (S i)) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro w hwi hwj
    have hsi := (Finset.mem_filter.mp (Finset.mem_filter.mp hwi).1).2
    have hsj := (Finset.mem_filter.mp (Finset.mem_filter.mp hwj).1).2
    have hcard := Finset.card_le_card (Finset.subset_inter hsi.1 hsj.1)
    have hsep' := hsep i hi j hj hij
    omega
  rwa [Finset.sum_add_distrib, ← Finset.card_biUnion hd] at hc

lemma edge_component_ledger_full {p l : ℕ} (E : Finset (Fin p × Fin l))
    (C : Circuit) (hG : good C)
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (J : Finset ℕ) (hJ : ∀ w ∈ J, w < p + l + C.size)
    (hwitness : ∀ a b, (a, b) ∈ E →
      (∃ w ∈ J, ∃ Q : Finset (Fin l), 2 ≤ Q.card ∧ b ∈ Q ∧
        (∀ b' ∈ Q, (a, b') ∈ E) ∧
        ∀ x, value C x w = decide (∃ b' ∈ Q, x (Fin.natAdd p b') = true)) ∨
      (∃ w ∈ J, ∃ P : Finset (Fin p), 2 ≤ P.card ∧ a ∈ P ∧
        (∀ a' ∈ P, (a', b) ∈ E) ∧
        ∀ x, value C x w = decide (∃ a' ∈ P, x (Fin.castAdd l a') = true))) :
    ∃ (Q : Fin p → Finset (Fin l)) (P : Fin l → Finset (Fin p))
      (F : Fin p ⊕ Fin l → Finset ℕ),
      (∀ a b, b ∈ Q a → (a, b) ∈ E) ∧
      (∀ b a, a ∈ P b → (a, b) ∈ E) ∧
      (∀ a b, (a, b) ∈ E → b ∈ Q a ∨ a ∈ P b) ∧
      (∀ c, F c ⊆ J) ∧
      (∀ c w, w ∈ F c →
        value C (fun u => decide (u ∉ starLeafFamily Q P c)) w = false) ∧
      (∀ c u, u ∈ starLeafFamily Q P c →
        ∃ w ∈ F c, value C (fun v => decide (v = u)) w = true) ∧
      E.card ≤ (∑ c : Fin p ⊕ Fin l, (starLeafFamily Q P c).card) ∧
      (∑ c : Fin p ⊕ Fin l, (starLeafFamily Q P c).card) ≤
        (Finset.univ.biUnion fun c : Fin p ⊕ Fin l =>
        ownedOr C (starLeafFamily Q P c)).card +
        ∑ c : Fin p ⊕ Fin l, Nat.card
          (PEqualNP.Outside.L_meta_4970.Components.familyGraph
            (restrictedSupport (starLeafFamily Q P c) C) (F c)).ConnectedComponent := by
  classical
  obtain ⟨Q, P, F, hQ, hP, hcover, hF, hneg, hpos⟩ :=
    star_families_from_witnesses E J (fun w x => value C x w) hwitness
  refine ⟨Q, P, F, hQ, hP, hcover, hF, hneg, hpos,
    edge_card_le_star_leaves E Q P hcover, ?_⟩
  have hsum := sum_count_or_components_owned C hG Finset.univ
    (starLeafFamily Q P) F (fun c _ w hw => hJ w (hF c hw))
    (fun c _ w hw => hneg c w hw)
    (fun c _ d _ hcd => starLeafFamily_separated E hC4 Q P hQ hP c d hcd)
  exact hsum

lemma owned_union_card_le_size {n : ℕ} {ι : Type*} [DecidableEq ι]
    (C : Circuit) (I : Finset ι) (S : ι → Finset (Fin n)) :
    (I.biUnion fun i => ownedOr C (S i)).card ≤ C.size := by
  have hsub : (I.biUnion fun i => ownedOr C (S i)) ⊆ Finset.Ico n (n + C.size) := by
    intro w hw
    obtain ⟨i, _, hwi⟩ := Finset.mem_biUnion.mp hw
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hwi).1).1
  simpa using Finset.card_le_card hsub

lemma finish_with_overlap (m s k c v t : ℕ) (hms : m ≤ s) (hsc : s ≤ k + c)
    (hkt : k ≤ t) (hres : c + v ≤ (t - k) + (s - m) + 1) : m + v ≤ t + 1 := by
  omega

end PEqualNP.Outside.L_meta_4970.OrCount
