import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2089

lemma maximal_pair_cover {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (R : α → β → Prop)
    (A U : Finset α) (B V : Finset β)
    (maxA : ∀ a, a ∉ A → ∃ b ∈ B, R a b)
    (maxB : ∀ b, b ∉ B → ∃ a ∈ A, R a b)
    (disjA : Disjoint U A) (disjB : Disjoint V B)
    (cover : ∀ a b, R a b → a ∈ U ∨ b ∈ V) :
    U = Aᶜ ∧ V = Bᶜ := by
  constructor
  · ext a
    simp only [Finset.mem_compl]
    constructor
    · intro ha hA
      exact Finset.disjoint_left.mp disjA ha hA
    · intro ha
      obtain ⟨b, hb, hab⟩ := maxA a ha
      rcases cover a b hab with hu | hv
      · exact hu
      · exact False.elim (Finset.disjoint_left.mp disjB hv hb)
  · ext b
    simp only [Finset.mem_compl]
    constructor
    · intro hb hB
      exact Finset.disjoint_left.mp disjB hb hB
    · intro hb
      obtain ⟨a, ha, hab⟩ := maxB b hb
      rcases cover a b hab with hu | hv
      · exact False.elim (Finset.disjoint_left.mp disjA hu ha)
      · exact hv

end PEqualNP.Outside.L_meta_2089

namespace PEqualNP.Outside.L_meta_2089.Structural

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


lemma weighted_cut {X : Type} (V : X → ℕ → Bool) (x : X) (G O : Finset ℕ)
    (hstep : ∀ w ∈ G, ∃ P : Finset ℕ,
      P.card ≤ 1 + (if w ∈ O then 1 else 0) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, V x r = false) ∧
      ∀ y, (∀ r ∈ P, V y r = false) → V y w = false)
    (t : ℕ) (F : Finset ℕ) (hF : ∀ w ∈ F, w ∈ G → w < t)
    (hFx : ∀ w ∈ F, V x w = false) :
    ∃ B : Finset ℕ, Disjoint B G ∧
      B.card ≤ F.card + (O.filter (· < t)).card ∧
      (∀ r ∈ B, V x r = false) ∧
      ∀ y, (∀ r ∈ B, V y r = false) → ∀ w ∈ F, V y w = false := by
  classical
  induction t generalizing F with
  | zero =>
    refine ⟨F, Finset.disjoint_left.mpr ?_, Nat.le_add_right .., hFx, ?_⟩
    · intro w hw hg
      have := hF w hw hg
      omega
    · exact fun _ h => h
  | succ t ih =>
    by_cases hex : t ∈ F ∧ t ∈ G
    · obtain ⟨P, hPcard, hP, hPx, hp⟩ := hstep t hex.2
      let F' := F.erase t ∪ P
      have hF' : ∀ w ∈ F', w ∈ G → w < t := by
        intro w hw hg
        rcases Finset.mem_union.mp hw with hw | hw
        · have hne := (Finset.mem_erase.mp hw).1
          have hlt := hF w (Finset.mem_erase.mp hw).2 hg
          omega
        · exact hP w hw
      have hF'x : ∀ w ∈ F', V x w = false := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hFx w (Finset.mem_erase.mp hw).2
        · exact hPx w hw
      obtain ⟨B, hd, hc, hBx, hi⟩ := ih F' hF' hF'x
      have hsize : F'.card ≤ F.card + (if t ∈ O then 1 else 0) := by
        have hu := Finset.card_union_le (F.erase t) P
        have he := Finset.card_erase_add_one hex.1
        change F'.card ≤ _ at hu
        omega
      have hfilter : (O.filter (· < t + 1)).card =
          (O.filter (· < t)).card + (if t ∈ O then 1 else 0) := by
        by_cases ht : t ∈ O
        · have heq : O.filter (· < t + 1) = insert t (O.filter (· < t)) := by
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
          rw [heq, Finset.card_insert_of_notMem (by simp), ite_eq_left ht]
        · have heq : O.filter (· < t + 1) = O.filter (· < t) := by
            ext w
            simp only [Finset.mem_filter]
            constructor
            · rintro ⟨hw, hlt⟩
              refine ⟨hw, ?_⟩
              have : w ≠ t := fun h => ht (h ▸ hw)
              omega
            · rintro ⟨hw, hlt⟩
              exact ⟨hw, by omega⟩
          rw [heq, ite_eq_right ht, add_zero]
      refine ⟨B, hd, ?_, hBx, ?_⟩
      · rw [hfilter]
        omega
      · intro y hy w hw
        by_cases h : w = t
        · subst w
          exact hp y fun r hr => hi y hy r (Finset.mem_union_right _ hr)
        · exact hi y hy w (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hw⟩))
    · have hF' : ∀ w ∈ F, w ∈ G → w < t := by
        intro w hw hg
        have hne : w ≠ t := fun e => hex ⟨e ▸ hw, e ▸ hg⟩
        have hlt := hF w hw hg
        omega
      obtain ⟨B, hd, hc, hBx, hi⟩ := ih F hF' hFx
      have hle : (O.filter (· < t)).card ≤ (O.filter (· < t + 1)).card :=
        Finset.card_le_card fun w hw =>
          Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,
            by have := (Finset.mem_filter.mp hw).2; omega⟩
      exact ⟨B, hd, by omega, hBx, hi⟩

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
    value C x w = (C.gates[w - n]'(by unfold Circuit.size at hw; omega)).op.eval
      ((C.gates[w - n]'(by unfold Circuit.size at hw; omega)).inputs.map
        fun r => if r < w then value C x r else false) := by
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

def orCharge : GateOp → ℕ
  | GateOp.or => 1
  | _ => 0

lemma gate_false_step {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (x : Fin n → Bool) (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size)
    (hoff : value C x w = false) :
    ∃ P : Finset ℕ, P.card ≤ 1 + orCharge (gateAt C (w - n)).op ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, value C x r = false) ∧
      ∀ y : Fin n → Bool, (∀ r ∈ P, value C y r = false) → value C y w = false := by
  classical
  have hj : w - n < C.gates.length := by unfold Circuit.size at hw; omega
  let g := C.gates[w - n]
  have hgate : gateAt C (w - n) = g := by
    exact List.getD_eq_getElem _ _ hj
  have formula (z : Fin n → Bool) : value C z w =
      g.op.eval (g.inputs.map fun r => if r < w then value C z r else false) :=
    gate_value C z w hn hw
  obtain ⟨hop, hlen⟩ := hm g (List.getElem_mem _)
  change g.op = GateOp.and ∨ g.op = GateOp.or at hop
  rcases hop with hop | hop
  · have hz := hoff
    rw [formula, hop] at hz
    simp only [GateOp.eval, List.all_eq_false, id_eq] at hz
    obtain ⟨b, hb, hbfalse⟩ := hz
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    by_cases hback : r < w
    · refine ⟨{r}, ?_, ?_, ?_, ?_⟩
      · simp [hgate, hop, orCharge]
      · intro q hq
        have hqr := Finset.mem_singleton.mp hq
        simpa [hqr] using hback
      · intro q hq
        have hqr := Finset.mem_singleton.mp hq
        subst q
        simpa [hback] using hbfalse
      · intro y hy
        rw [formula, hop]
        apply List.all_eq_false.mpr
        exact ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, by simp [hback, hy r (by simp)]⟩
    · refine ⟨∅, by simp, by simp, by simp, ?_⟩
      intro y _
      rw [formula, hop]
      apply List.all_eq_false.mpr
      exact ⟨_, List.mem_map.mpr ⟨r, hr, rfl⟩, by simp [hback]⟩
  · let P := g.inputs.toFinset.filter (· < w)
    have hp (r : ℕ) (hr : r ∈ P) : r ∈ g.inputs ∧ r < w := by
      simpa only [P, Finset.mem_filter, List.mem_toFinset] using hr
    have allfalse : ∀ r ∈ g.inputs, (if r < w then value C x r else false) = false := by
      rw [formula, hop] at hoff
      simp only [GateOp.eval, List.any_eq_false, List.mem_map, id_eq] at hoff
      intro r hr
      simpa using hoff _ ⟨r, hr, rfl⟩
    refine ⟨P, ?_, fun r hr => (hp r hr).2, ?_, ?_⟩
    · have hcard := (Finset.card_filter_le g.inputs.toFinset (· < w)).trans
        (List.toFinset_card_le g.inputs)
      simp only [hgate, hop, orCharge]
      exact hcard.trans hlen
    · intro r hr
      simpa [(hp r hr).2] using allfalse r (hp r hr).1
    · intro y hy
      rw [formula, hop]
      apply List.any_eq_false.mpr
      intro b hb
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
      by_cases hback : r < w
      · simp [hback, hy r (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hr, hback⟩)]
      · simp [hback]

lemma false_certificate {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (x : Fin n → Bool) (a : ℕ) (hoff : value C x a = false) :
    ∃ I : Finset ℕ, ∃ B : Finset (Fin n), B.card ≤ I.card + 1 ∧
      (∀ i ∈ I, n ≤ i ∧ i ≤ a ∧ (gateAt C (i - n)).op = GateOp.or ∧
        value C x i = false) ∧
      (∀ i ∈ B, x i = false) ∧
      ∀ y : Fin n → Bool, (∀ i ∈ B, y i = false) → value C y a = false := by
  classical
  let G := (Finset.Ico n (n + C.size)).filter (fun w => value C x w = false)
  let O := G.filter (fun w => (gateAt C (w - n)).op = GateOp.or)
  have ginfo (w : ℕ) (hw : w ∈ G) : n ≤ w ∧ w < n + C.size ∧ value C x w = false := by
    simpa only [G, Finset.mem_filter, Finset.mem_Ico, and_assoc] using hw
  have step (w : ℕ) (hw : w ∈ G) : ∃ P : Finset ℕ,
      P.card ≤ 1 + (if w ∈ O then 1 else 0) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, value C x r = false) ∧
      ∀ y : Fin n → Bool, (∀ r ∈ P, value C y r = false) → value C y w = false := by
    obtain ⟨hn, hlt, hfalse⟩ := ginfo w hw
    obtain ⟨P, hcard, hback, hPx, hpass⟩ := gate_false_step C hm x w hn hlt hfalse
    have hweight : orCharge (gateAt C (w - n)).op = (if w ∈ O then 1 else 0) := by
      cases h : (gateAt C (w - n)).op <;> simp [orCharge, O, hw, h]
    exact ⟨P, by simpa only [hweight] using hcard, hback, hPx, hpass⟩
  obtain ⟨B, hdisj, hcard, hBx, hpass⟩ := weighted_cut (fun y w => value C y w) x G O step
    (a + 1) {a} (by intro w hw _; obtain rfl := Finset.mem_singleton.mp hw; omega)
    (by intro w hw; obtain rfl := Finset.mem_singleton.mp hw; exact hoff)
  let I := O.filter (· < a + 1)
  let T : Finset (Fin n) := Finset.univ.filter (fun i => i.val ∈ B)
  have himage : T.image Fin.val ⊆ B := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp hi).2
  have hTcard : T.card ≤ B.card := by
    rw [← Finset.card_image_of_injective T Fin.val_injective]
    exact Finset.card_le_card himage
  refine ⟨I, T, ?_, ?_, ?_, ?_⟩
  · have hBcard : B.card ≤ I.card + 1 := by
      simpa only [Finset.card_singleton, I, Nat.add_comm] using hcard
    exact hTcard.trans hBcard
  · intro i hi
    obtain ⟨hO, hia⟩ := Finset.mem_filter.mp hi
    obtain ⟨hG, hop⟩ := Finset.mem_filter.mp hO
    obtain ⟨hn, _, hx⟩ := ginfo i hG
    exact ⟨hn, by omega, hop, hx⟩
  · intro i hi
    have hb := (Finset.mem_filter.mp hi).2
    exact (input_value C x i).symm.trans (hBx i hb)
  · intro y hy
    apply hpass y ?_ a (by simp)
    intro w hw
    by_cases hn : w < n
    · let i : Fin n := ⟨w, hn⟩
      change value C y i = false
      rw [input_value]
      exact hy i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩)
    · by_cases htotal : w < n + C.size
      · have hG : w ∈ G := Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨by omega, htotal⟩, hBx w hw⟩
        exact (Finset.disjoint_left.mp hdisj hw hG).elim
      · exact missing_value C y w (by omega)

end PEqualNP.Outside.L_meta_2089.Structural

namespace PEqualNP.Outside.L_meta_2089

def delta : Finset (Fin 13) := {0, 1, 3, 9}

def incidence (p l : Fin 13) : Prop := ∃ d ∈ delta, p = l + d

lemma separated_points : ∀ p q : Fin 13, p ≠ q →
    ∃ l : Fin 13, ¬incidence p l ∧ incidence q l := by
  unfold incidence delta
  decide

lemma singleton_maximal (p : Fin 13) : ∀ q ∉ ({p} : Finset (Fin 13)),
    ∃ l : Fin 13, (∀ x ∈ ({p} : Finset (Fin 13)), ¬incidence x l) ∧
      incidence q l := by
  intro q hq
  obtain ⟨l, hl, hql⟩ := separated_points p q (by simpa [eq_comm] using hq)
  refine ⟨l, ?_, hql⟩
  intro x hx
  obtain rfl := Finset.mem_singleton.mp hx
  exact hl

lemma incidence_refl (p : Fin 13) : incidence p p := by
  exact ⟨0, by simp [delta], by simp⟩

def pairInput (p l : Fin 13) (i : Fin 26) : Bool :=
  decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)

def cutInput (A : Finset (Fin 13)) (i : Fin 26) : Bool :=
  decide ((∃ p ∈ A, i = Fin.castAdd 13 p) ∨
    ∃ l, i = Fin.natAdd 13 l ∧ ∀ p ∈ A, ¬∃ d ∈ delta, p = l + d)

def isClosed (A : Finset (Fin 13)) : Prop :=
  ∀ p ∉ A, ∃ l, (∀ q ∈ A, ¬incidence q l) ∧ incidence p l

def isDegenerate (A : Finset (Fin 13)) : Prop :=
  (∃ l, ∀ p ∈ A, incidence p l) ∨
    ∃ p, ∀ l, (∀ q ∈ A, ¬incidence q l) → incidence p l

lemma singleton_degenerate (p : Fin 13) : isDegenerate {p} := by
  left
  refine ⟨p, ?_⟩
  intro q hq
  obtain rfl := Finset.mem_singleton.mp hq
  exact incidence_refl _

lemma nonincident_pair_le_cut (p l : Fin 13) (h : ¬incidence p l) :
    ∀ i, pairInput p l i = true → cutInput {p} i = true := by
  intro i hi
  simp only [pairInput, decide_eq_true_eq] at hi
  simp only [cutInput, decide_eq_true_eq]
  rcases hi with hi | hi
  · exact Or.inl ⟨p, Finset.mem_singleton_self p, hi⟩
  · refine Or.inr ⟨l, hi, ?_⟩
    intro q hq
    obtain rfl := Finset.mem_singleton.mp hq
    exact h

lemma nonincident_pair_rejected (f : (Fin 26 → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → f a = true → f b = true)
    (hnegative : ∀ A, isClosed A → isDegenerate A → f (cutInput A) = false)
    (p l : Fin 13) (h : ¬incidence p l) : f (pairInput p l) = false := by
  apply Bool.eq_false_iff.mpr
  intro hp
  have hm := hmono _ _ (nonincident_pair_le_cut p l h) hp
  have hn := hnegative {p} (singleton_maximal p) (singleton_degenerate p)
  exact Bool.noConfusion (hm.symm.trans hn)

lemma empty_closed : isClosed ∅ := by
  intro p hp
  exact ⟨p, by simp, incidence_refl p⟩

lemma empty_degenerate : isDegenerate ∅ := by
  exact Or.inl ⟨0, by simp⟩

lemma univ_closed : isClosed Finset.univ := by
  intro p hp
  exact False.elim (hp (Finset.mem_univ p))

lemma univ_degenerate : isDegenerate Finset.univ := by
  right
  refine ⟨0, ?_⟩
  intro l hl
  exact False.elim (hl l (Finset.mem_univ l) (incidence_refl l))

lemma point_only_rejected (f : (Fin 26 → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → f a = true → f b = true)
    (hnegative : ∀ A, isClosed A → isDegenerate A → f (cutInput A) = false)
    (a : Fin 26 → Bool) (ha : ∀ i, a i = true → ∃ p : Fin 13, i = Fin.castAdd 13 p) :
    f a = false := by
  apply Bool.eq_false_iff.mpr
  intro hfa
  have hm : f (cutInput Finset.univ) = true := by
    apply hmono a _ _ hfa
    intro i hi
    obtain ⟨p, hp⟩ := ha i hi
    simp only [cutInput, decide_eq_true_eq]
    exact Or.inl ⟨p, Finset.mem_univ p, hp⟩
  have hn := hnegative Finset.univ univ_closed univ_degenerate
  exact Bool.noConfusion (hm.symm.trans hn)

lemma line_only_rejected (f : (Fin 26 → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → f a = true → f b = true)
    (hnegative : ∀ A, isClosed A → isDegenerate A → f (cutInput A) = false)
    (a : Fin 26 → Bool) (ha : ∀ i, a i = true → ∃ l : Fin 13, i = Fin.natAdd 13 l) :
    f a = false := by
  apply Bool.eq_false_iff.mpr
  intro hfa
  have hm : f (cutInput ∅) = true := by
    apply hmono a _ _ hfa
    intro i hi
    obtain ⟨l, hl⟩ := ha i hi
    simp only [cutInput, decide_eq_true_eq]
    exact Or.inr ⟨l, hl, by simp⟩
  have hn := hnegative ∅ empty_closed empty_degenerate
  exact Bool.noConfusion (hm.symm.trans hn)

lemma pair_truth_iff (f : (Fin 26 → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → f a = true → f b = true)
    (hnegative : ∀ A, isClosed A → isDegenerate A → f (cutInput A) = false)
    (hpositive : ∀ p l, incidence p l → f (pairInput p l) = true)
    (p l : Fin 13) : f (pairInput p l) = true ↔ incidence p l := by
  constructor
  · intro h
    by_contra hn
    have hz := nonincident_pair_rejected f hmono hnegative p l hn
    exact Bool.noConfusion (h.symm.trans hz)
  · exact hpositive p l

end PEqualNP.Outside.L_meta_2089

namespace PEqualNP.Outside.L_meta_2089.BadPairs.Cardinality

open PEqualNP.HeptadCover

def fibP (X : Finset (Fin 13 × Fin 13)) (P : Fin 13) : Finset (Fin 13 × Fin 13) :=
  X.filter (fun x => x.1 = P)

def tgtP (X : Finset (Fin 13 × Fin 13)) (P : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (fun Q => ∀ x ∈ fibP X P, Q ∈ singerLines3 x.2)

def suppP (X : Finset (Fin 13 × Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter (fun P => (fibP X P).Nonempty)

lemma g_nine : ∀ P : Fin 13,
    (Finset.univ.filter (fun l : Fin 13 => P ∉ singerLines3 l)).card ≤ 9 := by
  decide

lemma g_three : ∀ P Q : Fin 13,
    (Finset.univ.filter (fun l : Fin 13 => P ∉ singerLines3 l ∧ Q ∈ singerLines3 l)).card ≤ 3 := by
  decide

lemma g_one : ∀ Q1 Q2 : Fin 13, Q1 ≠ Q2 →
    (Finset.univ.filter (fun l : Fin 13 => Q1 ∈ singerLines3 l ∧ Q2 ∈ singerLines3 l)).card ≤ 1 := by
  decide

lemma g_four : ∀ l : Fin 13, (singerLines3 l).card = 4 := by decide

lemma g_line : ∀ Q1 Q2 : Fin 13, ∃ h : Fin 13, Q1 ∈ singerLines3 h ∧ Q2 ∈ singerLines3 h := by
  decide

lemma mem_fibP {X : Finset (Fin 13 × Fin 13)} {P : Fin 13} {x : Fin 13 × Fin 13} :
    x ∈ fibP X P ↔ x ∈ X ∧ x.1 = P := by
  unfold fibP; exact Finset.mem_filter

lemma mem_tgtP {X : Finset (Fin 13 × Fin 13)} {P Q : Fin 13} :
    Q ∈ tgtP X P ↔ ∀ x ∈ fibP X P, Q ∈ singerLines3 x.2 := by
  unfold tgtP; simp

lemma mem_suppP {X : Finset (Fin 13 × Fin 13)} {P : Fin 13} :
    P ∈ suppP X ↔ (fibP X P).Nonempty := by
  unfold suppP; simp

lemma fib_card_le (X : Finset (Fin 13 × Fin 13)) (P : Fin 13) (p : Fin 13 → Prop) [DecidablePred p]
    (h : ∀ x ∈ fibP X P, p x.2) :
    (fibP X P).card ≤ (Finset.univ.filter p).card := by
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro x hx
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x (Finset.mem_coe.mp hx)⟩)
  · intro x hx y hy hxy
    have hx' := (mem_fibP.mp (Finset.mem_coe.mp hx)).2
    have hy' := (mem_fibP.mp (Finset.mem_coe.mp hy)).2
    exact Prod.ext (hx'.trans hy'.symm) hxy

lemma w_le9 (X : Finset (Fin 13 × Fin 13)) (hX : ∀ x ∈ X, x.1 ∉ singerLines3 x.2) (P : Fin 13) :
    (fibP X P).card ≤ 9 := by
  refine le_trans (fib_card_le X P (fun l => P ∉ singerLines3 l) ?_) (g_nine P)
  intro x hx
  obtain ⟨hxX, hx1⟩ := mem_fibP.mp hx
  have := hX x hxX
  rw [hx1] at this
  exact this

lemma w_le3 (X : Finset (Fin 13 × Fin 13)) (hX : ∀ x ∈ X, x.1 ∉ singerLines3 x.2) (P Q : Fin 13)
    (hQ : Q ∈ tgtP X P) : (fibP X P).card ≤ 3 := by
  refine le_trans (fib_card_le X P (fun l => P ∉ singerLines3 l ∧ Q ∈ singerLines3 l) ?_) (g_three P Q)
  intro x hx
  obtain ⟨hxX, hx1⟩ := mem_fibP.mp hx
  have := hX x hxX
  rw [hx1] at this
  exact ⟨this, mem_tgtP.mp hQ x hx⟩

lemma w_le1 (X : Finset (Fin 13 × Fin 13)) (P Q1 Q2 : Fin 13) (h1 : Q1 ∈ tgtP X P)
    (h2 : Q2 ∈ tgtP X P) (hne : Q1 ≠ Q2) : (fibP X P).card ≤ 1 := by
  refine le_trans (fib_card_le X P (fun l => Q1 ∈ singerLines3 l ∧ Q2 ∈ singerLines3 l) ?_)
    (g_one Q1 Q2 hne)
  intro x hx
  exact ⟨mem_tgtP.mp h1 x hx, mem_tgtP.mp h2 x hx⟩

lemma tgt_sub (X : Finset (Fin 13 × Fin 13)) (P : Fin 13) (x : Fin 13 × Fin 13)
    (hx : x ∈ fibP X P) : tgtP X P ⊆ singerLines3 x.2 := by
  intro Q hQ; exact mem_tgtP.mp hQ x hx

lemma tgt_card (X : Finset (Fin 13 × Fin 13)) (P : Fin 13) (hP : P ∈ suppP X) :
    (tgtP X P).card ≤ 4 := by
  obtain ⟨x, hx⟩ := mem_suppP.mp hP
  have := Finset.card_le_card (tgt_sub X P x hx)
  rw [g_four] at this; exact this

lemma line_unique (Q1 Q2 l l' : Fin 13) (hne : Q1 ≠ Q2) (h1 : Q1 ∈ singerLines3 l)
    (h2 : Q2 ∈ singerLines3 l) (h1' : Q1 ∈ singerLines3 l') (h2' : Q2 ∈ singerLines3 l') :
    l = l' := by
  have := Finset.card_le_one.mp (g_one Q1 Q2 hne)
  exact this l (by simp [h1, h2]) l' (by simp [h1', h2'])

lemma cross (X Y : Finset (Fin 13 × Fin 13))
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x.1 ∈ singerLines3 y.2 ∨ y.1 ∈ singerLines3 x.2)
    (P Q : Fin 13) : Q ∈ tgtP X P ∨ P ∈ tgtP Y Q := by
  by_contra hcon
  rw [not_or, mem_tgtP, mem_tgtP] at hcon
  obtain ⟨h1, h2⟩ := hcon
  push Not at h1 h2
  obtain ⟨x, hx, hxQ⟩ := h1
  obtain ⟨y, hy, hyP⟩ := h2
  obtain ⟨hxX, hx1⟩ := mem_fibP.mp hx
  obtain ⟨hyY, hy1⟩ := mem_fibP.mp hy
  rcases hXY x hxX y hyY with h | h
  · rw [hx1] at h; exact hyP h
  · rw [hy1] at h; exact hxQ h

lemma not_self (X : Finset (Fin 13 × Fin 13)) (hX : ∀ x ∈ X, x.1 ∉ singerLines3 x.2) (P : Fin 13)
    (hP : P ∈ suppP X) : P ∉ tgtP X P := by
  intro h
  obtain ⟨x, hx⟩ := mem_suppP.mp hP
  obtain ⟨hxX, hx1⟩ := mem_fibP.mp hx
  have h1 := mem_tgtP.mp h x hx
  have h2 := hX x hxX
  rw [hx1] at h2
  exact h2 h1

lemma card_supp_add (X Y : Finset (Fin 13 × Fin 13)) (hX : ∀ x ∈ X, x.1 ∉ singerLines3 x.2)
    (hY : ∀ x ∈ Y, x.1 ∉ singerLines3 x.2)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x.1 ∈ singerLines3 y.2 ∨ y.1 ∈ singerLines3 x.2) :
    (suppP X).card + (suppP Y).card ≤ 13 := by
  have hd : Disjoint (suppP X) (suppP Y) := by
    rw [Finset.disjoint_left]
    intro P hPX hPY
    rcases cross X Y hXY P P with h | h
    · exact not_self X hX P hPX h
    · exact not_self Y hY P hPY h
  rw [← Finset.card_union_of_disjoint hd]
  exact le_trans (Finset.card_le_univ _) (by simp)

lemma card_eq_sum (X : Finset (Fin 13 × Fin 13)) :
    X.card = ∑ P ∈ suppP X, (fibP X P).card := by
  have H : ((X : Set (Fin 13 × Fin 13))).MapsTo Prod.fst (suppP X) := by
    intro x hx
    rw [Finset.mem_coe, mem_suppP]
    exact ⟨x, mem_fibP.mpr ⟨Finset.mem_coe.mp hx, rfl⟩⟩
  rw [Finset.card_eq_sum_card_fiberwise H]
  rfl

lemma aimed_bound (X Y : Finset (Fin 13 × Fin 13)) (hX : ∀ x ∈ X, x.1 ∉ singerLines3 x.2)
    (P : Fin 13) (hP : P ∈ suppP X) (hT : (tgtP X P).Nonempty) :
    2 * ((suppP Y).filter (fun Q => Q ∈ tgtP X P)).card + 3 * (fibP X P).card ≤ 11 := by
  obtain ⟨Q0, hQ0⟩ := hT
  have hw3 := w_le3 X hX P Q0 hQ0
  have hsub : (suppP Y).filter (fun Q => Q ∈ tgtP X P) ⊆ tgtP X P := by
    intro Q hQ; exact (Finset.mem_filter.mp hQ).2
  have ha4 : ((suppP Y).filter (fun Q => Q ∈ tgtP X P)).card ≤ 4 :=
    le_trans (Finset.card_le_card hsub) (tgt_card X P hP)
  by_cases h2 : 1 < ((suppP Y).filter (fun Q => Q ∈ tgtP X P)).card
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h2
    have hw1 := w_le1 X P a b (hsub ha) (hsub hb) hab
    omega
  · omega

lemma edge_count (X Y : Finset (Fin 13 × Fin 13))
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x.1 ∈ singerLines3 y.2 ∨ y.1 ∈ singerLines3 x.2) :
    (suppP X).card * (suppP Y).card ≤
      ∑ P ∈ suppP X, ((suppP Y).filter (fun Q => Q ∈ tgtP X P)).card
      + ∑ Q ∈ suppP Y, ((suppP X).filter (fun P => P ∈ tgtP Y Q)).card := by
  have h1 : ∑ P ∈ suppP X, ((suppP Y).filter (fun Q => Q ∈ tgtP X P)).card
      = ((suppP X ×ˢ suppP Y).filter (fun pq => pq.2 ∈ tgtP X pq.1)).card := by
    simp only [Finset.card_filter, Finset.sum_product]
  have h2 : ∑ Q ∈ suppP Y, ((suppP X).filter (fun P => P ∈ tgtP Y Q)).card
      = ((suppP X ×ˢ suppP Y).filter (fun pq => pq.1 ∈ tgtP Y pq.2)).card := by
    simp only [Finset.card_filter, Finset.sum_product_right]
  rw [h1, h2, ← Finset.card_product]
  calc (suppP X ×ˢ suppP Y).card
      ≤ ((suppP X ×ˢ suppP Y).filter (fun pq => pq.2 ∈ tgtP X pq.1) ∪
          (suppP X ×ˢ suppP Y).filter (fun pq => pq.1 ∈ tgtP Y pq.2)).card := by
        apply Finset.card_le_card
        intro pq hpq
        rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
        rcases cross X Y hXY pq.1 pq.2 with h | h
        · exact Or.inl ⟨hpq, h⟩
        · exact Or.inr ⟨hpq, h⟩
    _ ≤ _ := Finset.card_union_le _ _

lemma aimed (A B : Finset (Fin 13 × Fin 13)) (hA : ∀ x ∈ A, x.1 ∉ singerLines3 x.2)
    (hB : ∀ x ∈ B, x.1 ∉ singerLines3 x.2)
    (hAB : ∀ x ∈ A, ∀ y ∈ B, x.1 ∈ singerLines3 y.2 ∨ y.1 ∈ singerLines3 x.2)
    (hA13 : 13 ≤ A.card) (hB13 : 13 ≤ B.card)
    (hTA : ∀ P ∈ suppP A, (tgtP A P).Nonempty) (hTB : ∀ Q ∈ suppP B, (tgtP B Q).Nonempty) :
    False := by
  have hs := card_supp_add A B hA hB hAB
  have he := edge_count A B hAB
  have sA : 2 * ∑ P ∈ suppP A, ((suppP B).filter (fun Q => Q ∈ tgtP A P)).card + 3 * A.card
      ≤ 11 * (suppP A).card := by
    rw [card_eq_sum A, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    calc _ ≤ ∑ P ∈ suppP A, 11 :=
          Finset.sum_le_sum (fun P hP => aimed_bound A B hA P hP (hTA P hP))
      _ = 11 * (suppP A).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have sB : 2 * ∑ Q ∈ suppP B, ((suppP A).filter (fun P => P ∈ tgtP B Q)).card + 3 * B.card
      ≤ 11 * (suppP B).card := by
    rw [card_eq_sum B, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    calc _ ≤ ∑ Q ∈ suppP B, 11 :=
          Finset.sum_le_sum (fun Q hQ => aimed_bound B A hB Q hQ (hTB Q hQ))
      _ = 11 * (suppP B).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have wA : A.card ≤ 3 * (suppP A).card := by
    rw [card_eq_sum A]
    calc _ ≤ ∑ P ∈ suppP A, 3 := Finset.sum_le_sum (fun P hP => by
          obtain ⟨Q, hQ⟩ := hTA P hP
          exact w_le3 A hA P Q hQ)
      _ = 3 * (suppP A).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have wB : B.card ≤ 3 * (suppP B).card := by
    rw [card_eq_sum B]
    calc _ ≤ ∑ Q ∈ suppP B, 3 := Finset.sum_le_sum (fun Q hQ => by
          obtain ⟨P, hP⟩ := hTB Q hQ
          exact w_le3 B hB Q P hP)
      _ = 3 * (suppP B).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  obtain ⟨u, hu⟩ : ∃ u, (suppP A).card = 5 + u := ⟨(suppP A).card - 5, by omega⟩
  obtain ⟨v, hv⟩ : ∃ v, (suppP B).card = 5 + v := ⟨(suppP B).card - 5, by omega⟩
  rw [hu, hv] at he
  rw [hu] at sA
  rw [hv] at sB
  rw [hu, hv] at hs
  nlinarith [Nat.zero_le (u * v)]

lemma unaimed (X Y : Finset (Fin 13 × Fin 13)) (hX : ∀ x ∈ X, x.1 ∉ singerLines3 x.2)
    (hY : ∀ x ∈ Y, x.1 ∉ singerLines3 x.2)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x.1 ∈ singerLines3 y.2 ∨ y.1 ∈ singerLines3 x.2)
    (hX13 : 13 ≤ X.card) (hY13 : 13 ≤ Y.card)
    (P0 : Fin 13) (hP0 : P0 ∈ suppP X) (hT0 : tgtP X P0 = ∅) : False := by
  have hs := card_supp_add X Y hX hY hXY
  have hall : ∀ Q, P0 ∈ tgtP Y Q := by
    intro Q
    rcases cross X Y hXY P0 Q with h | h
    · rw [hT0] at h; simp at h
    · exact h
  have wY3 : ∀ Q, (fibP Y Q).card ≤ 3 := fun Q => w_le3 Y hY Q P0 (hall Q)
  have hYsum := card_eq_sum Y
  have hXsplit : X.card = (fibP X P0).card + ∑ P ∈ (suppP X).erase P0, (fibP X P).card := by
    rw [card_eq_sum X, Finset.add_sum_erase (suppP X) (fun P => (fibP X P).card) hP0]
  have hw0 := w_le9 X hX P0
  have hce : ((suppP X).erase P0).card = (suppP X).card - 1 := Finset.card_erase_of_mem hP0
  have hcpos : 1 ≤ (suppP X).card := Finset.card_pos.mpr ⟨P0, hP0⟩
  have hYb : Y.card ≤ (suppP Y).card + 2 * ((suppP Y).filter (fun Q => 2 ≤ (fibP Y Q).card)).card := by
    rw [hYsum]
    calc ∑ Q ∈ suppP Y, (fibP Y Q).card
        ≤ ∑ Q ∈ suppP Y, (1 + 2 * (if 2 ≤ (fibP Y Q).card then 1 else 0)) := by
          apply Finset.sum_le_sum
          intro Q _
          have := wY3 Q
          split_ifs with h <;> omega
      _ = (suppP Y).card + 2 * ((suppP Y).filter (fun Q => 2 ≤ (fibP Y Q).card)).card := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.card_filter]
          simp
  by_cases hH : ((suppP Y).filter (fun Q => 2 ≤ (fibP Y Q).card)).card ≤ 1
  · have hsX : (suppP X).card ≤ 2 := by omega
    have hex : ∃ P1 ∈ (suppP X).erase P0, 4 ≤ (fibP X P1).card := by
      by_contra hno
      push Not at hno
      have : ∑ P ∈ (suppP X).erase P0, (fibP X P).card ≤ ∑ P ∈ (suppP X).erase P0, 3 :=
        Finset.sum_le_sum (fun P hP => by have := hno P hP; omega)
      rw [Finset.sum_const, smul_eq_mul] at this
      omega
    obtain ⟨P1, hP1e, hP1w⟩ := hex
    obtain ⟨hne, hP1⟩ := Finset.mem_erase.mp hP1e
    have hce1 : 1 ≤ ((suppP X).erase P0).card := Finset.card_pos.mpr ⟨P1, hP1e⟩
    have hall1 : ∀ Q, P1 ∈ tgtP Y Q := by
      intro Q
      rcases cross X Y hXY P1 Q with h | h
      · have := w_le3 X hX P1 Q h; omega
      · exact h
    have hY1 : Y.card ≤ (suppP Y).card := by
      rw [hYsum]
      calc _ ≤ ∑ Q ∈ suppP Y, 1 := Finset.sum_le_sum (fun Q _ => w_le1 Y Q P0 P1 (hall Q) (hall1 Q)
              (Ne.symm hne))
        _ = (suppP Y).card := by simp
    omega
  · have h2 : 1 < ((suppP Y).filter (fun Q => 2 ≤ (fibP Y Q).card)).card := by omega
    obtain ⟨Q1, hQ1, Q2, hQ2, hQ12⟩ := Finset.one_lt_card.mp h2
    have hQ1' := Finset.mem_filter.mp hQ1
    have hQ2' := Finset.mem_filter.mp hQ2
    have honly : ∀ Q ∈ (suppP Y).filter (fun Q => 2 ≤ (fibP Y Q).card), ∀ P, P ∈ tgtP Y Q → P = P0 := by
      intro Q hQ P hP
      by_contra hPne
      have := w_le1 Y Q P0 P (hall Q) hP (Ne.symm hPne)
      have := (Finset.mem_filter.mp hQ).2
      omega
    have haim : ∀ P ∈ (suppP X).erase P0, Q1 ∈ tgtP X P ∧ Q2 ∈ tgtP X P := by
      intro P hP
      obtain ⟨hne, _⟩ := Finset.mem_erase.mp hP
      constructor
      · rcases cross X Y hXY P Q1 with h | h
        · exact h
        · exact absurd (honly Q1 hQ1 P h) hne
      · rcases cross X Y hXY P Q2 with h | h
        · exact h
        · exact absurd (honly Q2 hQ2 P h) hne
    have hsum1 : ∑ P ∈ (suppP X).erase P0, (fibP X P).card ≤ ((suppP X).erase P0).card := by
      calc _ ≤ ∑ P ∈ (suppP X).erase P0, 1 := Finset.sum_le_sum (fun P hP =>
              w_le1 X P Q1 Q2 (haim P hP).1 (haim P hP).2 hQ12)
        _ = _ := by simp
    have hs5 : 5 ≤ (suppP X).card := by omega
    obtain ⟨h, hh1, hh2⟩ := g_line Q1 Q2
    have hsubh : ∀ P ∈ (suppP X).erase P0, tgtP X P ⊆ singerLines3 h := by
      intro P hP
      obtain ⟨_, hPS⟩ := Finset.mem_erase.mp hP
      obtain ⟨x, hx⟩ := mem_suppP.mp hPS
      have e1 := mem_tgtP.mp (haim P hP).1 x hx
      have e2 := mem_tgtP.mp (haim P hP).2 x hx
      have hxh : x.2 = h := line_unique Q1 Q2 x.2 h hQ12 e1 e2 hh1 hh2
      rw [← hxh]
      exact tgt_sub X P x hx
    have hYh : suppP Y ⊆ singerLines3 h := by
      intro Q hQ
      by_contra hQh
      have hsub : suppP X ⊆ tgtP Y Q := by
        intro P hP
        by_cases hPe : P = P0
        · rw [hPe]; exact hall Q
        · rcases cross X Y hXY P Q with hc | hc
          · exact absurd (hsubh P (Finset.mem_erase.mpr ⟨hPe, hP⟩) hc) hQh
          · exact hc
      have := le_trans (Finset.card_le_card hsub) (tgt_card Y Q hQ)
      omega
    have hsY : (suppP Y).card ≤ 4 := by
      have := Finset.card_le_card hYh
      rw [g_four] at this; exact this
    have hY3 : Y.card ≤ 3 * (suppP Y).card := by
      rw [hYsum]
      calc _ ≤ ∑ Q ∈ suppP Y, 3 := Finset.sum_le_sum (fun Q _ => wY3 Q)
        _ = 3 * (suppP Y).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    omega

lemma bound : ∀ (x1 x2 : Finset (Fin (13 : ℕ) × Fin (13 : ℕ))), (∀ x3 ∈ x1 ∪ x2, x3.1 ∉ PEqualNP.HeptadCover.singerLines3 x3.2) → (∀ x4 ∈ x1, ∀ x6 ∈ x2, x4.1 ∈ PEqualNP.HeptadCover.singerLines3 x6.2 ∨ x6.1 ∈ PEqualNP.HeptadCover.singerLines3 x4.2) → x1.card ≤ (12 : ℕ) ∨ x2.card ≤ (12 : ℕ) := by
  intro A B hU hAB
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hA13, hB13⟩ := hcon
  have hA : ∀ x ∈ A, x.1 ∉ PEqualNP.HeptadCover.singerLines3 x.2 :=
    fun x hx => hU x (Finset.mem_union_left _ hx)
  have hB : ∀ x ∈ B, x.1 ∉ PEqualNP.HeptadCover.singerLines3 x.2 :=
    fun x hx => hU x (Finset.mem_union_right _ hx)
  have hBA : ∀ y ∈ B, ∀ x ∈ A, y.1 ∈ PEqualNP.HeptadCover.singerLines3 x.2 ∨
      x.1 ∈ PEqualNP.HeptadCover.singerLines3 y.2 :=
    fun y hy x hx => (hAB x hx y hy).symm
  by_cases h1 : ∃ P ∈ PEqualNP.Outside.L_meta_2089.BadPairs.Cardinality.suppP A, PEqualNP.Outside.L_meta_2089.BadPairs.Cardinality.tgtP A P = ∅
  · obtain ⟨P, hP, hT⟩ := h1
    exact PEqualNP.Outside.L_meta_2089.BadPairs.Cardinality.unaimed A B hA hB hAB (by omega) (by omega) P hP hT
  by_cases h2 : ∃ Q ∈ PEqualNP.Outside.L_meta_2089.BadPairs.Cardinality.suppP B, PEqualNP.Outside.L_meta_2089.BadPairs.Cardinality.tgtP B Q = ∅
  · obtain ⟨Q, hQ, hT⟩ := h2
    exact PEqualNP.Outside.L_meta_2089.BadPairs.Cardinality.unaimed B A hB hA hBA (by omega) (by omega) Q hQ hT
  push Not at h1 h2
  exact PEqualNP.Outside.L_meta_2089.BadPairs.Cardinality.aimed A B hA hB hAB (by omega) (by omega)
    (fun P hP => h1 P hP)
    (fun Q hQ => h2 Q hQ)

end PEqualNP.Outside.L_meta_2089.BadPairs.Cardinality

namespace PEqualNP.Outside.L_meta_2089.BadPairs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.LowMerge
open PEqualNP.HeptadCover PEqualNP.GenericRejection

private def BitsLE (xs ys : List Bool) : Prop :=
  ∀ i, xs.getD i false = true → ys.getD i false = true

private lemma append_mono {xs ys as bs : List Bool}
    (hlen : xs.length = ys.length) (hxy : BitsLE xs ys) (hab : BitsLE as bs) :
    BitsLE (xs ++ as) (ys ++ bs) := by
  intro i hi
  by_cases h : i < xs.length
  · rw [List.getD_append _ _ _ _ h] at hi
    rw [List.getD_append _ _ _ _ (hlen ▸ h)]
    exact hxy i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by omega), ← hlen]
    exact hab _ hi

private lemma gate_mono {g : Gate} (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    {xs ys : List Bool} (hxy : BitsLE xs ys) :
    g.op.eval (g.inputs.map fun i => xs.getD i false) = true →
      g.op.eval (g.inputs.map fun i => ys.getD i false) = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    rintro h _ ⟨i, hi, rfl⟩
    exact hxy i (h _ ⟨i, hi, rfl⟩)
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨i, hi, rfl⟩, h⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hxy i h⟩

private def step (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

private lemma fold_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (xs ys : List Bool) (hlen : xs.length = ys.length) (hxy : BitsLE xs ys) :
    BitsLE (gs.foldl step xs) (gs.foldl step ys) := by
  induction gs generalizing xs ys with
  | nil => exact hxy
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hlen]
    · apply append_mono hlen hxy
      intro i hi
      cases i with
      | zero => exact gate_mono (hgs g List.mem_cons_self) hxy hi
      | succ i => simp at hi

private lemma wire_true_mono {C : Circuit} (hC : Monotone2 C) {xs ys : List Bool}
    (hlen : xs.length = ys.length) (hxy : BitsLE xs ys) (i : ℕ) :
    wireVal C xs i = true → wireVal C ys i = true := by
  apply fold_mono C.gates _ xs ys hlen hxy i
  intro g hg
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1

private lemma ofFn_mono {n : ℕ} {f g : Fin n → Bool}
    (hfg : ∀ i, f i = true → g i = true) : BitsLE (List.ofFn f) (List.ofFn g) := by
  intro i hi
  by_cases h : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
    exact hfg ⟨i, h⟩ hi
  · have h' : (List.ofFn f).length ≤ i := by simpa using Nat.le_of_not_gt h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h'] at hi
    cases hi

private lemma wire_incidence_mono {C : Circuit} (hC : Monotone2 C)
    {n m : ℕ} {X X' : Finset (Fin n)} {Y Y' : Finset (Fin m)}
    (hX : X ⊆ X') (hY : Y ⊆ Y') (i : ℕ) :
    wireVal C (incidenceInput X Y) i = true →
      wireVal C (incidenceInput X' Y') i = true := by
  apply wire_true_mono hC _ _ i
  · simp [incidenceInput]
  · unfold incidenceInput
    apply append_mono (by simp)
    · exact ofFn_mono (fun p hp => decide_eq_true (hX (of_decide_eq_true hp)))
    · exact ofFn_mono (fun l hl => decide_eq_true (hY (of_decide_eq_true hl)))

lemma pair_maximal : ∀ p q : Fin 13,
    ({p,q} : Finset (Fin 13)) = zeroSet singerLines3 (missLines singerLines3 {p,q}) ∧
    ∃ l, ({p,q} : Finset (Fin 13)) ⊆ singerLines3 l := by
  decide +kernel

lemma miss_pair {p q l : Fin 13} (hp : p ∉ singerLines3 l) (hq : q ∉ singerLines3 l) :
    l ∈ missLines singerLines3 {p,q} := by
  simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
  intro r hr hs
  rcases Finset.mem_insert.mp hs with rfl | hs
  · exact hp hr
  · have he : r = q := Finset.mem_singleton.mp hs
    exact hq (he ▸ hr)

def acceptedBad (C : Circuit) (a : ℕ) : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter fun e => e.1 ∉ singerLines3 e.2 ∧
    wireVal C (incidenceInput {e.1} {e.2}) a = true

lemma cross_bad (C : Circuit) (hC : Monotone2 C) (a b : ℕ)
    (hNeg : ∀ p q : Fin 13,
      (wireVal C (incidenceInput {p,q} (missLines singerLines3 {p,q})) a &&
       wireVal C (incidenceInput {p,q} (missLines singerLines3 {p,q})) b) = false) :
    ∀ e ∈ acceptedBad C a, ∀ f ∈ acceptedBad C b,
      e.1 ∈ singerLines3 f.2 ∨ f.1 ∈ singerLines3 e.2 := by
  intro e he f hf
  obtain ⟨heN,heV⟩ := (Finset.mem_filter.mp he).2
  obtain ⟨hfN,hfV⟩ := (Finset.mem_filter.mp hf).2
  by_contra! hn
  have heL := miss_pair heN hn.2
  have hfL := miss_pair hn.1 hfN
  have ha : wireVal C (incidenceInput {e.1,f.1} (missLines singerLines3 {e.1,f.1})) a = true :=
    wire_incidence_mono hC (by simp) (by simpa using heL) a heV
  have hb : wireVal C (incidenceInput {e.1,f.1} (missLines singerLines3 {e.1,f.1})) b = true :=
    wire_incidence_mono hC (by simp) (by simpa using hfL) b hfV
  have h := hNeg e.1 f.1
  simp only [ha,hb,Bool.true_and] at h
  contradiction

lemma few_bad (C : Circuit) (hC : Monotone2 C) (a b : ℕ)
    (hNeg : ∀ p q : Fin 13,
      (wireVal C (incidenceInput {p,q} (missLines singerLines3 {p,q})) a &&
       wireVal C (incidenceInput {p,q} (missLines singerLines3 {p,q})) b) = false) :
    (acceptedBad C a).card ≤ 12 ∨ (acceptedBad C b).card ≤ 12 := by
  apply Cardinality.bound (acceptedBad C a) (acceptedBad C b)
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact (Finset.mem_filter.mp he).2.1
    · exact (Finset.mem_filter.mp he).2.1
  · exact cross_bad C hC a b hNeg

abbrev rel (p l : Fin 13) : Prop := ∃ d ∈ ({0,1,3,9} : Finset (Fin 13)), p = l + d

lemma rel_iff : ∀ p l : Fin 13, p ∈ singerLines3 l ↔ rel p l := by
  decide +kernel

def postedRow (X : Finset (Fin 13)) (i : Fin (13+13)) : Bool :=
  decide ((∃ p ∈ X, i = Fin.castAdd 13 p) ∨
    ∃ l, i = Fin.natAdd 13 l ∧ ∀ p ∈ X, ¬rel p l)

lemma miss_rel (X : Finset (Fin 13)) (l : Fin 13) :
    l ∈ missLines singerLines3 X ↔ ∀ p ∈ X, ¬rel p l := by
  simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
  constructor
  · intro h p hp hi
    exact h ((rel_iff p l).mpr hi) hp
  · intro h p hi hp
    exact h p hp ((rel_iff p l).mp hi)

lemma postedRow_eq (X : Finset (Fin 13)) :
    incidenceInput X (missLines singerLines3 X) = List.ofFn (postedRow X) := by
  rw [List.ofFn_add]
  unfold incidenceInput
  congr 1
  · apply congrArg List.ofFn
    funext p
    apply decide_eq_decide.mpr
    change p ∈ X ↔ (∃ q ∈ X, Fin.castAdd 13 p = Fin.castAdd 13 q) ∨
      ∃ l, Fin.castAdd 13 p = Fin.natAdd 13 l ∧ _
    constructor
    · exact fun hp => Or.inl ⟨p,hp,rfl⟩
    · rintro (⟨q,hq,eq⟩ | ⟨l,eq,_⟩)
      · have e := congrArg Fin.val eq
        have pq : p = q := Fin.ext e
        simpa [pq] using hq
      · have e := congrArg Fin.val eq
        change p.val = 13+l.val at e
        omega
  · apply congrArg List.ofFn
    funext l
    apply decide_eq_decide.mpr
    change l ∈ missLines singerLines3 X ↔
      (∃ q ∈ X, Fin.natAdd 13 l = Fin.castAdd 13 q) ∨
      ∃ z, Fin.natAdd 13 l = Fin.natAdd 13 z ∧ ∀ p ∈ X, ¬rel p z
    constructor
    · exact fun h => Or.inr ⟨l,rfl,(miss_rel X l).mp h⟩
    · rintro (⟨q,_,eq⟩ | ⟨z,eq,hz⟩)
      · have e := congrArg Fin.val eq
        change 13+l.val=q.val at e
        omega
      · have e := congrArg Fin.val eq
        change 13+l.val=13+z.val at e
        have e' : l=z := Fin.ext (by omega)
        exact e' ▸ (miss_rel X z).mpr hz

lemma few_bad_posted (C : Circuit) (hC : Monotone2 C) (a b : ℕ)
    (hNeg : ∀ X : Finset (Fin 13),
      (∀ p ∉ X, ∃ l, (∀ q ∈ X, ¬rel q l) ∧ rel p l) →
      (∃ l, ∀ p ∈ X, rel p l) →
      GateOp.and.eval [(C.wires (List.ofFn (postedRow X))).getD a false,
        (C.wires (List.ofFn (postedRow X))).getD b false] = false) :
    (acceptedBad C a).card ≤ 12 ∨ (acceptedBad C b).card ≤ 12 := by
  apply few_bad C hC a b
  intro p q
  obtain ⟨hc,l,hl⟩ := pair_maximal p q
  have hmax : ∀ r ∉ ({p,q} : Finset (Fin 13)),
      ∃ m, (∀ s ∈ ({p,q} : Finset (Fin 13)), ¬rel s m) ∧ rel r m := by
    intro r hr
    have hout : r ∉ zeroSet singerLines3 (missLines singerLines3 {p,q}) := by
      rwa [←hc]
    simp only [zeroSet, Finset.mem_filter, Finset.mem_univ, true_and] at hout
    push Not at hout
    obtain ⟨m,hm,hrm⟩ := hout
    exact ⟨m,(miss_rel {p,q} m).mp hm,(rel_iff r m).mp hrm⟩
  have hh := hNeg {p,q} hmax ⟨l,fun r hr => (rel_iff r l).mp (hl hr)⟩
  rw [postedRow_eq]
  simpa only [wireVal,GateOp.eval,List.all_cons,List.all_nil,id_eq,Bool.and_true] using hh

end PEqualNP.Outside.L_meta_2089.BadPairs

namespace PEqualNP.Outside.L_meta_2089

lemma cutInput_point (A : Finset (Fin 13)) (p : Fin 13) :
    cutInput A (Fin.castAdd 13 p) = decide (p ∈ A) := by
  unfold cutInput
  apply decide_eq_decide.mpr
  constructor
  · rintro (⟨q, hq, heq⟩ | ⟨l, heq, _⟩)
    · have he := congrArg (fun i : Fin 26 => i.val) heq
      have hpq : p = q := Fin.ext he
      simpa [hpq] using hq
    · have he := congrArg Fin.val heq
      change p.val = 13 + l.val at he
      omega
  · exact fun hp => Or.inl ⟨p, hp, rfl⟩

lemma cutInput_line (A : Finset (Fin 13)) (l : Fin 13) :
    cutInput A (Fin.natAdd 13 l) = decide (∀ p ∈ A, ¬∃ d ∈ delta, p = l + d) := by
  unfold cutInput
  apply decide_eq_decide.mpr
  constructor
  · rintro (⟨p, _, heq⟩ | ⟨k, heq, hk⟩)
    · have he := congrArg Fin.val heq
      change 13 + l.val = p.val at he
      omega
    · have he := congrArg Fin.val heq
      change 13 + l.val = 13 + k.val at he
      have hlk : l = k := Fin.ext (by omega)
      simpa [hlk] using hk
  · exact fun hl => Or.inr ⟨l, rfl, hl⟩

lemma count_false_ofFn {n : ℕ} (x : Fin n → Bool) :
    (List.ofFn x).count false = (Finset.univ.filter (fun i => x i = false)).card := by
  classical
  have h := List.Nodup.card_eq_countP (P := fun i => x i = false) (List.nodup_finRange n)
  have hrange : (List.finRange n).toFinset = Finset.univ := by ext i; simp
  rw [hrange] at h
  rw [List.ofFn_eq_map, List.count_eq_countP, List.countP_map]
  simpa [Function.comp_def] using h.symm

lemma certificate_contains_zeros (A : Finset (Fin 13)) (hc : isClosed A)
    (B : Finset (Fin 26)) (hB : ∀ i ∈ B, cutInput A i = false)
    (hcover : ∀ p l, incidence p l → Fin.castAdd 13 p ∈ B ∨ Fin.natAdd 13 l ∈ B) :
    ∀ i, cutInput A i = false → i ∈ B := by
  classical
  let Y : Finset (Fin 13) := Finset.univ.filter (fun l => ∀ p ∈ A, ¬incidence p l)
  let U : Finset (Fin 13) := Finset.univ.filter (fun p => Fin.castAdd 13 p ∈ B)
  let V : Finset (Fin 13) := Finset.univ.filter (fun l => Fin.natAdd 13 l ∈ B)
  have maxA : ∀ p, p ∉ A → ∃ l ∈ Y, incidence p l := by
    intro p hp
    obtain ⟨l, hl, hpl⟩ := hc p hp
    exact ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩, hpl⟩
  have maxY : ∀ l, l ∉ Y → ∃ p ∈ A, incidence p l := by
    intro l hl
    have h : ¬∀ p ∈ A, ¬incidence p l := by simpa [Y] using hl
    push Not at h
    exact h
  have disjU : Disjoint U A := by
    apply Finset.disjoint_left.mpr
    intro p hp hA
    have hb := hB (Fin.castAdd 13 p) (Finset.mem_filter.mp hp).2
    rw [cutInput_point, decide_eq_true hA] at hb
    exact Bool.noConfusion hb
  have disjV : Disjoint V Y := by
    apply Finset.disjoint_left.mpr
    intro l hl hY
    have hb := hB (Fin.natAdd 13 l) (Finset.mem_filter.mp hl).2
    rw [cutInput_line] at hb
    have hy : ∀ p ∈ A, ¬∃ d ∈ delta, p = l + d := (Finset.mem_filter.mp hY).2
    rw [decide_eq_true hy] at hb
    exact Bool.noConfusion hb
  have cover : ∀ p l, incidence p l → p ∈ U ∨ l ∈ V := by
    intro p l hpl
    simpa [U, V] using hcover p l hpl
  obtain ⟨hU, hV⟩ := maximal_pair_cover incidence A U Y V maxA maxY disjU disjV cover
  intro i
  refine Fin.addCases (m := 13) (n := 13)
    (motive := fun i => cutInput A i = false → i ∈ B) ?_ ?_ i
  · intro p hp
    have hn : p ∉ A := by simpa only [cutInput_point, decide_eq_false_iff_not] using hp
    have hu : p ∈ U := by rw [hU]; exact Finset.mem_compl.mpr hn
    exact (Finset.mem_filter.mp hu).2
  · intro l hl
    have hn : l ∉ Y := by
      intro hY
      have ht : cutInput A (Fin.natAdd 13 l) = true := by
        rw [cutInput_line]
        exact decide_eq_true (Finset.mem_filter.mp hY).2
      exact Bool.noConfusion (ht.symm.trans hl)
    have hv : l ∈ V := by rw [hV]; exact Finset.mem_compl.mpr hn
    exact (Finset.mem_filter.mp hv).2

lemma or_quota (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (a : ℕ)
    (hpos : ∀ p l, incidence p l → Structural.value C (pairInput p l) a = true)
    (A : Finset (Fin 13)) (hc : isClosed A)
    (hoff : Structural.value C (cutInput A) a = false) :
    ∃ I : Finset ℕ, (List.ofFn (cutInput A)).count false ≤ I.card + 1 ∧
      ∀ i ∈ I, 26 ≤ i ∧ i ≤ a ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C (i - 26)).op =
          PEqualNP.CircuitLowerBounds.GateOp.or ∧ Structural.value C (cutInput A) i = false := by
  classical
  obtain ⟨I, B, hcard, hI, hB, hcert⟩ := Structural.false_certificate C hm (cutInput A) a hoff
  have hcover : ∀ p l, incidence p l → Fin.castAdd 13 p ∈ B ∨ Fin.natAdd 13 l ∈ B := by
    intro p l hpl
    by_contra! hnone
    have hzero : Structural.value C (pairInput p l) a = false := by
      apply hcert
      intro i hi
      apply Bool.eq_false_iff.mpr
      intro hv
      simp only [pairInput, decide_eq_true_eq] at hv
      rcases hv with rfl | rfl
      · exact hnone.1 hi
      · exact hnone.2 hi
    exact Bool.noConfusion ((hpos p l hpl).symm.trans hzero)
  have hsub : Finset.univ.filter (fun i => cutInput A i = false) ⊆ B := by
    intro i hi
    exact certificate_contains_zeros A hc B hB hcover i (Finset.mem_filter.mp hi).2
  refine ⟨I, ?_, hI⟩
  rw [count_false_ofFn]
  exact (Finset.card_le_card hsub).trans hcard

end PEqualNP.Outside.L_meta_2089

namespace PEqualNP.Outside.L_meta_2089

set_option synthInstance.maxSize 100000 in
lemma two_points_closed_degenerate : ∀ p q : Fin 13,
    isClosed {p, q} ∧ isDegenerate {p, q} := by
  unfold isClosed isDegenerate incidence delta
  decide

lemma small_points_closed_degenerate (A : Finset (Fin 13)) (hA : A.card ≤ 2) :
    isClosed A ∧ isDegenerate A := by
  have hs : A.card = 0 ∨ A.card = 1 ∨ A.card = 2 := by omega
  rcases hs with hs | hs | hs
  · obtain rfl := Finset.card_eq_zero.mp hs
    exact ⟨empty_closed, empty_degenerate⟩
  · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hs
    exact ⟨singleton_maximal p, singleton_degenerate p⟩
  · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hs
    exact two_points_closed_degenerate p q

def activePoints (a : Fin 26 → Bool) : Finset (Fin 13) :=
  Finset.univ.filter fun p => a (Fin.castAdd 13 p) = true

def activeLines (a : Fin 26 → Bool) : Finset (Fin 13) :=
  Finset.univ.filter fun l => a (Fin.natAdd 13 l) = true

def hasActiveEdge (a : Fin 26 → Bool) : Prop :=
  ∃ p l, a (Fin.castAdd 13 p) = true ∧ a (Fin.natAdd 13 l) = true ∧ incidence p l

lemma no_edge_le_active_cut (a : Fin 26 → Bool) (h : ¬hasActiveEdge a) :
    ∀ i, a i = true → cutInput (activePoints a) i = true := by
  intro i
  refine Fin.addCases (m := 13) (n := 13)
    (motive := fun j => a j = true → cutInput (activePoints a) j = true) ?_ ?_ i
  · intro p hp
    simp only [cutInput, decide_eq_true_eq]
    left
    exact ⟨p, by simpa [activePoints] using hp, rfl⟩
  · intro l hl
    simp only [cutInput, decide_eq_true_eq]
    right
    refine ⟨l, rfl, ?_⟩
    intro p hp hpl
    exact h ⟨p, l, by simpa [activePoints] using hp, hl, hpl⟩

lemma active_edge_accepted (f : (Fin 26 → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → f a = true → f b = true)
    (hpositive : ∀ p l, incidence p l → f (pairInput p l) = true)
    (a : Fin 26 → Bool) (h : hasActiveEdge a) : f a = true := by
  obtain ⟨p, l, hp, hl, hpl⟩ := h
  apply hmono (pairInput p l) a _ (hpositive p l hpl)
  intro i hi
  simp only [pairInput, decide_eq_true_eq] at hi
  rcases hi with rfl | rfl
  · exact hp
  · exact hl

lemma exact_on_two_points (f : (Fin 26 → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → f a = true → f b = true)
    (hnegative : ∀ A, isClosed A → isDegenerate A → f (cutInput A) = false)
    (hpositive : ∀ p l, incidence p l → f (pairInput p l) = true)
    (a : Fin 26 → Bool) (ha : (activePoints a).card ≤ 2) :
    f a = true ↔ hasActiveEdge a := by
  constructor
  · intro hfa
    by_contra hn
    have hm := hmono a _ (no_edge_le_active_cut a hn) hfa
    obtain ⟨hc, hd⟩ := small_points_closed_degenerate (activePoints a) ha
    exact Bool.noConfusion (hm.symm.trans (hnegative _ hc hd))
  · exact active_edge_accepted f hmono hpositive a

def avoidLines (B : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun p => ∀ l ∈ B, ¬∃ d ∈ delta, p = l + d

set_option synthInstance.maxSize 100000 in
lemma two_lines_closed_degenerate : ∀ l k : Fin 13,
    isClosed (avoidLines {l, k}) ∧ isDegenerate (avoidLines {l, k}) := by
  unfold isClosed isDegenerate avoidLines incidence delta
  decide +kernel

lemma small_lines_closed_degenerate (B : Finset (Fin 13)) (hB : B.card ≤ 2) :
    isClosed (avoidLines B) ∧ isDegenerate (avoidLines B) := by
  have hs : B.card = 0 ∨ B.card = 1 ∨ B.card = 2 := by omega
  rcases hs with hs | hs | hs
  · obtain rfl := Finset.card_eq_zero.mp hs
    simpa [avoidLines] using And.intro univ_closed univ_degenerate
  · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hs
    simpa using two_lines_closed_degenerate p p
  · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp hs
    exact two_lines_closed_degenerate p q

lemma no_edge_le_avoiding_cut (a : Fin 26 → Bool) (h : ¬hasActiveEdge a) :
    ∀ i, a i = true → cutInput (avoidLines (activeLines a)) i = true := by
  intro i
  refine Fin.addCases (m := 13) (n := 13)
    (motive := fun j => a j = true → cutInput (avoidLines (activeLines a)) j = true) ?_ ?_ i
  · intro p hp
    simp only [cutInput, decide_eq_true_eq]
    left
    refine ⟨p, ?_, rfl⟩
    simp only [avoidLines, Finset.mem_filter, Finset.mem_univ, true_and]
    intro l hl hpl
    exact h ⟨p, l, hp, by simpa [activeLines] using hl, hpl⟩
  · intro l hl
    simp only [cutInput, decide_eq_true_eq]
    right
    refine ⟨l, rfl, ?_⟩
    intro p hp
    simp only [avoidLines, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact hp l (by simpa [activeLines] using hl)

lemma exact_on_two_lines (f : (Fin 26 → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → f a = true → f b = true)
    (hnegative : ∀ A, isClosed A → isDegenerate A → f (cutInput A) = false)
    (hpositive : ∀ p l, incidence p l → f (pairInput p l) = true)
    (a : Fin 26 → Bool) (ha : (activeLines a).card ≤ 2) :
    f a = true ↔ hasActiveEdge a := by
  constructor
  · intro hfa
    by_contra hn
    have hm := hmono a _ (no_edge_le_avoiding_cut a hn) hfa
    obtain ⟨hc, hd⟩ := small_lines_closed_degenerate (activeLines a) ha
    exact Bool.noConfusion (hm.symm.trans (hnegative _ hc hd))
  · exact active_edge_accepted f hmono hpositive a

lemma spurious_input_large (f : (Fin 26 → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → f a = true → f b = true)
    (hnegative : ∀ A, isClosed A → isDegenerate A → f (cutInput A) = false)
    (hpositive : ∀ p l, incidence p l → f (pairInput p l) = true)
    (a : Fin 26 → Bool) (hfa : f a = true) (hne : ¬hasActiveEdge a) :
    3 ≤ (activePoints a).card ∧ 3 ≤ (activeLines a).card := by
  constructor
  · by_contra h
    exact hne ((exact_on_two_points f hmono hnegative hpositive a (by omega)).mp hfa)
  · by_contra h
    exact hne ((exact_on_two_lines f hmono hnegative hpositive a (by omega)).mp hfa)

end PEqualNP.Outside.L_meta_2089

namespace PEqualNP.Outside.L_meta_2089

def singletonInput (i j : Fin 26) : Bool := decide (j = i)

def forcedBad (i : Fin 26) : Finset (Fin 13 × Fin 13) := by
  letI : DecidableRel incidence := fun p l => by unfold incidence; infer_instance
  exact Finset.univ.filter fun e => ¬incidence e.1 e.2 ∧
    (i = Fin.castAdd 13 e.1 ∨ i = Fin.natAdd 13 e.2)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
lemma forced_bad_union_card : ∀ i j : Fin 26, i ≠ j →
    17 ≤ (forcedBad i ∪ forcedBad j).card := by
  unfold forcedBad incidence delta
  decide +kernel

lemma singleton_le_pair (i : Fin 26) (p l : Fin 13)
    (hi : i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l) :
    singletonInput i ≤ pairInput p l := by
  intro j
  by_cases h : j = i
  · subst j
    rcases hi with rfl | rfl <;> simp [singletonInput, pairInput]
  · simp [singletonInput, h]

def badPairSet (f : (Fin 26 → Bool) → Bool) : Finset (Fin 13 × Fin 13) := by
  letI : DecidableRel incidence := fun p l => by unfold incidence; infer_instance
  exact Finset.univ.filter fun e => ¬incidence e.1 e.2 ∧ f (pairInput e.1 e.2) = true

lemma small_bad_singleton_support (f : (Fin 26 → Bool) → Bool)
    (mono : Monotone f)
    (few : (badPairSet f).card ≤ 12) :
    (Finset.univ.filter fun i : Fin 26 => f (singletonInput i) = true).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  have hcard := forced_bad_union_card i j hij
  have sub : forcedBad i ∪ forcedBad j ⊆ badPairSet f := by
    intro e he
    have step : ∀ k : Fin 26, f (singletonInput k) = true → e ∈ forcedBad k →
        ¬incidence e.1 e.2 ∧ f (pairInput e.1 e.2) = true := by
      intro k hk he
      have heq : ¬incidence e.1 e.2 ∧ (k = Fin.castAdd 13 e.1 ∨ k = Fin.natAdd 13 e.2) := by
        simpa only [forcedBad, Finset.mem_filter, Finset.mem_univ, true_and] using he
      obtain ⟨hn, hkpair⟩ := heq
      refine ⟨hn, ?_⟩
      have := mono (singleton_le_pair k e.1 e.2 hkpair)
      cases hval : f (pairInput e.1 e.2) with
      | false =>
        have no : ¬((true : Bool) ≤ false) := by decide
        exact False.elim (no (by simpa only [hk, hval] using this))
      | true => rfl
    simp only [badPairSet, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Finset.mem_union.mp he with he | he
    · exact step i (Finset.mem_filter.mp hi).2 he
    · exact step j (Finset.mem_filter.mp hj).2 he
  have := Finset.card_le_card sub
  omega

end PEqualNP.Outside.L_meta_2089

namespace PEqualNP.Outside.L_meta_2089.MergedPair

open PEqualNP.HeptadCover

lemma separating_line : ∀ p q r : Fin 13, p ≠ q → r ≠ q →
    ∃ l : Fin 13, q ∈ singerLines3 l ∧ p ∉ singerLines3 l ∧ r ∉ singerLines3 l := by
  decide +kernel

lemma common_line : ∀ p q : Fin 13,
    ∃ l : Fin 13, p ∈ singerLines3 l ∧ q ∈ singerLines3 l := by
  decide

lemma common_line_count : ∀ p q : Fin 13, p ≠ q →
    (Finset.univ.filter fun l : Fin 13 => p ∈ singerLines3 l ∧ q ∈ singerLines3 l).card ≤ 1 := by
  decide

lemma nonincident_point_count : ∀ l : Fin 13,
    (Finset.univ.filter fun p : Fin 13 => p ∉ singerLines3 l).card = 9 := by
  decide

lemma common_line_unique (p q k l : Fin 13) (hpq : p ≠ q)
    (hpk : p ∈ singerLines3 k) (hqk : q ∈ singerLines3 k)
    (hpl : p ∈ singerLines3 l) (hql : q ∈ singerLines3 l) : k = l := by
  exact Finset.card_le_one.mp (common_line_count p q hpq) k (by simp [hpk, hqk])
    l (by simp [hpl, hql])

lemma forced_common_line (p q r k : Fin 13) (hpq : p ≠ q)
    (hrk : r ∉ singerLines3 k)
    (hp : ∀ l, q ∈ singerLines3 l → p ∉ singerLines3 l →
      p ∈ singerLines3 k ∨ r ∈ singerLines3 l)
    (hq : ∀ l, p ∈ singerLines3 l → q ∉ singerLines3 l →
      q ∈ singerLines3 k ∨ r ∈ singerLines3 l) :
    p ∈ singerLines3 k ∧ q ∈ singerLines3 k ∧ r ≠ p ∧ r ≠ q := by
  have hrp : r ≠ p := by
    intro he
    obtain ⟨l, hql, hpl, hrl⟩ := separating_line p q r hpq (by simpa [he] using hpq)
    rcases hp l hql hpl with hpk | hrl'
    · exact hrk (he ▸ hpk)
    · exact hrl hrl'
  have hrq : r ≠ q := by
    intro he
    obtain ⟨l, hpl, hql, hrl⟩ := separating_line q p r hpq.symm (by simpa [he] using hpq.symm)
    rcases hq l hpl hql with hqk | hrl'
    · exact hrk (he ▸ hqk)
    · exact hrl hrl'
  have hpk : p ∈ singerLines3 k := by
    obtain ⟨l, hql, hpl, hrl⟩ := separating_line p q r hpq hrq
    exact (hp l hql hpl).resolve_right hrl
  have hqk : q ∈ singerLines3 k := by
    obtain ⟨l, hpl, hql, hrl⟩ := separating_line q p r hpq.symm hrp
    exact (hq l hpl hql).resolve_right hrl
  exact ⟨hpk, hqk, hrp, hrq⟩

lemma bad_family_forced_common_line
    (A B : Finset (Fin 13 × Fin 13)) (p q : Fin 13) (hpq : p ≠ q)
    (hB : ∀ b ∈ B, b.1 ∉ singerLines3 b.2)
    (hcross : ∀ a ∈ A, ∀ b ∈ B,
      a.1 ∈ singerLines3 b.2 ∨ b.1 ∈ singerLines3 a.2)
    (hp : ∀ l, q ∈ singerLines3 l → p ∉ singerLines3 l → (p, l) ∈ A)
    (hq : ∀ l, p ∈ singerLines3 l → q ∉ singerLines3 l → (q, l) ∈ A)
    (b : Fin 13 × Fin 13) (hb : b ∈ B) :
    p ∈ singerLines3 b.2 ∧ q ∈ singerLines3 b.2 ∧ b.1 ≠ p ∧ b.1 ≠ q := by
  apply forced_common_line p q b.1 b.2 hpq (hB b hb)
  · intro l hql hpl
    exact hcross (p, l) (hp l hql hpl) b hb
  · intro l hpl hql
    exact hcross (q, l) (hq l hpl hql) b hb

lemma bad_family_column_and_card
    (A B : Finset (Fin 13 × Fin 13)) (p q : Fin 13) (hpq : p ≠ q)
    (hB : ∀ b ∈ B, b.1 ∉ singerLines3 b.2)
    (hcross : ∀ a ∈ A, ∀ b ∈ B,
      a.1 ∈ singerLines3 b.2 ∨ b.1 ∈ singerLines3 a.2)
    (hp : ∀ l, q ∈ singerLines3 l → p ∉ singerLines3 l → (p, l) ∈ A)
    (hq : ∀ l, p ∈ singerLines3 l → q ∉ singerLines3 l → (q, l) ∈ A) :
    (∃ k : Fin 13, p ∈ singerLines3 k ∧ q ∈ singerLines3 k ∧
      ∀ b ∈ B, b.2 = k ∧ b.1 ≠ p ∧ b.1 ≠ q) ∧ B.card ≤ 9 := by
  obtain ⟨k, hpk, hqk⟩ := common_line p q
  have hcolumn : ∀ b ∈ B, b.2 = k ∧ b.1 ≠ p ∧ b.1 ≠ q := by
    intro b hb
    obtain ⟨hpb, hqb, hrp, hrq⟩ :=
      bad_family_forced_common_line A B p q hpq hB hcross hp hq b hb
    exact ⟨common_line_unique p q b.2 k hpq hpb hqb hpk hqk, hrp, hrq⟩
  refine ⟨⟨k, hpk, hqk, hcolumn⟩, ?_⟩
  have hsub : B ⊆ (Finset.univ.filter fun r : Fin 13 => r ∉ singerLines3 k).product {k} := by
    intro b hb
    have hbk := (hcolumn b hb).1
    apply Finset.mem_product.mpr
    constructor
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [hbk] using hB b hb
    · simpa using hbk
  have hcard := Finset.card_le_card hsub
  simpa [Finset.card_product, nonincident_point_count] using hcard

end PEqualNP.Outside.L_meta_2089.MergedPair

namespace PEqualNP.Outside.L_meta_2089.LinearBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Structural

private def BitsLE (xs ys : List Bool) : Prop :=
  ∀ i, xs.getD i false = true → ys.getD i false = true

private lemma append_mono {xs ys as bs : List Bool}
    (hlen : xs.length = ys.length) (hxy : BitsLE xs ys) (hab : BitsLE as bs) :
    BitsLE (xs ++ as) (ys ++ bs) := by
  intro i hi
  by_cases h : i < xs.length
  · rw [List.getD_append _ _ _ _ h] at hi
    rw [List.getD_append _ _ _ _ (hlen ▸ h)]
    exact hxy i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
    rw [List.getD_append_right _ _ _ _ (by omega), ← hlen]
    exact hab _ hi

private lemma gate_mono {g : Gate} (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    {xs ys : List Bool} (hxy : BitsLE xs ys) :
    g.op.eval (g.inputs.map fun i => xs.getD i false) = true →
      g.op.eval (g.inputs.map fun i => ys.getD i false) = true := by
  rcases hop with hop | hop
  · rw [hop]
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    rintro h _ ⟨i, hi, rfl⟩
    exact hxy i (h _ ⟨i, hi, rfl⟩)
  · rw [hop]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨_, ⟨i, hi, rfl⟩, h⟩
    exact ⟨_, ⟨i, hi, rfl⟩, hxy i h⟩

private def step (xs : List Bool) (g : Gate) : List Bool :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

private lemma fold_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (xs ys : List Bool) (hlen : xs.length = ys.length) (hxy : BitsLE xs ys) :
    BitsLE (gs.foldl step xs) (gs.foldl step ys) := by
  induction gs generalizing xs ys with
  | nil => exact hxy
  | cons g gs ih =>
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hlen]
    · apply append_mono hlen hxy
      intro i hi
      cases i with
      | zero => exact gate_mono (hgs g List.mem_cons_self) hxy hi
      | succ i => simp at hi

private lemma wire_true_mono {C : Circuit} (hC : Monotone2 C) {xs ys : List Bool}
    (hlen : xs.length = ys.length) (hxy : BitsLE xs ys) (i : ℕ) :
    (C.wires xs).getD i false = true → (C.wires ys).getD i false = true := by
  apply fold_mono C.gates _ xs ys hlen hxy i
  intro g hg
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hC g hg).1

private lemma ofFn_mono {n : ℕ} {f g : Fin n → Bool}
    (hfg : ∀ i, f i = true → g i = true) : BitsLE (List.ofFn f) (List.ofFn g) := by
  intro i hi
  by_cases h : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
    exact hfg ⟨i, h⟩ hi
  · have h' : (List.ofFn f).length ≤ i := by simpa using Nat.le_of_not_gt h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h'] at hi
    cases hi

lemma wire_monotone {n : ℕ} (C : Circuit) (hm : Monotone2 C) (w : ℕ) :
    Monotone (fun x : Fin n → Bool => value C x w) := by
  intro x y hxy
  cases hx : value C x w with
  | false => simp [hx]
  | true =>
    have hh : value C y w = true := by
      apply wire_true_mono hm (by simp) (ofFn_mono ?_) w hx
      intro i hi
      have h := hxy i
      rw [hi] at h
      exact Bool.eq_true_of_true_le h
    simp [hx, hh]

def single {n : ℕ} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

def support {n : ℕ} (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => value C (single i) w = true)

lemma single_le {n : ℕ} (x : Fin n → Bool) (i : Fin n) (hi : x i = true) :
    single i ≤ x := by
  intro j
  by_cases h : j = i
  · subst j
    simp [single, hi]
  · simp [single, h]

lemma private_quota {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (hmono : ∀ w, Monotone (fun x : Fin n → Bool => value C x w))
    (x : Fin n → Bool) (a : ℕ) (hoff : value C x a = false) :
    ∃ I : Finset ℕ, (support (n := n) C a).card ≤ I.card + 1 ∧
      ∀ i ∈ I, n ≤ i ∧ i < n + C.size ∧ i ≤ a ∧
        (gateAt C (i - n)).op = GateOp.or ∧ value C x i = false ∧
        2 ≤ (support (n := n) C i).card := by
  classical
  let G := (Finset.Ico n (n + C.size)).filter (fun w => value C x w = false)
  let O := G.filter (fun w => (gateAt C (w - n)).op = GateOp.or ∧
    2 ≤ (support (n := n) C w).card)
  let V : Option (Fin n) → ℕ → Bool := fun z w =>
    value C (z.elim x single) w
  have ginfo (w : ℕ) (hw : w ∈ G) :
      n ≤ w ∧ w < n + C.size ∧ value C x w = false := by
    simpa only [G, Finset.mem_filter, Finset.mem_Ico, and_assoc] using hw
  have step (w : ℕ) (hw : w ∈ G) : ∃ P : Finset ℕ,
      P.card ≤ 1 + (if w ∈ O then 1 else 0) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, V none r = false) ∧
      ∀ y, (∀ r ∈ P, V y r = false) → V y w = false := by
    obtain ⟨hn, hlt, hx⟩ := ginfo w hw
    by_cases hs : 2 ≤ (support (n := n) C w).card
    · obtain ⟨P, hc, hb, hp, ht⟩ := gate_false_step C hm x w hn hlt hx
      have hweight : orCharge (gateAt C (w - n)).op = (if w ∈ O then 1 else 0) := by
        cases h : (gateAt C (w - n)).op <;> simp [orCharge, O, hw, hs, h]
      refine ⟨P, by simpa only [hweight] using hc, hb, hp, ?_⟩
      intro y hy
      exact ht (y.elim x single) hy
    · let P := (support (n := n) C w).image Fin.val
      refine ⟨P, ?_, ?_, ?_, ?_⟩
      · have hc := Finset.card_image_le (f := Fin.val) (s := support (n := n) C w)
        change P.card ≤ _ at hc
        omega
      · intro r hr
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
        omega
      · intro r hr
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
        change value C x i.val = false
        rw [input_value]
        have htrue : value C (single i) w = true := (Finset.mem_filter.mp hi).2
        cases hxi : x i with
        | false => rfl
        | true =>
          have hle := hmono w (single_le x i hxi)
          change value C (single i) w ≤ value C x w at hle
          rw [htrue, hx] at hle
          exact Bool.noConfusion (Bool.eq_true_of_true_le hle)
      · intro y hy
        cases y with
        | none => exact hx
        | some i =>
          change value C (single i) w = false
          cases hv : value C (single i) w with
          | false => rfl
          | true =>
            have hi : i ∈ support (n := n) C w := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
            have hh := hy i.val (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
            change value C (single i) i.val = false at hh
            rw [input_value] at hh
            simp [single] at hh
  obtain ⟨B, hd, hc, hBx, hp⟩ := weighted_cut V none G O step (a + 1) {a}
    (by intro w hw _; obtain rfl := Finset.mem_singleton.mp hw; omega)
    (by intro w hw; obtain rfl := Finset.mem_singleton.mp hw; exact hoff)
  let I := O.filter (· < a + 1)
  let T := Finset.univ.filter (fun i : Fin n => i.val ∈ B)
  have hsub : support (n := n) C a ⊆ T := by
    intro i hi
    by_contra hn
    have hout : value C (single i) a = false := by
      apply hp (some i) ?_ a (by simp)
      intro w hw
      by_cases hwin : w < n
      · let j : Fin n := ⟨w, hwin⟩
        change value C (single i) j.val = false
        rw [input_value]
        have hne : j ≠ i := by
          intro h
          have : i.val ∈ B := h ▸ hw
          exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, this⟩)
        simp [single, hne]
      · by_cases htot : w < n + C.size
        · have hg : w ∈ G := Finset.mem_filter.mpr
            ⟨Finset.mem_Ico.mpr ⟨by omega, htot⟩, hBx w hw⟩
          exact (Finset.disjoint_left.mp hd hw hg).elim
        · exact missing_value C (single i) w (by omega)
    have hin : value C (single i) a = true := (Finset.mem_filter.mp hi).2
    exact Bool.noConfusion (hin.symm.trans hout)
  have hTc : T.card ≤ B.card := by
    rw [← Finset.card_image_of_injective T Fin.val_injective]
    apply Finset.card_le_card
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    exact (Finset.mem_filter.mp hi).2
  refine ⟨I, ?_, ?_⟩
  · have hBc : B.card ≤ I.card + 1 := by
      simpa only [Finset.card_singleton, I, Nat.add_comm] using hc
    exact (Finset.card_le_card hsub).trans (hTc.trans hBc)
  · intro i hi
    obtain ⟨hO, hia⟩ := Finset.mem_filter.mp hi
    obtain ⟨hG, hop, hs⟩ := Finset.mem_filter.mp hO
    obtain ⟨hni, hlt, hx⟩ := ginfo i hG
    exact ⟨hni, hlt, by omega, hop, hx, hs⟩


def complementInput {n : ℕ} (U : Finset (Fin n)) : Fin n → Bool :=
  fun i => decide (i ∉ U)

lemma support_subset {n : ℕ} (C : Circuit)
    (hmono : ∀ w, Monotone (fun x : Fin n → Bool => value C x w))
    (U : Finset (Fin n)) (w : ℕ) (hf : value C (complementInput U) w = false) :
    support (n := n) C w ⊆ U := by
  classical
  intro i hi
  by_contra hn
  have hx : complementInput U i = true := by simp [complementInput, hn]
  have hle := hmono w (single_le (complementInput U) i hx)
  change value C (single i) w ≤ value C (complementInput U) w at hle
  have ht := (Finset.mem_filter.mp hi).2
  rw [ht, hf] at hle
  exact Bool.noConfusion (Bool.eq_true_of_true_le hle)

noncomputable def orGates (C : Circuit) (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico n (n + C.size)).filter (fun w => (gateAt C (w - n)).op = GateOp.or)

lemma linear_outputs_bound {n m : ℕ} (C : Circuit) (hm : Monotone2 C)
    (U : Fin m → Finset (Fin n)) (a : Fin m → ℕ)
    (hcard : ∀ j, 4 ≤ (U j).card)
    (hinter : ∀ i j, i ≠ j → (U i ∩ U j).card ≤ 1)
    (hpos : ∀ j i, i ∈ U j → value C (single i) (a j) = true)
    (hneg : ∀ j, value C (complementInput (U j)) (a j) = false) :
    3 * m ≤ (orGates C n).card := by
  classical
  have hmono := fun w => wire_monotone (n := n) C hm w
  choose I hI using fun j => private_quota C hm hmono (complementInput (U j)) (a j) (hneg j)
  have hquota : ∀ j, 3 ≤ (I j).card := by
    intro j
    have hs : U j ⊆ support (n := n) C (a j) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos j i hi⟩
    have hc := Finset.card_le_card hs
    have hb := (hI j).1
    have hu := hcard j
    omega
  have hdisj : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ Finset.univ,
      i ≠ j → Disjoint (I i) (I j) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro w hwi hwj
    have hi := (hI i).2 w hwi
    have hj := (hI j).2 w hwj
    have hs : support (n := n) C w ⊆ U i ∩ U j :=
      Finset.subset_inter (support_subset C hmono (U i) w hi.2.2.2.2.1)
        (support_subset C hmono (U j) w hj.2.2.2.2.1)
    have hc := Finset.card_le_card hs
    have hlarge := hi.2.2.2.2.2
    have hsmall := hinter i j hij
    omega
  let J := Finset.univ.biUnion I
  have hJ : J.card = ∑ i : Fin m, (I i).card := by
    exact Finset.card_biUnion hdisj
  have hlow : 3 * m ≤ J.card := by
    rw [hJ]
    calc
      3 * m = ∑ _i : Fin m, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ i : Fin m, (I i).card := Finset.sum_le_sum fun i _ => hquota i
  apply hlow.trans
  apply Finset.card_le_card
  intro w hw
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hw
  have hi := (hI j).2 w hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hi.1, hi.2.1⟩, hi.2.2.2.1⟩


def planeSupport (p : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter fun l => ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma plane_support_properties :
    (∀ p, (planeSupport p).card = 4) ∧
    (∀ p q, p ≠ q → (planeSupport p ∩ planeSupport q).card = 1) := by
  unfold planeSupport
  decide +kernel

lemma plane_linear_outputs_bound (C : Circuit) (hm : Monotone2 C)
    (a : Fin 13 → ℕ)
    (hpos : ∀ p l, l ∈ planeSupport p → value C (single l) (a p) = true)
    (hneg : ∀ p, value C (complementInput (planeSupport p)) (a p) = false) :
    39 ≤ (orGates C 13).card := by
  apply linear_outputs_bound C hm planeSupport a
  · intro p
    exact (plane_support_properties.1 p).ge
  · intro p q hpq
    exact (plane_support_properties.2 p q hpq).le
  · exact hpos
  · exact hneg

end PEqualNP.Outside.L_meta_2089.LinearBound

namespace PEqualNP.Outside.L_meta_2089.CofactorBridge

def onePoint (p : Fin 13) (y : Fin 13 → Bool) (i : Fin 26) : Bool :=
  decide (i = Fin.castAdd 13 p ∨ ∃ l, i = Fin.natAdd 13 l ∧ y l = true)

lemma pair_le_onePoint (p l : Fin 13) (y : Fin 13 → Bool) (hy : y l = true) :
    ∀ i, pairInput p l i = true → onePoint p y i = true := by
  intro i hi
  simp only [pairInput, decide_eq_true_eq] at hi
  simp only [onePoint, decide_eq_true_eq]
  rcases hi with hi | hi
  · exact Or.inl hi
  · exact Or.inr ⟨l, hi, hy⟩

lemma onePoint_le_cut (p : Fin 13) (y : Fin 13 → Bool)
    (hy : ¬∃ l, incidence p l ∧ y l = true) :
    ∀ i, onePoint p y i = true → cutInput {p} i = true := by
  intro i hi
  simp only [onePoint, decide_eq_true_eq] at hi
  simp only [cutInput, decide_eq_true_eq]
  rcases hi with hi | ⟨l, hi, hyl⟩
  · exact Or.inl ⟨p, Finset.mem_singleton_self p, hi⟩
  · refine Or.inr ⟨l, hi, ?_⟩
    intro q hq
    obtain rfl := Finset.mem_singleton.mp hq
    exact fun hpl => hy ⟨l, hpl, hyl⟩

lemma rejected_cut_linear_cofactor (f : (Fin 26 → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → f a = true → f b = true)
    (p : Fin 13)
    (hpositive : ∀ l, incidence p l → f (pairInput p l) = true)
    (hnegative : f (cutInput {p}) = false) (y : Fin 13 → Bool) :
    f (onePoint p y) = decide (∃ l, (∃ d ∈ delta, p = l + d) ∧ y l = true) := by
  classical
  by_cases h : ∃ l, (∃ d ∈ delta, p = l + d) ∧ y l = true
  · rw [decide_eq_true h]
    obtain ⟨l, hpl, hl⟩ := h
    exact hmono _ _ (pair_le_onePoint p l y hl) (hpositive l hpl)
  · rw [decide_eq_false h]
    apply Bool.eq_false_iff.mpr
    intro hf
    have hc := hmono _ _ (onePoint_le_cut p y h) hf
    exact Bool.noConfusion (hc.symm.trans hnegative)

lemma select_linear_factors (f g : (Fin 26 → Bool) → Bool)
    (hfmono : ∀ a b, (∀ i, a i = true → b i = true) → f a = true → f b = true)
    (hgmono : ∀ a b, (∀ i, a i = true → b i = true) → g a = true → g b = true)
    (hpositive : ∀ p l, incidence p l →
      (f (pairInput p l) && g (pairInput p l)) = true)
    (hnegative : ∀ A, isClosed A → isDegenerate A →
      (f (cutInput A) && g (cutInput A)) = false) :
    ∃ choose : Fin 13 → Bool, ∀ p y,
      (if choose p then f else g) (onePoint p y) =
        decide (∃ l, (∃ d ∈ delta, p = l + d) ∧ y l = true) := by
  classical
  refine ⟨fun p => decide (f (cutInput {p}) = false), ?_⟩
  intro p y
  have hn := hnegative {p} (singleton_maximal p) (singleton_degenerate p)
  by_cases hf : f (cutInput {p}) = false
  · simp only [decide_eq_true hf, ↓reduceIte]
    apply rejected_cut_linear_cofactor f hfmono p _ hf y
    intro l hl
    have hp : f (pairInput p l) = true ∧ g (pairInput p l) = true := by
      simpa using hpositive p l hl
    exact hp.1
  · have hg : g (cutInput {p}) = false := by
      cases hff : f (cutInput {p}) with
      | false => exact False.elim (hf hff)
      | true => simpa [hff] using hn
    simp only [decide_eq_false hf, Bool.false_eq_true, ↓reduceIte]
    apply rejected_cut_linear_cofactor g hgmono p _ hg y
    intro l hl
    have hp : f (pairInput p l) = true ∧ g (pairInput p l) = true := by
      simpa using hpositive p l hl
    exact hp.2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity Structural

lemma select_wire_linear_factors (C : Circuit) (hm : Monotone2 C) (a b : ℕ)
    (hpositive : ∀ p l, incidence p l →
      (value C (pairInput p l) a && value C (pairInput p l) b) = true)
    (hnegative : ∀ A, isClosed A → isDegenerate A →
      (value C (cutInput A) a && value C (cutInput A) b) = false) :
    ∃ choose : Fin 13 → Bool, ∀ p y,
      value C (onePoint p y) (if choose p then a else b) =
        decide (∃ l, (∃ d ∈ delta, p = l + d) ∧ y l = true) := by
  have monotone_wire (w : ℕ) : ∀ x y : Fin 26 → Bool,
      (∀ i, x i = true → y i = true) →
        value C x w = true → value C y w = true := by
    intro x y hxy hx
    have hh : value C x w ≤ value C y w := by
      apply LinearBound.wire_monotone C hm w
      intro i
      cases he : x i with
      | false => simp
      | true => simp [hxy i he]
    exact Bool.eq_true_of_true_le (hx ▸ hh)
  obtain ⟨choose, hc⟩ := select_linear_factors (fun x => value C x a)
    (fun x => value C x b) (monotone_wire a) (monotone_wire b) hpositive hnegative
  refine ⟨choose, ?_⟩
  intro p y
  cases hp : choose p <;> simpa [hp] using hc p y

end PEqualNP.Outside.L_meta_2089.CofactorBridge

namespace PEqualNP.Outside.L_meta_2089.CofactorQuota

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open Structural LinearBound

def testSupport {n m : ℕ} (C : Circuit) (Y : Fin m → Fin n → Bool) (w : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun j => value C (Y j) w = true

lemma test_quota {n m : ℕ} (C : Circuit) (hm : Monotone2 C)
    (Y : Fin m → Fin n → Bool) (x : Fin n → Bool)
    (hraw : ∀ i : Fin n, x i = false →
      (Finset.univ.filter fun j => Y j i = true).card ≤ 1)
    (a : ℕ) (hoff : value C x a = false) :
    ∃ I : Finset ℕ, (testSupport C Y a).card ≤ I.card + 1 ∧
      ∀ i ∈ I, n ≤ i ∧ i < n + C.size ∧ i ≤ a ∧
        (gateAt C (i - n)).op = GateOp.or ∧ value C x i = false ∧
        2 ≤ (testSupport C Y i).card := by
  classical
  let G := (Finset.Ico n (n + C.size)).filter
    (fun w => value C x w = false ∧ 2 ≤ (testSupport C Y w).card)
  let O := G.filter fun w => (gateAt C (w - n)).op = GateOp.or
  let V : Option (Fin m) → ℕ → Bool := fun z w => value C (z.elim x Y) w
  have ginfo (w : ℕ) (hw : w ∈ G) : n ≤ w ∧ w < n + C.size ∧
      value C x w = false ∧ 2 ≤ (testSupport C Y w).card := by
    simpa only [G, Finset.mem_filter, Finset.mem_Ico, and_assoc] using hw
  have step (w : ℕ) (hw : w ∈ G) : ∃ P : Finset ℕ,
      P.card ≤ 1 + (if w ∈ O then 1 else 0) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, V none r = false) ∧
      ∀ y, (∀ r ∈ P, V y r = false) → V y w = false := by
    obtain ⟨hn, hlt, hx, _⟩ := ginfo w hw
    obtain ⟨P, hc, hb, hp, ht⟩ := gate_false_step C hm x w hn hlt hx
    have he : orCharge (gateAt C (w - n)).op = (if w ∈ O then 1 else 0) := by
      cases h : (gateAt C (w - n)).op <;> simp [orCharge, O, hw, h]
    exact ⟨P, by simpa only [he] using hc, hb, hp, fun y hy => ht (y.elim x Y) hy⟩
  obtain ⟨B, hd, hc, hBx, hp⟩ := weighted_cut V none G O step (a + 1) {a}
    (by intro w hw _; obtain rfl := Finset.mem_singleton.mp hw; omega)
    (by intro w hw; obtain rfl := Finset.mem_singleton.mp hw; exact hoff)
  have hsmall : ∀ w ∈ B, (testSupport C Y w).card ≤ 1 := by
    intro w hw
    by_cases hn : w < n
    · let i : Fin n := ⟨w, hn⟩
      have hx : x i = false := by
        rw [← input_value C x i]
        exact hBx w hw
      have he : testSupport C Y w = Finset.univ.filter fun j => Y j i = true := by
        ext j
        simp only [testSupport, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Iff.of_eq (congrArg (· = true) (input_value C (Y j) i))
      rw [he]
      exact hraw i hx
    · by_cases htotal : w < n + C.size
      · by_contra hlarge
        have hg : w ∈ G := Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨by omega, htotal⟩, hBx w hw, by omega⟩
        exact Finset.disjoint_left.mp hd hw hg
      · have he : testSupport C Y w = ∅ := by
          ext j
          simp [testSupport, missing_value C (Y j) w (by omega)]
        simp [he]
  have hsub : testSupport C Y a ⊆ B.biUnion (testSupport C Y) := by
    intro j hj
    by_contra hn
    have hout : value C (Y j) a = false := by
      apply hp (some j) ?_ a (by simp)
      intro w hw
      change value C (Y j) w = false
      cases hv : value C (Y j) w with
      | false => rfl
      | true =>
        exact (hn (Finset.mem_biUnion.mpr ⟨w, hw,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩)).elim
    exact Bool.noConfusion ((Finset.mem_filter.mp hj).2.symm.trans hout)
  have hsize : (testSupport C Y a).card ≤ B.card := by
    calc
      (testSupport C Y a).card ≤ (B.biUnion (testSupport C Y)).card := Finset.card_le_card hsub
      _ ≤ ∑ w ∈ B, (testSupport C Y w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ B, 1 := Finset.sum_le_sum hsmall
      _ = B.card := by simp
  let I := O.filter (· < a + 1)
  refine ⟨I, ?_, ?_⟩
  · have hb : B.card ≤ I.card + 1 := by
      simpa only [Finset.card_singleton, I, Nat.add_comm] using hc
    exact hsize.trans hb
  · intro i hi
    obtain ⟨hO, hia⟩ := Finset.mem_filter.mp hi
    obtain ⟨hG, hop⟩ := Finset.mem_filter.mp hO
    obtain ⟨hn, hlt, hx, hs⟩ := ginfo i hG
    exact ⟨hn, hlt, by omega, hop, hx, hs⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
lemma point_raw_support : ∀ (p : Fin 13) (i : Fin 26), cutInput {p} i = false →
    (Finset.univ.filter fun l : Fin 13 => pairInput p l i = true).card ≤ 1 := by
  unfold cutInput pairInput delta
  decide +kernel

lemma point_cofactor_quota (C : Circuit) (hm : Monotone2 C) (p : Fin 13) (a : ℕ)
    (hpos : ∀ l, incidence p l → value C (pairInput p l) a = true)
    (hneg : value C (cutInput {p}) a = false) :
    ∃ I : Finset ℕ, 3 ≤ I.card ∧
      ∀ i ∈ I, 26 ≤ i ∧ i < 26 + C.size ∧ i ≤ a ∧
        (gateAt C (i - 26)).op = GateOp.or ∧ value C (cutInput {p}) i = false ∧
        2 ≤ (testSupport C (pairInput p) i).card := by
  obtain ⟨I, hc, hI⟩ := test_quota C hm (pairInput p) (cutInput {p}) (point_raw_support p) a hneg
  have hs : planeSupport p ⊆ testSupport C (pairInput p) a := by
    intro l hl
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos l ?_⟩
    exact (Finset.mem_filter.mp hl).2
  have hn := Finset.card_le_card hs
  have hg := plane_support_properties.1 p
  exact ⟨I, by omega, hI⟩


lemma joint_point_certificates (C : Circuit) (hm : Monotone2 C) (a b : ℕ)
    (hpositive : ∀ p l, incidence p l →
      (value C (pairInput p l) a && value C (pairInput p l) b) = true)
    (hnegative : ∀ A, isClosed A → isDegenerate A →
      (value C (cutInput A) a && value C (cutInput A) b) = false) :
    ∀ p : Fin 13, ∃ I : Finset ℕ, 3 ≤ I.card ∧
      ∀ i ∈ I, 26 ≤ i ∧ i < 26 + C.size ∧ i ≤ max a b ∧
        (gateAt C (i - 26)).op = GateOp.or ∧ value C (cutInput {p}) i = false ∧
        2 ≤ (testSupport C (pairInput p) i).card := by
  intro p
  have hn : value C (cutInput {p}) a = false ∨ value C (cutInput {p}) b = false := by
    have h := hnegative {p} (singleton_maximal p) (singleton_degenerate p)
    cases ha : value C (cutInput {p}) a with
    | false => exact Or.inl rfl
    | true => exact Or.inr (by simpa [ha] using h)
  have run (w : ℕ) (hw : w ≤ max a b)
      (hp : ∀ l, incidence p l → value C (pairInput p l) w = true)
      (hn : value C (cutInput {p}) w = false) :
      ∃ I : Finset ℕ, 3 ≤ I.card ∧
        ∀ i ∈ I, 26 ≤ i ∧ i < 26 + C.size ∧ i ≤ max a b ∧
          (gateAt C (i - 26)).op = GateOp.or ∧ value C (cutInput {p}) i = false ∧
          2 ≤ (testSupport C (pairInput p) i).card := by
    obtain ⟨I, hc, hI⟩ := point_cofactor_quota C hm p w hp hn
    refine ⟨I, hc, ?_⟩
    intro i hi
    obtain ⟨hl, hu, hw', hop, hf, hs⟩ := hI i hi
    exact ⟨hl, hu, hw'.trans hw, hop, hf, hs⟩
  rcases hn with ha | hb
  · apply run a (le_max_left a b) _ ha
    intro l hl
    have hh : value C (pairInput p l) a = true ∧ value C (pairInput p l) b = true := by
      simpa using hpositive p l hl
    exact hh.1
  · apply run b (le_max_right a b) _ hb
    intro l hl
    have hh : value C (pairInput p l) a = true ∧ value C (pairInput p l) b = true := by
      simpa using hpositive p l hl
    exact hh.2

end PEqualNP.Outside.L_meta_2089.CofactorQuota
