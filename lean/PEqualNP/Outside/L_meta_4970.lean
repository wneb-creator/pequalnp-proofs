import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_4970

namespace StarLedger

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
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (w : ℕ) (hn : n ≤ w) (hw : w < n + C.size) :
    ∃ P : Finset ℕ, P.card ≤ 2 ∧ (∀ r ∈ P, r < w) ∧
      ∀ (x y : Fin n → Bool), (∀ r ∈ P, value C x r = true → value C y r = true) →
        value C x w = true → value C y w = true := by
  let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
  obtain ⟨hop, hlen⟩ := hG g (List.getElem_mem _)
  obtain ⟨a, b, hab⟩ : ∃ a b : ℕ, g.inputs = [a, b] := by
    cases h : g.inputs with
    | nil => simp [h] at hlen
    | cons a rest =>
      cases rest with
      | nil => simp [h] at hlen
      | cons b tail =>
        have : tail = [] := by simpa [h] using hlen
        exact ⟨a, b, by simp [this]⟩
  let P := ({a, b} : Finset ℕ).filter (· < w)
  refine ⟨P, (Finset.card_filter_le _ _).trans ?_, ?_, ?_⟩
  · by_cases h : a = b <;> simp [h, Finset.card_insert_of_notMem]
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro x y hxy hx
    have hr (r : ℕ) (hr : r ∈ ({a, b} : Finset ℕ)) :
        (if r < w then value C x r else false) = true →
        (if r < w then value C y r else false) = true := by
      by_cases h : r < w
      · simpa [h] using hxy r (Finset.mem_filter.mpr ⟨hr, h⟩)
      · simp [h]
    have ha := hr a (by simp)
    have hb := hr b (by simp)
    have formula (z : Fin n → Bool) :
        value C z w = g.op.eval
          [if a < w then value C z a else false, if b < w then value C z b else false] := by
      simpa [g, hab] using gate_value C z w hn hw
    rw [formula x] at hx
    rw [formula y]
    rcases hop with hop | hop
    · simp only [hop, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
        Bool.and_eq_true] at hx ⊢
      exact ⟨ha hx.1, hb hx.2⟩
    · simp only [hop, GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
        Bool.or_eq_true] at hx ⊢
      exact hx.imp ha hb

lemma value_mono {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
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

lemma cut {n : ℕ} (C : Circuit)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
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

def assigned {n : ℕ} (C : Circuit) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.Ico n (n + C.size)).filter fun w => support C w ⊆ T ∧ 2 ≤ (support (n := n) C w).card

lemma card_assigned {n k c : ℕ} (C : Circuit) (T : Finset (Fin n)) (o : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hsparse : ∀ x : Fin n → Bool, (Finset.univ.filter (fun q => x q = true)).card ≤ k →
      (∀ q ∈ T, x q = false) → value C x o = false)
    (hk : c ≤ k) (hc : c + 1 ≤ (support (n := n) C o).card) : c ≤ (assigned C T).card := by
  classical
  let G := assigned C T
  by_contra! hsmall
  have hgate : ∀ w ∈ G, n ≤ w ∧ w < n + C.size := by
    intro w hw
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hw).1
  obtain ⟨B, hd, hBcard, hcut⟩ := cut C hG G hgate (n + C.size) {o}
    (fun w _ hw => (hgate w hw).2)
  have hb : B.card ≤ c := by
    have hfilter := Finset.card_filter_le G (fun w => w < n + C.size)
    simp only [Finset.card_singleton] at hBcard
    change G.card < c at hsmall
    omega
  let clean (w : ℕ) : Finset (Fin n) := if support C w ⊆ T then support C w else ∅
  have hclean : ∀ w ∈ B, (clean w).card ≤ 1 := by
    intro w hw
    by_cases hs : support C w ⊆ T
    · change (if support C w ⊆ T then support (n := n) C w else ∅).card ≤ 1
      rw [ite_eq_left hs]
      by_contra! hlarge
      exact Finset.disjoint_left.mp hd hw
        (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (support_gate C w (by omega)), hs, by omega⟩)
    · simp [clean, hs]
  have hcover : (B.biUnion clean).card < (support (n := n) C o).card := by
    have h := Finset.card_biUnion_le_card_mul B clean 1 hclean
    simp only [mul_one] at h
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcover
  let D := B.filter (fun w => ¬ support C w ⊆ T)
  have hout (w : {w // w ∈ D}) : ∃ q : Fin n, q ∈ support C w.val ∧ q ∉ T := by
    by_contra! h
    exact (Finset.mem_filter.mp w.property).2 h
  choose q hq using hout
  let U := D.attach.image q
  let y : Fin n → Bool := fun r => decide (r ∈ U)
  have hu : U.card ≤ k := calc
    U.card ≤ D.attach.card := Finset.card_image_le
    _ = D.card := Finset.card_attach
    _ ≤ B.card := Finset.card_filter_le _ _
    _ ≤ k := hb.trans hk
  have hyfalse : value C y o = false := by
    apply hsparse y
    · have hset : Finset.univ.filter (fun r => y r = true) = U := by ext r; simp [y]
      rwa [hset]
    · intro r hr
      have hnot : r ∉ U := by
        intro hmem
        obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hmem
        exact (hq w).2 hr
      simp [y, hnot]
  have hytrue : value C y o = true := by
    apply hcut (fun r => decide (r = p)) y _ o (Finset.mem_singleton_self o) ((mem_support C o p).mp hp)
    intro w hw hx
    by_cases hs : support C w ⊆ T
    · exact False.elim (hpnot (Finset.mem_biUnion.mpr
        ⟨w, hw, by simpa only [clean, ite_eq_left hs, mem_support] using hx⟩))
    · let d : {w // w ∈ D} := ⟨w, Finset.mem_filter.mpr ⟨hw, hs⟩⟩
      apply value_mono C hG (fun r => decide (r = q d)) y _ w ((mem_support C w (q d)).mp (hq d).1)
      intro r hr
      have he : r = q d := of_decide_eq_true hr
      subst r
      have hm : q d ∈ U := Finset.mem_image_of_mem q (Finset.mem_attach D d)
      simp [y, hm]
  simp [hyfalse] at hytrue


lemma assigned_disjoint {n : ℕ} (C : Circuit) (S T : Finset (Fin n))
    (hst : (S ∩ T).card ≤ 1) : Disjoint (assigned C S) (assigned C T) := by
  classical
  refine Finset.disjoint_left.mpr fun w hws hwt => ?_
  have hs := (Finset.mem_filter.mp hws).2
  have ht := (Finset.mem_filter.mp hwt).2
  have hsub : support C w ⊆ S ∩ T := fun p hp => Finset.mem_inter.mpr ⟨hs.1 hp, ht.1 hp⟩
  have hle := Finset.card_le_card hsub
  omega

lemma pure_or_card_assigned {n : ℕ} (C : Circuit) (Q T : Finset (Fin n)) (o : ℕ)
    (hG : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hQT : Q ⊆ T)
    (hf : ∀ x : Fin n → Bool, value C x o = decide (∃ q ∈ Q, x q = true)) :
    Q.card - 1 ≤ (assigned C T).card := by
  classical
  by_cases hQ : Q.Nonempty
  · have hsupport : support C o = Q := by
      ext p
      simp only [mem_support, hf, decide_eq_true_eq]
      simp
    apply card_assigned (k := n) C T o hG
    · intro x _ hx
      rw [hf]
      apply decide_eq_false_iff_not.mpr
      rintro ⟨q, hq, htrue⟩
      simp [hx q (hQT hq)] at htrue
    · exact (Nat.sub_le _ _).trans (by simpa using Finset.card_le_univ Q)
    · rw [hsupport]
      exact le_of_eq (Nat.sub_add_cancel (Finset.card_pos.mpr hQ))
  · simp [Finset.not_nonempty_iff_eq_empty.mp hQ]

end StarLedger

namespace ReadObstruction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def duplicateStar : Circuit :=
  ⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.and, [4, 4]⟩], 5⟩

lemma duplicateStar_properties :
    PEqualNP.TopForm.IsAO2 3 duplicateStar ∧
    (∀ x : Fin 3 → Bool, circuitFun 3 duplicateStar x = (x 0 && (x 1 || x 2))) ∧
    PEqualNP.TwoColour.tCount 3 duplicateStar (fun i => decide (1 ≤ i)) = 0 ∧
    ¬ PEqualNP.ReadK.IsReadK 3 duplicateStar 1 := by
  decide +kernel

lemma duplicateStar_service (a : Fin 1) (b : Fin 2) :
    ∃ (j : ℕ) (Q : Finset (Fin 2)), j < duplicateStar.gates.length ∧
      (gateAt duplicateStar j).op = GateOp.or ∧ 2 ≤ Q.card ∧ b ∈ Q ∧
      (∀ b' ∈ Q, (a, b') ∈ (Finset.univ : Finset (Fin 1 × Fin 2))) ∧
      ∀ x : Fin (1 + 2) → Bool,
        (duplicateStar.wires (List.ofFn x)).getD (1 + 2 + j) false =
          decide (∃ b' ∈ Q, x (Fin.natAdd 1 b') = true) := by
  refine ⟨0, Finset.univ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · rfl
  · decide
  · simp
  · simp
  · decide +kernel

end ReadObstruction

namespace Structure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma or_support_eq {V : Type*} [Fintype V] [DecidableEq V] (A B : Finset V)
    (h : ∀ x : V → Bool, decide (∃ a ∈ A, x a = true) =
      decide (∃ b ∈ B, x b = true)) : A = B := by
  ext v
  have hv := h (fun w => decide (w = v))
  simpa using hv

lemma two_members {V : Type*} [DecidableEq V] (A : Finset V) (hA : 2 ≤ A.card) :
    ∃ a ∈ A, ∃ b ∈ A, a ≠ b := by
  exact Finset.one_lt_card.mp (by omega)

lemma centre_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (a a' : Fin p) (Q : Finset (Fin l)) (hq : 2 ≤ Q.card)
    (ha : ∀ b ∈ Q, (a,b) ∈ E) (ha' : ∀ b ∈ Q, (a',b) ∈ E) : a = a' := by
  by_contra hne
  obtain ⟨b,hb,b',hb',hne'⟩ := two_members Q hq
  exact hE a a' b b' hne hne' ⟨ha b hb,ha b' hb',ha' b hb,ha' b' hb'⟩

lemma centre_unique_right {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (b b' : Fin l) (P : Finset (Fin p)) (hp : 2 ≤ P.card)
    (hb : ∀ a ∈ P, (a,b) ∈ E) (hb' : ∀ a ∈ P, (a,b') ∈ E) : b = b' := by
  by_contra hne
  obtain ⟨a,ha,a',ha',hne'⟩ := two_members P hp
  exact hE a a' b b' hne' hne ⟨hb a ha,hb' a ha,hb a' ha',hb' a' ha'⟩

lemma row_support_eq {p l : ℕ} (Q R : Finset (Fin l))
    (h : ∀ x : Fin (p+l) → Bool,
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) =
      decide (∃ b ∈ R, x (Fin.natAdd p b) = true)) : Q = R := by
  apply or_support_eq
  intro y
  have hx := h (Fin.addCases (fun _ => false) y)
  simpa using hx

lemma col_support_eq {p l : ℕ} (P R : Finset (Fin p))
    (h : ∀ x : Fin (p+l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
      decide (∃ a ∈ R, x (Fin.castAdd l a) = true)) : P = R := by
  apply or_support_eq
  intro y
  have hx := h (Fin.addCases y (fun _ => false))
  simpa using hx

lemma opposite_support_ne {p l : ℕ} (P : Finset (Fin p)) (Q : Finset (Fin l))
    (hP : P.Nonempty)
    (h : ∀ x : Fin (p+l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) : False := by
  have hx := h (Fin.addCases (fun _ => true) (fun _ => false))
  have hempty : ∀ a, a ∉ P := by simpa using hx
  obtain ⟨a, ha⟩ := hP
  exact hempty a ha

def Witness (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (j : ℕ) (v : Fin (p+l)) : Prop :=
  (∃ (a : Fin p) (Q : Finset (Fin l)), v = Fin.castAdd l a ∧ 2 ≤ Q.card ∧
    (∀ b ∈ Q, (a,b) ∈ E) ∧ ∀ x : Fin (p+l) → Bool,
      (C.wires (List.ofFn x)).getD (p+l+j) false =
        decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) ∨
  (∃ (b : Fin l) (P : Finset (Fin p)), v = Fin.natAdd p b ∧ 2 ≤ P.card ∧
    (∀ a ∈ P, (a,b) ∈ E) ∧ ∀ x : Fin (p+l) → Bool,
      (C.wires (List.ofFn x)).getD (p+l+j) false =
        decide (∃ a ∈ P, x (Fin.castAdd l a) = true))

lemma witness_unique {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    {j : ℕ} {v w : Fin (p+l)} (hv : Witness p l E C j v)
    (hw : Witness p l E C j w) : v = w := by
  rcases hv with ⟨a,Q,rfl,hQ,ha,hv⟩ | ⟨b,P,rfl,hP,hb,hv⟩
  · rcases hw with ⟨a',R,rfl,hR,ha',hw⟩ | ⟨b,R,rfl,hR,hb,hw⟩
    · have hQR : Q = R := row_support_eq Q R (fun x => (hv x).symm.trans (hw x))
      subst R
      exact congrArg (Fin.castAdd l) (centre_unique E hE a a' Q hQ ha ha')
    · exact (opposite_support_ne R Q (Finset.card_pos.mp (by omega))
        (fun x => (hw x).symm.trans (hv x))).elim
  · rcases hw with ⟨a,R,rfl,hR,ha,hw⟩ | ⟨b',R,rfl,hR,hb',hw⟩
    · exact (opposite_support_ne P R (Finset.card_pos.mp (by omega))
        (fun x => (hv x).symm.trans (hw x))).elim
    · have hPR : P = R := col_support_eq P R (fun x => (hv x).symm.trans (hw x))
      subst R
      exact congrArg (Fin.natAdd p) (centre_unique_right E hE b b' P hP hb hb')

lemma witness_cover_bound {p l : ℕ} (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (J : Finset ℕ)
    (hcover : ∀ (a : Fin p) (b : Fin l), (a,b) ∈ E →
      ∃ j ∈ J, Witness p l E C j (Fin.castAdd l a) ∨
        Witness p l E C j (Fin.natAdd p b)) :
    ∃ S : Finset (Fin (p+l)),
      (∀ (a : Fin p) (b : Fin l), (a,b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧ S.card ≤ J.card := by
  classical
  let S : Finset (Fin (p+l)) := Finset.univ.filter fun v => ∃ j ∈ J, Witness p l E C j v
  have hs (v : {v // v ∈ S}) : ∃ j : {j // j ∈ J}, Witness p l E C j v := by
    obtain ⟨j,hj,hv⟩ := (Finset.mem_filter.mp v.property).2
    exact ⟨⟨j,hj⟩,hv⟩
  let f : {v // v ∈ S} → {j // j ∈ J} := fun v => Classical.choose (hs v)
  have hf (v : {v // v ∈ S}) : Witness p l E C (f v) v := Classical.choose_spec (hs v)
  have hinj : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    have hw := hf w
    rw [← h] at hw
    exact witness_unique E C hE (hf v) hw
  refine ⟨S, ?_, ?_⟩
  · intro a b he
    obtain ⟨j,hj,h⟩ := hcover a b he
    rcases h with ha | hb
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hj,ha⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,hj,hb⟩)
  · simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

end Structure

namespace OrPartition

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z : X) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
    ∃ a b, g.op.eval (g.inputs.map (f z)) = false →
      (f z a = false ∧ f z b = false ∧
        ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y a = true ∨ f y b = true) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · right
      exact ⟨0, 0, by simp [GateOp.eval]⟩
    · left
      simp [GateOp.eval]
  | [a], _ =>
    right
    refine ⟨a, a, ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · right
      by_cases h : f z a = false
      · refine ⟨a, a, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro _
        exact ⟨h, h, fun y hy => Or.inl hy.1⟩
      · refine ⟨b, b, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro hz
        have hb : f z b = false := by
          cases ha : f z a <;> cases hb : f z b <;> simp_all
        exact ⟨hb, hb, fun y hy => Or.inl hy.2⟩
    · right
      refine ⟨a, b, ?_⟩
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff]
      intro hz
      exact ⟨hz.1, hz.2, fun y hy => hy⟩
  | _ :: _ :: _ :: _, h => simp at h

def Zof {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ S)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val gs (Zof S) i = false → val gs (eof u) i = true → val gs (eof v) i = true →
    u ∈ S ∧ l u = l v

def Cnt {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof S) i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true

open Classical in
noncomputable def D {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i =>
    Cnt S gs i ∧ (gs[i - n]?.map Gate.op) = some GateOp.or

lemma D_mono {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D S gs ⊆ D S (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huv, hu, hv⟩ := hi.2.1
  refine ⟨⟨?_, u, v, huv, ?_, ?_⟩, ?_⟩
  · rw [val_snoc, if_neg hne]; exact hz
  · rw [val_snoc, if_neg hne]; exact hu
  · rw [val_snoc, if_neg hne]; exact hv
  · rw [List.getElem?_append_left (by omega)]
    exact hi.2.2

lemma and_false_parent {X : Type} (g : Gate) (hop : g.op = GateOp.and)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z u v : X)
    (hz : g.op.eval (g.inputs.map (f z)) = false)
    (hu : g.op.eval (g.inputs.map (f u)) = true)
    (hv : g.op.eval (g.inputs.map (f v)) = true) :
    ∃ r, f z r = false ∧ f u r = true ∧ f v r = true := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen hz hu hv
  subst op
  match ins, hlen with
  | [], _ => simp [GateOp.eval] at hz
  | [a], _ => exact ⟨a, by simpa [GateOp.eval] using hz,
      by simpa [GateOp.eval] using hu, by simpa [GateOp.eval] using hv⟩
  | [a,b], _ =>
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true, Bool.and_eq_true] at hu hv
    by_cases ha : f z a = false
    · exact ⟨a, ha, hu.1, hv.1⟩
    · refine ⟨b, ?_, hu.2, hv.2⟩
      cases hza : f z a <;> cases hzb : f z b <;> simp_all [GateOp.eval]
  | _ :: _ :: _ :: _, h => simp at h

lemma main_inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ l : Fin n → Fin n, Inv S gs l ∧ S.card ≤ (S.image l).card + (D S gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, Zof, eof, decide_eq_false_iff_not, not_not,
        decide_eq_true_eq] at hz hu hv
      subst hu
      subst hv
      exact ⟨hz, rfl⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, hinv, hcard⟩ := ih (fun g' hg' => hg g' (by simp [hg']))
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, if_pos hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, if_neg hi]
    have key : P (Zof S) = false → ∀ u, P (eof u) = true →
        u ∈ S ∧ ∃ A B : Fin n → Prop, (∀ w, P (eof w) = true → A w ∨ B w) ∧
          (∀ w w', A w → A w' → l w = l w') ∧ (∀ w w', B w → B w' → l w = l w') := by
      intro hz u hu
      rcases gate_cases g hop hlen (fun x j => val gs x j) (Zof S) with hall | ⟨a, b, hab⟩
      · have := hall (eof u)
        simp only [hP] at hu
        rw [this] at hu
        exact absurd hu (by simp)
      · obtain ⟨ha, hb, hy⟩ := hab hz
        refine ⟨?_, fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
          fun w hw => hy (eof w) hw, fun w w' hw hw' => (hinv a w w' ha hw hw').2,
          fun w w' hw hw' => (hinv b w w' hb hw hw').2⟩
        rcases hy (eof u) hu with h | h
        · exact (hinv a u u ha h h).1
        · exact (hinv b u u hb h h).1
    by_cases hm : P (Zof S) = false ∧ ∃ u v, P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, v0, hu0, hv0, hne⟩ := hm
      have hop_or : g.op = GateOp.or := by
        rcases hop with hop | hop
        · obtain ⟨r, hrz, hru, hrv⟩ := and_false_parent g hop hlen
            (fun x j => val gs x j) (Zof S) (eof u0) (eof v0) hz hu0 hv0
          exact False.elim (hne (hinv r u0 v0 hrz hru hrv).2)
        · exact hop
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, A, B, hAB, hA, hB⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          have two : ∀ w, P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hw
            rcases hAB w hw with h | h <;> rcases hAB u0 hu0 with h0 | h0 <;>
              rcases hAB v0 hv0 with h1 | h1
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inr (hA w v0 h h1)
            · exact absurd (hB u0 v0 h0 h1) hne
            · exact absurd (hA u0 v0 h0 h1) hne
            · exact Or.inr (hB w v0 h h1)
            · exact Or.inl (hB w u0 h h0)
            · exact Or.inl (hB w u0 h h0)
          have red : ∀ w, P (eof w) = true → (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hw
            rcases two w hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [if_pos h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u hiu, red v hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          obtain ⟨huS, hl⟩ := hinv i u v hiz hiu hiv
          refine ⟨huS, ?_⟩
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl]
      · have himg : S.image l ⊆
            insert (l v0) (S.image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [if_neg h]
        have h1 : (S.image l).card ≤
            (S.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNin : N ∈ D S (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ⟨?_, u0, v0, ?_, ?_, ?_⟩, ?_⟩
          · rw [hnew]; exact hz
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
          · simp [hN, hop_or]
        have hNnot : N ∉ D S gs := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico]
          intro h
          omega
        have h2 : (D S gs).card + 1 ≤ (D S (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact D_mono S gs g hi
        omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, -⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          by_contra hne
          exact hm ⟨hiz, u, v, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hiz hiu hiv
      · have := Finset.card_le_card (D_mono S gs g)
        omega


lemma roots_bound {n : ℕ} (gs : List Gate) (T : Finset (Fin n))
    (O : Finset ℕ) (Q : ℕ → Finset (Fin n)) (R : Finset (Fin n))
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hQT : ∀ o ∈ O, Q o ⊆ T)
    (hf : ∀ o ∈ O, ∀ x : Fin n → Bool, val gs x o = decide (∃ q ∈ Q o, x q = true))
    (hR : ∀ u ∈ T, ∃ r ∈ R, Relation.ReflTransGen
      (fun a b : Fin n => ∃ o ∈ O, a ∈ Q o ∧ b ∈ Q o) u r) :
    T.card ≤ R.card + (D T gs).card := by
  classical
  obtain ⟨l, hinv, hcard⟩ := main_inv T gs hg
  have hstep {u v : Fin n} (h : ∃ o ∈ O, u ∈ Q o ∧ v ∈ Q o) : l u = l v := by
    obtain ⟨o, ho, hu, hv⟩ := h
    have hz : val gs (Zof T) o = false := by
      rw [hf o ho]
      apply decide_eq_false_iff_not.mpr
      rintro ⟨q, hq, hval⟩
      have hqT := hQT o ho hq
      simp [Zof, hqT] at hval
    have he (w : Fin n) (hw : w ∈ Q o) : val gs (eof w) o = true := by
      rw [hf o ho]
      exact decide_eq_true ⟨w, hw, by simp [eof]⟩
    exact (hinv o u v hz (he u hu) (he v hv)).2
  have hpath {u v : Fin n} (h : Relation.ReflTransGen
      (fun a b : Fin n => ∃ o ∈ O, a ∈ Q o ∧ b ∈ Q o) u v) : l u = l v := by
    induction h with
    | refl => rfl
    | tail _ h ih => exact ih.trans (hstep h)
  have hsub : T.image l ⊆ R.image l := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨r, hr, hconn⟩ := hR u hu
    exact Finset.mem_image.mpr ⟨r, hr, (hpath hconn).symm⟩
  have hle := (Finset.card_le_card hsub).trans (Finset.card_image_le (s := R) (f := l))
  omega

end OrPartition

end PEqualNP.Outside.L_meta_4970
