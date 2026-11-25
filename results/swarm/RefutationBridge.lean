import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.RefutationBridge

lemma rectangle_degenerate {N : ℕ} {I : Fin N → Fin N → Prop}
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    {p p' l l' : Fin N} (hpl : I p l) (hpl' : I p l')
    (hp'l : I p' l) (hp'l' : I p' l') : p = p' ∨ l = l' := by
  by_cases hp : p = p'
  · exact Or.inl hp
  · obtain ⟨k, _, hk⟩ := hu p p' hp
    exact Or.inr ((hk l ⟨hpl, hp'l⟩).trans (hk l' ⟨hpl', hp'l'⟩).symm)

lemma point_lines_card {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hc : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) : (Finset.univ.filter fun l => I p l).card = q + 1 := by
  classical
  let L := Finset.univ.filter fun l => I p l
  let R := fun l => (Finset.univ.filter fun x => I x l).erase p
  have hcover : L.biUnion R = Finset.univ.erase p := by
    ext x
    constructor
    · intro hx
      obtain ⟨l, _, hx⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ _⟩
    · intro hx
      have hxp := (Finset.mem_erase.mp hx).1
      obtain ⟨l, hl, _⟩ := hu p x hxp.symm
      exact Finset.mem_biUnion.mpr ⟨l, by simp [L, hl.1], by simp [R, hxp, hl.2]⟩
  have hd : (L : Set (Fin N)).PairwiseDisjoint R := by
    intro l hl l' hl' hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    have hpx : p ≠ x := (Finset.mem_erase.mp hx).1.symm
    have hlp : I p l := (Finset.mem_filter.mp hl).2
    have hlp' : I p l' := (Finset.mem_filter.mp hl').2
    have hlx : I x l := (Finset.mem_filter.mp (Finset.mem_erase.mp hx).2).2
    have hlx' : I x l' := (Finset.mem_filter.mp (Finset.mem_erase.mp hx').2).2
    exact hne ((rectangle_degenerate hu hlp hlp' hlx hlx').resolve_left hpx)
  have hr (l : Fin N) (hl : l ∈ L) : (R l).card = q := by
    have hp : p ∈ Finset.univ.filter fun x => I x l := by
      simpa only [L, Finset.mem_filter, Finset.mem_univ, true_and] using hl
    simp only [R, Finset.card_erase_of_mem hp, hc]
    omega
  have he := Finset.card_biUnion hd
  rw [hcover, Finset.card_erase_of_mem (Finset.mem_univ p)] at he
  simp only [Finset.card_univ, Fintype.card_fin] at he
  have hsum : ∑ l ∈ L, (R l).card = L.card * q := by
    simp only [Finset.sum_congr rfl hr, Finset.sum_const, smul_eq_mul]
  rw [hsum] at he
  have : L.card * q = (q + 1) * q := by
    rw [← he, hN]
    simp only [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) this

lemma plane_cover_bound {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hc : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (hcover : ∀ p l, I p l → p ∈ A ∨ l ∈ B) :
    N ≤ A.card + B.card := by
  classical
  have hr := point_lines_card I hq hN hc hu
  have hrows (p : Fin N) : (∑ l : Fin N, if I p l then (1 : ℕ) else 0) = q + 1 := by
    simpa using hr p
  have hcols (l : Fin N) : (∑ p : Fin N, if I p l then (1 : ℕ) else 0) = q + 1 := by
    simpa using hc l
  have hineq : N * (q + 1) ≤ (A.card + B.card) * (q + 1) := by
    calc
      N * (q + 1) = ∑ p : Fin N, ∑ l : Fin N, if I p l then (1 : ℕ) else 0 := by
        simp [hrows]
      _ ≤ ∑ p : Fin N, ∑ l : Fin N,
          ((if p ∈ A then (if I p l then (1 : ℕ) else 0) else 0) +
            (if l ∈ B then (if I p l then (1 : ℕ) else 0) else 0)) := by
        apply Finset.sum_le_sum
        intro p _
        apply Finset.sum_le_sum
        intro l _
        by_cases hi : I p l
        · rcases hcover p l hi with hp | hl
          · simp [hi, hp]
          · simp [hi, hl]
        · simp [hi]
      _ = (A.card + B.card) * (q + 1) := by
        simp only [Finset.sum_add_distrib]
        have ha : (∑ p : Fin N, ∑ l : Fin N,
            if p ∈ A then (if I p l then (1 : ℕ) else 0) else 0) = A.card * (q + 1) := by
          simp [Finset.sum_ite_irrel, hrows]
        have hb : (∑ p : Fin N, ∑ l : Fin N,
            if l ∈ B then (if I p l then (1 : ℕ) else 0) else 0) = B.card * (q + 1) := by
          rw [Finset.sum_comm]
          simp [Finset.sum_ite_irrel, hcols]
        rw [ha, hb, Nat.add_mul]
  exact Nat.le_of_mul_le_mul_right hineq (by omega)

end PEqualNP.Outside.L_meta_2583.RefutationBridge

namespace PEqualNP.Outside.L_meta_2583.RefutationBridge.ReadLower



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def s2230_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2230_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2230_stepWire x := rfl

lemma s2230_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2230_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2230_stepWire]
    omega

lemma s2230_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2230_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2230_stepWire w g).length := by simp [s2230_stepWire]; omega
    rw [ih (s2230_stepWire w g) hlt]
    simp [s2230_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2230_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2230_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [s2230_wires_eq_foldl, s2230_foldl_stepWire_length, List.length_ofFn]

lemma s2230_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def s2230_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma s2230_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma s2230_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    s2230_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then s2230_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2230_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [s2230_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl s2230_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, s2230_foldl_stepWire_length, hpre_len]
  have hCj : s2230_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [s2230_W]
    rw [s2230_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [s2230_foldl_stepWire_getD_lt post (s2230_stepWire w0 gj) (n + k) (by simp [s2230_stepWire]; omega)]
    simp [s2230_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [s2230_W]
    rw [s2230_wires_eq_foldl, hgs, List.foldl_append]
    exact (s2230_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact s2230_getD_ge_length w0 i (by omega)

lemma s2230_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    s2230_W n C x u = x ⟨u, hu⟩ := by
  simp only [s2230_W]
  rw [s2230_wires_eq_foldl, s2230_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma s2230_orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma s2230_orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma s2230_orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma s2230_orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact s2230_orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma s2230_orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := s2230_split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [s2230_gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [s2230_orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, s2230_orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, s2230_orFold_getD_lt n post _ m (by omega)]
    exact s2230_orStep_getD_lt n _ gk m (by omega)
  have h3 := s2230_orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩

open PEqualNP.CleanedNonEdge PEqualNP.ReadK PEqualNP.TopForm

lemma s2230_orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    OrReaches n C (n + j) j := by
  unfold OrReaches
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, s2230_orSets_mem_iff n C j j hj]
  exact Or.inl rfl

lemma s2230_orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : OrReaches n C i g) : OrReaches n C (n + j) g := by
  unfold OrReaches at h ⊢
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left, s2230_orSets_mem_iff n C j g hj]
  exact Or.inr ⟨hop, i, hi, h.1, hlt, h.2⟩

lemma s2230_mem_filter_iff_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma s2230_mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold orIn
  exact ⟨fun h => ((s2230_mem_filter_iff_gen _ _ _ _).1 h).2,
    fun h => (s2230_mem_filter_iff_gen _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma s2230_orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ orIn n C i) : a ∈ orIn n C (n + j) := by
  rw [s2230_mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, s2230_orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, s2230_orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩

def s2230_FR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  match g.op with
  | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
  | _ => []

def s2230_stepR (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List (List ℕ)) :=
  R ++ [s2230_FR S k R g]

lemma s2230_readVectors_eq (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = C.gates.foldl (s2230_stepR S k) ((List.range n).map (leafVectors S k)) := by
  first
    | rfl
    | (unfold readVectors; congr 1; funext R g; rcases g with ⟨op, ins⟩; cases op <;> rfl)

lemma s2230_FR_or (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) (h : g.op = GateOp.or) :
    s2230_FR S k R g =
      (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) [] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.or := h
  subst h2
  rfl

lemma s2230_FR_and (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate)
    (h : g.op = GateOp.and) :
    s2230_FR S k R g = (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0] := by
  obtain ⟨op, ins⟩ := g
  have h2 : op = GateOp.and := h
  subst h2
  rfl

lemma s2230_foldR_length (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) :
    (gs.foldl (s2230_stepR S k) R).length = R.length + gs.length := by
  induction gs generalizing R with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2230_stepR]
    omega

lemma s2230_foldR_getD_lt (S : List ℕ) (k : ℕ) (gs : List Gate) (R : List (List (List ℕ))) (i : ℕ)
    (hi : i < R.length) : (gs.foldl (s2230_stepR S k) R).getD i [] = R.getD i [] := by
  induction gs generalizing R with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2230_stepR S k R g).length := by simp [s2230_stepR]; omega
    rw [ih (s2230_stepR S k R g) hlt]
    simp [s2230_stepR, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def s2230_RV (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) : List (List ℕ) :=
  (readVectors C n S k).getD w []

lemma s2230_RV_input (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (w : ℕ) (hw : w < n) :
    s2230_RV C n S k w = leafVectors S k w := by
  simp only [s2230_RV]
  rw [s2230_readVectors_eq, s2230_foldR_getD_lt S k C.gates ((List.range n).map (leafVectors S k)) w
    (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma s2230_RV_gate (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) (j : ℕ) (hj : j < C.gates.length) :
    ∃ Rp : List (List (List ℕ)),
      (∀ i, i < n + j → Rp.getD i [] = s2230_RV C n S k i) ∧
      s2230_RV C n S k (n + j) = s2230_FR S k Rp (gateAt C j) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2230_split_gates C.gates j hj
  have hga : gateAt C j = gj := by rw [s2230_gateAt_eq C j hj]; exact hgj
  rw [hga]
  obtain ⟨Rp, hRp⟩ : ∃ Rp, Rp = pre.foldl (s2230_stepR S k) ((List.range n).map (leafVectors S k)) :=
    ⟨_, rfl⟩
  have hlen : Rp.length = n + j := by
    rw [hRp, s2230_foldR_length]
    simp only [List.length_map, List.length_range, hpre_len]
  have hall : readVectors C n S k = post.foldl (s2230_stepR S k) (s2230_stepR S k Rp gj) := by
    rw [s2230_readVectors_eq, hgs, List.foldl_append, List.foldl_cons, hRp]
  have hlen1 : (s2230_stepR S k Rp gj).length = n + j + 1 := by
    simp [s2230_stepR, hlen]
  refine ⟨Rp, ?_, ?_⟩
  · intro i hi
    simp only [s2230_RV]
    rw [hall, s2230_foldR_getD_lt S k post (s2230_stepR S k Rp gj) i (by omega)]
    simp [s2230_stepR, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show i < Rp.length by omega)]
  · simp only [s2230_RV]
    rw [hall, s2230_foldR_getD_lt S k post (s2230_stepR S k Rp gj) (n + j) (by omega)]
    simp [s2230_stepR, List.getD_eq_getElem?_getD, hlen]

lemma s2230_mem_foldl_insertNew (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ L.foldl insertNew acc) : v ∈ acc ∨ v ∈ L := by
  induction L generalizing acc with
  | nil => exact Or.inl h
  | cons x L ih =>
    rw [List.foldl_cons] at h
    rcases ih _ h with h1 | h1
    · unfold insertNew at h1
      split_ifs at h1
      · exact Or.inl h1
      · rcases List.mem_append.1 h1 with h2 | h2
        · exact Or.inl h2
        · have h3 : v = x := by simpa using h2
          exact Or.inr (by simp [h3])
    · exact Or.inr (List.mem_cons_of_mem _ h1)

lemma s2230_mem_andStep (k : ℕ) (A B : List (List ℕ)) (v : List ℕ) (h : v ∈ andStep k A B) :
    ∃ u ∈ A, ∃ u2 ∈ B, v = capAdd k u u2 := by
  unfold andStep at h
  rcases s2230_mem_foldl_insertNew _ _ _ h with h1 | h1
  · simp at h1
  · simp only [List.mem_flatMap, List.mem_map] at h1
    obtain ⟨u, hu, u2, hu2, rfl⟩ := h1
    exact ⟨u, hu, u2, hu2, rfl⟩

lemma s2230_capAdd_pair (k x1 y1 x2 y2 : ℕ) :
    capAdd k [x1, y1] [x2, y2] = [min (x1 + x2) (k + 1), min (y1 + y2) (k + 1)] := by
  first
    | rfl
    | simp [capAdd]

lemma s2230_leaf_eq (a b w : ℕ) :
    leafVectors [a, b] 1 w =
      if w ∈ [a, b] then [[if a = w then 1 else 0, if b = w then 1 else 0]] else [] := by
  first
    | rfl
    | (unfold leafVectors; simp)

lemma s2230_inv (n : ℕ) (C : Circuit) (a b : Fin n) (hC : IsAO2 n C) (hab : a.val < b.val) :
    ∀ w : ℕ, ∀ v ∈ s2230_RV C n [a.val, b.val] 1 w, ∃ x y : ℕ, v = [x, y] ∧ 1 ≤ x + y ∧
      (x = 1 → y = 0 →
        a ∈ orIn n C w ∧ s2230_W n C (fun k1 : Fin n => decide (k1 = a)) w = true) ∧
      (x = 0 → y = 1 →
        b ∈ orIn n C w ∧ s2230_W n C (fun k1 : Fin n => decide (k1 = b)) w = true) ∧
      (x = 1 → y = 1 → ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
        OrReaches n C w j ∧
        ((a ∈ side (n := n) C j 0 ∧ b ∈ side (n := n) C j 1) ∨
          (b ∈ side (n := n) C j 0 ∧ a ∈ side (n := n) C j 1))) := by
  obtain ⟨hAnd, hBack, hTwo⟩ := hC
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    by_cases hwn : w < n
    · rw [s2230_RV_input C n _ 1 w hwn, s2230_leaf_eq] at hv
      by_cases hwa : a.val = w
      · have hwb : ¬ b.val = w := by omega
        rw [if_pos (List.mem_cons.2 (Or.inl hwa.symm)), if_pos hwa, if_neg hwb] at hv
        have hv2 : v = [1, 0] := List.mem_singleton.1 hv
        refine ⟨1, 0, hv2, by omega, ?_, ?_, ?_⟩
        · intro _ _
          refine ⟨?_, ?_⟩
          · rw [s2230_mem_orIn]
            exact Or.inl hwa
          · rw [s2230_W_input n C _ w hwn]
            exact decide_eq_true (Fin.ext hwa.symm)
        · intro h3 h4
          omega
        · intro h3 h4
          omega
      · by_cases hwb : b.val = w
        · rw [if_pos (List.mem_cons.2 (Or.inr (List.mem_cons.2 (Or.inl hwb.symm)))),
            if_neg hwa, if_pos hwb] at hv
          have hv2 : v = [0, 1] := List.mem_singleton.1 hv
          refine ⟨0, 1, hv2, by omega, ?_, ?_, ?_⟩
          · intro h3 h4
            omega
          · intro _ _
            refine ⟨?_, ?_⟩
            · rw [s2230_mem_orIn]
              exact Or.inl hwb
            · rw [s2230_W_input n C _ w hwn]
              exact decide_eq_true (Fin.ext hwb.symm)
          · intro h3 h4
            omega
        · exfalso
          have hm : ¬ w ∈ [a.val, b.val] := by
            intro hm
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
            omega
          rw [if_neg hm] at hv
          simp at hv
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      by_cases hj : j < C.gates.length
      · have hmem : gateAt C j ∈ C.gates := by
          rw [s2230_gateAt_eq C j hj]
          exact List.getElem_mem hj
        have hlen2 := hTwo _ hmem
        have hback := hBack j hj
        obtain ⟨Rp, hRp, hRV⟩ := s2230_RV_gate C n [a.val, b.val] 1 j hj
        rcases hinp : (gateAt C j).inputs with _ | ⟨i1, _ | ⟨i2, _ | ⟨i3, rest⟩⟩⟩
        · exfalso
          rw [hinp] at hlen2
          simp at hlen2
        · exfalso
          rw [hinp] at hlen2
          simp at hlen2
        · have hm1 : i1 ∈ (gateAt C j).inputs := by rw [hinp]; simp
          have hm2 : i2 ∈ (gateAt C j).inputs := by rw [hinp]; simp
          have hi1 : i1 < n + j := hback i1 hm1
          have hi2 : i2 < n + j := hback i2 hm2
          rcases hAnd _ hmem with hop | hop
          · rw [hRV, s2230_FR_and _ _ _ _ hop, hinp] at hv
            simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
              hRp i1 hi1, hRp i2 hi2] at hv
            obtain ⟨t, ht, u2, hu2, rfl⟩ := s2230_mem_andStep _ _ _ _ hv
            obtain ⟨z, hz, u1, hu1, rfl⟩ := s2230_mem_andStep _ _ _ _ ht
            have hz2 : z = [0, 0] := by simpa using hz
            subst hz2
            obtain ⟨x1, y1, rfl, h1, ha1, hb1, _⟩ := ih i1 hi1 u1 hu1
            obtain ⟨x2, y2, rfl, h2, ha2, hb2, _⟩ := ih i2 hi2 u2 hu2
            refine ⟨min (min (0 + x1) (1 + 1) + x2) (1 + 1),
              min (min (0 + y1) (1 + 1) + y2) (1 + 1), ?_, by omega, ?_, ?_, ?_⟩
            · rw [s2230_capAdd_pair, s2230_capAdd_pair]
            · intro hx hy
              omega
            · intro hx hy
              omega
            · intro hx hy
              have hcase : (x1 = 1 ∧ y1 = 0 ∧ x2 = 0 ∧ y2 = 1) ∨
                  (x1 = 0 ∧ y1 = 1 ∧ x2 = 1 ∧ y2 = 0) := by omega
              refine ⟨j, hj, hop, s2230_orReaches_self n C j hj, ?_⟩
              have hs0 : side (n := n) C j 0 = orIn n C i1 := by
                first
                  | (unfold side opnd; rw [hinp]; rfl)
                  | simp [side, opnd, hinp]
              have hs1 : side (n := n) C j 1 = orIn n C i2 := by
                first
                  | (unfold side opnd; rw [hinp]; rfl)
                  | simp [side, opnd, hinp]
              rw [hs0, hs1]
              rcases hcase with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩
              · exact Or.inl ⟨(ha1 e1 e2).1, (hb2 e3 e4).1⟩
              · exact Or.inr ⟨(hb1 e1 e2).1, (ha2 e3 e4).1⟩
          · rw [hRV, s2230_FR_or _ _ _ _ hop, hinp] at hv
            simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
              hRp i1 hi1, hRp i2 hi2] at hv
            have hsrc : ∃ i, i ∈ (gateAt C j).inputs ∧ i < n + j ∧
                v ∈ s2230_RV C n [a.val, b.val] 1 i := by
              rcases s2230_mem_foldl_insertNew _ _ _ hv with h | h
              · rcases s2230_mem_foldl_insertNew _ _ _ h with h3 | h3
                · simp at h3
                · exact ⟨i1, hm1, hi1, h3⟩
              · exact ⟨i2, hm2, hi2, h⟩
            obtain ⟨i, him, hilt, hvi⟩ := hsrc
            obtain ⟨x, y, hxy, h1, ha1, hb1, hab1⟩ := ih i hilt v hvi
            have hW : ∀ z : Fin n → Bool, s2230_W n C z i = true → s2230_W n C z (n + j) = true := by
              intro z hz
              rw [s2230_W_gate n C z j hj, hop]
              simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
              exact ⟨i, him, by simp only [hilt, ite_true]; exact hz⟩
            refine ⟨x, y, hxy, h1, ?_, ?_, ?_⟩
            · intro hx hy
              exact ⟨s2230_orIn_up n C j i a hj hop him hilt (ha1 hx hy).1, hW _ (ha1 hx hy).2⟩
            · intro hx hy
              exact ⟨s2230_orIn_up n C j i b hj hop him hilt (hb1 hx hy).1, hW _ (hb1 hx hy).2⟩
            · intro hx hy
              obtain ⟨j2, hj2, hop2, hr2, hsd⟩ := hab1 hx hy
              exact ⟨j2, hj2, hop2, s2230_orReaches_step n C j i j2 hj hop him hilt hr2, hsd⟩
        · exfalso
          rw [hinp] at hlen2
          simp at hlen2 <;> omega
      · exfalso
        have hnil : s2230_RV C n [a.val, b.val] 1 (n + j) = [] := by
          simp only [s2230_RV]
          rw [s2230_readVectors_eq]
          exact List.getD_eq_default _ _ (by
            rw [s2230_foldR_length]
            simp only [List.length_map, List.length_range]
            omega)
        rw [hnil] at hv
        simp at hv

lemma s2230 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : Fin n), PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → a < b → PEqualNP.ReadK.readsAtMost C n [a.val, b.val] 1 = true → ∃ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j ∧ ((a ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ b ∈ PEqualNP.TopForm.side (n := n) C j 1) ∨ (b ∈ PEqualNP.TopForm.side (n := n) C j 0 ∧ a ∈ PEqualNP.TopForm.side (n := n) C j 1)) := by
  intro n C a b hC hsingle hab hread
  have hlt : a.val < b.val := hab
  unfold readsAtMost at hread
  rw [List.any_eq_true] at hread
  obtain ⟨v, hv, hall⟩ := hread
  obtain ⟨x, y, rfl, h1, ha, hb, hab2⟩ := s2230_inv n C a b hC hlt C.output v hv
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at hall
  obtain ⟨hx, hy⟩ := hall
  have hcases : (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 1) := by omega
  rcases hcases with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exfalso
    have h3 : circuitFun n C (fun k1 : Fin n => decide (k1 = a)) = true := (ha e1 e2).2
    rw [hsingle a] at h3
    exact Bool.false_ne_true h3
  · exfalso
    have h3 : circuitFun n C (fun k1 : Fin n => decide (k1 = b)) = true := (hb e1 e2).2
    rw [hsingle b] at h3
    exact Bool.false_ne_true h3
  · exact hab2 e1 e2

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def s2231_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2231_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2231_stepWire x := rfl

lemma s2231_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2231_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2231_stepWire]
    omega

lemma s2231_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2231_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2231_stepWire w g).length := by simp [s2231_stepWire]; omega
    rw [ih (s2231_stepWire w g) hlt]
    simp [s2231_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2231_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2231_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [s2231_wires_eq_foldl, s2231_foldl_stepWire_length, List.length_ofFn]

lemma s2231_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def s2231_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma s2231_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma s2231_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    s2231_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then s2231_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2231_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [s2231_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl s2231_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, s2231_foldl_stepWire_length, hpre_len]
  have hCj : s2231_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [s2231_W]
    rw [s2231_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [s2231_foldl_stepWire_getD_lt post (s2231_stepWire w0 gj) (n + k) (by simp [s2231_stepWire]; omega)]
    simp [s2231_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [s2231_W]
    rw [s2231_wires_eq_foldl, hgs, List.foldl_append]
    exact (s2231_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact s2231_getD_ge_length w0 i (by omega)

lemma s2231_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    s2231_W n C x u = x ⟨u, hu⟩ := by
  simp only [s2231_W]
  rw [s2231_wires_eq_foldl, s2231_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma s2231_orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma s2231_orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma s2231_orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma s2231_orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact s2231_orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma s2231_orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := s2231_split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [s2231_gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [s2231_orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, s2231_orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, s2231_orFold_getD_lt n post _ m (by omega)]
    exact s2231_orStep_getD_lt n _ gk m (by omega)
  have h3 := s2231_orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma s2231_W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
    (hlt : i < n + r) (hv : s2231_W n C x i = true) : s2231_W n C x (n + r) = true := by
  rw [s2231_W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨i, hi, by rw [if_pos hlt]; exact hv⟩

lemma s2231_W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and)
    (h : ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ s2231_W n C x i = true) :
    s2231_W n C x (n + r) = true := by
  rw [s2231_W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  intro i hi
  rw [if_pos (h i hi).1]; exact (h i hi).2

open PEqualNP.CleanedNonEdge in
lemma s2231_reach_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : s2231_W n C x (n + g) = true) :
    ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] → s2231_W n C x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    rcases (s2231_orSets_mem_iff n C k g hk).mp hmem with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← h]; exact hv
    · have h3 := ih (w - n) (by omega) (by omega) hx
      have e : n + (w - n) = w := by omega
      rw [e] at h3
      exact s2231_W_or n C x k hk hop w hw hlt h3

open PEqualNP.CleanedNonEdge in
lemma s2231_reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w g : ℕ)
    (h : OrReaches n C w g) (hv : s2231_W n C x (n + g) = true) : s2231_W n C x w = true := by
  obtain ⟨hn, hmem⟩ := h
  by_cases hk : w - n < C.gates.length
  · have h3 := s2231_reach_val n C x g hv (w - n) hk hmem
    have e : n + (w - n) = w := by omega
    rw [e] at h3
    exact h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [s2231_orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma s2231_mem_filter_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α)
    (h : a ∈ @Finset.filter α p d s) : p a :=
  ((@Finset.mem_filter α p d s a).mp h).2

lemma s2231_side_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (b : Fin 2) (i : Fin n)
    (hi : i ∈ PEqualNP.TopForm.side (n := n) C j b) (hx : x i = true) :
    s2231_W n C x (PEqualNP.TopForm.opnd C j b) = true := by
  unfold PEqualNP.TopForm.side PEqualNP.TopForm.orIn at hi
  have hi2 := s2231_mem_filter_gen _ _ _ _ hi
  rcases hi2 with h | ⟨k, hk, hreach, hop, hin⟩
  · rw [← h, s2231_W_input n C x i.val i.isLt]; exact hx
  · have hk1 : s2231_W n C x (n + k) = true := by
      apply s2231_W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
      rw [s2231_W_input n C x i.val i.isLt]; exact hx
    exact s2231_reach_up n C x _ k hreach hk1

def s2231_px {n : ℕ} (u v : Fin n) : Fin n → Bool := fun k => decide (k = u ∨ k = v)

lemma s2231_px_self {n : ℕ} (t : Fin n) : s2231_px t t = (fun k : Fin n => decide (k = t)) := by
  funext k; simp [s2231_px]

lemma s2231_part1 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hNF : PEqualNP.TopForm.NoFourCycle G) (hAO : PEqualNP.TopForm.IsAO2 n C)
    (h1 : ∀ a1 : Fin n, circuitFun n C (fun k1 => decide (k1 = a1)) = false)
    (h2 : ∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 →
      circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C C.output j) :
    (∀ w : Fin n, w ∈ PEqualNP.TopForm.side (n := n) C j 0 →
        w ∉ PEqualNP.TopForm.side (n := n) C j 1) ∧
      (∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 →
        ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v) ∧
      ((PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∨
        (PEqualNP.TopForm.side (n := n) C j 1).card ≤ 1) := by
  obtain ⟨_, hRB, hlen2⟩ := hAO
  have hgm : gateAt C j ∈ C.gates := by rw [s2231_gateAt_eq C j hj]; exact List.getElem_mem hj
  have hl2 : (gateAt C j).inputs.length = 2 := hlen2 _ hgm
  have hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j := hRB j hj
  obtain ⟨a0, b0, hl⟩ := List.length_eq_two.mp hl2
  have e0 : PEqualNP.TopForm.opnd C j 0 = a0 := by
    unfold PEqualNP.TopForm.opnd; rw [hl]; rfl
  have e1 : PEqualNP.TopForm.opnd C j 1 = b0 := by
    unfold PEqualNP.TopForm.opnd; rw [hl]; rfl
  have hcross : ∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 →
      ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → u ≠ v ∧ G.Adj u v := by
    intro u hu v hv
    have hxu : s2231_px u v u = true := by simp [s2231_px]
    have hxv : s2231_px u v v = true := by simp [s2231_px]
    have va := s2231_side_val n C (s2231_px u v) j 0 u hu hxu
    have vb := s2231_side_val n C (s2231_px u v) j 1 v hv hxv
    rw [e0] at va
    rw [e1] at vb
    have hg : s2231_W n C (s2231_px u v) (n + j) = true := by
      apply s2231_W_and n C (s2231_px u v) j hj hop
      intro i hi
      have hi2 := hi
      rw [hl] at hi2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi2
      rcases hi2 with h | h
      · exact ⟨hrb i hi, by rw [h]; exact va⟩
      · exact ⟨hrb i hi, by rw [h]; exact vb⟩
    have hW : circuitFun n C (s2231_px u v) = true := s2231_reach_up n C (s2231_px u v) C.output j hr hg
    have hne : u ≠ v := by
      intro e
      subst e
      rw [s2231_px_self] at hW
      have hf : true = false := hW.symm.trans (h1 _)
      cases hf
    refine ⟨hne, ?_⟩
    by_contra hna
    have hf : true = false := hW.symm.trans (h2 u v hne hna)
    cases hf
  refine ⟨?_, fun u hu v hv => (hcross u hu v hv).2, ?_⟩
  · intro w hw0 hw1
    exact (hcross w hw0 w hw1).1 rfl
  · by_contra hcon
    push_neg at hcon
    obtain ⟨c0, c1⟩ := hcon
    obtain ⟨u, hu, u2, hu2, hne⟩ := Finset.one_lt_card.mp c0
    obtain ⟨v, hv, v2, hv2, hnv⟩ := Finset.one_lt_card.mp c1
    have hc := hNF u u2 hne
    rw [Finset.card_le_one] at hc
    exact hnv (hc v (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcross u hu v hv).2,
      (hcross u2 hu2 v hv).2⟩) v2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (hcross u hu v2 hv2).2, (hcross u2 hu2 v2 hv2).2⟩))

def s2231_cen (n : ℕ) (C : Circuit) (i : ℕ) : Finset (Fin n) :=
  if (PEqualNP.TopForm.side (n := n) C i 0).card ≤ 1 then PEqualNP.TopForm.side (n := n) C i 0
  else if (PEqualNP.TopForm.side (n := n) C i 1).card ≤ 1 then
    PEqualNP.TopForm.side (n := n) C i 1
  else ∅

lemma s2231_cen_card (n : ℕ) (C : Circuit) (i : ℕ) : (s2231_cen n C i).card ≤ 1 := by
  unfold s2231_cen
  split_ifs with h0 h1
  · exact h0
  · exact h1
  · simp

lemma s2231 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 → PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.CleanedNonEdge.OrReaches n C C.output j → (∀ w : Fin n, w ∈ PEqualNP.TopForm.side (n := n) C j 0 → w ∉ PEqualNP.TopForm.side (n := n) C j 1) ∧ (∀ u : Fin n, u ∈ PEqualNP.TopForm.side (n := n) C j 0 → ∀ v : Fin n, v ∈ PEqualNP.TopForm.side (n := n) C j 1 → G.Adj u v) ∧ ((PEqualNP.TopForm.side (n := n) C j 0).card ≤ 1 ∨ (PEqualNP.TopForm.side (n := n) C j 1).card ≤ 1)) ∧ (∀ F : Finset ℕ, (∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), ∃ i ∈ F, i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i ∧ ((e.1 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.2 ∈ PEqualNP.TopForm.side (n := n) C i 1) ∨ (e.2 ∈ PEqualNP.TopForm.side (n := n) C i 0 ∧ e.1 ∈ PEqualNP.TopForm.side (n := n) C i 1))) → ∃ T : Finset (Fin n), T.card ≤ F.card ∧ ∀ e3 ∈ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)), e3.1 ∈ T ∨ e3.2 ∈ T) := by
  intro n G _ C hNF hAO h1 h2
  have P1 := s2231_part1 n G C hNF hAO h1 h2
  refine ⟨P1, ?_⟩
  intro F hF
  refine ⟨F.biUnion (s2231_cen n C), ?_, ?_⟩
  · have hc1 : (F.biUnion (s2231_cen n C)).card ≤ F.sum (fun i => (s2231_cen n C i).card) :=
      Finset.card_biUnion_le
    have hc2 : F.sum (fun i => (s2231_cen n C i).card) ≤ F.sum (fun _ : ℕ => (1 : ℕ)) :=
      Finset.sum_le_sum (fun i _ => s2231_cen_card n C i)
    have hc3 : F.sum (fun _ : ℕ => (1 : ℕ)) = F.card := by simp
    exact le_trans hc1 (le_trans hc2 (le_of_eq hc3))
  · intro e he
    obtain ⟨i, hiF, hi, hop, hreach, hside⟩ := hF e he
    obtain ⟨_, _, hcard⟩ := P1 i hi hop hreach
    by_cases c0 : (PEqualNP.TopForm.side (n := n) C i 0).card ≤ 1
    · have hc : s2231_cen n C i = PEqualNP.TopForm.side (n := n) C i 0 := by
        unfold s2231_cen; rw [if_pos c0]
      rcases hside with ⟨h, _⟩ | ⟨h, _⟩
      · left; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hc]; exact h⟩
      · right; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hc]; exact h⟩
    · have c1 : (PEqualNP.TopForm.side (n := n) C i 1).card ≤ 1 := hcard.resolve_left c0
      have hc : s2231_cen n C i = PEqualNP.TopForm.side (n := n) C i 1 := by
        unfold s2231_cen; rw [if_neg c0, if_pos c1]
      rcases hside with ⟨_, h⟩ | ⟨_, h⟩
      · right; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hc]; exact h⟩
      · left; exact Finset.mem_biUnion.mpr ⟨i, hiF, by rw [hc]; exact h⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

lemma s2233_gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma s2233_gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [s2233_gateAt_eq hj]; exact List.getElem_mem hj

open PEqualNP.CleanedNonEdge

lemma s2233_orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma s2233_orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [s2233_orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma s2233_orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := s2233_orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma s2233_tail_step (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w, OrReaches n C w g → g ≠ w - n →
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        n + g ∈ (gateAt C k).inputs := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h hne
    have hnw : n ≤ w := h.1
    obtain ⟨k0, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (s2233_orReaches_iff n C k0 g).mp h
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hr⟩
    · exact (hne (by omega)).elim
    · have hself : OrReaches n C (n + k0) k0 :=
        (s2233_orReaches_iff n C k0 k0).mpr ⟨hk, Or.inl rfl⟩
      by_cases hg : g = i - n
      · refine ⟨k0, hk, hself, hop, ?_⟩
        have hni : n ≤ i := hr.1
        have e : n + g = i := by omega
        rw [e]
        exact hi
      · obtain ⟨k, hkl, hrk, hopk, hin⟩ := ih i hlt hr hg
        exact ⟨k, hkl,
          (s2233_orReaches_iff n C k0 k).mpr ⟨hk, Or.inr ⟨hop, i, hi, hlt, hrk⟩⟩, hopk, hin⟩

def s2233_par (n : ℕ) (C : Circuit) (O : Finset ℕ) : Finset ℕ :=
  O.biUnion (fun k => ((gateAt C k).inputs.toFinset).image (fun w => w - n))

lemma s2233_par_card (n : ℕ) (C : Circuit) (O : Finset ℕ)
    (h : ∀ k ∈ O, (gateAt C k).inputs.length = 2) : (s2233_par n C O).card ≤ O.card * 2 := by
  unfold s2233_par
  calc (O.biUnion (fun k => ((gateAt C k).inputs.toFinset).image (fun w => w - n))).card
      ≤ ∑ k ∈ O, (((gateAt C k).inputs.toFinset).image (fun w => w - n)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ O, 2 := by
        apply Finset.sum_le_sum
        intro k hk
        exact Finset.card_image_le.trans
          ((List.toFinset_card_le _).trans (le_of_eq (h k hk)))
    _ = O.card * 2 := by rw [Finset.sum_const, smul_eq_mul]

lemma s2233 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ), PEqualNP.TopForm.IsAO2 n C → (∀ j ∈ F, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output j) → F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ PEqualNP.CleanedNonEdge.OrReaches n C C.output i} + 1 := by
  intro n C F hC hF
  obtain ⟨_, _, hlen⟩ := hC
  obtain ⟨O, hO⟩ : ∃ O : Finset ℕ, ∀ i, i ∈ O ↔ (i < C.gates.length ∧
      (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i) :=
      by
    have hfin : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i}.Finite := by
      apply (Finset.finite_toSet (Finset.range C.gates.length)).subset
      intro i hi
      have hi2 : i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
          OrReaches n C C.output i := Eq.mp Set.mem_setOf_eq hi
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr hi2.1)
    refine ⟨hfin.toFinset, fun i => ?_⟩
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hset : {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      OrReaches n C C.output i} = (↑O : Set ℕ) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.mem_coe, hO]
  rw [hset, Set.ncard_coe_finset]
  have hdisj : Disjoint F O := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have h1 := (hF a ha).2.1
    have h2 := ((hO a).mp hb).2.1
    rw [h1] at h2
    exact GateOp.noConfusion h2
  have hsub : F ∪ O ⊆ insert (C.output - n) (s2233_par n C O) := by
    intro g hg
    have hr : OrReaches n C C.output g := by
      rcases Finset.mem_union.mp hg with h | h
      · exact (hF g h).2.2
      · exact ((hO g).mp h).2.2
    by_cases hgo : g = C.output - n
    · exact Finset.mem_insert.mpr (Or.inl hgo)
    · obtain ⟨k, hk, hrk, hop, hin⟩ := s2233_tail_step n C g C.output hr hgo
      refine Finset.mem_insert.mpr (Or.inr ?_)
      unfold s2233_par
      exact Finset.mem_biUnion.mpr ⟨k, (hO k).mpr ⟨hk, hop, hrk⟩,
        Finset.mem_image.mpr ⟨n + g, List.mem_toFinset.mpr hin, by omega⟩⟩
  have hcard := s2233_par_card n C O (fun k hk => hlen _ (s2233_gateAt_mem ((hO k).mp hk).1))
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at h1
  have h2 := Finset.card_insert_le (C.output - n) (s2233_par n C O)
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge

def s2234_stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma s2234_wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl s2234_stepWire x := rfl

lemma s2234_foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl s2234_stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [s2234_stepWire]
    omega

lemma s2234_foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl s2234_stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (s2234_stepWire w g).length := by simp [s2234_stepWire]; omega
    rw [ih (s2234_stepWire w g) hlt]
    simp [s2234_stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma s2234_getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma s2234_wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [s2234_wires_eq_foldl, s2234_foldl_stepWire_length, List.length_ofFn]

lemma s2234_split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def s2234_W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma s2234_gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma s2234_W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    s2234_W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then s2234_W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := s2234_split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [s2234_gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl s2234_stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, s2234_foldl_stepWire_length, hpre_len]
  have hCj : s2234_W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [s2234_W]
    rw [s2234_wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [s2234_foldl_stepWire_getD_lt post (s2234_stepWire w0 gj) (n + k) (by simp [s2234_stepWire]; omega)]
    simp [s2234_stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [s2234_W]
    rw [s2234_wires_eq_foldl, hgs, List.foldl_append]
    exact (s2234_foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact s2234_getD_ge_length w0 i (by omega)

lemma s2234_W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    s2234_W n C x u = x ⟨u, hu⟩ := by
  simp only [s2234_W]
  rw [s2234_wires_eq_foldl, s2234_foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

lemma s2234_orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma s2234_orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

lemma s2234_orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma s2234_orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact s2234_orStep_getD_lt n cs g k hk

lemma s2234_orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := s2234_split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [s2234_gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [s2234_orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, s2234_orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, s2234_orFold_getD_lt n post _ m (by omega)]
    exact s2234_orStep_getD_lt n _ gk m (by omega)
  have h3 := s2234_orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma s2234_qorSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  simp only [orSets]
  rw [s2234_orFold_length]
  simp

lemma s2234_qreach_iff (n : ℕ) (C : Circuit) (k g : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) g ↔ g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, w < n + k ∧ OrReaches n C w g) := by
  have e : n + k - n = k := by omega
  constructor
  · intro h
    have h2 := h.2
    rw [e] at h2
    rcases (s2234_orSets_mem_iff n C k g hk).1 h2 with h3 | ⟨hop, w, hw, hn, hlt, hx⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, hlt, hn, hx⟩
  · intro h
    refine ⟨by omega, ?_⟩
    rw [e]
    refine (s2234_orSets_mem_iff n C k g hk).2 ?_
    rcases h with h | ⟨hop, w, hw, hlt, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hr.1, hlt, hr.2⟩

lemma s2234_qreach_bound (n : ℕ) (C : Circuit) (w g : ℕ) (h : OrReaches n C w g) :
    n ≤ w ∧ w - n < C.gates.length := by
  refine ⟨h.1, ?_⟩
  by_contra hc
  have h2 := h.2
  have hlen : (orSets n C).length ≤ w - n := by rw [s2234_qorSets_len]; omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen] at h2
  simp at h2

lemma s2234_qreach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := (s2234_qreach_iff n C k k hk).2 (Or.inl rfl)

lemma s2234_qreach_le (n : ℕ) (C : Circuit) (g : ℕ) : ∀ w : ℕ, OrReaches n C w g → n + g ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    obtain ⟨h1, h2⟩ := s2234_qreach_bound n C w g h
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (s2234_qreach_iff n C k g hk).1 h with h3 | ⟨_, w', _, hlt, hr⟩
    · omega
    · have := ih w' hlt hr
      omega

lemma s2234_qreach_trans (n : ℕ) (C : Circuit) (i g : ℕ) (hg : OrReaches n C (n + i) g) :
    ∀ w : ℕ, OrReaches n C w i → OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    obtain ⟨h1, h2⟩ := s2234_qreach_bound n C w i h
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (s2234_qreach_iff n C k i hk).1 h with h3 | ⟨hop, w', hw', hlt, hr⟩
    · rw [← h3]; exact hg
    · exact (s2234_qreach_iff n C k g hk).2 (Or.inr ⟨hop, w', hw', hlt, ih w' hlt hr⟩)

lemma s2234_qmem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (b : Fin n) :
    b ∈ PEqualNP.TopForm.orIn n C w ↔ ((b : ℕ) = w ∨ ∃ k, k < C.gates.length ∧
      OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧ (b : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma s2234_qorIn_eq_self (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : ¬ (n ≤ w ∧ w - n < C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or)) :
    ∀ b ∈ PEqualNP.TopForm.orIn n C w, (b : ℕ) = w := by
  intro b hb
  rcases (s2234_qmem_orIn n C w b).1 hb with h | ⟨k', hk', hr, hop', hi⟩
  · exact h
  · exfalso
    obtain ⟨h1, h2⟩ := s2234_qreach_bound n C w k' hr
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have e : n + k - n = k := by omega
    rw [e] at hw h2
    rcases (s2234_qreach_iff n C k k' h2).1 hr with h | ⟨hop, _⟩
    · rw [h] at hop'
      exact hw ⟨h1, h2, hop'⟩
    · exact hw ⟨h1, h2, hop⟩

lemma s2234_qorIn_small (n : ℕ) (C : Circuit) (w : ℕ)
    (hw : ¬ (n ≤ w ∧ w - n < C.gates.length ∧ (gateAt C (w - n)).op = GateOp.or)) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  have h1 := s2234_qorIn_eq_self n C w hw a ha
  have h2 := s2234_qorIn_eq_self n C w hw b hb
  exact Fin.ext (by omega)

lemma s2234_qorIn_or (n : ℕ) (C : Circuit) (k a b : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hin : (gateAt C k).inputs = [a, b])
    (ha : a < n + k) (hb : b < n + k) :
    PEqualNP.TopForm.orIn n C (n + k) =
      PEqualNP.TopForm.orIn n C a ∪ PEqualNP.TopForm.orIn n C b := by
  have hma : a ∈ (gateAt C k).inputs := by rw [hin]; simp
  have hmb : b ∈ (gateAt C k).inputs := by rw [hin]; simp
  ext i
  rw [Finset.mem_union, s2234_qmem_orIn, s2234_qmem_orIn, s2234_qmem_orIn]
  constructor
  · rintro (h | ⟨k', hk', hr, hop', hi⟩)
    · exfalso
      have := i.2
      omega
    · rcases (s2234_qreach_iff n C k k' hk).1 hr with h | ⟨_, w, hw, hwlt, hr'⟩
      · rw [h, hin, List.mem_cons, List.mem_singleton] at hi
        rcases hi with h4 | h4
        · exact Or.inl (Or.inl h4)
        · exact Or.inr (Or.inl h4)
      · rw [hin, List.mem_cons, List.mem_singleton] at hw
        rcases hw with h4 | h4
        · rw [h4] at hr'
          exact Or.inl (Or.inr ⟨k', hk', hr', hop', hi⟩)
        · rw [h4] at hr'
          exact Or.inr (Or.inr ⟨k', hk', hr', hop', hi⟩)
  · rintro ((h | ⟨k', hk', hr, hop', hi⟩) | (h | ⟨k', hk', hr, hop', hi⟩))
    · exact Or.inr ⟨k, hk, s2234_qreach_self n C k hk, hop, by rw [h]; exact hma⟩
    · exact Or.inr ⟨k', hk', (s2234_qreach_iff n C k k' hk).2 (Or.inr ⟨hop, a, hma, ha, hr⟩), hop', hi⟩
    · exact Or.inr ⟨k, hk, s2234_qreach_self n C k hk, hop, by rw [h]; exact hmb⟩
    · exact Or.inr ⟨k', hk', (s2234_qreach_iff n C k k' hk).2 (Or.inr ⟨hop, b, hmb, hb, hr⟩), hop', hi⟩

lemma s2234_qorIn_sub (n : ℕ) (C : Circuit) (i w : ℕ) (hr : OrReaches n C w i) :
    PEqualNP.TopForm.orIn n C (n + i) ⊆ PEqualNP.TopForm.orIn n C w := by
  intro b hb
  rcases (s2234_qmem_orIn n C (n + i) b).1 hb with h | ⟨k, hk, hr', hop, hi⟩
  · exfalso
    have := b.2
    omega
  · exact (s2234_qmem_orIn n C w b).2 (Or.inr ⟨k, hk, s2234_qreach_trans n C i k hr' w hr, hop, hi⟩)

lemma s2234_qval_reach (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : s2234_W n C x (n + g) = true) :
    ∀ w : ℕ, OrReaches n C w g → s2234_W n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    obtain ⟨h1, h2⟩ := s2234_qreach_bound n C w g h
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    rcases (s2234_qreach_iff n C k g hk).1 h with h3 | ⟨hop, w', hw', hlt, hr⟩
    · rw [← h3]; exact hv
    · rw [s2234_W_gate n C x k hk, hop]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
      exact ⟨w', hw', by simp only [hlt, ite_true]; exact ih w' hlt hr⟩

lemma s2234_qval_orIn (n : ℕ) (C : Circuit) (w : ℕ) (b : Fin n)
    (hb : b ∈ PEqualNP.TopForm.orIn n C w) :
    s2234_W n C (fun r : Fin n => decide (r = b)) w = true := by
  rcases (s2234_qmem_orIn n C w b).1 hb with h | ⟨k, hk, hr, hop, hi⟩
  · rw [← h, s2234_W_input n C _ (b : ℕ) b.2]
    simp
  · refine s2234_qval_reach n C _ k ?_ w hr
    rw [s2234_W_gate n C _ k hk, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id]
    have hlt : (b : ℕ) < n + k := by
      have := b.2
      omega
    refine ⟨(b : ℕ), hi, ?_⟩
    simp only [hlt, ite_true]
    rw [s2234_W_input n C _ (b : ℕ) b.2]
    simp

lemma s2234_qpart1 (n : ℕ) (C : Circuit)
    (h0 : ∀ a1 : Fin n, circuitFun n C (fun k1 => decide (k1 = a1)) = false)
    (i : ℕ) (hcard : 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card) :
    ¬ OrReaches n C C.output i := by
  intro hr
  have hpos : 0 < (PEqualNP.TopForm.orIn n C (n + i)).card := by omega
  obtain ⟨b, hb⟩ := Finset.card_pos.1 hpos
  have h1 := s2234_qval_orIn n C (n + i) b hb
  have h2 := s2234_qval_reach n C _ i h1 C.output hr
  have h3 : s2234_W n C (fun r : Fin n => decide (r = b)) C.output = false := h0 b
  rw [h2] at h3
  cases h3

noncomputable def s2234_srv (n : ℕ) (C : Circuit) (R : Finset ℕ) : Finset ℕ :=
  @Finset.filter ℕ (fun i => (gateAt C i).op = GateOp.or ∧
    2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card ∧ ∃ w ∈ R, OrReaches n C w i)
    (fun _ => Classical.propDecidable _) (Finset.range C.gates.length)

lemma s2234_qmem_srv (n : ℕ) (C : Circuit) (R : Finset ℕ) (i : ℕ) :
    i ∈ s2234_srv n C R ↔ (i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
      2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card ∧ ∃ w ∈ R, OrReaches n C w i) := by
  unfold s2234_srv
  rw [@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _), Finset.mem_range]

lemma s2234_qsrv_mono (n : ℕ) (C : Circuit) (R R' : Finset ℕ) (h : R ⊆ R') :
    s2234_srv n C R ⊆ s2234_srv n C R' := by
  intro i hi
  obtain ⟨h1, h2, h3, w, hw, hr⟩ := (s2234_qmem_srv n C R i).1 hi
  exact (s2234_qmem_srv n C R' i).2 ⟨h1, h2, h3, w, h hw, hr⟩

lemma s2234_qcount (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (hlen2 : ∀ g ∈ C.gates, g.inputs.length = 2) :
    ∀ (m : ℕ) (R : Finset ℕ), (∀ w ∈ R, w < m) →
      (R.biUnion (PEqualNP.TopForm.orIn n C)).card ≤ (s2234_srv n C R).card + R.card := by
  intro m
  induction m with
  | zero =>
    intro R hR
    have hRe : R = ∅ := Finset.eq_empty_of_forall_notMem (fun w hw => by
      have := hR w hw
      omega)
    subst hRe
    simp
  | succ m ih =>
    intro R hR
    by_cases hm : m ∈ R
    · have hR0 : ∀ w ∈ R.erase m, w < m := by
        intro w hw
        have h1 := Finset.ne_of_mem_erase hw
        have h2 := hR w (Finset.mem_of_mem_erase hw)
        omega
      have hins : insert m (R.erase m) = R := Finset.insert_erase hm
      have hcardR : (R.erase m).card + 1 = R.card := Finset.card_erase_add_one hm
      have hU : R.biUnion (PEqualNP.TopForm.orIn n C) =
          PEqualNP.TopForm.orIn n C m ∪ (R.erase m).biUnion (PEqualNP.TopForm.orIn n C) := by
        rw [← Finset.biUnion_insert (a := m) (s := R.erase m)
          (t := PEqualNP.TopForm.orIn n C), hins]
      by_cases hs : n ≤ m ∧ m - n < C.gates.length ∧ (gateAt C (m - n)).op = GateOp.or ∧
          2 ≤ (PEqualNP.TopForm.orIn n C m).card
      · obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
        obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
        have e : n + k - n = k := by omega
        rw [e] at hs2 hs3
        have hmem : gateAt C k ∈ C.gates := by
          rw [s2234_gateAt_eq C k hs2]
          exact List.getElem_mem hs2
        have hl := hlen2 _ hmem
        obtain ⟨a, b, hin⟩ : ∃ a b, (gateAt C k).inputs = [a, b] := List.length_eq_two.1 hl
        have hma : a ∈ (gateAt C k).inputs := by rw [hin]; simp
        have hmb : b ∈ (gateAt C k).inputs := by rw [hin]; simp
        have ha : a < n + k := hRB k hs2 a hma
        have hb : b < n + k := hRB k hs2 b hmb
        have hor := s2234_qorIn_or n C k a b hs2 hs3 hin ha hb
        have hR' : ∀ w ∈ insert a (insert b (R.erase (n + k))), w < n + k := by
          intro w hw
          rw [Finset.mem_insert, Finset.mem_insert] at hw
          rcases hw with h | h | h
          · omega
          · omega
          · exact hR0 w h
        have hih := ih _ hR'
        have hU' : (insert a (insert b (R.erase (n + k)))).biUnion (PEqualNP.TopForm.orIn n C) =
            R.biUnion (PEqualNP.TopForm.orIn n C) := by
          rw [hU, Finset.biUnion_insert, Finset.biUnion_insert, hor, Finset.union_assoc]
        have hc' : (insert a (insert b (R.erase (n + k)))).card ≤ (R.erase (n + k)).card + 2 := by
          have h1 := Finset.card_insert_le a (insert b (R.erase (n + k)))
          have h2 := Finset.card_insert_le b (R.erase (n + k))
          omega
        have hsub : s2234_srv n C (insert a (insert b (R.erase (n + k)))) ⊆ (s2234_srv n C R).erase k := by
          intro i hi
          obtain ⟨h1, h2, h3, w, hw, hr⟩ := (s2234_qmem_srv n C _ i).1 hi
          have hle := s2234_qreach_le n C i w hr
          have hwlt := hR' w hw
          rw [Finset.mem_erase]
          refine ⟨by omega, (s2234_qmem_srv n C R i).2 ⟨h1, h2, h3, ?_⟩⟩
          rw [Finset.mem_insert, Finset.mem_insert] at hw
          rcases hw with h | h | h
          · rw [h] at hr
            exact ⟨n + k, hm, (s2234_qreach_iff n C k i hs2).2 (Or.inr ⟨hs3, a, hma, ha, hr⟩)⟩
          · rw [h] at hr
            exact ⟨n + k, hm, (s2234_qreach_iff n C k i hs2).2 (Or.inr ⟨hs3, b, hmb, hb, hr⟩)⟩
          · exact ⟨w, Finset.mem_of_mem_erase h, hr⟩
        have hkmem : k ∈ s2234_srv n C R :=
          (s2234_qmem_srv n C R k).2 ⟨hs2, hs3, hs4, n + k, hm, s2234_qreach_self n C k hs2⟩
        have hc2 : ((s2234_srv n C R).erase k).card + 1 = (s2234_srv n C R).card :=
          Finset.card_erase_add_one hkmem
        have hc3 := Finset.card_le_card hsub
        rw [hU'] at hih
        omega
      · have hsmall : (PEqualNP.TopForm.orIn n C m).card ≤ 1 := by
          by_cases hs' : n ≤ m ∧ m - n < C.gates.length ∧ (gateAt C (m - n)).op = GateOp.or
          · by_contra hc
            exact hs ⟨hs'.1, hs'.2.1, hs'.2.2, by omega⟩
          · exact s2234_qorIn_small n C m hs'
        have hih := ih _ hR0
        have hmono := Finset.card_le_card (s2234_qsrv_mono n C _ _ (Finset.erase_subset m R))
        have hun := Finset.card_union_le (PEqualNP.TopForm.orIn n C m)
          ((R.erase m).biUnion (PEqualNP.TopForm.orIn n C))
        rw [hU]
        omega
    · refine ih R (fun w hw => ?_)
      have h1 := hR w hw
      have h2 : w ≠ m := fun h => hm (h ▸ hw)
      omega

lemma s2234_qfinal (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (F : Finset ℕ)
    (ctr : ℕ → Fin n) (lf : ℕ → ℕ)
    (hG : PEqualNP.TopForm.NoFourCycle G) (hRB : ReadsBack n C)
    (hlen2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hadj : ∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) :
    ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  have key : ∀ (S : Set ℕ) (A B : ℕ), (∀ i, i ∈ S ↔ i ∈ s2234_srv n C (F.image lf)) →
      A ≤ (s2234_srv n C (F.image lf)).card + B → A ≤ S.ncard + B := by
    intro S A B hS hA
    have hSe : S = ((s2234_srv n C (F.image lf) : Finset ℕ) : Set ℕ) := by
      ext i
      exact (hS i).trans Finset.mem_coe.symm
    rw [hSe, Set.ncard_coe_finset]
    exact hA
  refine key _ _ _ ?_ ?_
  · intro i
    rw [Set.mem_ofPred_eq, s2234_qmem_srv]
    constructor
    · rintro ⟨h1, h2, h3, j, hj, hr⟩
      exact ⟨h1, h2, h3, lf j, Finset.mem_image_of_mem lf hj, hr⟩
    · rintro ⟨h1, h2, h3, w, hw, hr⟩
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
      exact ⟨h1, h2, h3, j, hj, hr⟩
  · have hpt : ∀ c : Fin n, ∀ X : Finset (Fin n),
        (∀ b, b ∈ X ↔ ∃ j ∈ F, ctr j = c ∧ b ∈ PEqualNP.TopForm.orIn n C (lf j)) →
        X.card ≤ (s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf)).card +
          (F.filter (fun j => ctr j = c)).card := by
      intro c X hX
      have hXe : X = ((F.filter (fun j => ctr j = c)).image lf).biUnion
          (PEqualNP.TopForm.orIn n C) := by
        ext b
        rw [hX b, Finset.mem_biUnion]
        constructor
        · rintro ⟨j, hj, hc, hb⟩
          exact ⟨lf j, Finset.mem_image_of_mem lf (Finset.mem_filter.2 ⟨hj, hc⟩), hb⟩
        · rintro ⟨w, hw, hb⟩
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
          obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
          exact ⟨j, hj1, hj2, hb⟩
      have hc := s2234_qcount n C hRB hlen2
        (((F.filter (fun j => ctr j = c)).image lf).sup id + 1)
        ((F.filter (fun j => ctr j = c)).image lf)
        (fun w hw => Nat.lt_succ_of_le (Finset.le_sup (f := id) hw))
      have hi := Finset.card_image_le (s := F.filter (fun j => ctr j = c)) (f := lf)
      rw [hXe]
      omega
    have hdisj : ∀ c c' : Fin n, c ≠ c' → ∀ i,
        i ∈ s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf) →
        i ∈ s2234_srv n C ((F.filter (fun j => ctr j = c')).image lf) → False := by
      intro c c' hne i h1 h2
      obtain ⟨hi, hop, hcard, w, hw, hr⟩ := (s2234_qmem_srv n C _ i).1 h1
      obtain ⟨_, _, _, w', hw', hr'⟩ := (s2234_qmem_srv n C _ i).1 h2
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.1 hw'
      obtain ⟨hjF, hjc⟩ := Finset.mem_filter.1 hj
      obtain ⟨hjF', hjc'⟩ := Finset.mem_filter.1 hj'
      refine absurd (le_trans hcard (le_trans (Finset.card_le_card ?_) (hG c c' hne))) (by omega)
      intro b hb
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rw [← hjc]
        exact hadj j hjF b (s2234_qorIn_sub n C i (lf j) hr hb)
      · rw [← hjc']
        exact hadj j' hjF' b (s2234_qorIn_sub n C i (lf j') hr' hb)
    have hpd : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint
        (fun c => s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf)) := by
      intro c _ c' _ hne
      exact Finset.disjoint_left.2 (fun i h1 h2 => hdisj c c' hne i h1 h2)
    have hsum1 : ∑ c : Fin n, (s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf)).card ≤
        (s2234_srv n C (F.image lf)).card := by
      rw [← Finset.card_biUnion hpd]
      apply Finset.card_le_card
      intro i hi
      obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.1 hi
      exact s2234_qsrv_mono n C _ _ (Finset.image_subset_image (Finset.filter_subset _ _)) hc
    have hsum2 : ∑ c : Fin n, (F.filter (fun j => ctr j = c)).card = F.card :=
      (Finset.card_eq_sum_card_fiberwise (f := ctr) (s := F) (t := Finset.univ)
        (by intro x _; simp)).symm
    have hpt2 : ∀ c ∈ (Finset.univ : Finset (Fin n)), (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤
        (s2234_srv n C ((F.filter (fun j => ctr j = c)).image lf)).card +
          (F.filter (fun j => ctr j = c)).card := fun c _ => hpt c _ (fun b => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    refine le_trans (Finset.sum_le_sum hpt2) ?_
    rw [Finset.sum_add_distrib]
    exact add_le_add hsum1 (le_of_eq hsum2)

lemma s2234 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ j ∈ F, ∀ b : Fin n, b ∈ PEqualNP.TopForm.orIn n C (lf j) → G.Adj (ctr j) b) → (∀ i < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op = PEqualNP.CircuitLowerBounds.GateOp.or → 2 ≤ (PEqualNP.TopForm.orIn n C (n + i)).card → (∃ j1 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j1) i) → ¬ PEqualNP.CleanedNonEdge.OrReaches n C C.output i) ∧ ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n => ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ PEqualNP.TopForm.orIn n C (lf j2))).card ≤ Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C i2).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ 2 ≤ (PEqualNP.TopForm.orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, PEqualNP.CleanedNonEdge.OrReaches n C (lf j3) i2} + F.card := by
  intro n G hdec C F ctr lf hG hAO h0 hadj
  refine ⟨?_, ?_⟩
  · intro i _ _ hcard _
    exact s2234_qpart1 n C h0 i hcard
  · exact s2234_qfinal n G C F ctr lf hG hAO.2.1 hAO.2.2 hadj

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma three_count (L : ℕ) (F : Finset ℕ) (A B : Set ℕ)
    (hF : ∀ j ∈ F, j < L) (hA : ∀ i ∈ A, i < L) (hB : ∀ i ∈ B, i < L)
    (hFA : ∀ j ∈ F, j ∉ A) (hFB : ∀ j ∈ F, j ∉ B) (hAB : ∀ i ∈ A, i ∉ B) :
    F.card + A.ncard + B.ncard ≤ L := by
  classical
  have hAf : A.Finite := (Set.finite_lt_nat L).subset (fun i hi => hA i hi)
  have hBf : B.Finite := (Set.finite_lt_nat L).subset (fun i hi => hB i hi)
  rw [Set.ncard_eq_toFinset_card A hAf, Set.ncard_eq_toFinset_card B hBf]
  have h1 : Disjoint F hAf.toFinset := by
    rw [Finset.disjoint_left]
    intro j hj hj2
    exact hFA j hj ((Set.Finite.mem_toFinset hAf).mp hj2)
  have h2 : Disjoint (F ∪ hAf.toFinset) hBf.toFinset := by
    rw [Finset.disjoint_left]
    intro j hj hj2
    have hjB := (Set.Finite.mem_toFinset hBf).mp hj2
    rcases Finset.mem_union.mp hj with h | h
    · exact hFB j h hjB
    · exact hAB j ((Set.Finite.mem_toFinset hAf).mp h) hjB
  have h3 : (F ∪ hAf.toFinset) ∪ hBf.toFinset ⊆ Finset.range L := by
    intro j hj
    rw [Finset.mem_range]
    rcases Finset.mem_union.mp hj with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact hF j h
      · exact hA j ((Set.Finite.mem_toFinset hAf).mp h)
    · exact hB j ((Set.Finite.mem_toFinset hBf).mp h)
  have h4 := Finset.card_le_card h3
  rw [Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1, Finset.card_range] at h4
  exact h4

lemma sum_card_ge {n : ℕ} (E : Finset (Fin n × Fin n)) (U : Fin n → Finset (Fin n))
    (hlt : ∀ e ∈ E, e.1 < e.2) (h : ∀ e ∈ E, e.2 ∈ U e.1 ∨ e.1 ∈ U e.2) :
    E.card ≤ ∑ c : Fin n, (U c).card := by
  classical
  have hs := Finset.card_sigma (Finset.univ : Finset (Fin n)) U
  rw [← hs]
  have key1 : ∀ e ∈ E, (if e.2 ∈ U e.1 then (⟨e.1, e.2⟩ : Σ _ : Fin n, Fin n) else ⟨e.2, e.1⟩)
      ∈ (Finset.univ : Finset (Fin n)).sigma U := by
    intro e he
    by_cases hc : e.2 ∈ U e.1
    · rw [if_pos hc]
      exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hc⟩
    · rw [if_neg hc]
      rcases h e he with h1 | h1
      · exact absurd h1 hc
      · exact Finset.mem_sigma.mpr ⟨Finset.mem_univ _, h1⟩
  have key2 : ∀ e e2 : Fin n × Fin n, e.1 < e.2 → e2.1 < e2.2 →
      (if e.2 ∈ U e.1 then (⟨e.1, e.2⟩ : Σ _ : Fin n, Fin n) else ⟨e.2, e.1⟩) =
      (if e2.2 ∈ U e2.1 then (⟨e2.1, e2.2⟩ : Σ _ : Fin n, Fin n) else ⟨e2.2, e2.1⟩) → e = e2 := by
    intro e e2 h1 h2 heq
    by_cases c1 : e.2 ∈ U e.1
    · by_cases c2 : e2.2 ∈ U e2.1
      · rw [if_pos c1, if_pos c2] at heq
        have ha : e.1 = e2.1 := congrArg Sigma.fst heq
        have hb : e.2 = e2.2 := congrArg (fun s : (Σ _ : Fin n, Fin n) => (s.2 : Fin n)) heq
        exact Prod.ext ha hb
      · rw [if_pos c1, if_neg c2] at heq
        have ha : e.1 = e2.2 := congrArg Sigma.fst heq
        have hb : e.2 = e2.1 := congrArg (fun s : (Σ _ : Fin n, Fin n) => (s.2 : Fin n)) heq
        rw [ha, hb] at h1
        exact absurd h1 (lt_asymm h2)
    · by_cases c2 : e2.2 ∈ U e2.1
      · rw [if_neg c1, if_pos c2] at heq
        have ha : e.2 = e2.1 := congrArg Sigma.fst heq
        have hb : e.1 = e2.2 := congrArg (fun s : (Σ _ : Fin n, Fin n) => (s.2 : Fin n)) heq
        rw [ha, hb] at h1
        exact absurd h1 (lt_asymm h2)
      · rw [if_neg c1, if_neg c2] at heq
        have ha : e.2 = e2.2 := congrArg Sigma.fst heq
        have hb : e.1 = e2.1 := congrArg (fun s : (Σ _ : Fin n, Fin n) => (s.2 : Fin n)) heq
        exact Prod.ext hb ha
  refine Finset.card_le_card_of_injOn
    (fun e => if e.2 ∈ U e.1 then (⟨e.1, e.2⟩ : Σ _ : Fin n, Fin n) else ⟨e.2, e.1⟩) ?_ ?_
  · intro e he
    exact key1 e he
  · intro e he e2 he2 heq
    exact key2 e e2 (hlt e he) (hlt e2 he2) heq

lemma core (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (E : Finset (Fin n × Fin n))
    (hlt : ∀ e ∈ E, e.1 < e.2)
    (h30 : ∀ e ∈ E, ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧
      ((e.1 ∈ side (n := n) C j 0 ∧ e.2 ∈ side (n := n) C j 1) ∨
        (e.2 ∈ side (n := n) C j 0 ∧ e.1 ∈ side (n := n) C j 1)))
    (h31a : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → OrReaches n C C.output j →
      (∀ w : Fin n, w ∈ side (n := n) C j 0 → w ∉ side (n := n) C j 1) ∧
      (∀ u : Fin n, u ∈ side (n := n) C j 0 → ∀ v : Fin n, v ∈ side (n := n) C j 1 → G.Adj u v) ∧
      ((side (n := n) C j 0).card ≤ 1 ∨ (side (n := n) C j 1).card ≤ 1))
    (h31b : ∀ F : Finset ℕ, (∀ e ∈ E, ∃ i ∈ F, i < C.gates.length ∧
        (gateAt C i).op = GateOp.and ∧ OrReaches n C C.output i ∧
        ((e.1 ∈ side (n := n) C i 0 ∧ e.2 ∈ side (n := n) C i 1) ∨
          (e.2 ∈ side (n := n) C i 0 ∧ e.1 ∈ side (n := n) C i 1))) →
      ∃ T : Finset (Fin n), T.card ≤ F.card ∧ ∀ e3 ∈ E, e3.1 ∈ T ∨ e3.2 ∈ T)
    (h33 : ∀ F : Finset ℕ, (∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
        OrReaches n C C.output j) →
      F.card ≤ Set.ncard {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧
        OrReaches n C C.output i} + 1)
    (h34 : ∀ (F : Finset ℕ) (ctr : ℕ → Fin n) (lf : ℕ → ℕ),
      (∀ j ∈ F, ∀ b : Fin n, b ∈ orIn n C (lf j) → G.Adj (ctr j) b) →
      (∀ i < C.gates.length, (gateAt C i).op = GateOp.or → 2 ≤ (orIn n C (n + i)).card →
        (∃ j1 ∈ F, OrReaches n C (lf j1) i) → ¬ OrReaches n C C.output i) ∧
      ∑ c : Fin n, (Finset.univ.filter (fun b2 : Fin n =>
        ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))).card ≤
        Set.ncard {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧
          2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, OrReaches n C (lf j3) i2} + F.card) :
    ∃ T : Finset (Fin n), (∀ e ∈ E, e.1 ∈ T ∨ e.2 ∈ T) ∧ E.card + T.card ≤ C.size + 1 := by
  classical
  by_cases hE : E = ∅
  · subst hE
    refine ⟨∅, ?_, ?_⟩
    · intro e he
      simp at he
    · rw [Finset.card_empty, Finset.card_empty]
      exact Nat.zero_le _
  obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.mpr hE
  obtain ⟨F, hF⟩ : ∃ F : Finset ℕ, ∀ j, j ∈ F ↔ (j < C.gates.length ∧
      (gateAt C j).op = GateOp.and ∧ OrReaches n C C.output j ∧
      (side (n := n) C j 0).Nonempty ∧ (side (n := n) C j 1).Nonempty) :=
    ⟨(Finset.range C.gates.length).filter (fun j => (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j ∧
      (side (n := n) C j 0).Nonempty ∧ (side (n := n) C j 1).Nonempty),
      fun j => by rw [Finset.mem_filter, Finset.mem_range]⟩
  have hper : ∀ j : ℕ, ∃ (c : Fin n) (l : ℕ), j ∈ F →
      (∀ b : Fin n, b ∈ orIn n C l → G.Adj c b) ∧
      (∀ u : Fin n, u ∈ side (n := n) C j 0 → ∀ v : Fin n, v ∈ side (n := n) C j 1 →
        (c = u ∧ v ∈ orIn n C l) ∨ (c = v ∧ u ∈ orIn n C l)) := by
    intro j
    by_cases hj : j ∈ F
    · obtain ⟨hjl, hand, hor, hn0, hn1⟩ := (hF j).mp hj
      obtain ⟨hdis, hadj, hcard⟩ := h31a j hjl hand hor
      rcases hcard with hc | hc
      · obtain ⟨c, hc0⟩ := hn0
        refine ⟨c, opnd C j 1, fun _ => ⟨?_, ?_⟩⟩
        · intro b hb
          exact hadj c hc0 b hb
        · intro u hu v hv
          exact Or.inl ⟨Finset.card_le_one.mp hc c hc0 u hu, hv⟩
      · obtain ⟨c, hc1⟩ := hn1
        refine ⟨c, opnd C j 0, fun _ => ⟨?_, ?_⟩⟩
        · intro b hb
          exact (hadj b hb c hc1).symm
        · intro u hu v hv
          exact Or.inr ⟨Finset.card_le_one.mp hc c hc1 v hv, hu⟩
    · exact ⟨e0.1, 0, fun h => absurd h hj⟩
  choose ctr lf hcl using hper
  have hw : ∀ e ∈ E, ∃ i ∈ F, i < C.gates.length ∧
      (gateAt C i).op = GateOp.and ∧ OrReaches n C C.output i ∧
      ((e.1 ∈ side (n := n) C i 0 ∧ e.2 ∈ side (n := n) C i 1) ∨
        (e.2 ∈ side (n := n) C i 0 ∧ e.1 ∈ side (n := n) C i 1)) := by
    intro e he
    obtain ⟨j, hjl, hand, hor, hs⟩ := h30 e he
    refine ⟨j, (hF j).mpr ⟨hjl, hand, hor, ?_, ?_⟩, hjl, hand, hor, hs⟩
    · rcases hs with hs | hs
      · exact ⟨e.1, hs.1⟩
      · exact ⟨e.2, hs.1⟩
    · rcases hs with hs | hs
      · exact ⟨e.2, hs.2⟩
      · exact ⟨e.1, hs.2⟩
  obtain ⟨T, hTc, hTcov⟩ := h31b F hw
  have hFand : ∀ j ∈ F, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      OrReaches n C C.output j := by
    intro j hj
    obtain ⟨ha, hb, hc, _⟩ := (hF j).mp hj
    exact ⟨ha, hb, hc⟩
  have h3 := h33 F hFand
  obtain ⟨h4a, h4b⟩ := h34 F ctr lf (fun j hj => (hcl j hj).1)
  have hEsum := le_trans (sum_card_ge E (fun c => Finset.univ.filter (fun b2 : Fin n =>
      ∃ j2 ∈ F, ctr j2 = c ∧ b2 ∈ orIn n C (lf j2))) hlt (by
    intro e he
    obtain ⟨j, hjF, _, _, _, hs⟩ := hw e he
    rcases hs with hs | hs
    · rcases (hcl j hjF).2 e.1 hs.1 e.2 hs.2 with h | h
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
    · rcases (hcl j hjF).2 e.2 hs.1 e.1 hs.2 with h | h
      · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩)
      · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hjF, h.1, h.2⟩))) h4b
  have hcount := three_count C.gates.length F
    {i : ℕ | i < C.gates.length ∧ (gateAt C i).op = GateOp.or ∧ OrReaches n C C.output i}
    {i2 : ℕ | i2 < C.gates.length ∧ (gateAt C i2).op = GateOp.or ∧
      2 ≤ (orIn n C (n + i2)).card ∧ ∃ j3 ∈ F, OrReaches n C (lf j3) i2}
    (fun j hj => (hFand j hj).1) (fun i hi => hi.1) (fun i hi => hi.1)
    (fun j hj hjA => by
      have h1 := (hFand j hj).2.1
      have h2 : (gateAt C j).op = GateOp.or := hjA.2.1
      rw [h2] at h1
      cases h1)
    (fun j hj hjB => by
      have h1 := (hFand j hj).2.1
      have h2 : (gateAt C j).op = GateOp.or := hjB.2.1
      rw [h2] at h1
      cases h1)
    (fun i hi hiB => h4a i hi.1 hi.2.1 hiB.2.2.1 hiB.2.2.2 hi.2.2)
  refine ⟨T, hTcov, ?_⟩
  have hsz : C.size = C.gates.length := rfl
  rw [hsz]
  omega

lemma S35_main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 → PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false) → ∃ T : Finset (Fin n), (∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), e.1 ∈ T ∨ e.2 ∈ T) ∧ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)).card + T.card ≤ C.size + 1 := by
  intro n G _ C h4 hA h1 h2
  have h31 := s2231 n G C h4 hA h1 h2
  exact core n G C _ (fun e he => (Finset.mem_filter.mp he).2.1)
    (fun e he => s2230 n C e.1 e.2 hA h1 (Finset.mem_filter.mp he).2.1
      (Finset.mem_filter.mp he).2.2.2)
    h31.1 h31.2 (fun F => s2233 n C F hA) (fun F ctr lf => s2234 n G C F ctr lf h4 hA h1)

lemma cor_setList_pair {n : ℕ} (a b : Fin n) (hab : a < b) :
    PEqualNP.ReadK.setList ({a, b} : Finset (Fin n)) = [a.val, b.val] := by
  have key : ∀ x y : Fin n, x < y → y < x → x = y :=
    fun x y h1 h2 => absurd h1 (lt_asymm h2)
  have hp1 : List.Pairwise (fun x y : Fin n => x < y)
      ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))) :=
    List.Pairwise.filter _ (List.pairwise_lt_finRange n)
  have hp2 : List.Pairwise (fun x y : Fin n => x < y) [a, b] := by
    simp [hab]
  have hperm : List.Perm
      ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))) [a, b] := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.Nodup.filter _ (List.nodup_finRange n)
    · simp [ne_of_lt hab]
    · ext x
      simp
  have h : (List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n)))) = [a, b] :=
    List.Perm.eq_of_pairwise (fun x y _ _ => key x y) hp1 hp2 hperm
  unfold PEqualNP.ReadK.setList
  rw [h]
  rfl

lemma main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ x : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x = decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → PEqualNP.ReadK.IsReadK n C 1 → ∃ T : Finset (Fin n), (∀ u2 v2 : Fin n, G.Adj u2 v2 → u2 ∈ T ∨ v2 ∈ T) ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  intro n G _ C h4 hAO hfun hread
  have hw1 : ∀ a1 : Fin n,
      PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false := by
    intro a1
    rw [hfun, decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hu, hv⟩
    have hu1 : u = a1 := by simpa using hu
    have hv1 : v = a1 := by simpa using hv
    exact huv.ne (hu1.trans hv1.symm)
  have hw2 : ∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 →
      PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false := by
    intro a2 b2 hne hna
    rw [hfun, decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hu, hv⟩
    have hu1 : u = a2 ∨ u = b2 := by simpa using hu
    have hv1 : v = a2 ∨ v = b2 := by simpa using hv
    rcases hu1 with h1 | h1 <;> rcases hv1 with h2 | h2
    · exact huv.ne (h1.trans h2.symm)
    · rw [h1, h2] at huv
      exact hna huv
    · rw [h1, h2] at huv
      exact hna huv.symm
    · exact huv.ne (h1.trans h2.symm)
  have hrd : ∀ a b : Fin n, a < b → G.Adj a b →
      PEqualNP.ReadK.readsAtMost C n [a.val, b.val] 1 = true := by
    intro a b hab hadj
    have hpi : PEqualNP.ReadK.IsPrimeImplicant n C ({a, b} : Finset (Fin n)) := by
      constructor
      · rw [hfun, decide_eq_true_eq]
        exact ⟨a, b, hadj, by simp [PEqualNP.ReadK.setInput], by simp [PEqualNP.ReadK.setInput]⟩
      · intro T hT
        rw [hfun, decide_eq_false_iff_not]
        rintro ⟨u, v, huv, hu, hv⟩
        have hu1 : u ∈ T := by simpa [PEqualNP.ReadK.setInput] using hu
        have hv1 : v ∈ T := by simpa [PEqualNP.ReadK.setInput] using hv
        obtain ⟨hsub, hnot⟩ := Finset.ssubset_def.mp (Finset.mem_ssubsets.mp hT)
        have hu2 := hsub hu1
        have hv2 := hsub hv1
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu2 hv2
        have hboth : a ∈ T ∧ b ∈ T := by
          rcases hu2 with h1 | h1 <;> rcases hv2 with h2 | h2
          · exact absurd (h1.trans h2.symm) huv.ne
          · rw [h1] at hu1
            rw [h2] at hv1
            exact ⟨hu1, hv1⟩
          · rw [h1] at hu1
            rw [h2] at hv1
            exact ⟨hv1, hu1⟩
          · exact absurd (h1.trans h2.symm) huv.ne
        apply hnot
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with hx | hx
        · rw [hx]
          exact hboth.1
        · rw [hx]
          exact hboth.2
    have h1 := hread ({a, b} : Finset (Fin n)) hpi
    rw [cor_setList_pair a b hab] at h1
    exact h1
  obtain ⟨T, hT, hcard⟩ := S35_main_aux n G C h4 hAO hw1 hw2
  refine ⟨T, ?_, ?_⟩
  · intro u2 v2 huv
    rcases lt_trichotomy u2 v2 with hlt | heq | hgt
    · exact hT (u2, v2) (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hlt, huv, hrd u2 v2 hlt huv⟩)
    · exact absurd heq huv.ne
    · exact (hT (v2, u2) (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hgt, huv.symm, hrd v2 u2 hgt huv.symm⟩)).symm
  · have hsub : G.edgeFinset ⊆ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)).image (fun e : Fin n × Fin n => Sym2.mk e.1 e.2) := by
      intro e he
      obtain ⟨⟨u, v⟩, rfl⟩ := Quot.exists_rep e
      rw [SimpleGraph.mem_edgeFinset] at he
      have he2 : Sym2.mk u v ∈ G.edgeSet := he
      have huv : G.Adj u v := (SimpleGraph.mem_edgeSet G).mp he2
      rcases lt_trichotomy u v with hlt | heq | hgt
      · exact Finset.mem_image.mpr ⟨(u, v), Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hlt, huv, hrd u v hlt huv⟩, rfl⟩
      · exact absurd heq huv.ne
      · exact Finset.mem_image.mpr ⟨(v, u), Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hgt, huv.symm, hrd v u hgt huv.symm⟩, Sym2.eq_swap⟩
    have hle := (Finset.card_le_card hsub).trans Finset.card_image_le
    exact le_trans (Nat.add_le_add_right hle T.card) hcard




def directed {n : ℕ} (I : Fin n → Fin n → Prop) (x y : ℕ) :=
  ∃ p l, x = p.val ∧ y = n + l.val ∧ I p l

def adj {n : ℕ} (I : Fin n → Fin n → Prop) (x y : ℕ) :=
  directed I x y ∨ directed I y x

lemma adj_sym {n : ℕ} {I : Fin n → Fin n → Prop} {x y} (h : adj I x y) :
    adj I y x := h.symm

lemma sides {n : ℕ} {I : Fin n → Fin n → Prop} {x y} (h : directed I x y) :
    x < n ∧ n ≤ y := by
  obtain ⟨p,l,rfl,rfl,_⟩ := h
  exact ⟨p.isLt, Nat.le_add_right ..⟩

lemma adj_irrefl {n : ℕ} {I : Fin n → Fin n → Prop} (x : ℕ) : ¬ adj I x x := by
  intro h
  have h' := sides (h.elim id id)
  omega

lemma rectangle {n : ℕ} {I : Fin n → Fin n → Prop}
    (hu : ∀ p p' : Fin n, p ≠ p' → ∃! l, I p l ∧ I p' l)
    {x z y v} (a : directed I x y) (b : directed I z y)
    (c : directed I x v) (d : directed I z v) : x = z ∨ y = v := by
  obtain ⟨p,l,rfl,rfl,ap⟩ := a
  obtain ⟨s,l',rfl,e,bs⟩ := b
  have el : l = l' := Fin.ext (Nat.add_left_cancel e)
  subst l'
  obtain ⟨p',k,f,rfl,cp⟩ := c
  have ep : p = p' := Fin.ext f
  subst p'
  obtain ⟨s',k',g,j,ds⟩ := d
  have es : s = s' := Fin.ext g
  have ek : k = k' := Fin.ext (Nat.add_left_cancel j)
  subst s'
  subst k'
  by_cases h : p = s
  · exact Or.inl (congrArg Fin.val h)
  · obtain ⟨_,_,uniq⟩ := hu p s h
    exact Or.inr (congrArg (fun t : Fin n => n + t.val)
      ((uniq l ⟨ap,bs⟩).trans (uniq k ⟨cp,ds⟩).symm))

lemma adj_unique {n : ℕ} {I : Fin n → Fin n → Prop}
    (hu : ∀ p p' : Fin n, p ≠ p' → ∃! l, I p l ∧ I p' l) : ∀ {x z y v}, x ≠ z → adj I x y → adj I z y → adj I x v → adj I z v → y = v := by
  intro x z y v hn a b c d
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> rcases d with d | d
  all_goals first
    | exact (rectangle hu a b c d).resolve_left hn
    | exact (rectangle hu a c b d).resolve_right hn
    | have := sides a; have := sides b; have := sides c; have := sides d; omega


noncomputable def allEdges {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2)

lemma allEdges_card {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (q : ℕ)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    (allEdges I).card = N * (q + 1) := by
  classical
  let F (l : Fin N) : Finset (Fin N × Fin N) :=
    (Finset.univ.filter (fun p => I p l)).map ⟨fun p => (p, l), fun _ _ h => congrArg Prod.fst h⟩
  have hF (l : Fin N) (e : Fin N × Fin N) : e ∈ F l ↔ I e.1 l ∧ e.2 = l := by
    constructor
    · intro he
      obtain ⟨p, hp, ht⟩ := Finset.mem_map.mp he
      change (p, l) = e at ht
      rw [← ht]
      exact ⟨(Finset.mem_filter.mp hp).2, rfl⟩
    · rintro ⟨hi, hh⟩
      refine Finset.mem_map.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, ?_⟩
      exact Prod.ext rfl hh.symm
  have heq : allEdges I = Finset.univ.biUnion F := by
    ext e
    simp only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, hF]
    exact ⟨fun h => ⟨e.2, h, rfl⟩, fun ⟨l, hi, he⟩ => he ▸ hi⟩
  rw [heq, Finset.card_biUnion]
  · simp [F, hL]
  · intro l _ l' _ hne
    refine Finset.disjoint_left.mpr ?_
    intro e he he'
    exact hne (((hF l e).mp he).2.symm.trans ((hF l' e).mp he').2)


def incidenceGraph {N : ℕ} (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N + N)) where
  Adj a b := adj I a.val b.val
  symm := ⟨fun _ _ h => adj_sym h⟩
  loopless := ⟨fun a => adj_irrefl a.val⟩

open Classical in
lemma incidence_noFour {N : ℕ} (I : Fin N → Fin N → Prop)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l, I p l ∧ I p' l) :
    PEqualNP.TopForm.NoFourCycle (incidenceGraph I) := by
  intro a b hn
  apply Finset.card_le_one.mpr
  intro y hy v hv
  apply Fin.ext
  exact adj_unique hu (fun h => hn (Fin.ext h))
    (Finset.mem_filter.mp hy).2.1 (Finset.mem_filter.mp hy).2.2
    (Finset.mem_filter.mp hv).2.1 (Finset.mem_filter.mp hv).2.2

lemma incidence_formula {N : ℕ} (I : Fin N → Fin N → Prop) (x : Fin (N + N) → Bool) :
    (∃ u v : Fin (N + N), (incidenceGraph I).Adj u v ∧ x u = true ∧ x v = true) ↔
      (∃ p l : Fin N, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) := by
  constructor
  · rintro ⟨u,v,h,hu,hv⟩
    rcases h with h | h
    · obtain ⟨p,l,hp,hl,hi⟩ := h
      have ep : u = Fin.castAdd N p := Fin.ext hp
      have el : v = Fin.natAdd N l := Fin.ext hl
      exact ⟨p,l,hi,ep ▸ hu,el ▸ hv⟩
    · obtain ⟨p,l,hp,hl,hi⟩ := h
      have ep : v = Fin.castAdd N p := Fin.ext hp
      have el : u = Fin.natAdd N l := Fin.ext hl
      exact ⟨p,l,hi,ep ▸ hv,el ▸ hu⟩
  · rintro ⟨p,l,hi,hp,hl⟩
    exact ⟨Fin.castAdd N p,Fin.natAdd N l,Or.inl ⟨p,l,rfl,rfl,hi⟩,hp,hl⟩

def incidenceEdge {N : ℕ} (e : Fin N × Fin N) : Sym2 (Fin (N + N)) :=
  Sym2.mk (Fin.castAdd N e.1) (Fin.natAdd N e.2)

lemma incidenceEdge_injective {N : ℕ} : Function.Injective (@incidenceEdge N) := by
  rintro ⟨p,l⟩ ⟨p',l'⟩ he
  change Sym2.mk (Fin.castAdd N p) (Fin.natAdd N l) =
    Sym2.mk (Fin.castAdd N p') (Fin.natAdd N l') at he
  rcases Sym2.eq_iff.mp he with ⟨hp,hl⟩ | ⟨hp,hl⟩
  · apply Prod.ext
    · have hv := congrArg Fin.val hp
      exact Fin.ext hv
    · exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val hl))
  · have h := congrArg Fin.val hp
    have := p.isLt
    change p.val = N + l'.val at h
    omega

open Classical in
lemma incidence_edge_count {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    N * (q + 1) ≤ (incidenceGraph I).edgeFinset.card := by
  have hsub : (allEdges I).image incidenceEdge ⊆ (incidenceGraph I).edgeFinset := by
    intro e he
    obtain ⟨⟨p,l⟩,hp,rfl⟩ := Finset.mem_image.mp he
    rw [SimpleGraph.mem_edgeFinset]
    have hi : I p l := by simpa only [allEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hp
    exact Or.inl ⟨p,l,rfl,rfl,hi⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ incidenceEdge_injective, allEdges_card I q hc] at h
  exact h

lemma incidence_cover_count {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (T : Finset (Fin (N + N)))
    (hT : ∀ u v, (incidenceGraph I).Adj u v → u ∈ T ∨ v ∈ T) : N ≤ T.card := by
  classical
  let A : Finset (Fin N) := Finset.univ.filter (fun p => Fin.castAdd N p ∈ T)
  let B : Finset (Fin N) := Finset.univ.filter (fun l => Fin.natAdd N l ∈ T)
  have hab : N ≤ A.card + B.card := plane_cover_bound I hq hN hc hu A B (by
    intro p l hi
    have h := hT (Fin.castAdd N p) (Fin.natAdd N l) (Or.inl ⟨p,l,rfl,rfl,hi⟩)
    simpa only [A,B,Finset.mem_filter,Finset.mem_univ,true_and] using h)
  have hd : Disjoint (A.image (Fin.castAdd N)) (B.image (Fin.natAdd N)) := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hv
    obtain ⟨l,_,hl⟩ := Finset.mem_image.mp hv'
    have h := congrArg Fin.val (hp.trans hl.symm)
    change p.val = N + l.val at h
    have := p.isLt
    omega
  have hs : A.image (Fin.castAdd N) ∪ B.image (Fin.natAdd N) ⊆ T := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hp).2
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hl).2
  have ha : Function.Injective (Fin.castAdd N : Fin N → Fin (N + N)) := by
    intro p p' h
    have hv := congrArg Fin.val h
    exact Fin.ext hv
  have hb : Function.Injective (Fin.natAdd N : Fin N → Fin (N + N)) := by
    intro l l' h
    exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))
  have hs' := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ ha,
    Finset.card_image_of_injective _ hb] at hs'
  exact hab.trans hs'

lemma plane_read_one_lower {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hc : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hfun : ∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (hread : PEqualNP.ReadK.IsReadK (N + N) C 1) : N * (q + 2) - 1 ≤ C.size := by
  classical
  have hfun' : ∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z =
      decide (∃ u v : Fin (N + N), (incidenceGraph I).Adj u v ∧ z u = true ∧ z v = true) := by
    intro z
    rw [hfun]
    exact decide_eq_decide.mpr (incidence_formula I z).symm
  obtain ⟨T,hT,hsize⟩ := main_aux (N + N) (incidenceGraph I) C (incidence_noFour I hu) hAO hfun' hread
  have he := incidence_edge_count I hc
  have ht := incidence_cover_count I hq hN hc hu T hT
  have hm : N * (q + 2) = N * (q + 1) + N := by ring
  omega

end PEqualNP.Outside.L_meta_2583.RefutationBridge.ReadLower

namespace PEqualNP.Outside.L_meta_2583.RefutationBridge
namespace Repair
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK
def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl
lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega
lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key
def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]
lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj
lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)
lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega
lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj
lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩
lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2
lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]
lemma gate_op {C : Circuit} (hm : Monotone2 C) {k : ℕ} (hk : k < C.gates.length) :
    (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  simpa using (hm _ (gateAt_mem hk)).1
lemma pair_mono {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {x y : Fin n → Bool} (hxy : ∀ u, x u = true → y u = true) :
    ∀ w, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hinput : w < n
    · let u : Fin n := ⟨w, hinput⟩
      change val C (List.ofFn x) u.val = true at hw
      change val C (List.ofFn y) u.val = true
      rw [val_ofFn] at *
      exact hxy u hw
    · have hwlt : w < n + C.gates.length := by
        by_contra! h
        rw [val_ge (by simp : (List.ofFn x).length = n) h] at hw
        cases hw
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rcases gate_op hm hk with hop | hop
      · apply (val_and (by simp) hk hop).2
        intro i hi
        obtain ⟨hlt, ht⟩ := (val_and (by simp) hk hop).1 hw i hi
        exact ⟨hlt, ih i hlt ht⟩
      · obtain ⟨i, hi, hlt, ht⟩ := (val_or (by simp) hk hop).1 hw
        exact (val_or (by simp) hk hop).2 ⟨i, hi, hlt, ih i hlt ht⟩
lemma foldl_append_length {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β) :
    (l.foldl (fun w g => w ++ [f w g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, List.length_append, List.length_singleton]
    omega
lemma foldl_append_getD_lt {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (k : ℕ) (hk : k < acc.length) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD k d = acc.getD k d := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have hk' : k < (acc ++ [f acc a]).length := by
      rw [List.length_append, List.length_singleton]
      omega
    rw [ih (acc ++ [f acc a]) hk']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hk]
lemma foldl_append_getD_gate {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j : ℕ) (hj : j < l.length) (defaultA : α) :
    (l.foldl (fun w g => w ++ [f w g]) acc).getD (acc.length + j) d =
      f ((l.take j).foldl (fun w g => w ++ [f w g]) acc) (l.getD j defaultA) := by
  have hsplit : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    have h1 := (List.take_append_drop j l).symm
    have h2 : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← h2]
    exact h1
  have hget : l.getD j defaultA = l[j] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
    rfl
  rw [hget]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pre := (l.take j).foldl (fun w g => w ++ [f w g]) acc
  have hprelen : pre.length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hlt : acc.length + j < (pre ++ [f pre l[j]]).length := by
    rw [List.length_append, List.length_singleton, hprelen]
    omega
  rw [foldl_append_getD_lt f (l.drop (j + 1)) (pre ++ [f pre l[j]]) d (acc.length + j) hlt]
  rw [List.getD_eq_getElem?_getD, ← hprelen]
  simp
lemma foldl_append_take_getD {α β : Type*} (f : List β → α → β) (l : List α) (acc : List β)
    (d : β) (j i : ℕ) (hj : j ≤ l.length) (hi : i < acc.length + j) :
    ((l.take j).foldl (fun w g => w ++ [f w g]) acc).getD i d =
      (l.foldl (fun w g => w ++ [f w g]) acc).getD i d := by
  have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hprelen : ((l.take j).foldl (fun w g => w ++ [f w g]) acc).length = acc.length + j := by
    rw [foldl_append_length, List.length_take, Nat.min_eq_left hj]
  rw [foldl_append_getD_lt f (l.drop j) _ d i (hprelen ▸ hi)]
lemma readVectors_getD_gate {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (S : List ℕ) (k : ℕ) {j : ℕ} (hj : j < C.gates.length) :
    (readVectors C n S k).getD (n + j) [] =
      let ins := (gateAt C j).inputs.map fun i => (readVectors C n S k).getD i []
      match (gateAt C j).op with
      | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
      | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
      | _ => [] := by
  let step : List (List (List ℕ)) → Gate → List (List ℕ) := fun R g =>
    match g.op with
    | GateOp.or => (g.inputs.map fun i => R.getD i []).foldl (fun acc A => A.foldl insertNew acc) []
    | GateOp.and => (g.inputs.map fun i => R.getD i []).foldl (andStep k) [S.map fun _ => 0]
    | _ => []
  have hrv : readVectors C n S k =
      C.gates.foldl (fun R g => R ++ [step R g]) ((List.range n).map (leafVectors S k)) := rfl
  rw [hrv]
  have hgate := foldl_append_getD_gate step
    C.gates ((List.range n).map (leafVectors S k)) [] j hj ⟨GateOp.or, []⟩
  rw [List.length_map, List.length_range] at hgate
  rw [hgate]
  have hmap :
      (gateAt C j).inputs.map (fun i =>
        ((C.gates.take j).foldl (fun R g => R ++ [step R g])
          ((List.range n).map (leafVectors S k))).getD i []) =
      (gateAt C j).inputs.map (fun i =>
        (C.gates.foldl (fun R g => R ++ [step R g])
          ((List.range n).map (leafVectors S k))).getD i []) := by
    apply List.map_congr_left
    intro i hi
    have hilt : i < ((List.range n).map (leafVectors S k)).length + j := by
      rw [List.length_map, List.length_range]
      exact hAO.2.1 j hj i hi
    exact foldl_append_take_getD step C.gates ((List.range n).map (leafVectors S k)) [] j i
      (Nat.le_of_lt hj) hilt
  change (match (gateAt C j).op with
    | GateOp.or =>
      ((gateAt C j).inputs.map fun i => _).foldl (fun acc (A : List (List ℕ)) => A.foldl insertNew acc) []
    | GateOp.and =>
      ((gateAt C j).inputs.map fun i => _).foldl (andStep k) [S.map fun _ => 0]
    | _ => []) = _
  rw [hmap]
end Repair
namespace StructuralAbsorption
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover
end StructuralAbsorption
namespace ReducedCheck
def avoidingRight {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter fun l => ∀ p ∈ P, ¬ I p l
def closureLeft {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun p => ∀ l ∈ avoidingRight I P, ¬ I p l
lemma mem_avoidingRight {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) (l : Fin m) :
    l ∈ avoidingRight I P ↔ ∀ p ∈ P, ¬ I p l := by
  simp [avoidingRight]
lemma mem_closureLeft {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) (p : Fin n) :
    p ∈ closureLeft I P ↔ ∀ l ∈ avoidingRight I P, ¬ I p l := by
  simp [closureLeft]
lemma subset_closureLeft {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) : P ⊆ closureLeft I P := by
  intro p hp
  apply (mem_closureLeft I P p).2
  intro l hl
  exact (mem_avoidingRight I P l).1 hl p hp
lemma avoidingRight_closureLeft {n m : ℕ} (I : Fin n → Fin m → Prop)
    [DecidableRel I] (P : Finset (Fin n)) :
    avoidingRight I (closureLeft I P) = avoidingRight I P := by
  ext l
  constructor
  · intro hl
    apply (mem_avoidingRight I P l).2
    intro p hp
    exact (mem_avoidingRight I (closureLeft I P) l).1 hl p
      (subset_closureLeft I P hp)
  · intro hl
    apply (mem_avoidingRight I (closureLeft I P) l).2
    intro p hp
    exact (mem_closureLeft I P p).1 hp l hl
lemma closureLeft_idem {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) : closureLeft I (closureLeft I P) = closureLeft I P := by
  ext p
  simp only [mem_closureLeft, avoidingRight_closureLeft]
def independentInput {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (P : Finset (Fin n)) : Sum (Fin n) (Fin m) → Bool :=
  Sum.elim (fun p => decide (p ∈ P)) (fun l => decide (l ∈ avoidingRight I P))
def edgeInput {n m : ℕ} (p : Fin n) (l : Fin m) : Sum (Fin n) (Fin m) → Bool :=
  Sum.elim (fun a => decide (a = p)) (fun b => decide (b = l))
lemma exact_certificate {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (f : (Sum (Fin n) (Fin m) → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hpos : ∀ p l, I p l → f (edgeInput p l) = true)
    (hneg : ∀ P : Finset (Fin n), closureLeft I P = P →
      f (independentInput I P) = false) :
    ∀ z, f z = decide (∃ p l, I p l ∧ z (Sum.inl p) = true ∧
      z (Sum.inr l) = true) := by
  intro z
  by_cases h : ∃ p l, I p l ∧ z (Sum.inl p) = true ∧ z (Sum.inr l) = true
  · rw [decide_eq_true h]
    obtain ⟨p, l, hI, hp, hl⟩ := h
    apply hmono (edgeInput p l) z _ (hpos p l hI)
    intro i hi
    cases i with
    | inl a =>
      have ha : a = p := by simpa [edgeInput] using hi
      simpa [ha] using hp
    | inr b =>
      have hb : b = l := by simpa [edgeInput] using hi
      simpa [hb] using hl
  · rw [decide_eq_false h]
    let P := Finset.univ.filter fun p : Fin n => z (Sum.inl p) = true
    have hext : ∀ i, z i = true → independentInput I (closureLeft I P) i = true := by
      intro i hi
      cases i with
      | inl p =>
        apply decide_eq_true
        exact subset_closureLeft I P (by simp [P, hi])
      | inr l =>
        apply decide_eq_true
        rw [avoidingRight_closureLeft]
        apply (mem_avoidingRight I P l).2
        intro p hp hI
        have hp' : z (Sum.inl p) = true := (Finset.mem_filter.1 hp).2
        exact h ⟨p, l, hI, hp', hi⟩
    cases hf : f z with
    | false => rfl
    | true =>
      have ht := hmono z (independentInput I (closureLeft I P)) hext hf
      rw [hneg _ (closureLeft_idem I P)] at ht
      cases ht
end ReducedCheck
namespace CircuitCheckWrapper
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.RefutationBridge.ReducedCheck
def liftInput {n m : ℕ} (z : Sum (Fin n) (Fin m) → Bool) : Fin (n + m) → Bool :=
  Fin.addCases (fun p => z (Sum.inl p)) (fun l => z (Sum.inr l))
def lowerInput {n m : ℕ} (z : Fin (n + m) → Bool) : Sum (Fin n) (Fin m) → Bool :=
  Sum.elim (fun p => z (Fin.castAdd m p)) (fun l => z (Fin.natAdd n l))
lemma lift_lower {n m : ℕ} (z : Fin (n + m) → Bool) :
    liftInput (lowerInput z) = z := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro p
    simp [liftInput, lowerInput]
  · intro l
    simp [liftInput, lowerInput]
lemma ao2_monotone2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) : Monotone2 C := by
  intro g hg
  refine ⟨?_, (hAO.2.2 g hg).le⟩
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hAO.1 g hg
lemma circuitFun_lift_mono {n m : ℕ} {C : Circuit} (hAO : IsAO2 (n + m) C)
    {x y : Sum (Fin n) (Fin m) → Bool}
    (hxy : ∀ i, x i = true → y i = true)
    (hx : circuitFun (n + m) C (liftInput x) = true) :
    circuitFun (n + m) C (liftInput y) = true := by
  apply PEqualNP.Outside.L_meta_2583.RefutationBridge.Repair.pair_mono (ao2_monotone2 hAO) ?_ C.output hx
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p hp
    simpa [liftInput] using hxy (Sum.inl p) (by simpa [liftInput] using hp)
  · intro l hl
    simpa [liftInput] using hxy (Sum.inr l) (by simpa [liftInput] using hl)
lemma ao2_exact_certificate {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (C : Circuit) (hAO : IsAO2 (n + m) C)
    (hpos : ∀ p l, I p l → circuitFun (n + m) C (liftInput (edgeInput p l)) = true)
    (hneg : ∀ P : Finset (Fin n), closureLeft I P = P →
      circuitFun (n + m) C (liftInput (independentInput I P)) = false) :
    ∀ z : Fin (n + m) → Bool,
      circuitFun (n + m) C z = decide (∃ p l, I p l ∧
        z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true) := by
  have hcert := exact_certificate I
    (fun v => circuitFun (n + m) C (liftInput v))
    (fun x y hxy hx => circuitFun_lift_mono hAO hxy hx) hpos hneg
  intro z
  have hz := hcert (lowerInput z)
  rw [lift_lower] at hz
  exact hz.trans (Bool.decide_congr (by rfl))
end CircuitCheckWrapper
namespace PurePointBudget
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_2583.RefutationBridge.Repair
end PurePointBudget
namespace Repair
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK
end Repair
namespace ProjectedBudget
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_2583.RefutationBridge.Repair
open PEqualNP.Outside.L_meta_2583.RefutationBridge.PurePointBudget
end ProjectedBudget
namespace PlaneMatching
end PlaneMatching
namespace PathDegreeObstruction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
end PathDegreeObstruction
namespace PartialPointBudget
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_2583.RefutationBridge.Repair
open PEqualNP.Outside.L_meta_2583.RefutationBridge.PurePointBudget
end PartialPointBudget
namespace PackedEval
open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
def gate (w : List ℕ) (g : Gate) : ℕ :=
  match g.op with
  | .and => (w.getD (g.inputs.getD 0 0) 0) &&& (w.getD (g.inputs.getD 1 0) 0)
  | .or => (w.getD (g.inputs.getD 0 0) 0) ||| (w.getD (g.inputs.getD 1 0) 0)
  | _ => 0
def wires (C : Circuit) (w : List ℕ) : List ℕ :=
  C.gates.foldl (fun w g => w ++ [gate w g]) w
def eval (C : Circuit) (w : List ℕ) : ℕ :=
  (wires C w).getD C.output 0
lemma testBit_getD (w : List ℕ) (r i : ℕ) :
    (w.getD i 0).testBit r = (w.map fun a => a.testBit r).getD i false := by
  induction w generalizing i with
  | nil => simp
  | cons a w ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i
lemma gate_testBit (w : List ℕ) (g : Gate) (r : ℕ)
    (hop : g.op = .and ∨ g.op = .or) (hlen : g.inputs.length = 2) :
    (gate w g).testBit r =
      g.op.eval (g.inputs.map fun i => (w.map fun a => a.testBit r).getD i false) := by
  obtain ⟨a, b, hi⟩ := List.length_eq_two.mp hlen
  have ha := testBit_getD w r a
  have hb := testBit_getD w r b
  rcases hop with hop | hop
  · simpa [gate, hop, hi, GateOp.eval] using congrArg₂ (fun a b : Bool => a && b) ha hb
  · simpa [gate, hop, hi, GateOp.eval] using congrArg₂ (fun a b : Bool => a || b) ha hb
lemma fold_testBit (gs : List Gate) (w : List ℕ) (r : ℕ)
    (hgs : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    (gs.foldl (fun w g => w ++ [gate w g]) w).map (fun a => a.testBit r) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (w.map fun a => a.testBit r) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hg := hgs g (by simp)
    have hs : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 :=
      fun g h => hgs g (by simp [h])
    simp only [List.foldl_cons]
    rw [ih _ hs]
    simp only [List.map_append, List.map_cons, List.map_nil, gate_testBit w g r hg.1 hg.2]
lemma wires_testBit (C : Circuit) (w : List ℕ) (r : ℕ)
    (hC : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    (wires C w).map (fun a => a.testBit r) = C.wires (w.map fun a => a.testBit r) :=
  fold_testBit C.gates w r hC
lemma eval_testBit (C : Circuit) (w : List ℕ) (r : ℕ)
    (hC : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) :
    (eval C w).testBit r = C.eval (w.map fun a => a.testBit r) := by
  rw [eval, testBit_getD, wires_testBit C w r hC]
  rfl
lemma eval_testBit_of_isAO2 (n : ℕ) (C : Circuit) (w : List ℕ) (r : ℕ)
    (hC : IsAO2 n C) :
    (eval C w).testBit r = C.eval (w.map fun a => a.testBit r) :=
  eval_testBit C w r (fun g hg => ⟨hC.1 g hg, hC.2.2 g hg⟩)
end PackedEval
namespace PackedColumns
def col : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, j =>
    if j < n then
      let v := col n j
      v ||| (v <<< (2 ^ n))
    else if j = n then
      ((2 ^ (2 ^ n) - 1) <<< (2 ^ n))
    else 0
lemma col_testBit (n j : ℕ) (hj : j < n) (r : ℕ) :
    (col n j).testBit r = (decide (r < 2 ^ n) && r.testBit j) := by
  induction n generalizing j r with
  | zero => omega
  | succ n ih =>
    have hp : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; omega
    by_cases hjn : j < n
    · rw [col, ite_eq_left hjn]
      simp only [Nat.testBit_lor, Nat.testBit_shiftLeft, ih j hjn]
      by_cases hr : r < 2 ^ n
      · have hn : ¬ 2 ^ n ≤ r := by omega
        have hr' : r < 2 ^ (n + 1) := by omega
        simp [hr, hn, hr']
      · have hn : 2 ^ n ≤ r := by omega
        have he : r.testBit j = (r - 2 ^ n).testBit j := by
          have h := Nat.testBit_two_pow_add_gt hjn (r - 2 ^ n)
          rw [Nat.add_sub_of_le hn] at h
          exact h
        by_cases hr' : r < 2 ^ (n + 1)
        · have hd : r - 2 ^ n < 2 ^ n := by omega
          simp [hr, hn, hr', hd, he]
        · have hd : ¬ r - 2 ^ n < 2 ^ n := by omega
          simp [hr, hn, hr', hd]
    · have he : j = n := by omega
      subst j
      simp only [col, Nat.lt_irrefl, ite_false, ite_true,
        Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      by_cases hr : r < 2 ^ n
      · have hn : ¬ 2 ^ n ≤ r := by omega
        have hb := Nat.testBit_lt_two_pow hr
        simp [hn, hb]
      · have hn : 2 ^ n ≤ r := by omega
        by_cases hr' : r < 2 ^ (n + 1)
        · have hd : r - 2 ^ n < 2 ^ n := by omega
          have hb := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hn hr'
          simp [hn, hr', hd, hb]
        · have hd : ¬ r - 2 ^ n < 2 ^ n := by omega
          simp [hn, hr', hd]
lemma col_testBit_lt (n j r : ℕ) (hj : j < n) (hr : r < 2 ^ n) :
    (col n j).testBit r = r.testBit j := by
  simp [col_testBit n j hj r, hr]
end PackedColumns
namespace PackedLineColumns
def joinWords (ws : List Nat) : Nat := ws.foldr (· ||| ·) 0
lemma joinWords_bit (ws : List Nat) (r : Nat) :
    (joinWords ws).testBit r = ws.any (fun w => w.testBit r) := by
  induction ws with
  | nil => simp [joinWords]
  | cons w ws ih => simpa [joinWords, Nat.testBit_lor] using congrArg (fun b => w.testBit r || b) ih
end PackedLineColumns
namespace PackedInputCode
def code {n : Nat} (x : Fin n → Bool) : Fin (2 ^ n) :=
  ⟨(BitVec.ofBoolListLE (List.ofFn x)).toNat, by
    simpa using (BitVec.ofBoolListLE (List.ofFn x)).isLt⟩
lemma code_bit {n : Nat} (x : Fin n → Bool) (i : Fin n) :
    (code x).val.testBit i.val = x i := by
  unfold code
  rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE]
  simp [List.getD_eq_getElem?_getD]
end PackedInputCode
namespace PackedBoundary
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.RefutationBridge.ReducedCheck
open PEqualNP.Outside.L_meta_2583.RefutationBridge.CircuitCheckWrapper
end PackedBoundary
namespace Q3PackedColumnCache
lemma power_0 : (2 : Nat) ^ (2 ^ 0) = 2 := by
  decide
lemma power_1 : (2 : Nat) ^ (2 ^ 1) = 4 := by
  rw [show (2 : Nat) ^ 1 = 2 ^ 0 * 2 by decide, pow_mul, power_0]
  decide
lemma power_2 : (2 : Nat) ^ (2 ^ 2) = 16 := by
  rw [show (2 : Nat) ^ 2 = 2 ^ 1 * 2 by decide, pow_mul, power_1]
  decide
lemma power_3 : (2 : Nat) ^ (2 ^ 3) = 256 := by
  rw [show (2 : Nat) ^ 3 = 2 ^ 2 * 2 by decide, pow_mul, power_2]
  decide
lemma power_4 : (2 : Nat) ^ (2 ^ 4) = 65536 := by
  rw [show (2 : Nat) ^ 4 = 2 ^ 3 * 2 by decide, pow_mul, power_3]
  decide
lemma power_5 : (2 : Nat) ^ (2 ^ 5) = 4294967296 := by
  rw [show (2 : Nat) ^ 5 = 2 ^ 4 * 2 by decide, pow_mul, power_4]
  decide
lemma power_6 : (2 : Nat) ^ (2 ^ 6) = 18446744073709551616 := by
  rw [show (2 : Nat) ^ 6 = 2 ^ 5 * 2 by decide, pow_mul, power_5]
  decide
lemma power_7 : (2 : Nat) ^ (2 ^ 7) = 340282366920938463463374607431768211456 := by
  rw [show (2 : Nat) ^ 7 = 2 ^ 6 * 2 by decide, pow_mul, power_6]
  decide
lemma power_8 : (2 : Nat) ^ (2 ^ 8) = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
  rw [show (2 : Nat) ^ 8 = 2 ^ 7 * 2 by decide, pow_mul, power_7]
  decide
lemma power_9 : (2 : Nat) ^ (2 ^ 9) = 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 := by
  rw [show (2 : Nat) ^ 9 = 2 ^ 8 * 2 by decide, pow_mul, power_8]
  decide
lemma power_10 : (2 : Nat) ^ (2 ^ 10) = 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137216 := by
  rw [show (2 : Nat) ^ 10 = 2 ^ 9 * 2 by decide, pow_mul, power_9]
  decide
lemma col_1_0 : PackedColumns.col 1 0 = 2 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_0]
  decide
lemma col_2_0 : PackedColumns.col 2 0 = 10 := by
  rw [PackedColumns.col]
  simp only [show 0 < 1 by decide, ↓reduceIte]
  simp only [col_1_0]
  decide
lemma col_2_1 : PackedColumns.col 2 1 = 12 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_1]
  decide
lemma col_3_0 : PackedColumns.col 3 0 = 170 := by
  rw [PackedColumns.col]
  simp only [show 0 < 2 by decide, ↓reduceIte]
  simp only [col_2_0]
  decide
lemma col_3_1 : PackedColumns.col 3 1 = 204 := by
  rw [PackedColumns.col]
  simp only [show 1 < 2 by decide, ↓reduceIte]
  simp only [col_2_1]
  decide
lemma col_3_2 : PackedColumns.col 3 2 = 240 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_2]
  decide
lemma col_4_0 : PackedColumns.col 4 0 = 43690 := by
  rw [PackedColumns.col]
  simp only [show 0 < 3 by decide, ↓reduceIte]
  simp only [col_3_0]
  decide
lemma col_4_1 : PackedColumns.col 4 1 = 52428 := by
  rw [PackedColumns.col]
  simp only [show 1 < 3 by decide, ↓reduceIte]
  simp only [col_3_1]
  decide
lemma col_4_2 : PackedColumns.col 4 2 = 61680 := by
  rw [PackedColumns.col]
  simp only [show 2 < 3 by decide, ↓reduceIte]
  simp only [col_3_2]
  decide
lemma col_4_3 : PackedColumns.col 4 3 = 65280 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_3]
  decide
lemma col_5_0 : PackedColumns.col 5 0 = 2863311530 := by
  rw [PackedColumns.col]
  simp only [show 0 < 4 by decide, ↓reduceIte]
  simp only [col_4_0]
  decide
lemma col_5_1 : PackedColumns.col 5 1 = 3435973836 := by
  rw [PackedColumns.col]
  simp only [show 1 < 4 by decide, ↓reduceIte]
  simp only [col_4_1]
  decide
lemma col_5_2 : PackedColumns.col 5 2 = 4042322160 := by
  rw [PackedColumns.col]
  simp only [show 2 < 4 by decide, ↓reduceIte]
  simp only [col_4_2]
  decide
lemma col_5_3 : PackedColumns.col 5 3 = 4278255360 := by
  rw [PackedColumns.col]
  simp only [show 3 < 4 by decide, ↓reduceIte]
  simp only [col_4_3]
  decide
lemma col_5_4 : PackedColumns.col 5 4 = 4294901760 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_4]
  decide
lemma col_6_0 : PackedColumns.col 6 0 = 12297829382473034410 := by
  rw [PackedColumns.col]
  simp only [show 0 < 5 by decide, ↓reduceIte]
  simp only [col_5_0]
  decide
lemma col_6_1 : PackedColumns.col 6 1 = 14757395258967641292 := by
  rw [PackedColumns.col]
  simp only [show 1 < 5 by decide, ↓reduceIte]
  simp only [col_5_1]
  decide
lemma col_6_2 : PackedColumns.col 6 2 = 17361641481138401520 := by
  rw [PackedColumns.col]
  simp only [show 2 < 5 by decide, ↓reduceIte]
  simp only [col_5_2]
  decide
lemma col_6_3 : PackedColumns.col 6 3 = 18374966859414961920 := by
  rw [PackedColumns.col]
  simp only [show 3 < 5 by decide, ↓reduceIte]
  simp only [col_5_3]
  decide
lemma col_6_4 : PackedColumns.col 6 4 = 18446462603027742720 := by
  rw [PackedColumns.col]
  simp only [show 4 < 5 by decide, ↓reduceIte]
  simp only [col_5_4]
  decide
lemma col_6_5 : PackedColumns.col 6 5 = 18446744069414584320 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_5]
  decide
lemma col_7_0 : PackedColumns.col 7 0 = 226854911280625642308916404954512140970 := by
  rw [PackedColumns.col]
  simp only [show 0 < 6 by decide, ↓reduceIte]
  simp only [col_6_0]
  decide
lemma col_7_1 : PackedColumns.col 7 1 = 272225893536750770770699685945414569164 := by
  rw [PackedColumns.col]
  simp only [show 1 < 6 by decide, ↓reduceIte]
  simp only [col_6_1]
  decide
lemma col_7_2 : PackedColumns.col 7 2 = 320265757102059730318470218759311257840 := by
  rw [PackedColumns.col]
  simp only [show 2 < 6 by decide, ↓reduceIte]
  simp only [col_6_2]
  decide
lemma col_7_3 : PackedColumns.col 7 3 = 338958311018522360492699998064329424640 := by
  rw [PackedColumns.col]
  simp only [show 3 < 6 by decide, ↓reduceIte]
  simp only [col_6_3]
  decide
lemma col_7_4 : PackedColumns.col 7 4 = 340277174703306882242637262502835978240 := by
  rw [PackedColumns.col]
  simp only [show 4 < 6 by decide, ↓reduceIte]
  simp only [col_6_4]
  decide
lemma col_7_5 : PackedColumns.col 7 5 = 340282366841710300967557013907638845440 := by
  rw [PackedColumns.col]
  simp only [show 5 < 6 by decide, ↓reduceIte]
  simp only [col_6_5]
  decide
lemma col_7_6 : PackedColumns.col 7 6 = 340282366920938463444927863358058659840 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_6]
  decide
lemma col_8_0 : PackedColumns.col 8 0 = 77194726158210796949047323339125271902179989777093709359638389338608753093290 := by
  rw [PackedColumns.col]
  simp only [show 0 < 7 by decide, ↓reduceIte]
  simp only [col_7_0]
  decide
lemma col_8_1 : PackedColumns.col 8 1 = 92633671389852956338856788006950326282615987732512451231566067206330503711948 := by
  rw [PackedColumns.col]
  simp only [show 1 < 7 by decide, ↓reduceIte]
  simp only [col_7_1]
  decide
lemma col_8_2 : PackedColumns.col 8 2 = 108980789870415242751596221184647442685430573802955824978313020242741769072880 := by
  rw [PackedColumns.col]
  simp only [show 2 < 7 by decide, ↓reduceIte]
  simp only [col_7_2]
  decide
lemma col_8_3 : PackedColumns.col 8 3 = 115341536360906404779899502576747487978354537254490211650198994186870666100480 := by
  rw [PackedColumns.col]
  simp only [show 3 < 7 by decide, ↓reduceIte]
  simp only [col_7_3]
  decide
lemma col_8_4 : PackedColumns.col 8 4 = 115790322417210952336529717160220497262186272106556906860092653394915770695680 := by
  rw [PackedColumns.col]
  simp only [show 4 < 7 by decide, ↓reduceIte]
  simp only [col_7_4]
  decide
lemma col_8_5 : PackedColumns.col 8 5 = 115792089210356248762697446947946071893095522863849111501270640965525260206080 := by
  rw [PackedColumns.col]
  simp only [show 5 < 7 by decide, ↓reduceIte]
  simp only [col_7_5]
  decide
lemma col_8_6 : PackedColumns.col 8 6 = 115792089237316195417293883273301227089774477609353836086800156426807153786880 := by
  rw [PackedColumns.col]
  simp only [show 6 < 7 by decide, ↓reduceIte]
  simp only [col_7_6]
  decide
lemma col_8_7 : PackedColumns.col 8 7 = 115792089237316195423570985008687907852929702298719625575994209400481361428480 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_7]
  decide
lemma col_9_0 : PackedColumns.col 9 0 = 8938538619961731399716016665470564084986243880394928918482374295814509353382364651201249532111268951793354572124324033902502588541297713297622432670722730 := by
  rw [PackedColumns.col]
  simp only [show 0 < 8 by decide, ↓reduceIte]
  simp only [col_8_0]
  decide
lemma col_9_1 : PackedColumns.col 9 1 = 10726246343954077679659219998564676901983492656473914702178849154977411224058837581441499438533522742152025486549188840683003106249557255957146919204867276 := by
  rw [PackedColumns.col]
  simp only [show 1 < 8 by decide, ↓reduceIte]
  simp only [col_8_1]
  decide
lemma col_9_2 : PackedColumns.col 9 2 = 12619113345828326681952023527723149296451167831145782002563351947032248498892750095813528751215909108414147631234339812568238948528890889361349316711608560 := by
  rw [PackedColumns.col]
  simp only [show 2 < 8 by decide, ↓reduceIte]
  simp only [col_8_2]
  decide
lemma col_9_3 : PackedColumns.col 9 3 = 13355637471071225126423931515722554897411352724014212858744092333045803858750303603351283347590378511628981150567083381395178964979993470452478654262869760 := by
  rw [PackedColumns.col]
  simp only [show 3 < 8 by decide, ↓reduceIte]
  simp only [col_8_3]
  decide
lemma col_9_4 : PackedColumns.col 9 4 = 13407603346151304507647333602124270744930157291580986197148043437687863763597662002711256755796972443613438635551055889478487182262900810351549134401372160 := by
  rw [PackedColumns.col]
  simp only [show 4 < 8 by decide, ↓reduceIte]
  simp only [col_8_4]
  decide
lemma col_9_5 : PackedColumns.col 9 5 = 13407807926820848549984871490950625460264621687587329935306297008442977448960781863686381587396241115434734742314166555940848600484775015044616064818216960 := by
  rw [PackedColumns.col]
  simp only [show 5 < 8 by decide, ↓reduceIte]
  simp only [col_8_5]
  decide
lemma col_9_6 : PackedColumns.col 9 6 = 13407807929942597098847186273910239236969444018900783322580063136098668673514857287274768220802268387129003177701362428774192761570871467260109520434626560 := by
  rw [PackedColumns.col]
  simp only [show 6 < 8 by decide, ↓reduceIte]
  simp only [col_8_6]
  decide
lemma col_9_7 : PackedColumns.col 9 7 = 13407807929942597099574024998205846127439963814395998898511282403621620416268583029620646167694378705270794824322841769944638336182637648515027502377205760 := by
  rw [PackedColumns.col]
  simp only [show 7 < 8 by decide, ↓reduceIte]
  simp only [col_8_7]
  decide
lemma col_9_8 : PackedColumns.col 9 8 = 13407807929942597099574024998205846127479365820592393377723561443721764030073431184712636981971479856705023170278632780869088242247907112362425735876444160 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_8]
  decide
lemma col_10_0 : PackedColumns.col 10 0 = 119846208990821060515287012719268315574531798596153771515620054105155117203667308755138984881605024014080075919914262238439193179209611081661898287092982749585178595616576990184201479734164062746302055301390003845892100454894975254315942073693884824775567007123057532159964830625653144203223570886416149424810 := by
  rw [PackedColumns.col]
  simp only [show 0 < 9 by decide, ↓reduceIte]
  simp only [col_9_0]
  decide
lemma col_10_1 : PackedColumns.col 10 1 = 143815450788985272618344415263121978689438158315384525818744064926186140644400770506166781857926028816896091103897114686127031815051533297994277944511579299502214314739892388221041775680996875295562466361668004615070520545873970305179130488432661789730680408547669038591957796750783773043868285063699379309772 := by
  rw [PackedColumns.col]
  simp only [show 1 < 9 by decide, ↓reduceIte]
  simp only [col_9_1]
  decide
lemma col_10_2 : PackedColumns.col 10 2 = 169194647987041497198052253250731739634633127429864148022051841089630753699295024124902096303442386843407166004584840807208272723590039174110915228837152117061428605576343986142402089036466912112426431013727064253024141818675259182563682927567837399683153421820787104225832702059745615345727394192587505070320 := by
  rw [PackedColumns.col]
  simp only [show 2 < 9 by decide, ↓reduceIte]
  simp only [col_9_2]
  decide
lemma col_10_3 : PackedColumns.col 10 3 = 179069821994067265517004719393770557123035839147560499073922571114317373565012632536861362624654977515201358572945823733699027940920197102560968646862666832065013932750060561209079253766221790251284004808302573839776523636885877422791135238515376547524582609864801915756523326693582908070186191519003118206720 := by
  rw [PackedColumns.col]
  simp only [show 3 < 9 by decide, ↓reduceIte]
  simp only [col_9_3]
  decide
lemma col_10_4 : PackedColumns.col 10 4 = 179766570466052360237648572536963127610949142151705149077185617265867657072940646045213890928808158455225716514812268414598264282604049739409665520460023745597470080465874001603182053859457467143941243028332742390810947146161643764595180884270010128854499581430719252352917935056902309958553029775825154539520 := by
  rw [PackedColumns.col]
  simp only [show 4 < 9 by decide, ↓reduceIte]
  simp only [col_9_4]
  decide
lemma col_10_5 : PackedColumns.col 10 5 = 179769313444375785814462265863485611229889718115776549548420631039577310219318555512504201030636628662239812719543346771400604958784932998973090366819193438631844709885019339289485527600645229101680144570744617427323613239093066544488844122372018577072445227788470567772585250041087614243742592599359351685120 := by
  rw [PackedColumns.col]
  simp only [show 5 < 9 by decide, ↓reduceIte]
  simp only [col_9_5]
  decide
lemma col_10_6 : PackedColumns.col 10 6 = 179769313486231590763185205067502474281972610037491134208877555181135709923949037735690276024213413705823039792595812100825199281213020878487102478859428781160318831728534053767098825058678708531551206723464342007537350133167915838047987720003371153224504147359993809275143228500884134199151686065190149816320 := by
  rw [PackedColumns.col]
  simp only [show 6 < 9 by decide, ↓reduceIte]
  simp only [col_9_6]
  decide
lemma col_10_7 : PackedColumns.col 10 7 = 179769313486231590772930519078902473361269403363094992027077741372816159198983668324764656509214724291581902479869920821760871587342679845464593386307578492764517105656857966598509267284159204378328176331317696638943488431251920295735812264550083217605459765810970935573515804682568218669795142748890432798720 := by
  rw [PackedColumns.col]
  simp only [show 7 < 9 by decide, ↓reduceIte]
  simp only [col_9_7]
  decide
lemma col_10_8 : PackedColumns.col 10 8 = 179769313486231590772930519078902473361797697894230657273430081157732675805499410614616176613472387041631651377316136471641673072203277570454821379686787760899244944958633938372376730076395090525612731964434268678008150116831451773765893368201788358737656950422124978427902852027528247743196825908506284523520 := by
  rw [PackedColumns.col]
  simp only [show 8 < 9 by decide, ↓reduceIte]
  simp only [col_9_8]
  decide
lemma col_10_9 : PackedColumns.col 10 9 = 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474110969959963482268385702277221395399966640087262359691628045276706960578432807926936308666529070259922820652728111753896392184596904358265409895975218053120 := by
  rw [PackedColumns.col]
  simp only [Nat.lt_irrefl, ↓reduceIte]
  rw [power_9]
  decide
end Q3PackedColumnCache
namespace PackedLineArithmetic
open PackedLineColumns
lemma complement_bit {k a b : Nat} (h : a + b + 1 = 2 ^ k) (r : Nat) :
    a.testBit r = (decide (r < k) && !b.testBit r) := by
  have ha : a = 2 ^ k - (b + 1) := by omega
  rw [ha]
  exact Nat.testBit_two_pow_sub_succ (by omega) r
lemma line_bits {n m : Nat} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (cols : Fin n → Nat) (r : Fin (2 ^ n)) (l : Fin m) (a : Nat)
    (hcomp : a + joinWords (List.ofFn (fun p => if I p l then cols p else 0)) + 1 =
      2 ^ (2 ^ n))
    (hc : ∀ p : Fin n, (cols p).testBit r.val = r.val.testBit p.val) :
    a.testBit r.val = decide (∀ p : Fin n, I p l → r.val.testBit p.val = false) := by
  rw [complement_bit hcomp]
  have hnot (b : Bool) : (!b) = true ↔ b = false := by cases b <;> decide
  apply Bool.eq_iff_iff.mpr
  simp only [r.isLt, decide_true, Bool.true_and, joinWords_bit, hnot,
    decide_eq_true_eq, List.any_eq_false, List.forall_mem_ofFn_iff]
  constructor
  · intro h p hp
    simpa [hp, hc] using h p
  · intro h p
    by_cases hp : I p l
    · simp [hp, hc, h p hp]
    · simp [hp]
end PackedLineArithmetic
namespace Q3PackedCertificate
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open ReducedCheck CircuitCheckWrapper
abbrev I (p l : Fin 13) : Prop := (([1170,113,2584,4372,15,4674,2338,7169,1352,1572,897,2244,4264] : List Nat).getD p.val 0).testBit l.val = true
def pairWords : List Nat := [
  8191,
  67100672,
  549688705024,
  4503049871556608,
  36888984547791732736,
  302194561415509874573312,
  2475577847115856892504571904,
  20279933723573099663397453037568,
  166133217063510832442551935283757056,
  1360963314184280739369385453844537802752,
  11149011469797627816914005637894453680144384,
  91332701960582167076159534185631364547742793728,
  748197494461089112687898904048692138375108966219776,
  91355004067076339167413824240109498970069278721,
  182710008134152678334827648480218997940138557442,
  365420016268305356669655296960437995880277114884,
  730840032536610713339310593920875991760554229768,
  1461680065073221426678621187841751983521108459536,
  2923360130146442853357242375683503967042216919072,
  5846720260292885706714484751367007934084433838144,
  11693440520585771413428969502734015868168867676288,
  23386881041171542826857939005468031736337735352576,
  46773762082343085653715878010936063472675470705152,
  93547524164686171307431756021872126945350941410304,
  187095048329372342614863512043744253890701882820608,
  374190096658744685229727024087488507781403765641216
]
def incidenceMask : Nat := 389515209005992732313513829080319019620122288333970
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma pair_rows : ∀ p l : Fin 13,
    pairWords.map (fun a => a.testBit (p.val * 13 + l.val)) =
      List.ofFn (liftInput (edgeInput p l)) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma mask_true : ∀ p l : Fin 13, I p l → incidenceMask.testBit (p.val * 13 + l.val) = true := by
  decide +kernel
lemma positive_of_packed (C : Circuit) (hAO : IsAO2 26 C)
    (hpos : PackedEval.eval C pairWords = incidenceMask) :
    ∀ p l : Fin 13, I p l → circuitFun 26 C (liftInput (edgeInput p l)) = true := by
  intro p l hI
  have h := PackedEval.eval_testBit_of_isAO2 26 C pairWords (p.val * 13 + l.val) hAO
  rw [hpos, pair_rows p l] at h
  simpa [circuitFun] using h.symm.trans (mask_true p l hI)
def canonicalC : Circuit := ⟨[
  { op := GateOp.or, inputs := [1, 4] },
  { op := GateOp.or, inputs := [26, 7] },
  { op := GateOp.or, inputs := [27, 10] },
  { op := GateOp.and, inputs := [28, 13] },
  { op := GateOp.or, inputs := [0, 4] },
  { op := GateOp.or, inputs := [30, 5] },
  { op := GateOp.or, inputs := [31, 6] },
  { op := GateOp.and, inputs := [32, 14] },
  { op := GateOp.or, inputs := [3, 4] },
  { op := GateOp.or, inputs := [34, 9] },
  { op := GateOp.or, inputs := [35, 11] },
  { op := GateOp.and, inputs := [36, 15] },
  { op := GateOp.or, inputs := [2, 4] },
  { op := GateOp.or, inputs := [38, 8] },
  { op := GateOp.or, inputs := [39, 12] },
  { op := GateOp.and, inputs := [40, 16] },
  { op := GateOp.or, inputs := [0, 1] },
  { op := GateOp.or, inputs := [42, 2] },
  { op := GateOp.or, inputs := [43, 3] },
  { op := GateOp.and, inputs := [44, 17] },
  { op := GateOp.or, inputs := [1, 6] },
  { op := GateOp.or, inputs := [46, 9] },
  { op := GateOp.or, inputs := [47, 12] },
  { op := GateOp.and, inputs := [48, 18] },
  { op := GateOp.or, inputs := [1, 5] },
  { op := GateOp.or, inputs := [50, 8] },
  { op := GateOp.or, inputs := [51, 11] },
  { op := GateOp.and, inputs := [52, 19] },
  { op := GateOp.or, inputs := [0, 10] },
  { op := GateOp.or, inputs := [54, 11] },
  { op := GateOp.or, inputs := [55, 12] },
  { op := GateOp.and, inputs := [56, 20] },
  { op := GateOp.or, inputs := [3, 6] },
  { op := GateOp.or, inputs := [58, 8] },
  { op := GateOp.or, inputs := [59, 10] },
  { op := GateOp.and, inputs := [60, 21] },
  { op := GateOp.or, inputs := [2, 5] },
  { op := GateOp.or, inputs := [62, 9] },
  { op := GateOp.or, inputs := [63, 10] },
  { op := GateOp.and, inputs := [64, 22] },
  { op := GateOp.or, inputs := [0, 7] },
  { op := GateOp.or, inputs := [66, 8] },
  { op := GateOp.or, inputs := [67, 9] },
  { op := GateOp.and, inputs := [68, 23] },
  { op := GateOp.or, inputs := [2, 6] },
  { op := GateOp.or, inputs := [70, 7] },
  { op := GateOp.or, inputs := [71, 11] },
  { op := GateOp.and, inputs := [72, 24] },
  { op := GateOp.or, inputs := [3, 5] },
  { op := GateOp.or, inputs := [74, 7] },
  { op := GateOp.or, inputs := [75, 12] },
  { op := GateOp.and, inputs := [76, 25] },
  { op := GateOp.or, inputs := [29, 33] },
  { op := GateOp.or, inputs := [78, 37] },
  { op := GateOp.or, inputs := [79, 41] },
  { op := GateOp.or, inputs := [80, 45] },
  { op := GateOp.or, inputs := [81, 49] },
  { op := GateOp.or, inputs := [82, 53] },
  { op := GateOp.or, inputs := [83, 57] },
  { op := GateOp.or, inputs := [84, 61] },
  { op := GateOp.or, inputs := [85, 65] },
  { op := GateOp.or, inputs := [86, 69] },
  { op := GateOp.or, inputs := [87, 73] },
  { op := GateOp.or, inputs := [88, 77] }
], 89⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma plane_geometry :
    (∀ l : Fin 13, (Finset.univ.filter (fun p => I p l)).card = 4) ∧
    (∀ p p' : Fin 13, p ≠ p' → ∃! l : Fin 13, I p l ∧ I p' l) := by
  unfold I ExistsUnique
  decide +kernel
end Q3PackedCertificate
namespace ChunkedBoundary
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open PEqualNP.Outside.L_meta_2583.RefutationBridge.ReducedCheck
open PEqualNP.Outside.L_meta_2583.RefutationBridge.CircuitCheckWrapper
def lowCode {a b : ℕ} (P : Finset (Fin (a + b))) : Fin (2 ^ a) :=
  PackedInputCode.code (fun p : Fin a => decide (Fin.castAdd b p ∈ P))
def highCode {a b : ℕ} (P : Finset (Fin (a + b))) : Fin (2 ^ b) :=
  PackedInputCode.code (fun p : Fin b => decide (Fin.natAdd a p ∈ P))
lemma input_bits {a b m : ℕ} (I : Fin (a + b) → Fin m → Prop) [DecidableRel I]
    (w : Fin (2 ^ b) → List ℕ) (hlen : ∀ h, (w h).length = a + b + m)
    (hlow : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (p : Fin a),
      ((w h).getD p.val 0).testBit r.val = r.val.testBit p.val)
    (hhigh : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (p : Fin b),
      ((w h).getD (a + p.val) 0).testBit r.val = h.val.testBit p.val)
    (hline : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (l : Fin m),
      ((w h).getD (a + b + l.val) 0).testBit r.val = decide
        ((∀ p : Fin a, I (Fin.castAdd b p) l → r.val.testBit p.val = false) ∧
          (∀ p : Fin b, I (Fin.natAdd a p) l → h.val.testBit p.val = false)))
    (P : Finset (Fin (a + b))) :
    (w (highCode P)).map (fun v => v.testBit (lowCode P).val) =
      List.ofFn (liftInput (independentInput I P)) := by
  let high := highCode P
  let low := lowCode P
  have hwire : ∀ i : Fin (a + b + m), ((w high).getD i.val 0).testBit low.val =
      liftInput (independentInput I P) i := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro p
      refine Fin.addCases ?_ ?_ p
      · intro p
        simpa [low, lowCode, liftInput, independentInput] using
          (hlow high low p).trans
            (PackedInputCode.code_bit (fun p : Fin a => decide (Fin.castAdd b p ∈ P)) p)
      · intro p
        simpa [high, highCode, liftInput, independentInput] using
          (hhigh high low p).trans
            (PackedInputCode.code_bit (fun p : Fin b => decide (Fin.natAdd a p ∈ P)) p)
    · intro l
      have hwline : ((w high).getD (a + b + l.val) 0).testBit low.val =
          decide (l ∈ avoidingRight I P) := by
        rw [hline high low l]
        congr 1
        apply propext
        rw [mem_avoidingRight]
        constructor
        · intro h p
          refine Fin.addCases ?_ ?_ p
          · intro p hp hI
            have hf := h.1 p hI
            simp [low, lowCode, PackedInputCode.code_bit, hp] at hf
          · intro p hp hI
            have hf := h.2 p hI
            simp [high, highCode, PackedInputCode.code_bit, hp] at hf
        · intro h
          constructor
          · intro p hI
            have hp : Fin.castAdd b p ∉ P := fun hp => h _ hp hI
            simp [low, lowCode, PackedInputCode.code_bit, hp]
          · intro p hI
            have hp : Fin.natAdd a p ∉ P := fun hp => h _ hp hI
            simp [high, highCode, PackedInputCode.code_bit, hp]
      simpa [liftInput, independentInput] using hwline
  apply List.ext_getElem
  · simpa using hlen high
  · intro i hi hj
    have hwi : i < (w high).length := by simpa using hi
    have hib : i < a + b + m := by simpa [hlen high] using hwi
    simpa [List.getD_eq_getElem?_getD, hwi] using hwire ⟨i, hib⟩
lemma independent_false_of_chunks {a b m : ℕ} (I : Fin (a + b) → Fin m → Prop)
    [DecidableRel I] (C : Circuit) (hAO : IsAO2 (a + b + m) C)
    (w : Fin (2 ^ b) → List ℕ) (hlen : ∀ h, (w h).length = a + b + m)
    (hlow : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (p : Fin a),
      ((w h).getD p.val 0).testBit r.val = r.val.testBit p.val)
    (hhigh : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (p : Fin b),
      ((w h).getD (a + p.val) 0).testBit r.val = h.val.testBit p.val)
    (hline : ∀ (h : Fin (2 ^ b)) (r : Fin (2 ^ a)) (l : Fin m),
      ((w h).getD (a + b + l.val) 0).testBit r.val = decide
        ((∀ p : Fin a, I (Fin.castAdd b p) l → r.val.testBit p.val = false) ∧
          (∀ p : Fin b, I (Fin.natAdd a p) l → h.val.testBit p.val = false)))
    (hzero : ∀ h, PackedEval.eval C (w h) = 0) :
    ∀ P : Finset (Fin (a + b)),
      circuitFun (a + b + m) C (liftInput (independentInput I P)) = false := by
  intro P
  have h := PackedEval.eval_testBit_of_isAO2 (a + b + m) C (w (highCode P))
    (lowCode P).val hAO
  rw [hzero, input_bits I w hlen hlow hhigh hline P] at h
  simpa [circuitFun] using h.symm
end ChunkedBoundary
namespace Q3ChunkedCertificate
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open ReducedCheck CircuitCheckWrapper
open Q3PackedCertificate (I pairWords incidenceMask canonicalC)
def lowPointWords : List Nat := [
  119846208990821060515287012719268315574531798596153771515620054105155117203667308755138984881605024014080075919914262238439193179209611081661898287092982749585178595616576990184201479734164062746302055301390003845892100454894975254315942073693884824775567007123057532159964830625653144203223570886416149424810,
  143815450788985272618344415263121978689438158315384525818744064926186140644400770506166781857926028816896091103897114686127031815051533297994277944511579299502214314739892388221041775680996875295562466361668004615070520545873970305179130488432661789730680408547669038591957796750783773043868285063699379309772,
  169194647987041497198052253250731739634633127429864148022051841089630753699295024124902096303442386843407166004584840807208272723590039174110915228837152117061428605576343986142402089036466912112426431013727064253024141818675259182563682927567837399683153421820787104225832702059745615345727394192587505070320,
  179069821994067265517004719393770557123035839147560499073922571114317373565012632536861362624654977515201358572945823733699027940920197102560968646862666832065013932750060561209079253766221790251284004808302573839776523636885877422791135238515376547524582609864801915756523326693582908070186191519003118206720,
  179766570466052360237648572536963127610949142151705149077185617265867657072940646045213890928808158455225716514812268414598264282604049739409665520460023745597470080465874001603182053859457467143941243028332742390810947146161643764595180884270010128854499581430719252352917935056902309958553029775825154539520,
  179769313444375785814462265863485611229889718115776549548420631039577310219318555512504201030636628662239812719543346771400604958784932998973090366819193438631844709885019339289485527600645229101680144570744617427323613239093066544488844122372018577072445227788470567772585250041087614243742592599359351685120,
  179769313486231590763185205067502474281972610037491134208877555181135709923949037735690276024213413705823039792595812100825199281213020878487102478859428781160318831728534053767098825058678708531551206723464342007537350133167915838047987720003371153224504147359993809275143228500884134199151686065190149816320,
  179769313486231590772930519078902473361269403363094992027077741372816159198983668324764656509214724291581902479869920821760871587342679845464593386307578492764517105656857966598509267284159204378328176331317696638943488431251920295735812264550083217605459765810970935573515804682568218669795142748890432798720,
  179769313486231590772930519078902473361797697894230657273430081157732675805499410614616176613472387041631651377316136471641673072203277570454821379686787760899244944958633938372376730076395090525612731964434268678008150116831451773765893368201788358737656950422124978427902852027528247743196825908506284523520,
  179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474110969959963482268385702277221395399966640087262359691628045276706960578432807926936308666529070259922820652728111753896392184596904358265409895975218053120
]
def lowLineWords : List Nat := [
  1612202362438516399445625478482434675121823726883503404772301843350203396559111756406055148913550443347281823494806389103104468523147286808346284746286493861864005434387625707294085024003364773297834340878416831890049116906832362379820380108676007858279181472248627,
  11540594032658607306566862601501305269438134594985383637573631145613154769671340896777851149190755077723567764553128464542387995665915090527196023934338072556743923144455916925710573989989925907747028471236585529682186524614830995187538005219136435186722779142022605140153685,
  796045880515921893740840784340009919099334674736111188786015696109986287490171558823122061988264889467792355759382783138912642201399201885270835455,
  1393481448109428024177612725692000257830902900038233105088416187017886575689496888172687782322825188039705927097314219305260869837098837594210872808275440014594128991381499292894772743965303669543108482905900987801709156765455,
  2743103890840491199709018373066338191222975477137875292186313895746283296032669003322018422559052964387275713433606368469654227036154980125014838340420754167662590881587937518521434647154132816349326054048752662986772727280727288952070086374316429955952552234448558758525173509399247979016332590671003649,
  145367744859121378101984360338322011028699661524619071311737937905421215472927008112205736097024724415912224248215020537264825714291507,
  72294757326097933040861497784880691502824544888109615384531391835929546202845673426460479344206140712111202128718028925208414114298998390254824122401745389029896603612666735780901582145914989584815640143462939230781780787,
  59923104495410530257643506359634157787265899298076885757810027052577558601833654377569492440802512007040037959957131119219596589604805540830949143546491374792589297808288495092100739867082031373151027650695001922946050227447487627157971036846942412387783503561528766079982415312826572101611785443208074712405,
  327479277917408467359118278243034488056076247630130719693098679591209568603539525136273912089569344449019920319495285561697522348095392811331331240221415944707369595257330459289632194594578979695157867955814655,
  183632267622891382779718862777337890176768437789250849134046269477221477242087806515921312485605712698371734994876781313363032641283387305168655,
  113427455640312821154458202477256070485,
  1684641406969115364874486225963184091504279981394597057304974334423198082012594085395335671627782269635974753234311105849883066826689934540267397107598739745340130446522310749429691706754229252102351376690654656563612029603792517803755816029321629455,
  478611500756798850801714011323471660170568768659788346620398081151254972618377633362909867462188365193808315833746849196845099826791196907804893604951762174510088758215373707240627875944495525099088412524971307892190284093278822273880968004004958098409062655
]
def allOnes : Nat := 179769313486231590772930519078902473361797697894230657273430081157732675805500963132708477322407536021120113879871393357658789768814416622492847430639474124377767893424865485276302219601246094119453082952085005768838150682342462881473913110540827237163350510684586298239947245938479716304835356329624224137215
lemma lowPointWords_spec (p : Fin 10) :
    lowPointWords.getD p.val 0 = PackedColumns.col 10 p.val := by
  fin_cases p
  · exact Q3PackedColumnCache.col_10_0.symm
  · exact Q3PackedColumnCache.col_10_1.symm
  · exact Q3PackedColumnCache.col_10_2.symm
  · exact Q3PackedColumnCache.col_10_3.symm
  · exact Q3PackedColumnCache.col_10_4.symm
  · exact Q3PackedColumnCache.col_10_5.symm
  · exact Q3PackedColumnCache.col_10_6.symm
  · exact Q3PackedColumnCache.col_10_7.symm
  · exact Q3PackedColumnCache.col_10_8.symm
  · exact Q3PackedColumnCache.col_10_9.symm
lemma low_point_bits (r : Fin 1024) (p : Fin 10) :
    (lowPointWords.getD p.val 0).testBit r.val = r.val.testBit p.val := by
  rw [lowPointWords_spec]
  exact PackedColumns.col_testBit_lt 10 p.val r.val p.isLt r.isLt
lemma allOnes_spec : allOnes = 2 ^ (2 ^ 10) - 1 := by
  rw [Q3PackedColumnCache.power_10]
  rfl
lemma allOnes_bits (r : Fin 1024) : allOnes.testBit r.val = true := by
  rw [allOnes_spec, Nat.testBit_two_pow_sub_one]
  simp [r.isLt]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma low_line_complement : ∀ l : Fin 13,
    lowLineWords.getD l.val 0 + PackedLineColumns.joinWords
      (List.ofFn (fun p : Fin 10 => if I (Fin.castAdd 3 p) l
        then lowPointWords.getD p.val 0 else 0)) + 1 = 2 ^ (2 ^ 10) := by
  rw [Q3PackedColumnCache.power_10]
  decide +kernel
lemma low_line_bits (r : Fin 1024) (l : Fin 13) :
    (lowLineWords.getD l.val 0).testBit r.val =
      decide (∀ p : Fin 10, I (Fin.castAdd 3 p) l → r.val.testBit p.val = false) := by
  exact PackedLineArithmetic.line_bits (fun p : Fin 10 => I (Fin.castAdd 3 p))
    (fun p => lowPointWords.getD p.val 0) r l _ (low_line_complement l) (low_point_bits r)
def data (h : Fin 8) (i : Fin 26) : Nat :=
  Fin.addCases (motive := fun _ => Nat)
    (fun p : Fin 13 => Fin.addCases (motive := fun _ => Nat)
      (fun p : Fin 10 => lowPointWords.getD p.val 0)
      (fun p : Fin 3 => if h.val.testBit p.val then allOnes else 0) p)
    (fun l : Fin 13 => if ∀ p : Fin 3,
        I (Fin.natAdd 10 p) l → h.val.testBit p.val = false
      then lowLineWords.getD l.val 0 else 0) i
def words (h : Fin 8) : List Nat := List.ofFn (data h)
lemma words_length (h : Fin 8) : (words h).length = 26 := by simp [words]
lemma words_getD (h : Fin 8) (i : Fin 26) : (words h).getD i.val 0 = data h i := by
  simp only [words, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    i.isLt, dite_eq_left, Option.getD_some]
lemma low_lookup (h : Fin 8) (p : Fin 10) :
    (words h).getD p.val 0 = lowPointWords.getD p.val 0 := by
  simpa [data] using words_getD h (Fin.castAdd 13 (Fin.castAdd 3 p))
lemma high_lookup (h : Fin 8) (p : Fin 3) :
    (words h).getD (10 + p.val) 0 = if h.val.testBit p.val then allOnes else 0 := by
  simpa [data] using words_getD h (Fin.castAdd 13 (Fin.natAdd 10 p))
lemma line_lookup (h : Fin 8) (l : Fin 13) :
    (words h).getD (13 + l.val) 0 = if ∀ p : Fin 3,
        I (Fin.natAdd 10 p) l → h.val.testBit p.val = false
      then lowLineWords.getD l.val 0 else 0 := by
  have hw := words_getD h (Fin.natAdd 13 l)
  simp only [data, Fin.addCases_right] at hw
  exact hw
lemma low_bits (h : Fin 8) (r : Fin 1024) (p : Fin 10) :
    ((words h).getD p.val 0).testBit r.val = r.val.testBit p.val := by
  rw [low_lookup]
  exact low_point_bits r p
lemma high_bits (h : Fin 8) (r : Fin 1024) (p : Fin 3) :
    ((words h).getD (10 + p.val) 0).testBit r.val = h.val.testBit p.val := by
  rw [high_lookup]
  cases h.val.testBit p.val <;> simp [allOnes_bits r]
lemma line_bits (h : Fin 8) (r : Fin 1024) (l : Fin 13) :
    ((words h).getD (13 + l.val) 0).testBit r.val = decide
      ((∀ p : Fin 10, I (Fin.castAdd 3 p) l → r.val.testBit p.val = false) ∧
        (∀ p : Fin 3, I (Fin.natAdd 10 p) l → h.val.testBit p.val = false)) := by
  rw [line_lookup]
  split
  · rename_i hh
    rw [low_line_bits r l]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (and_iff_left hh).symm
  · rename_i hh
    simp [hh]
lemma negative_of_chunks (C : Circuit) (hAO : IsAO2 26 C)
    (hneg : ∀ h : Fin 8, PackedEval.eval C (words h) = 0) :
    ∀ P : Finset (Fin 13), circuitFun 26 C (liftInput (independentInput I P)) = false := by
  exact ChunkedBoundary.independent_false_of_chunks (a := 10) (b := 3)
    I C hAO words words_length low_bits high_bits line_bits hneg
lemma exact_of_chunks (C : Circuit) (hAO : IsAO2 26 C)
    (hpos : PackedEval.eval C pairWords = incidenceMask)
    (hneg : ∀ h : Fin 8, PackedEval.eval C (words h) = 0) :
    ∀ z : Fin 26 → Bool, circuitFun 26 C z = decide (∃ p l : Fin 13,
      I p l ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true) := by
  exact ao2_exact_certificate I C hAO (Q3PackedCertificate.positive_of_packed C hAO hpos)
    (fun P _ => negative_of_chunks C hAO hneg P)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma canonical_checks : IsAO2 26 canonicalC ∧ canonicalC.size = 64 ∧
    PackedEval.eval canonicalC pairWords = incidenceMask ∧
    (∀ h : Fin 8, PackedEval.eval canonicalC (words h) = 0) := by decide +kernel
lemma canonical_exact : ∀ z : Fin 26 → Bool, circuitFun 26 canonicalC z =
    decide (∃ p l : Fin 13, I p l ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true) :=
  exact_of_chunks canonicalC canonical_checks.1 canonical_checks.2.2.1 canonical_checks.2.2.2
end Q3ChunkedCertificate
end PEqualNP.Outside.L_meta_2583.RefutationBridge

namespace PEqualNP.Outside.L_meta_2583.RefutationBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
open Q3PackedCertificate (I pairWords incidenceMask)
open Q3ChunkedCertificate (words)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma q3_columns : ∀ l : Fin 13, (Finset.univ.filter (fun p => I p l)).card = 3+1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma q3_unique : ∀ p p' : Fin 13, p ≠ p' → ∃! l : Fin 13, I p l ∧ I p' l := by
  unfold ExistsUnique
  decide +kernel

lemma refute_of_chunks (C : Circuit) (hAO : IsAO2 26 C) (hsize : C.size ≤ 63)
    (hpos : PackedEval.eval C pairWords = incidenceMask)
    (hneg : ∀ h : Fin 8, PackedEval.eval C (words h) = 0) :
    ¬ (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1) := by
  intro hgap
  have hfun := Q3ChunkedCertificate.exact_of_chunks C hAO hpos hneg
  obtain ⟨D,hD,hDf,hDC,hread⟩ := hgap 3 13 I C (by decide) (by decide)
    q3_columns q3_unique hAO hfun
  have hlower := ReadLower.plane_read_one_lower I D
    (by decide : 2 ≤ 3) (by decide : 13 = 3^2+3+1)
    q3_columns q3_unique hD hDf hread
  norm_num at hlower
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma refute_of_eight_chunks (C : Circuit) (hAO : IsAO2 26 C) (hsize : C.size ≤ 63)
    (hpos : PackedEval.eval C pairWords = incidenceMask)
    (hneg0 : PackedEval.eval C (words 0) = 0)
    (hneg1 : PackedEval.eval C (words 1) = 0)
    (hneg2 : PackedEval.eval C (words 2) = 0)
    (hneg3 : PackedEval.eval C (words 3) = 0)
    (hneg4 : PackedEval.eval C (words 4) = 0)
    (hneg5 : PackedEval.eval C (words 5) = 0)
    (hneg6 : PackedEval.eval C (words 6) = 0)
    (hneg7 : PackedEval.eval C (words 7) = 0)
    : ¬ (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1) := by
  apply refute_of_chunks C hAO hsize hpos
  intro h
  fin_cases h <;> assumption

end PEqualNP.Outside.L_meta_2583.RefutationBridge
