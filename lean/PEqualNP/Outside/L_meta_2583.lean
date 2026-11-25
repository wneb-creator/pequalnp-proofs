import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

lemma plane_point_degree (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ pa pb : Fin N, pa ≠ pb → ∃! lb : Fin N, I pa lb ∧ I pb lb) (p : Fin N) :
    (Finset.univ.filter (fun l => I p l)).card = q + 1 := by
  have : Nonempty (Fin N) := ⟨p⟩
  choose! f hf using fun (p' : Fin N) (h : p' ≠ p) => (hu p' p h).exists
  have hfu : ∀ p' l, p' ≠ p → I p' l → I p l → f p' = l := by
    intro p' l h h1 h2
    exact (hu p' p h).unique (hf p' h) ⟨h1, h2⟩
  have hcount := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.erase p)
    (t := Finset.univ.filter (fun l => I p l)) (f := f) (fun p' hp' => by
      have hne := Finset.ne_of_mem_erase hp'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hf p' hne).2⟩)
  have hfib : ∀ l ∈ Finset.univ.filter (fun l => I p l),
      ((Finset.univ.erase p).filter (fun p' => f p' = l)).card = q := by
    intro l hl'
    have hpl : I p l := (Finset.mem_filter.mp hl').2
    have e : (Finset.univ.erase p).filter (fun p' => f p' = l)
        = (Finset.univ.filter (fun p' => I p' l)).erase p := by
      ext p'
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      constructor
      · rintro ⟨hne, hfl⟩
        exact ⟨hne, hfl ▸ (hf p' hne).1⟩
      · rintro ⟨hne, hI⟩
        exact ⟨hne, hfu p' l hne hI hpl⟩
    rw [e, Finset.card_erase_of_mem (show p ∈ Finset.univ.filter (fun p' => I p' l) from
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩), hl l]
    rfl
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, Nat.nsmul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at hcount
  subst hN
  have h2 : q ^ 2 + q + 1 - 1 = (q + 1) * q := by
    rw [Nat.add_sub_cancel]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) (hcount.symm.trans h2)

lemma incidence_card_left {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ p ∈ A, (B.filter (fun w => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Finset.card_filter]

lemma incidence_card_right {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (A B : Finset (Fin N)) :
    ((A ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)).card
      = ∑ w ∈ B, (A.filter (fun p => I p w)).card := by
  rw [Finset.card_filter, Finset.sum_product_right]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [Finset.card_filter]

lemma regular_cover_card {N : ℕ} (q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hpt : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1)
    (A B : Finset (Fin N)) (hc : ∀ p w : Fin N, I p w → p ∈ A ∨ w ∈ B) :
    N ≤ A.card + B.card := by
  have hE : (((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = N * (q + 1) := by
    rw [incidence_card_right, Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, Nat.nsmul_eq_mul]
  have hA : ((A ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = A.card * (q + 1) := by
    rw [incidence_card_left, Finset.sum_congr rfl (fun p _ => hpt p), Finset.sum_const, Nat.nsmul_eq_mul]
  have hB : (((Finset.univ : Finset (Fin N)) ×ˢ B).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)).card = B.card * (q + 1) := by
    rw [incidence_card_right, Finset.sum_congr rfl (fun w _ => hl w), Finset.sum_const, Nat.nsmul_eq_mul]
  have hsub : ((Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ : Finset (Fin N))).filter
      (fun pw : Fin N × Fin N => I pw.1 pw.2)
      ⊆ ((A ×ˢ (Finset.univ : Finset (Fin N))).filter (fun pw : Fin N × Fin N => I pw.1 pw.2))
        ∪ (((Finset.univ : Finset (Fin N)) ×ˢ B).filter (fun pw : Fin N × Fin N => I pw.1 pw.2)) := by
    rintro ⟨p, w⟩ h
    have hI : I p w := (Finset.mem_filter.mp h).2
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_product,
      Finset.mem_product]
    rcases hc p w hI with h1 | h1
    · exact Or.inl ⟨⟨h1, Finset.mem_univ _⟩, hI⟩
    · exact Or.inr ⟨⟨Finset.mem_univ _, h1⟩, hI⟩
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [hE, hA, hB, ← Nat.add_mul] at h
  exact Nat.le_of_mul_le_mul_right h (Nat.succ_pos q)

lemma plane_cover_card (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (hcover : ∀ p l : Fin N, I p l → p ∈ A ∨ l ∈ B) :
    N ≤ A.card + B.card := by
  exact regular_cover_card q I hL (plane_point_degree q N I hq hN hL hU) A B hcover

lemma regular_incidence_matching (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hL : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hP : ∀ p : Fin N, (Finset.univ.filter (fun l => I p l)).card = q + 1) :
    ∃ f : Fin N → Fin N, Function.Injective f ∧ ∀ p, I p (f p) := by
  classical
  let adj (p : Fin N) : Finset (Fin N) := Finset.univ.filter fun l => I p l
  have hall (S : Finset (Fin N)) : S.card ≤ (S.biUnion adj).card := by
    have hcover : ∀ p l : Fin N, I p l → p ∈ Finset.univ \ S ∨ l ∈ S.biUnion adj := by
      intro p l hpl
      by_cases hp : p ∈ S
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩⟩)
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hp⟩)
    have h := regular_cover_card q I hL hP (Finset.univ \ S) (S.biUnion adj) hcover
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  obtain ⟨f, hf, ha⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' adj).mp hall
  exact ⟨f, hf, fun p => (Finset.mem_filter.mp (ha p)).2⟩

lemma plane_incidence_matching (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∃ f : Fin N → Fin N, Function.Injective f ∧ ∀ p, I p (f p) := by
  exact regular_incidence_matching q N I hL (plane_point_degree q N I hq hN hL hU)

lemma plane_incidence_perm (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∃ σ : Equiv.Perm (Fin N), ∀ p, I p (σ p) := by
  classical
  obtain ⟨f, hf, hi⟩ := plane_incidence_matching q N I hq hN hL hU
  exact ⟨Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, rfl⟩), hi⟩

lemma plane_no_rectangle (N : ℕ) (I : Fin N → Fin N → Prop)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬(I p l ∧ I p l' ∧ I p' l ∧ I p' l') := by
  rintro p p' l l' hp hl ⟨hpl, hpl', hp'l, hp'l'⟩
  exact hl ((hU p p' hp).unique ⟨hpl, hp'l⟩ ⟨hpl', hp'l'⟩)

lemma plane_matching_edges (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∃ M : Finset (Fin N × Fin N),
      (∀ e ∈ M, I e.1 e.2) ∧
      (∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f) ∧
      (∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f) ∧ M.card = N := by
  classical
  obtain ⟨σ, hσ⟩ := plane_incidence_perm q N I hq hN hL hU
  let pair (p : Fin N) : Fin N × Fin N := (p, σ p)
  have hi : Function.Injective pair := fun _ _ h => congrArg Prod.fst h
  refine ⟨Finset.univ.image pair, ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    exact hσ p
  · intro e he f hf heq
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨p', _, rfl⟩ := Finset.mem_image.mp hf
    exact congrArg pair heq
  · intro e he f hf heq
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨p', _, rfl⟩ := Finset.mem_image.mp hf
    exact congrArg pair (σ.injective heq)
  · simp [Finset.card_image_of_injective _ hi]

namespace A3692

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.EdgeOwnership

private def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma foldl_stepW_len (gs : List Gate) (inp : List Bool) :
    (gs.foldl stepW inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp
  | cons g rest ih =>
    simp [List.foldl, stepW, ih]
    omega

private lemma wires_eq_foldl (C : Circuit) (inp : List Bool) :
    C.wires inp = C.gates.foldl stepW inp := rfl

private lemma wires_len (C : Circuit) (inp : List Bool) :
    (C.wires inp).length = inp.length + C.gates.length := by
  simpa [wires_eq_foldl] using foldl_stepW_len C.gates inp

private lemma getD_append_left (l1 l2 : List Bool) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_append_self (l1 : List Bool) (b : Bool) :
    (l1 ++ [b]).getD l1.length false = b := by
  simp [List.getD]

private lemma getD_of_ge (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  simp [List.getD, List.getElem?_eq_none hi]

private lemma getD_ofFn {n : ℕ} (z : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn z).getD i false = z ⟨i, hi⟩ := by
  simp [List.getD, hi]

private def wireVal (n : ℕ) (gs : List Gate) (z : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl stepW (List.ofFn z)).getD i false

private lemma wireVal_append_gate_lt (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool)
    (i : ℕ) (hi : i < n + gs.length) :
    wireVal n (gs ++ [g]) z i = wireVal n gs z i := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  exact getD_append_left _ _ i (by omega)

private lemma wireVal_append_gate_self (n : ℕ) (gs : List Gate) (g : Gate) (z : Fin n → Bool) :
    wireVal n (gs ++ [g]) z (n + gs.length) =
      g.op.eval (g.inputs.map (fun i => wireVal n gs z i)) := by
  unfold wireVal
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlen : (gs.foldl stepW (List.ofFn z)).length = n + gs.length := by
    rw [foldl_stepW_len, List.length_ofFn]
  rw [← hlen]
  exact getD_append_self (gs.foldl stepW (List.ofFn z)) _

private def gateAtL (gs : List Gate) (j : ℕ) : Gate :=
  gs.getD j ⟨GateOp.or, []⟩

private lemma gateAtL_append_lt (gs : List Gate) (g : Gate) (j : ℕ) (hj : j < gs.length) :
    gateAtL (gs ++ [g]) j = gateAtL gs j := by
  simp [gateAtL, List.getD, List.getElem?_append_left hj]

private lemma gateAtL_append_self (gs : List Gate) (g : Gate) :
    gateAtL (gs ++ [g]) gs.length = g := by
  simp [gateAtL, List.getD]

private def Good (x1 x2 : ℕ) (S : Bool → Finset ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gateAtL gs j).inputs, i < x1 + x2 + j) ∧
  (∀ b : Bool, ∀ w ∈ S b, w < x1 + x2 + gs.length) ∧
  (∀ b : Bool, ∀ w ∈ S b,
    (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
    ∃ j < gs.length, w = x1 + x2 + j ∧ (gateAtL gs j).op = GateOp.or ∧
      ∀ u ∈ (gateAtL gs j).inputs, u ∈ S b) ∧
  (∀ j < gs.length, (gateAtL gs j).op = GateOp.and →
    ∃ a c : ℕ, (gateAtL gs j).inputs = [a, c] ∧ a ∈ S false ∧ c ∈ S true)

private def S0 (x1 x2 : ℕ) (b : Bool) : Finset ℕ :=
  if b then Finset.Ico x1 (x1 + x2) else Finset.range x1

private lemma good_init (x1 x2 : ℕ) : Good x1 x2 (S0 x1 x2) [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg; cases hg
  · intro j hj; simp at hj
  · intro b w hw
    cases b <;> simp [S0] at hw <;> omega
  · intro b w hw
    left
    cases b <;> simp [S0] at hw
    · exact ⟨by omega, by simp [show ¬(x1 ≤ w) by omega]⟩
    · exact ⟨hw.2, by simp [hw.1]⟩
  · intro j hj; simp at hj

private lemma mem_S0_false {x1 x2 : ℕ} (p : Fin x1) : p.1 ∈ S0 x1 x2 false := by
  simp [S0, p.2]

private lemma mem_S0_true {x1 x2 : ℕ} (l : Fin x2) : x1 + l.1 ∈ S0 x1 x2 true := by
  simp [S0]

private lemma good_append_or_side {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) (b : Bool) {u v : ℕ} (hu : u ∈ S b) (hv : v ∈ S b) :
    let w := x1 + x2 + gs.length
    let S' : Bool → Finset ℕ := fun b' => if b' = b then insert w (S b') else S b'
    Good x1 x2 S' (gs ++ [⟨GateOp.or, [u, v]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  have hu_lt : u < x1 + x2 + gs.length := hLt b u hu
  have hv_lt : v < x1 + x2 + gs.length := hLt b v hv
  dsimp only
  have hSub : ∀ b' : Bool, S b' ⊆ (if b' = b then insert (x1 + x2 + gs.length) (S b') else S b') := by
    intro b'
    by_cases hbb : b' = b
    · simp [hbb]
    · simp [hbb]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b' w hw
    simp only [List.length_append, List.length_singleton]
    by_cases hbb : b' = b
    · simp only [hbb, ite_true, Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · omega
      · have := hLt b w hw; omega
    · simp only [hbb, ite_false] at hw
      have := hLt b' w hw; omega
  · intro b' w hw
    by_cases hbb : b' = b
    · subst hbb
      simp only [ite_true, Finset.mem_insert] at hw
      rcases hw with rfl | hw
      · right
        refine ⟨gs.length, by simp, rfl, ?_, ?_⟩
        · rw [gateAtL_append_self]
        · rw [gateAtL_append_self]
          intro t ht
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          rcases ht with rfl | rfl
          · exact hSub b' hu
          · exact hSub b' hv
      · rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
        · exact Or.inl h1
        · right
          refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
          · rw [gateAtL_append_lt _ _ _ hj]; exact hop
          · rw [gateAtL_append_lt _ _ _ hj]
            intro t ht
            exact hSub b' (hin t ht)
    · simp only [hbb, ite_false] at hw
      rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
      · exact Or.inl h1
      · right
        refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
        · rw [gateAtL_append_lt _ _ _ hj]; exact hop
        · rw [gateAtL_append_lt _ _ _ hj]
          intro t ht
          simp only [hbb, ite_false]
          exact hin t ht
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      rcases hAnd j hlt hop with ⟨a, c, hin, ha, hc⟩
      exact ⟨a, c, hin, hSub false ha, hSub true hc⟩
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hop
      cases hop

private lemma good_append_or_top {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) {u v : ℕ} (hu : u < x1 + x2 + gs.length) (hv : v < x1 + x2 + gs.length) :
    Good x1 x2 S (gs ++ [⟨GateOp.or, [u, v]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inr rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b w hw
    simp only [List.length_append, List.length_singleton]
    have := hLt b w hw; omega
  · intro b w hw
    rcases hSide b w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
    · exact Or.inl h1
    · right
      refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
      · rw [gateAtL_append_lt _ _ _ hj]; exact hop
      · rw [gateAtL_append_lt _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      exact hAnd j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hop
      cases hop

private lemma good_append_and {x1 x2 : ℕ} {S : Bool → Finset ℕ} {gs : List Gate}
    (hG : Good x1 x2 S gs) {a c : ℕ} (ha : a ∈ S false) (hc : c ∈ S true) :
    Good x1 x2 S (gs ++ [⟨GateOp.and, [a, c]⟩]) := by
  rcases hG with ⟨hAO, hRB, hLt, hSide, hAnd⟩
  have ha_lt : a < x1 + x2 + gs.length := hLt false a ha
  have hc_lt : c < x1 + x2 + gs.length := hLt true c hc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO g hg
    · exact ⟨Or.inl rfl, rfl⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hi
      exact hRB j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · intro b' w hw
    simp only [List.length_append, List.length_singleton]
    have := hLt b' w hw; omega
  · intro b' w hw
    rcases hSide b' w hw with h1 | ⟨j, hj, hweq, hop, hin⟩
    · exact Or.inl h1
    · right
      refine ⟨j, by simp; omega, hweq, ?_, ?_⟩
      · rw [gateAtL_append_lt _ _ _ hj]; exact hop
      · rw [gateAtL_append_lt _ _ _ hj]; exact hin
  · intro j hj hop
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · rw [gateAtL_append_lt _ _ _ hlt] at hop ⊢
      exact hAnd j hlt hop
    · have hjeq : j = gs.length := by omega
      subst hjeq
      rw [gateAtL_append_self]
      exact ⟨a, c, rfl, ha, hc⟩

private lemma addOrInSide {x1 x2 : ℕ} (b : Bool) (ws : List ℕ) (hne : ws ≠ []) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ u ∈ ws, u ∈ S b) →
      ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (w : ℕ),
        gs'.length = gs.length + (ws.length - 1) ∧
        Good x1 x2 S' gs' ∧
        (∀ b', S b' ⊆ S' b') ∧
        w ∈ S' b ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, wireVal (x1 + x2) gs' z w = ws.any (fun u => wireVal (x1 + x2) gs z u)) := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons u rest ih =>
    intro S gs hG hws
    cases rest with
    | nil =>
      refine ⟨S, gs, u, by simp, hG, fun _ => Finset.Subset.rfl, hws u (by simp), ?_, ?_⟩
      · intro z i _; rfl
      · intro z; simp
    | cons v rest' =>
      have hne' : v :: rest' ≠ [] := List.cons_ne_nil v rest'
      have hws' : ∀ t ∈ v :: rest', t ∈ S b := fun t ht => hws t (List.mem_cons_of_mem u ht)
      rcases ih hne' S gs hG hws' with ⟨S1, gs1, w1, hlen1, hG1, hSub1, hw1, hPres1, hVal1⟩
      have hu1 : u ∈ S1 b := hSub1 b (hws u (by simp))
      let w := x1 + x2 + gs1.length
      let gs2 := gs1 ++ [⟨GateOp.or, [u, w1]⟩]
      let S2 : Bool → Finset ℕ := fun b' => if b' = b then insert w (S1 b') else S1 b'
      have hG2 : Good x1 x2 S2 gs2 := good_append_or_side hG1 b hu1 hw1
      have hSub2 : ∀ b', S b' ⊆ S2 b' := by
        intro b'
        refine Finset.Subset.trans (hSub1 b') ?_
        by_cases hbb : b' = b
        · simp [S2, hbb]
        · simp [S2, hbb]
      have hw2 : w ∈ S2 b := by simp [S2]
      have hu_lt : u < x1 + x2 + gs.length := hG.2.2.1 b u (hws u (by simp))
      refine ⟨S2, gs2, w, ?_, hG2, hSub2, hw2, ?_, ?_⟩
      · simp [gs2, hlen1]; omega
      · intro z i hi
        have hi1 : i < x1 + x2 + gs1.length := by omega
        rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
        exact hPres1 z i hi
      · intro z
        rw [wireVal_append_gate_self]
        simp only [List.map, GateOp.eval, List.any_cons]
        rw [hPres1 z u hu_lt, hVal1 z]
        simp

private lemma addOrTop {x1 x2 : ℕ} (ws : List ℕ) (hne : ws ≠ []) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ u ∈ ws, u < x1 + x2 + gs.length) →
      ∃ (gs' : List Gate) (w : ℕ),
        gs'.length = gs.length + (ws.length - 1) ∧
        Good x1 x2 S gs' ∧
        w < x1 + x2 + gs'.length ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, wireVal (x1 + x2) gs' z w = ws.any (fun u => wireVal (x1 + x2) gs z u)) := by
  induction ws with
  | nil => exact absurd rfl hne
  | cons u rest ih =>
    intro S gs hG hws
    cases rest with
    | nil =>
      refine ⟨gs, u, by simp, hG, hws u (by simp), ?_, ?_⟩
      · intro z i _; rfl
      · intro z; simp
    | cons v rest' =>
      have hne' : v :: rest' ≠ [] := List.cons_ne_nil v rest'
      have hws' : ∀ t ∈ v :: rest', t < x1 + x2 + gs.length :=
        fun t ht => hws t (List.mem_cons_of_mem u ht)
      rcases ih hne' S gs hG hws' with ⟨gs1, w1, hlen1, hG1, hw1, hPres1, hVal1⟩
      have hu_lt : u < x1 + x2 + gs.length := hws u (by simp)
      have hu1 : u < x1 + x2 + gs1.length := by omega
      let w := x1 + x2 + gs1.length
      let gs2 := gs1 ++ [⟨GateOp.or, [u, w1]⟩]
      have hG2 : Good x1 x2 S gs2 := good_append_or_top hG1 hu1 hw1
      refine ⟨gs2, w, ?_, hG2, ?_, ?_, ?_⟩
      · simp [gs2, hlen1]; omega
      · simp [gs2, w]
      · intro z i hi
        have hi1 : i < x1 + x2 + gs1.length := by omega
        rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
        exact hPres1 z i hi
      · intro z
        rw [wireVal_append_gate_self]
        simp only [List.map, GateOp.eval, List.any_cons]
        rw [hPres1 z u hu_lt, hVal1 z]
        simp

private abbrev Star (x1 x2 : ℕ) := (Fin x1 × List (Fin x2)) ⊕ (Fin x2 × List (Fin x1))

private def starSize {x1 x2 : ℕ} : Star x1 x2 → ℕ
  | Sum.inl (_, ls) => ls.length
  | Sum.inr (_, ps) => ps.length

private def starEval {x1 x2 : ℕ} (z : Fin (x1 + x2) → Bool) : Star x1 x2 → Bool
  | Sum.inl (p, ls) => z (Fin.castAdd x2 p) && ls.any (fun l => z (Fin.natAdd x1 l))
  | Sum.inr (l, ps) => ps.any (fun p => z (Fin.castAdd x2 p)) && z (Fin.natAdd x1 l)

private lemma wireVal_input_left {x1 x2 : ℕ} (gs : List Gate) (z : Fin (x1 + x2) → Bool)
    (p : Fin x1) :
    wireVal (x1 + x2) gs z p.1 = z (Fin.castAdd x2 p) := by
  induction gs using List.reverseRecOn with
  | nil =>
    unfold wireVal
    simp only [List.foldl_nil]
    have hlt : p.1 < x1 + x2 := by omega
    rw [getD_ofFn z p.1 hlt]
    rfl
  | append_singleton gs g ih =>
    rw [wireVal_append_gate_lt _ _ _ _ _ (by omega)]
    exact ih

private lemma wireVal_input_right {x1 x2 : ℕ} (gs : List Gate) (z : Fin (x1 + x2) → Bool)
    (l : Fin x2) :
    wireVal (x1 + x2) gs z (x1 + l.1) = z (Fin.natAdd x1 l) := by
  induction gs using List.reverseRecOn with
  | nil =>
    unfold wireVal
    simp only [List.foldl_nil]
    have hlt : x1 + l.1 < x1 + x2 := by omega
    rw [getD_ofFn z (x1 + l.1) hlt]
    rfl
  | append_singleton gs g ih =>
    rw [wireVal_append_gate_lt _ _ _ _ _ (by omega)]
    exact ih

private lemma addStar {x1 x2 : ℕ} (st : Star x1 x2) (hpos : 0 < starSize st)
    (S : Bool → Finset ℕ) (gs : List Gate)
    (hG : Good x1 x2 S gs) (hBase : ∀ b, S0 x1 x2 b ⊆ S b) :
    ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (w : ℕ),
      gs'.length = gs.length + starSize st ∧
      Good x1 x2 S' gs' ∧
      (∀ b, S b ⊆ S' b) ∧
      w < x1 + x2 + gs'.length ∧
      (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
      (∀ z, wireVal (x1 + x2) gs' z w = starEval z st) := by
  cases st with
  | inl pl =>
    rcases pl with ⟨p, ls⟩
    have hne_ls : ls ≠ [] := by
      intro h; simp [starSize, h] at hpos
    let ws : List ℕ := ls.map (fun l => x1 + l.1)
    have hne_ws : ws ≠ [] := by
      simp [ws, hne_ls]
    have hws_mem : ∀ u ∈ ws, u ∈ S true := by
      intro u hu
      simp only [ws, List.mem_map] at hu
      rcases hu with ⟨l, _, rfl⟩
      exact hBase true (mem_S0_true l)
    rcases addOrInSide true ws hne_ws S gs hG hws_mem with
      ⟨S1, gs1, wL, hlen1, hG1, hSub1, hwL, hPres1, hVal1⟩
    have hp1 : p.1 ∈ S1 false := hSub1 false (hBase false (mem_S0_false p))
    let w := x1 + x2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [p.1, wL]⟩]
    have hG2 : Good x1 x2 S1 gs2 := good_append_and hG1 hp1 hwL
    refine ⟨S1, gs2, w, ?_, hG2, hSub1, ?_, ?_, ?_⟩
    · simp only [gs2, List.length_append, List.length_singleton, hlen1, ws, List.length_map,
        starSize]
      have : 0 < ls.length := by simpa [starSize] using hpos
      omega
    · simp [gs2, w]
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
      exact hPres1 z i hi
    · intro z
      rw [wireVal_append_gate_self]
      simp only [List.map, GateOp.eval, starEval]
      rw [wireVal_input_left, hVal1 z]
      simp only [ws, List.any_map]
      have hfn : (fun l : Fin x2 => wireVal (x1 + x2) gs z (x1 + l.1)) =
          (fun l : Fin x2 => z (Fin.natAdd x1 l)) := by
        funext l
        exact wireVal_input_right gs z l
      simp [Function.comp_def, hfn]
  | inr lp =>
    rcases lp with ⟨l, ps⟩
    have hne_ps : ps ≠ [] := by
      intro h; simp [starSize, h] at hpos
    let ws : List ℕ := ps.map (fun p => p.1)
    have hne_ws : ws ≠ [] := by
      simp [ws, hne_ps]
    have hws_mem : ∀ u ∈ ws, u ∈ S false := by
      intro u hu
      simp only [ws, List.mem_map] at hu
      rcases hu with ⟨p, _, rfl⟩
      exact hBase false (mem_S0_false p)
    rcases addOrInSide false ws hne_ws S gs hG hws_mem with
      ⟨S1, gs1, wP, hlen1, hG1, hSub1, hwP, hPres1, hVal1⟩
    have hl1 : x1 + l.1 ∈ S1 true := hSub1 true (hBase true (mem_S0_true l))
    let w := x1 + x2 + gs1.length
    let gs2 := gs1 ++ [⟨GateOp.and, [wP, x1 + l.1]⟩]
    have hG2 : Good x1 x2 S1 gs2 := good_append_and hG1 hwP hl1
    refine ⟨S1, gs2, w, ?_, hG2, hSub1, ?_, ?_, ?_⟩
    · simp only [gs2, List.length_append, List.length_singleton, hlen1, ws, List.length_map,
        starSize]
      have : 0 < ps.length := by simpa [starSize] using hpos
      omega
    · simp [gs2, w]
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [wireVal_append_gate_lt _ _ _ _ _ hi1]
      exact hPres1 z i hi
    · intro z
      rw [wireVal_append_gate_self]
      simp only [List.map, GateOp.eval, starEval]
      rw [wireVal_input_right, hVal1 z]
      simp only [ws, List.any_map]
      have hfn : (fun p : Fin x1 => wireVal (x1 + x2) gs z p.1) =
          (fun p : Fin x1 => z (Fin.castAdd x2 p)) := by
        funext p
        exact wireVal_input_left gs z p
      simp [Function.comp_def, hfn]

private lemma addStars {x1 x2 : ℕ} (stars : List (Star x1 x2))
    (hpos : ∀ st ∈ stars, 0 < starSize st) :
    ∀ (S : Bool → Finset ℕ) (gs : List Gate),
      Good x1 x2 S gs →
      (∀ b, S0 x1 x2 b ⊆ S b) →
      ∃ (S' : Bool → Finset ℕ) (gs' : List Gate) (ws : List ℕ),
        gs'.length = gs.length + (stars.map starSize).sum ∧
        ws.length = stars.length ∧
        Good x1 x2 S' gs' ∧
        (∀ w ∈ ws, w < x1 + x2 + gs'.length) ∧
        (∀ z i, i < x1 + x2 + gs.length → wireVal (x1 + x2) gs' z i = wireVal (x1 + x2) gs z i) ∧
        (∀ z, ws.any (fun w => wireVal (x1 + x2) gs' z w) = stars.any (fun st => starEval z st)) := by
  induction stars with
  | nil =>
    intro S gs hG _
    refine ⟨S, gs, [], by simp, rfl, hG, by simp, ?_, ?_⟩
    · intro z i _; rfl
    · intro z; simp
  | cons st rest ih =>
    intro S gs hG hBase
    rcases addStar st (hpos st (by simp)) S gs hG hBase with
      ⟨S1, gs1, w1, hlen1, hG1, hSub1, hw1, hPres1, hVal1⟩
    have hBase1 : ∀ b, S0 x1 x2 b ⊆ S1 b := fun b => Finset.Subset.trans (hBase b) (hSub1 b)
    have hpos_rest : ∀ s ∈ rest, 0 < starSize s := fun s hs => hpos s (List.mem_cons_of_mem st hs)
    rcases ih hpos_rest S1 gs1 hG1 hBase1 with
      ⟨S2, gs2, ws2, hlen2, hwslen2, hG2, hws2_lt, hPres2, hVal2⟩
    refine ⟨S2, gs2, w1 :: ws2, ?_, ?_, hG2, ?_, ?_, ?_⟩
    · simp [hlen2, hlen1, Nat.add_assoc]
    · simp [hwslen2]
    · intro w hw
      simp only [List.mem_cons] at hw
      rcases hw with rfl | hw
      · omega
      · exact hws2_lt w hw
    · intro z i hi
      have hi1 : i < x1 + x2 + gs1.length := by omega
      rw [hPres2 z i hi1]
      exact hPres1 z i hi
    · intro z
      simp only [List.any_cons]
      rw [hPres2 z w1 hw1, hVal1 z, hVal2 z]

private lemma circuit_from_good {x1 x2 : ℕ} (S : Bool → Finset ℕ) (gs : List Gate) (out : ℕ)
    (hG : Good x1 x2 S gs) :
    let C : Circuit := ⟨gs, out⟩
    IsAO2 (x1 + x2) C ∧
    (∀ b : Bool, ∀ w ∈ S b,
      (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
      ∃ j < C.size, w = x1 + x2 + j ∧ (gateAt C j).op = GateOp.or ∧
        ∀ u ∈ (gateAt C j).inputs, u ∈ S b) ∧
    (∀ j < C.size, (gateAt C j).op = GateOp.and →
      ∃ a c : ℕ, (gateAt C j).inputs = [a, c] ∧ a ∈ S false ∧ c ∈ S true) := by
  rcases hG with ⟨hAO, hRB, _, hSide, hAnd⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro g hg; exact (hAO g hg).1
  · intro j hj i hi; exact hRB j hj i hi
  · intro g hg; exact (hAO g hg).2
  · intro b w hw; exact hSide b w hw
  · intro j hj hop; exact hAnd j hj hop

end A3692

open A3692 in
theorem t3692 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)),   (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) →     ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool → Finset ℕ),       PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧         x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧           (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x3 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) ∧             have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x7;             (∀ (x10 : Bool), ∀ x11 ∈ x8 x10, x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨ ∃ x13 < x7.size, x11 = x1 + x2 + x13 ∧ (x9 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (x9 x13).inputs, x14 ∈ x8 x10) ∧ ∀ x10 < x7.size, (x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x9 x10).inputs = [x13, x14] ∧ x13 ∈ x8 Bool.false ∧ x14 ∈ x8 Bool.true := by
  intro x1 x2 E A B hcov
  by_cases hE : E = ∅
  · subst hE
    refine ⟨⟨[], x1 + x2⟩, fun _ => ∅, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg; cases hg
      · intro j hj; simp at hj
      · intro g hg; cases hg
    · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
    · intro z
      simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, List.foldl_nil, Finset.notMem_empty,
        false_and, exists_false, decide_false]
      exact getD_of_ge (List.ofFn z) (x1 + x2) (by simp)
    · intro b w hw; simp at hw
    · intro j hj; simp [PEqualNP.CircuitLowerBounds.Circuit.size] at hj
  · have hE_ne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hE
    let NA : Fin x1 → Finset (Fin x2) := fun p => Finset.univ.filter (fun l => (p, l) ∈ E)
    let NB : Fin x2 → Finset (Fin x1) := fun l => Finset.univ.filter (fun p => (p, l) ∈ E ∧ p ∉ A)
    let A' : Finset (Fin x1) := A.filter (fun p => (NA p).Nonempty)
    let B' : Finset (Fin x2) := B.filter (fun l => (NB l).Nonempty)
    let starsA : List (Star x1 x2) := A'.toList.map (fun p => Sum.inl (p, (NA p).toList))
    let starsB : List (Star x1 x2) := B'.toList.map (fun l => Sum.inr (l, (NB l).toList))
    let stars : List (Star x1 x2) := starsA ++ starsB
    have hpos : ∀ st ∈ stars, 0 < starSize st := by
      intro st hst
      simp only [stars, starsA, starsB, List.mem_append, List.mem_map, Finset.mem_toList] at hst
      rcases hst with ⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩
      · simp only [starSize, Finset.length_toList]
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hp).2
      · simp only [starSize, Finset.length_toList]
        exact Finset.card_pos.mpr (Finset.mem_filter.mp hl).2
    have hsumA : (starsA.map starSize).sum = ∑ p ∈ A', (NA p).card := by
      have h1 : (starsA.map starSize) = A'.toList.map (fun p => (NA p).card) := by
        simp [starsA, starSize, Function.comp_def]
      rw [h1, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    have hsumB : (starsB.map starSize).sum = ∑ l ∈ B', (NB l).card := by
      have h1 : (starsB.map starSize) = B'.toList.map (fun l => (NB l).card) := by
        simp [starsB, starSize, Function.comp_def]
      rw [h1, ← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
      rfl
    have hcardE : (∑ p ∈ A', (NA p).card) + (∑ l ∈ B', (NB l).card) = E.card := by
      let EA : Finset (Fin x1 × Fin x2) := A'.biUnion (fun p => (NA p).image (fun l => (p, l)))
      let EB : Finset (Fin x1 × Fin x2) := B'.biUnion (fun l => (NB l).image (fun p => (p, l)))
      have hEA_card : EA.card = ∑ p ∈ A', (NA p).card := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl ?_
          intro p _
          exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)
        · intro p1 _ p2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro e he1 he2
          simp only [Finset.mem_image] at he1 he2
          rcases he1 with ⟨l1, _, rfl⟩
          rcases he2 with ⟨l2, _, heq⟩
          exact hne (Prod.mk.inj heq).1.symm
      have hEB_card : EB.card = ∑ l ∈ B', (NB l).card := by
        rw [Finset.card_biUnion]
        · refine Finset.sum_congr rfl ?_
          intro l _
          exact Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)
        · intro l1 _ l2 _ hne
          dsimp only [Function.onFun]
          rw [Finset.disjoint_left]
          intro e he1 he2
          simp only [Finset.mem_image] at he1 he2
          rcases he1 with ⟨p1, _, rfl⟩
          rcases he2 with ⟨p2, _, heq⟩
          exact hne (Prod.mk.inj heq).2.symm
      have hdisj : Disjoint EA EB := by
        rw [Finset.disjoint_left]
        intro e he1 he2
        simp only [EA, EB, Finset.mem_biUnion, Finset.mem_image] at he1 he2
        rcases he1 with ⟨p1, hp1, l1, _, rfl⟩
        rcases he2 with ⟨l2, _, p2, hp2, heq⟩
        have hp_eq : p2 = p1 := (Prod.mk.inj heq).1
        subst hp_eq
        have hp1A : p2 ∈ A := (Finset.mem_filter.mp hp1).1
        have hp2nA : p2 ∉ A := (Finset.mem_filter.mp hp2).2.2
        exact hp2nA hp1A
      have hunion : EA ∪ EB = E := by
        ext ⟨p, l⟩
        simp only [EA, EB, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
        constructor
        · rintro (⟨p1, _, l1, hl1, heq⟩ | ⟨l1, _, p1, hp1, heq⟩)
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact (Finset.mem_filter.mp hl1).2
          · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
            exact (Finset.mem_filter.mp hp1).2.1
        · intro hpl
          by_cases hpA : p ∈ A
          · left
            refine ⟨p, Finset.mem_filter.mpr ⟨hpA, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩⟩⟩,
              l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩, rfl⟩
          · right
            have hlB : l ∈ B := (hcov (p, l) hpl).resolve_left hpA
            refine ⟨l, Finset.mem_filter.mpr ⟨hlB, ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩⟩⟩,
              p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩, rfl⟩
      rw [← hEA_card, ← hEB_card, ← Finset.card_union_of_disjoint hdisj, hunion]
    have hsum_stars : (stars.map starSize).sum = E.card := by
      simp only [stars, List.map_append, List.sum_append, hsumA, hsumB, hcardE]
    have hstars_len : stars.length = A'.card + B'.card := by
      simp [stars, starsA, starsB]
    have hstars_ne : stars ≠ [] := by
      intro hnil
      have h0 : E.card = 0 := by
        rw [← hsum_stars, hnil]; rfl
      exact (Finset.card_pos.mpr hE_ne).ne' h0
    rcases addStars stars hpos (S0 x1 x2) [] (good_init x1 x2) (fun _ => Finset.Subset.rfl) with
      ⟨S1, gs1, ws1, hlen1, hwslen1, hG1, hws1_lt, _, hVal1⟩
    have hws1_ne : ws1 ≠ [] := by
      intro hnil
      apply hstars_ne
      apply List.eq_nil_of_length_eq_zero
      rw [← hwslen1, hnil]
      rfl
    rcases addOrTop ws1 hws1_ne S1 gs1 hG1 hws1_lt with
      ⟨gs2, wOut, hlen2, hG2, _, hPres2, hVal2⟩
    let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨gs2, wOut⟩
    have hC := circuit_from_good S1 gs2 wOut hG2
    refine ⟨C, S1, hC.1, ?_, ?_, hC.2.1, hC.2.2⟩
    · have hA' : A'.card ≤ A.card := Finset.card_filter_le _ _
      have hB' : B'.card ≤ B.card := Finset.card_filter_le _ _
      have hk_pos : 1 ≤ ws1.length := by
        cases ws1 with
        | nil => exact absurd rfl hws1_ne
        | cons _ _ => simp
      simp only [C, PEqualNP.CircuitLowerBounds.Circuit.size, hlen2, hlen1, List.length_nil,
        Nat.zero_add, hsum_stars, hwslen1, hstars_len]
      omega
    · intro z
      have hcf : PEqualNP.MetaComplexity.circuitFun (x1 + x2) C z = wireVal (x1 + x2) gs2 z wOut := rfl
      rw [hcf, hVal2 z, hVal1 z]
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨st, hst, hst_eval⟩
        simp only [stars, starsA, starsB, List.mem_append, List.mem_map, Finset.mem_toList] at hst
        rcases hst with ⟨p, _, rfl⟩ | ⟨l, _, rfl⟩
        · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList] at hst_eval
          rcases hst_eval with ⟨hzp, l, hl, hzl⟩
          exact ⟨p, l, (Finset.mem_filter.mp hl).2, hzp, hzl⟩
        · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList] at hst_eval
          rcases hst_eval with ⟨⟨p, hp, hzp⟩, hzl⟩
          exact ⟨p, l, (Finset.mem_filter.mp hp).2.1, hzp, hzl⟩
      · rintro ⟨p, l, hpl, hzp, hzl⟩
        by_cases hpA : p ∈ A
        · refine ⟨Sum.inl (p, (NA p).toList), ?_, ?_⟩
          · simp only [stars, starsA, List.mem_append, List.mem_map, Finset.mem_toList]
            left
            exact ⟨p, Finset.mem_filter.mpr ⟨hpA, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩⟩⟩, rfl⟩
          · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList]
            exact ⟨hzp, l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hpl⟩, hzl⟩
        · have hlB : l ∈ B := (hcov (p, l) hpl).resolve_left hpA
          refine ⟨Sum.inr (l, (NB l).toList), ?_, ?_⟩
          · simp only [stars, starsB, List.mem_append, List.mem_map, Finset.mem_toList]
            right
            exact ⟨l, Finset.mem_filter.mpr ⟨hlB, ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩⟩⟩, rfl⟩
          · simp only [starEval, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList]
            exact ⟨⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hpl, hpA⟩, hzp⟩, hzl⟩

namespace B6579

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadK PEqualNP.TopForm

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


lemma mem_foldl_insertNew_of_acc (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ acc) : v ∈ L.foldl insertNew acc := by
  induction L generalizing acc with
  | nil => exact h
  | cons x L ih =>
    rw [List.foldl_cons]
    apply ih
    unfold insertNew
    split_ifs
    · exact h
    · exact List.mem_append_left _ h

lemma mem_foldl_insertNew_of_mem (L : List (List ℕ)) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ L) : v ∈ L.foldl insertNew acc := by
  induction L generalizing acc with
  | nil => simp at h
  | cons x L ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with h1 | h1
    · apply mem_foldl_insertNew_of_acc
      subst h1
      unfold insertNew
      split_ifs with h2
      · exact h2
      · simp
    · exact ih _ h1

lemma mem_andStep_of (k : ℕ) (A B : List (List ℕ)) (u u2 : List ℕ) (hu : u ∈ A) (hu2 : u2 ∈ B) :
    capAdd k u u2 ∈ andStep k A B := by
  unfold andStep
  apply mem_foldl_insertNew_of_mem
  simp only [List.mem_flatMap, List.mem_map]
  exact ⟨u, hu, u2, hu2, rfl⟩

lemma mem_orFold (As : List (List (List ℕ))) (acc : List (List ℕ)) (v : List ℕ)
    (h : v ∈ acc ∨ ∃ A ∈ As, v ∈ A) :
    v ∈ As.foldl (fun acc A => A.foldl insertNew acc) acc := by
  induction As generalizing acc with
  | nil =>
    rcases h with h | ⟨A, hA, _⟩
    · exact h
    · simp at hA
  | cons A0 As ih =>
    rw [List.foldl_cons]
    apply ih
    rcases h with h | ⟨A, hA, hv⟩
    · exact Or.inl (mem_foldl_insertNew_of_acc _ _ _ h)
    · rcases List.mem_cons.1 hA with h1 | h1
      · subst h1
        exact Or.inl (mem_foldl_insertNew_of_mem _ _ _ hv)
      · exact Or.inr ⟨A, h1, hv⟩

lemma capAdd_map (L : List ℕ) (f g : ℕ → ℕ) (k : ℕ) :
    capAdd k (L.map f) (L.map g) = L.map (fun j => min (f j + g j) (k + 1)) := by
  unfold capAdd
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.zipWith_cons_cons, ih]

def uv (L : List ℕ) (i : ℕ) : List ℕ := L.map fun j => if j = i then min 1 (1 + 1) else 0

lemma mem_setList {n : ℕ} (S : Finset (Fin n)) (w : ℕ) (hw : w < n) (h : (⟨w, hw⟩ : Fin n) ∈ S) :
    w ∈ setList S := by
  unfold setList
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  exact ⟨⟨w, hw⟩, h, rfl⟩

theorem inv (x1 x2 : ℕ) (C : Circuit) (x4 : Bool → Finset ℕ) (hC : IsAO2 (x1 + x2) C)
    (hx4 : ∀ (b : Bool), ∀ w ∈ x4 b, (w < x1 + x2 ∧ decide (x1 ≤ w) = b) ∨
      ∃ j < C.size, w = x1 + x2 + j ∧ (gateAt C j).op = GateOp.or ∧
        ∀ i ∈ (gateAt C j).inputs, i ∈ x4 b)
    (hand : ∀ j < C.size, (gateAt C j).op = GateOp.and →
      ∃ (a : ℕ) (c : ℕ), (gateAt C j).inputs = [a, c] ∧ a ∈ x4 false ∧ c ∈ x4 true)
    (S : Finset (Fin (x1 + x2))) :
    ∀ w, s2230_W (x1 + x2) C (setInput S) w = true →
      (∃ v ∈ s2230_RV C (x1 + x2) (setList S) 1 w, ∀ a ∈ v, a ≤ 1) ∧
      (∀ b, w ∈ x4 b → ∃ i, decide (x1 ≤ i) = b ∧
        uv (setList S) i ∈ s2230_RV C (x1 + x2) (setList S) 1 w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hw
  obtain ⟨hAO, hRB, _⟩ := hC
  by_cases hwn : w < x1 + x2
  · have hS : (⟨w, hwn⟩ : Fin (x1 + x2)) ∈ S := by
      rw [s2230_W_input (x1 + x2) C _ w hwn] at hw
      simpa [setInput] using hw
    have hmem : w ∈ setList S := mem_setList S w hwn hS
    have hRV : s2230_RV C (x1 + x2) (setList S) 1 w = [uv (setList S) w] := by
      rw [s2230_RV_input C (x1 + x2) (setList S) 1 w hwn]
      unfold leafVectors uv
      rw [if_pos hmem]
    refine ⟨⟨uv (setList S) w, by rw [hRV]; exact List.mem_singleton_self _, ?_⟩, ?_⟩
    · intro a ha
      unfold uv at ha
      simp only [List.mem_map] at ha
      obtain ⟨j, _, rfl⟩ := ha
      split_ifs <;> omega
    · intro b hb
      refine ⟨w, ?_, by rw [hRV]; exact List.mem_singleton_self _⟩
      rcases hx4 b w hb with ⟨_, hside⟩ | ⟨j, _, hj, _⟩
      · exact hside
      · omega
  · by_cases hwl : w < x1 + x2 + C.gates.length
    swap
    · exfalso
      have hf : s2230_W (x1 + x2) C (setInput S) w = false := by
        unfold s2230_W
        exact s2230_getD_ge_length _ _ (by rw [s2230_wires_length]; omega)
      rw [hf] at hw
      exact Bool.false_ne_true hw
    obtain ⟨j, rfl⟩ : ∃ j, w = x1 + x2 + j := ⟨w - (x1 + x2), by omega⟩
    have hj : j < C.gates.length := by omega
    have hgW := s2230_W_gate (x1 + x2) C (setInput S) j hj
    obtain ⟨Rp, hRp, hRVj⟩ := s2230_RV_gate C (x1 + x2) (setList S) 1 j hj
    have hRB' : ∀ i ∈ (gateAt C j).inputs, i < x1 + x2 + j := hRB j hj
    have hmapW : ((gateAt C j).inputs.map fun i =>
        if i < x1 + x2 + j then s2230_W (x1 + x2) C (setInput S) i else false) =
        (gateAt C j).inputs.map fun i => s2230_W (x1 + x2) C (setInput S) i := by
      refine List.map_congr_left fun i hi => ?_
      rw [if_pos (hRB' i hi)]
    have hmapR : ((gateAt C j).inputs.map fun i => Rp.getD i []) =
        (gateAt C j).inputs.map fun i => s2230_RV C (x1 + x2) (setList S) 1 i := by
      refine List.map_congr_left fun i hi => ?_
      exact hRp i (hRB' i hi)
    have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or :=
      hAO (gateAt C j) (by rw [s2230_gateAt_eq C j hj]; exact List.getElem_mem hj)
    have hor_true : (gateAt C j).op = GateOp.or →
        ∃ i ∈ (gateAt C j).inputs, s2230_W (x1 + x2) C (setInput S) i = true := by
      intro ho
      have hw' := hw
      rw [hgW, hmapW, ho] at hw'
      simpa [GateOp.eval] using hw'
    have hor_mem : (gateAt C j).op = GateOp.or → ∀ i ∈ (gateAt C j).inputs,
        ∀ v ∈ s2230_RV C (x1 + x2) (setList S) 1 i,
          v ∈ s2230_RV C (x1 + x2) (setList S) 1 (x1 + x2 + j) := by
      intro ho i hi v hv
      rw [hRVj, s2230_FR_or _ _ _ _ ho, hmapR]
      apply mem_orFold
      exact Or.inr ⟨_, List.mem_map.2 ⟨i, hi, rfl⟩, hv⟩
    refine ⟨?_, ?_⟩
    · rcases hop with ho | ho
      · obtain ⟨a, c, hac, ha, hc⟩ := hand j hj ho
        have hw' := hw
        rw [hgW, hmapW, ho, hac] at hw'
        have hwa : s2230_W (x1 + x2) C (setInput S) a = true ∧
            s2230_W (x1 + x2) C (setInput S) c = true := by
          simpa [GateOp.eval] using hw'
        have hRBa : a < x1 + x2 + j := hRB' a (by rw [hac]; simp)
        have hRBc : c < x1 + x2 + j := hRB' c (by rw [hac]; simp)
        obtain ⟨ia, hia, hA⟩ := (ih a hRBa hwa.1).2 false ha
        obtain ⟨ic, hic, hCc⟩ := (ih c hRBc hwa.2).2 true hc
        have hne : ia ≠ ic := by
          rintro rfl
          rw [hia] at hic
          exact Bool.false_ne_true hic
        refine ⟨capAdd 1 (capAdd 1 ((setList S).map fun _ => 0) (uv (setList S) ia))
          (uv (setList S) ic), ?_, ?_⟩
        · rw [hRVj, s2230_FR_and _ _ _ _ ho, hmapR, hac]
          simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
          exact mem_andStep_of _ _ _ _ _
            (mem_andStep_of _ _ _ _ _ (List.mem_singleton_self _) hA) hCc
        · intro e he
          unfold uv at he
          rw [capAdd_map, capAdd_map] at he
          simp only [List.mem_map] at he
          obtain ⟨t, _, rfl⟩ := he
          split_ifs <;> omega
      · obtain ⟨i, hi, hwi⟩ := hor_true ho
        obtain ⟨v, hv, hle⟩ := (ih i (hRB' i hi) hwi).1
        exact ⟨v, hor_mem ho i hi v hv, hle⟩
    · intro b hb
      rcases hx4 b _ hb with ⟨hlt, _⟩ | ⟨j', _, hjj, ho, hins⟩
      · omega
      · have hjj' : j' = j := by omega
        subst hjj'
        obtain ⟨i, hi, hwi⟩ := hor_true ho
        obtain ⟨ia, hia, hA⟩ := (ih i (hRB' i hi) hwi).2 b (hins i hi)
        exact ⟨ia, hia, hor_mem ho i hi _ hA⟩

end B6579

theorem t6579 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Bool → Finset ℕ), PEqualNP.TopForm.IsAO2 (x1 + x2) x3 → (∀ (x6 : Bool), ∀ x7 ∈ x4 x6, x7 < x1 + x2 ∧ Decidable.decide (x1 ≤ x7) = x6 ∨ ∃ x9 < x3.size, x7 = x1 + x2 + x9 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x10 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x9).inputs, x10 ∈ x4 x6) → (∀ x7 < x3.size, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x10 : ℕ) (x11 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x7).inputs = [x10, x11] ∧ x10 ∈ x4 Bool.false ∧ x11 ∈ x4 Bool.true) → PEqualNP.ReadK.IsReadK (x1 + x2) x3 (1 : ℕ) := by
  intro x1 x2 C x4 hC hx4 hand S hS
  have hout : PEqualNP.Outside.L_meta_2583.B6579.s2230_W (x1 + x2) C (PEqualNP.ReadK.setInput S)
      C.output = true := hS.1
  obtain ⟨⟨v, hv, hle⟩, _⟩ :=
    PEqualNP.Outside.L_meta_2583.B6579.inv x1 x2 C x4 hC hx4 hand S C.output hout
  unfold PEqualNP.ReadK.readsAtMost
  apply List.any_eq_true.2
  refine ⟨v, hv, ?_⟩
  apply List.all_eq_true.2
  intro a ha
  exact decide_eq_true (hle a ha)

lemma starCoverRead1 : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)), (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧ x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧ (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), (x9, x10) ∈ x3 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) ∧ PEqualNP.ReadK.IsReadK (x1 + x2) x7 (1 : ℕ) := by
  intro x1 x2 x3 x4 x5 hcov
  obtain ⟨C, F, hao, hsize, hfun, hF1, hF2⟩ := PEqualNP.Outside.L_meta_2583.t3692 x1 x2 x3 x4 x5 hcov
  exact ⟨C, hao, hsize, hfun, PEqualNP.Outside.L_meta_2583.t6579 x1 x2 C F hao hF1 hF2⟩


def incidenceEdges {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] :
    Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun e => I e.1 e.2)

lemma incidenceEdges_card {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    (incidenceEdges I).card = N * (q + 1) := by
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
  have heq : incidenceEdges I = Finset.univ.biUnion F := by
    ext e
    simp only [incidenceEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, hF]
    exact ⟨fun h => ⟨e.2, h, rfl⟩, fun ⟨l, hi, he⟩ => he ▸ hi⟩
  rw [heq, Finset.card_biUnion]
  · simp [F, hL]
  · intro l _ l' _ hne
    refine Finset.disjoint_left.mpr ?_
    intro e he he'
    exact hne (((hF l e).mp he).2.symm.trans ((hF l' e).mp he').2)

lemma plane_read1_upper {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) D z =
          decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
            z (Fin.natAdd N l) = true)) ∧
      D.size ≤ N * (q + 2) - 1 ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  classical
  obtain ⟨D, hao, hsize, hfun, hread⟩ := starCoverRead1 N N (incidenceEdges I)
    Finset.univ ∅ (by intro e _; exact Or.inl (Finset.mem_univ _))
  refine ⟨D, hao, ?_, ?_, hread⟩
  · simpa only [incidenceEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hfun
  · have hcard := incidenceEdges_card I hL
    have harith : N * (q + 1) + N = N * (q + 2) := by simp [Nat.mul_add, Nat.mul_two, Nat.add_assoc]
    simpa [hcard, harith] using hsize

lemma normalization_of_size {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hsize : N * (q + 2) - 1 ≤ C.size) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) D z =
          decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
            z (Fin.natAdd N l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  obtain ⟨D, hao, hfun, hbound, hread⟩ := plane_read1_upper I hL
  exact ⟨D, hao, hfun, hbound.trans hsize, hread⟩

namespace NoJunk

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

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

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  exact foldl_getD_gate C.gates x j hj

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

def V (C : Circuit) {N : ℕ} (x : Fin N → Bool) (u : ℕ) : Bool := val C (List.ofFn x) u

def in0 (C : Circuit) (k : ℕ) : ℕ := (gateAt C k).inputs.getD 0 0

def in1 (C : Circuit) (k : ℕ) : ℕ := (gateAt C k).inputs.getD 1 0

def oh (N v : ℕ) : Fin N → Bool := fun z => decide (z.val = v)

def th (N u v : ℕ) : Fin N → Bool := fun z => decide (z.val = u ∨ z.val = v)

def S (C : Circuit) (N w : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun v => V C (oh N v) w = true)

def mn (C : Circuit) (N w : ℕ) : ℕ := if h : (S C N w).Nonempty then (S C N w).min' h else 0

def kap (C : Circuit) (N k : ℕ) : ℕ := max (mn C N (in0 C k)) (mn C N (in1 C k))

def adj (n : ℕ) (L : Fin n → Finset (Fin n)) (u v : ℕ) : Prop :=
  ∃ a b : Fin n, a ∈ L b ∧ ((u = a.val ∧ v = n + b.val) ∨ (u = n + b.val ∧ v = a.val))

def stp (C : Circuit) (N : ℕ) (W : Finset ℕ) (u v : ℕ) : Prop :=
  ∃ k < C.gates.length, u = N + k ∧ (gateAt C k).op = GateOp.or ∧ u ∉ W ∧ v ∈ (gateAt C k).inputs

def Rch (C : Circuit) (N : ℕ) (W : Finset ℕ) (v : ℕ) : Prop :=
  Relation.ReflTransGen (stp C N W) C.output v

open Classical in
noncomputable def Aset (C : Circuit) (N : ℕ) (W : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k => (gateAt C k).op = GateOp.and ∧ Rch C N W (N + k))

open Classical in
noncomputable def Tset (C : Circuit) (N : ℕ) (W : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter
    (fun k => (gateAt C k).op = GateOp.or ∧ N + k ∉ W ∧ Rch C N W (N + k))

open Classical in
noncomputable def Oset (C : Circuit) (N : ℕ) (W : Finset ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun k => N + k ∈ W)

lemma V_input (C : Circuit) {N : ℕ} (x : Fin N → Bool) {u : ℕ} (hu : u < N) :
    V C x u = x ⟨u, hu⟩ := by
  unfold V
  rw [val_input (n := N) (by simp) hu]
  simp [List.getD_eq_getElem?_getD, hu]

lemma V_ge (C : Circuit) {N : ℕ} (x : Fin N → Bool) {u : ℕ} (hu : N + C.gates.length ≤ u) :
    V C x u = false := by
  unfold V
  exact val_ge (n := N) (by simp) hu

lemma gate_two {N : ℕ} {C : Circuit} (hAO : PEqualNP.TopForm.IsAO2 N C) {k : ℕ}
    (hk : k < C.gates.length) :
    (gateAt C k).inputs = [in0 C k, in1 C k] ∧ in0 C k < N + k ∧ in1 C k < N + k ∧
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) := by
  have hmem : gateAt C k ∈ C.gates := by rw [gateAt_eq hk]; exact List.getElem_mem hk
  have hl := hAO.2.2 _ hmem
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
  have hr := hAO.2.1 k hk
  have ha := hr a (by simp [hab])
  have hb := hr b (by simp [hab])
  refine ⟨?_, ?_, ?_, hAO.1 _ hmem⟩
  · simp [in0, in1, hab]
  · simpa [in0, hab] using ha
  · simpa [in1, hab] using hb

lemma V_gate {N : ℕ} {C : Circuit} (hAO : PEqualNP.TopForm.IsAO2 N C) {k : ℕ}
    (hk : k < C.gates.length) (x : Fin N → Bool) :
    V C x (N + k) = (gateAt C k).op.eval [V C x (in0 C k), V C x (in1 C k)] := by
  obtain ⟨h2, ha, hb, _⟩ := gate_two hAO hk
  unfold V
  rw [val_gate (n := N) (by simp) hk, ← gateAt_eq hk, h2]
  simp [ha, hb]

lemma V_and {N : ℕ} {C : Circuit} (hAO : PEqualNP.TopForm.IsAO2 N C) {k : ℕ}
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.and) (x : Fin N → Bool) :
    V C x (N + k) = (V C x (in0 C k) && V C x (in1 C k)) := by
  rw [V_gate hAO hk, hop]; simp [GateOp.eval]

lemma V_or {N : ℕ} {C : Circuit} (hAO : PEqualNP.TopForm.IsAO2 N C) {k : ℕ}
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or) (x : Fin N → Bool) :
    V C x (N + k) = (V C x (in0 C k) || V C x (in1 C k)) := by
  rw [V_gate hAO hk, hop]; simp [GateOp.eval]

lemma memS {C : Circuit} {N w v : ℕ} : v ∈ S C N w ↔ v < N ∧ V C (oh N v) w = true := by
  simp [S]

lemma S_or {N : ℕ} {C : Circuit} (hAO : PEqualNP.TopForm.IsAO2 N C) {k : ℕ}
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or) (v : ℕ) :
    v ∈ S C N (N + k) ↔ v ∈ S C N (in0 C k) ∨ v ∈ S C N (in1 C k) := by
  simp only [memS, V_or hAO hk hop, Bool.or_eq_true, and_or_left]

lemma mn_mem {C : Circuit} {N w : ℕ} (h : (S C N w).Nonempty) : mn C N w ∈ S C N w := by
  unfold mn; rw [dite_cond_eq_true (eq_true h)]; exact Finset.min'_mem _ _

lemma mn_le {C : Circuit} {N w v : ℕ} (h : v ∈ S C N w) : mn C N w ≤ v := by
  unfold mn; rw [dite_cond_eq_true (eq_true ⟨v, h⟩)]; exact Finset.min'_le _ _ h

def WH (C : Circuit) (N : ℕ) (W : Finset ℕ) : Prop :=
  ∀ w ∈ W, w < N ∨ ∃ k < C.gates.length, w = N + k ∧ (gateAt C k).op = GateOp.or ∧
    ∀ i ∈ (gateAt C k).inputs, i ∈ W

lemma S_input {C : Circuit} {N w : ℕ} (hw : w < N) (v : ℕ) : v ∈ S C N w ↔ v = w := by
  rw [memS, V_input C _ hw]
  simp [oh]
  omega

lemma disj {N : ℕ} {C : Circuit} {W : Finset ℕ} (hAO : PEqualNP.TopForm.IsAO2 N C)
    (hW : WH C N W) : ∀ w ∈ W, (∀ x : Fin N → Bool, V C x w = true ↔
      ∃ z : Fin N, z.val ∈ S C N w ∧ x z = true) ∧ (S C N w).Nonempty := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hwW
  rcases hW w hwW with hw | ⟨k, hk, rfl, hop, hin⟩
  · refine ⟨fun x => ?_, ⟨w, (S_input hw w).2 rfl⟩⟩
    rw [V_input C x hw]
    constructor
    · intro h; exact ⟨⟨w, hw⟩, (S_input hw w).2 rfl, h⟩
    · rintro ⟨z, hz, hx⟩
      have := (S_input hw _).1 hz
      have e : z = ⟨w, hw⟩ := Fin.ext this
      rw [← e]; exact hx
  · obtain ⟨h2, ha, hb, _⟩ := gate_two hAO hk
    have haW : in0 C k ∈ W := hin _ (by rw [h2]; simp)
    have hbW : in1 C k ∈ W := hin _ (by rw [h2]; simp)
    obtain ⟨IA, NA⟩ := ih _ ha haW
    obtain ⟨IB, _⟩ := ih _ hb hbW
    refine ⟨fun x => ?_, ?_⟩
    · rw [V_or hAO hk hop, Bool.or_eq_true, IA, IB]
      constructor
      · rintro (⟨z, hz, hx⟩ | ⟨z, hz, hx⟩)
        · exact ⟨z, (S_or hAO hk hop _).2 (Or.inl hz), hx⟩
        · exact ⟨z, (S_or hAO hk hop _).2 (Or.inr hz), hx⟩
      · rintro ⟨z, hz, hx⟩
        rcases (S_or hAO hk hop _).1 hz with h | h
        · exact Or.inl ⟨z, h, hx⟩
        · exact Or.inr ⟨z, h, hx⟩
    · obtain ⟨v, hv⟩ := NA
      exact ⟨v, (S_or hAO hk hop _).2 (Or.inl hv)⟩

lemma kill {N : ℕ} {C : Circuit} {W : Finset ℕ} (hAO : PEqualNP.TopForm.IsAO2 N C)
    (hW : WH C N W) : ∀ w ∈ W, ∀ v ∈ S C N w, v ≠ mn C N w →
      ∃ g < C.gates.length, N + g ∈ W ∧ S C N (N + g) ⊆ S C N w ∧ kap C N g = v ∧
        v ≠ mn C N (N + g) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  intro hwW v hv hne
  rcases hW w hwW with hw | ⟨k, hk, rfl, hop, hin⟩
  · exfalso
    have h1 := (S_input hw _).1 hv
    have h2 := (S_input hw _).1 (mn_mem ⟨v, hv⟩)
    exact hne (h1.trans h2.symm)
  · obtain ⟨h2, ha, hb, _⟩ := gate_two hAO hk
    have haW : in0 C k ∈ W := hin _ (by rw [h2]; simp)
    have hbW : in1 C k ∈ W := hin _ (by rw [h2]; simp)
    have subA : S C N (in0 C k) ⊆ S C N (N + k) :=
      fun z hz => (S_or hAO hk hop _).2 (Or.inl hz)
    have subB : S C N (in1 C k) ⊆ S C N (N + k) :=
      fun z hz => (S_or hAO hk hop _).2 (Or.inr hz)
    by_cases c1 : v ∈ S C N (in0 C k) ∧ v ≠ mn C N (in0 C k)
    · obtain ⟨g, hg, hgW, hsub, hk2, hne2⟩ := ih _ ha haW v c1.1 c1.2
      exact ⟨g, hg, hgW, hsub.trans subA, hk2, hne2⟩
    by_cases c2 : v ∈ S C N (in1 C k) ∧ v ≠ mn C N (in1 C k)
    · obtain ⟨g, hg, hgW, hsub, hk2, hne2⟩ := ih _ hb hbW v c2.1 c2.2
      exact ⟨g, hg, hgW, hsub.trans subB, hk2, hne2⟩
    refine ⟨k, hk, hwW, subset_refl _, ?_, hne⟩
    have hm := mn_mem (C := C) (N := N) (w := N + k) ⟨v, hv⟩
    have hmw := mn_le (C := C) (N := N) (w := N + k) hv
    unfold kap
    rcases (S_or hAO hk hop _).1 hv with h | h
    · have e : v = mn C N (in0 C k) := by
        by_contra h'; exact c1 ⟨h, h'⟩
      have l1 := mn_le (subA (mn_mem ⟨v, h⟩))
      rcases (S_or hAO hk hop _).1 hm with h3 | h3
      · have := mn_le h3; omega
      · have := mn_le h3
        have := mn_le (subB (mn_mem ⟨_, h3⟩))
        omega
    · have e : v = mn C N (in1 C k) := by
        by_contra h'; exact c2 ⟨h, h'⟩
      have l1 := mn_le (subB (mn_mem ⟨v, h⟩))
      rcases (S_or hAO hk hop _).1 hm with h3 | h3
      · have := mn_le h3
        have := mn_le (subA (mn_mem ⟨_, h3⟩))
        omega
      · have := mn_le h3; omega

lemma rch_up {N : ℕ} {C : Circuit} {W : Finset ℕ} (hAO : PEqualNP.TopForm.IsAO2 N C)
    {v : ℕ} (hv : Rch C N W v) (x : Fin N → Bool) (h : V C x v = true) :
    V C x C.output = true := by
  induction hv with
  | refl => exact h
  | tail _ hst ih =>
    obtain ⟨k, hk, rfl, hop, _, hin⟩ := hst
    apply ih
    obtain ⟨h2, _, _, _⟩ := gate_two hAO hk
    rw [V_or hAO hk hop, Bool.or_eq_true]
    rw [h2] at hin
    simp at hin
    rcases hin with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h

lemma nr {N : ℕ} {C : Circuit} {W : Finset ℕ} (hAO : PEqualNP.TopForm.IsAO2 N C)
    (hf0 : ∀ v, V C (oh N v) C.output = false) {u : ℕ} (hu : Rch C N W u) (v : ℕ)
    (h : V C (oh N v) u = true) : False := by
  have := rch_up hAO hu _ h
  rw [hf0 v] at this
  exact Bool.false_ne_true this

lemma rch_notW {N : ℕ} {C : Circuit} {W : Finset ℕ} (hAO : PEqualNP.TopForm.IsAO2 N C)
    (hW : WH C N W) (hf0 : ∀ v, V C (oh N v) C.output = false) {u : ℕ} (hu : Rch C N W u)
    (huW : u ∈ W) : False := by
  obtain ⟨v, hv⟩ := (disj hAO hW u huW).2
  exact nr hAO hf0 hu v (memS.1 hv).2

lemma rch_notIn {N : ℕ} {C : Circuit} {W : Finset ℕ} (hAO : PEqualNP.TopForm.IsAO2 N C)
    (hf0 : ∀ v, V C (oh N v) C.output = false) {u : ℕ} (hu : Rch C N W u) (hlt : u < N) :
    False := by
  apply nr hAO hf0 hu u
  rw [V_input C _ hlt]
  simp [oh]

lemma descend {N : ℕ} {C : Circuit} {W : Finset ℕ} (hAO : PEqualNP.TopForm.IsAO2 N C)
    (hW : WH C N W) (hf0 : ∀ v, V C (oh N v) C.output = false) (x : Fin N → Bool) :
    ∀ u, Rch C N W u → V C x u = true → ∃ k ∈ Aset C N W, V C x (N + k) = true := by
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
  intro hu hx
  have h1 : N ≤ u := by
    by_contra h; exact rch_notIn hAO hf0 hu (by omega)
  have h2 : u < N + C.gates.length := by
    by_contra h
    rw [V_ge C x (by omega)] at hx
    exact Bool.false_ne_true hx
  obtain ⟨k, rfl⟩ : ∃ k, u = N + k := ⟨u - N, by omega⟩
  have hk : k < C.gates.length := by omega
  obtain ⟨h2, ha, hb, hop⟩ := gate_two hAO hk
  rcases hop with hop | hop
  · refine ⟨k, ?_, hx⟩
    simp [Aset, hk, hop, hu]
  · have hnW : N + k ∉ W := fun h => rch_notW hAO hW hf0 hu h
    rw [V_or hAO hk hop, Bool.or_eq_true] at hx
    rcases hx with hx | hx
    · exact ih _ ha (Relation.ReflTransGen.tail hu ⟨k, hk, rfl, hop, hnW, by rw [h2]; simp⟩) hx
    · exact ih _ hb (Relation.ReflTransGen.tail hu ⟨k, hk, rfl, hop, hnW, by rw [h2]; simp⟩) hx

lemma card_AT {N : ℕ} {C : Circuit} {W : Finset ℕ} (hAO : PEqualNP.TopForm.IsAO2 N C) :
    (Aset C N W).card ≤ (Tset C N W).card + 1 := by
  classical
  have hdis : Disjoint (Aset C N W) (Tset C N W) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    simp only [Aset, Tset, Finset.mem_filter] at h1 h2
    rw [h1.2.1] at h2
    exact GateOp.noConfusion h2.2.1
  have hsub : Aset C N W ∪ Tset C N W ⊆ insert (C.output - N)
      ((Tset C N W ×ˢ Finset.range 2).image
        (fun p => (gateAt C p.1).inputs.getD p.2 0 - N)) := by
    intro k hk
    have hR : Rch C N W (N + k) := by
      rcases Finset.mem_union.1 hk with h | h
      · simp only [Aset, Finset.mem_filter] at h; exact h.2.2
      · simp only [Tset, Finset.mem_filter] at h; exact h.2.2.2
    rcases Relation.ReflTransGen.cases_tail hR with h | ⟨u, hu, k', hk', rfl, hop, hnW, hin⟩
    · rw [Finset.mem_insert]; left; omega
    · rw [Finset.mem_insert]; right
      rw [Finset.mem_image]
      have hT : k' ∈ Tset C N W := by
        simp only [Tset, Finset.mem_filter, Finset.mem_range]; exact ⟨hk', hop, hnW, hu⟩
      obtain ⟨h2, _, _, _⟩ := gate_two hAO hk'
      rw [h2] at hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with e | e
      · refine ⟨(k', 0), by simp [hT], ?_⟩
        simp only [h2, List.getD_cons_zero]; omega
      · refine ⟨(k', 1), by simp [hT], ?_⟩
        simp only [h2, List.getD_cons_succ, List.getD_cons_zero]; omega
  have c1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at c1
  have c2 := Finset.card_insert_le (C.output - N) ((Tset C N W ×ˢ Finset.range 2).image
        (fun p => (gateAt C p.1).inputs.getD p.2 0 - N))
  have c3 := Finset.card_image_le (s := Tset C N W ×ˢ Finset.range 2)
    (f := fun p => (gateAt C p.1).inputs.getD p.2 0 - N)
  rw [Finset.card_product, Finset.card_range] at c3
  omega

lemma twoF {n : ℕ} {L : Fin n → Finset (Fin n)} (hI : ∀ b b', b ≠ b' → (L b ∩ L b').card ≤ 1)
    {a a' b b' : Fin n} (ha : a ≠ a') (hb : b ≠ b') (h1 : a ∈ L b) (h2 : a ∈ L b')
    (h3 : a' ∈ L b) (h4 : a' ∈ L b') : False := by
  classical
  have hs : ({a, a'} : Finset (Fin n)) ⊆ L b ∩ L b' := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp [*]
  have c := Finset.card_le_card hs
  rw [Finset.card_pair ha] at c
  have := hI b b' hb
  omega

def inc (n : ℕ) (L : Fin n → Finset (Fin n)) (p l : ℕ) : Prop :=
  ∃ a b : Fin n, a ∈ L b ∧ a.val = p ∧ b.val = l

lemma incF {n : ℕ} {L : Fin n → Finset (Fin n)} {p l : ℕ} (h : inc n L p l) (a b : Fin n)
    (ha : a.val = p) (hb : b.val = l) : a ∈ L b := by
  obtain ⟨a1, b1, m, e1, f1⟩ := h
  have x1 : a1 = a := Fin.ext (by omega)
  have x2 : b1 = b := Fin.ext (by omega)
  subst x1 x2
  exact m

lemma twoN {n : ℕ} {L : Fin n → Finset (Fin n)} (hI : ∀ b b', b ≠ b' → (L b ∩ L b').card ≤ 1)
    {p p' l l' : ℕ} (hp : p ≠ p') (hl : l ≠ l') (h1 : inc n L p l) (h2 : inc n L p l')
    (h3 : inc n L p' l) (h4 : inc n L p' l') : False := by
  obtain ⟨a1, b1, m1, e1, f1⟩ := h1
  obtain ⟨a3, b2, m4, e4, f4⟩ := h4
  refine twoF hI (a := a1) (a' := a3) (b := b1) (b' := b2) (by rintro rfl; omega)
    (by rintro rfl; omega) m1 (incF h2 _ _ e1 f4) (incF h3 _ _ e4 f1) m4

lemma adj_symm {n : ℕ} {L : Fin n → Finset (Fin n)} {u v : ℕ} (h : adj n L u v) :
    adj n L v u := by
  obtain ⟨a, b, m, h⟩ := h
  exact ⟨a, b, m, by omega⟩

lemma adj_ne {n : ℕ} {L : Fin n → Finset (Fin n)} {u v : ℕ} (h : adj n L u v) : u ≠ v := by
  obtain ⟨a, b, m, h⟩ := h
  have := a.isLt
  omega

lemma c4 {n : ℕ} {L : Fin n → Finset (Fin n)} (hI : ∀ b b', b ≠ b' → (L b ∩ L b').card ≤ 1)
    {u u' v v' : ℕ} (hu : u ≠ u') (hv : v ≠ v') (h1 : adj n L u v) (h2 : adj n L u v')
    (h3 : adj n L u' v) (h4 : adj n L u' v') : False := by
  obtain ⟨p1, l1, m1, d1⟩ := h1
  obtain ⟨p2, l2, m2, d2⟩ := h2
  obtain ⟨p3, l3, m3, d3⟩ := h3
  obtain ⟨p4, l4, m4, d4⟩ := h4
  have := p1.isLt; have := p2.isLt; have := p3.isLt; have := p4.isLt
  rcases d1 with ⟨e1, f1⟩ | ⟨e1, f1⟩ <;> rcases d2 with ⟨e2, f2⟩ | ⟨e2, f2⟩ <;>
    rcases d3 with ⟨e3, f3⟩ | ⟨e3, f3⟩ <;> rcases d4 with ⟨e4, f4⟩ | ⟨e4, f4⟩ <;>
    first
    | omega
    | exact twoN hI (p := u) (p' := u') (l := v - n) (l' := v' - n) hu (by omega)
        ⟨p1, l1, m1, by omega, by omega⟩ ⟨p2, l2, m2, by omega, by omega⟩
        ⟨p3, l3, m3, by omega, by omega⟩ ⟨p4, l4, m4, by omega, by omega⟩
    | exact twoN hI (p := v) (p' := v') (l := u - n) (l' := u' - n) hv (by omega)
        ⟨p1, l1, m1, by omega, by omega⟩ ⟨p3, l3, m3, by omega, by omega⟩
        ⟨p2, l2, m2, by omega, by omega⟩ ⟨p4, l4, m4, by omega, by omega⟩

def pr (n : ℕ) (e : Fin n × Fin n) (x y : ℕ) : Prop :=
  (x = e.1.val ∧ y = n + e.2.val) ∨ (x = n + e.2.val ∧ y = e.1.val)

lemma pr_inj {n : ℕ} {e e' : Fin n × Fin n} {x y : ℕ} (h : pr n e x y) (h' : pr n e' x y) :
    e = e' := by
  unfold pr at h h'
  have := e.1.isLt; have := e'.1.isLt
  ext <;> omega

lemma pr_swap {n : ℕ} {e : Fin n × Fin n} {x y : ℕ} (h : pr n e x y) : pr n e y x := by
  unfold pr at h ⊢; omega

lemma pr_adj {n : ℕ} {L : Fin n → Finset (Fin n)} {e : Fin n × Fin n} (he : e.1 ∈ L e.2)
    {x y : ℕ} (h : pr n e x y) : adj n L x y := ⟨e.1, e.2, he, h⟩

lemma hf0_of {n : ℕ} {L : Fin n → Finset (Fin n)} {C : Circuit}
    (hf : ∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = decide (∃ a b : Fin n, a ∈ L b ∧
      x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true)) (v : ℕ) :
    V C (oh (n + n) v) C.output = false := by
  have e : V C (oh (n + n) v) C.output = circuitFun (n + n) C (oh (n + n) v) := rfl
  rw [e, hf, decide_eq_false_iff_not]
  rintro ⟨a, b, _, h1, h2⟩
  simp [oh] at h1 h2
  have := a.isLt
  omega

lemma and_adj {n : ℕ} {L : Fin n → Finset (Fin n)} {C : Circuit} {W : Finset ℕ}
    (hAO : PEqualNP.TopForm.IsAO2 (n + n) C) (hW : WH C (n + n) W)
    (hA : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ i ∈ (gateAt C k).inputs, i ∈ W)
    (hf : ∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = decide (∃ a b : Fin n, a ∈ L b ∧
      x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true))
    {k : ℕ} (hk : k ∈ Aset C (n + n) W) {u v : ℕ} (hu : u ∈ S C (n + n) (in0 C k))
    (hv : v ∈ S C (n + n) (in1 C k)) : adj n L u v := by
  simp only [Aset, Finset.mem_filter, Finset.mem_range] at hk
  obtain ⟨hk, hop, hR⟩ := hk
  obtain ⟨h2, _, _, _⟩ := gate_two hAO hk
  have haW : in0 C k ∈ W := hA k hk hop _ (by rw [h2]; simp)
  have hbW : in1 C k ∈ W := hA k hk hop _ (by rw [h2]; simp)
  have hu' := (memS.1 hu).1
  have hv' := (memS.1 hv).1
  have va : V C (th (n + n) u v) (in0 C k) = true :=
    ((disj hAO hW _ haW).1 _).2 ⟨⟨u, hu'⟩, hu, by simp [th]⟩
  have vb : V C (th (n + n) u v) (in1 C k) = true :=
    ((disj hAO hW _ hbW).1 _).2 ⟨⟨v, hv'⟩, hv, by simp [th]⟩
  have vk : V C (th (n + n) u v) (n + n + k) = true := by
    rw [V_and hAO hk hop, va, vb]; rfl
  have vo := rch_up hAO hR _ vk
  have e : V C (th (n + n) u v) C.output = circuitFun (n + n) C (th (n + n) u v) := rfl
  rw [e, hf, decide_eq_true_iff] at vo
  obtain ⟨a, b, m, h1, h2⟩ := vo
  simp [th] at h1 h2
  have := a.isLt
  exact ⟨a, b, m, by omega⟩

lemma pick {n : ℕ} {L : Fin n → Finset (Fin n)} {C : Circuit} {W : Finset ℕ}
    (hAO : PEqualNP.TopForm.IsAO2 (n + n) C) (hW : WH C (n + n) W)
    (hA : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ i ∈ (gateAt C k).inputs, i ∈ W)
    (hf : ∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = decide (∃ a b : Fin n, a ∈ L b ∧
      x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true))
    {e : Fin n × Fin n} (he : e.1 ∈ L e.2) :
    ∃ k ∈ Aset C (n + n) W, ∃ z1 ∈ S C (n + n) (in0 C k), ∃ z2 ∈ S C (n + n) (in1 C k),
      pr n e z1 z2 := by
  have hf0 := hf0_of hf
  set x := th (n + n) e.1.val (n + e.2.val) with hx
  have vo : V C x C.output = true := by
    have e0 : V C x C.output = circuitFun (n + n) C x := rfl
    rw [e0, hf, decide_eq_true_iff]
    exact ⟨e.1, e.2, he, by simp [hx, th], by simp [hx, th]; omega⟩
  obtain ⟨k, hkA, vk⟩ := descend hAO hW hf0 x _ Relation.ReflTransGen.refl vo
  have hkA' := hkA
  simp only [Aset, Finset.mem_filter, Finset.mem_range] at hkA'
  obtain ⟨hk, hop, _⟩ := hkA'
  obtain ⟨h2, _, _, _⟩ := gate_two hAO hk
  have haW : in0 C k ∈ W := hA k hk hop _ (by rw [h2]; simp)
  have hbW : in1 C k ∈ W := hA k hk hop _ (by rw [h2]; simp)
  rw [V_and hAO hk hop, Bool.and_eq_true] at vk
  obtain ⟨z1, hz1, x1⟩ := ((disj hAO hW _ haW).1 x).1 vk.1
  obtain ⟨z2, hz2, x2⟩ := ((disj hAO hW _ hbW).1 x).1 vk.2
  have hne := adj_ne (and_adj (L := L) hAO hW hA hf hkA hz1 hz2)
  simp [hx, th] at x1 x2
  refine ⟨k, hkA, z1, hz1, z2, hz2, ?_⟩
  unfold pr
  omega

lemma oset_or {N : ℕ} {C : Circuit} {W : Finset ℕ} (hW : WH C N W) {k : ℕ}
    (hk : k ∈ Oset C N W) : (gateAt C k).op = GateOp.or := by
  simp only [Oset, Finset.mem_filter, Finset.mem_range] at hk
  rcases hW _ hk.2 with h | ⟨k', _, e, hop, _⟩
  · omega
  · have : k' = k := by omega
    subst this; exact hop

def Good (n : ℕ) (L : Fin n → Finset (Fin n)) (C : Circuit) (W : Finset ℕ)
    (e : Fin n × Fin n) (k : ℕ) : Prop :=
  (k ∈ Aset C (n + n) W ∧ pr n e (mn C (n + n) (in0 C k)) (mn C (n + n) (in1 C k))) ∨
  (k ∈ Oset C (n + n) W ∧ ∃ c, pr n e (kap C (n + n) k) c ∧ adj n L c (mn C (n + n) (n + n + k)) ∧
    kap C (n + n) k ≠ mn C (n + n) (n + n + k))

lemma good_inj {n : ℕ} {L : Fin n → Finset (Fin n)} {C : Circuit} {W : Finset ℕ}
    (hI : ∀ b b', b ≠ b' → (L b ∩ L b').card ≤ 1) (hW : WH C (n + n) W)
    {e e' : Fin n × Fin n} (he : e.1 ∈ L e.2) (he' : e'.1 ∈ L e'.2) {k : ℕ}
    (g1 : Good n L C W e k) (g2 : Good n L C W e' k) : e = e' := by
  rcases g1 with ⟨hA1, p1⟩ | ⟨hO1, c, p1, a1, ne1⟩ <;>
    rcases g2 with ⟨hA2, p2⟩ | ⟨hO2, c', p2, a2, ne2⟩
  · exact pr_inj p1 p2
  · exfalso
    simp only [Aset, Finset.mem_filter] at hA1
    rw [oset_or hW hO2] at hA1
    exact GateOp.noConfusion hA1.2.1
  · exfalso
    simp only [Aset, Finset.mem_filter] at hA2
    rw [oset_or hW hO1] at hA2
    exact GateOp.noConfusion hA2.2.1
  · by_cases hc : c = c'
    · subst hc; exact pr_inj p1 p2
    · exact (c4 hI hc ne1 (adj_symm (pr_adj he p1)) a1 (adj_symm (pr_adj he' p2)) a2).elim

lemma good_ex {n : ℕ} {L : Fin n → Finset (Fin n)} {C : Circuit} {W : Finset ℕ}
    (hAO : PEqualNP.TopForm.IsAO2 (n + n) C) (hW : WH C (n + n) W)
    (hA : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ i ∈ (gateAt C k).inputs, i ∈ W)
    (hf : ∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = decide (∃ a b : Fin n, a ∈ L b ∧
      x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true))
    {e : Fin n × Fin n} (he : e.1 ∈ L e.2) : ∃ k, Good n L C W e k := by
  obtain ⟨k, hkA, z1, hz1, z2, hz2, hp⟩ := pick hAO hW hA hf he
  have hkA' := hkA
  simp only [Aset, Finset.mem_filter, Finset.mem_range] at hkA'
  obtain ⟨hk, hop, _⟩ := hkA'
  obtain ⟨h2, _, _, _⟩ := gate_two hAO hk
  have haW : in0 C k ∈ W := hA k hk hop _ (by rw [h2]; simp)
  have hbW : in1 C k ∈ W := hA k hk hop _ (by rw [h2]; simp)
  by_cases c1 : z1 = mn C (n + n) (in0 C k)
  · by_cases c2 : z2 = mn C (n + n) (in1 C k)
    · rw [c1, c2] at hp
      exact ⟨k, Or.inl ⟨hkA, hp⟩⟩
    · obtain ⟨g, hg, hgW, hsub, hkap, hne⟩ := kill hAO hW _ hbW z2 hz2 c2
      have hmem := hsub (mn_mem (disj hAO hW _ hgW).2)
      refine ⟨g, Or.inr ⟨?_, z1, ?_, and_adj hAO hW hA hf hkA hz1 hmem, ?_⟩⟩
      · simp only [Oset, Finset.mem_filter, Finset.mem_range]; exact ⟨hg, hgW⟩
      · rw [hkap]; exact pr_swap hp
      · rw [hkap]; exact hne
  · obtain ⟨g, hg, hgW, hsub, hkap, hne⟩ := kill hAO hW _ haW z1 hz1 c1
    have hmem := hsub (mn_mem (disj hAO hW _ hgW).2)
    refine ⟨g, Or.inr ⟨?_, z2, ?_, adj_symm (and_adj hAO hW hA hf hkA hmem hz2), ?_⟩⟩
    · simp only [Oset, Finset.mem_filter, Finset.mem_range]; exact ⟨hg, hgW⟩
    · rw [hkap]; exact hp
    · rw [hkap]; exact hne

lemma card_E {n : ℕ} {L : Fin n → Finset (Fin n)} {C : Circuit} {W : Finset ℕ}
    (hI : ∀ b b', b ≠ b' → (L b ∩ L b').card ≤ 1)
    (hAO : PEqualNP.TopForm.IsAO2 (n + n) C) (hW : WH C (n + n) W)
    (hA : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ i ∈ (gateAt C k).inputs, i ∈ W)
    (hf : ∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = decide (∃ a b : Fin n, a ∈ L b ∧
      x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true)) :
    (PEqualNP.HeptadCover.incidences L).card ≤ (Aset C (n + n) W ∪ Oset C (n + n) W).card := by
  classical
  have memI : ∀ e, e ∈ PEqualNP.HeptadCover.incidences L ↔ e.1 ∈ L e.2 := by
    intro e; simp [PEqualNP.HeptadCover.incidences]
  let f : Fin n × Fin n → ℕ := fun e => if h : ∃ k, Good n L C W e k then h.choose else 0
  have fg : ∀ e, e.1 ∈ L e.2 → Good n L C W e (f e) := by
    intro e he
    have h := good_ex hAO hW hA hf he
    simp only [f, dif_pos h]
    exact h.choose_spec
  apply Finset.card_le_card_of_injOn f
  · intro e he
    have g := fg e ((memI e).1 he)
    rw [Finset.mem_coe, Finset.mem_union]
    rcases g with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  · intro e he e' he' hee
    have he1 := (memI e).1 he
    have he2 := (memI e').1 he'
    have g1 := fg e he1
    have g2 := fg e' he2
    rw [hee] at g1
    exact good_inj hI hW he1 he2 g1 g2

lemma card_n {n : ℕ} {L : Fin n → Finset (Fin n)} {C : Circuit} {W : Finset ℕ}
    (hL : ∀ a : Fin n, a ∈ L a) (hI : ∀ b b', b ≠ b' → (L b ∩ L b').card ≤ 1)
    (hAO : PEqualNP.TopForm.IsAO2 (n + n) C) (hW : WH C (n + n) W)
    (hA : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ i ∈ (gateAt C k).inputs, i ∈ W)
    (hf : ∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = decide (∃ a b : Fin n, a ∈ L b ∧
      x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true)) :
    n ≤ (Aset C (n + n) W).card := by
  classical
  let P : Fin n → ℕ → Prop := fun a k => k ∈ Aset C (n + n) W ∧
    ∃ z1 ∈ S C (n + n) (in0 C k), ∃ z2 ∈ S C (n + n) (in1 C k), pr n (a, a) z1 z2
  have ex : ∀ a, ∃ k, P a k := by
    intro a
    obtain ⟨k, hk, z1, h1, z2, h2, hp⟩ := pick hAO hW hA hf (e := (a, a)) (hL a)
    exact ⟨k, hk, z1, h1, z2, h2, hp⟩
  let f : Fin n → ℕ := fun a => (ex a).choose
  have fp : ∀ a, P a (f a) := fun a => (ex a).choose_spec
  have c := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin n)))
    (t := Aset C (n + n) W) f (fun a _ => (fp a).1) (by
      intro a _ a' _ haa
      by_contra hne
      obtain ⟨hk, z1, h1, z2, h2, hp⟩ := fp a
      obtain ⟨_, z1', h1', z2', h2', hp'⟩ := fp a'
      rw [← haa] at h1' h2'
      obtain ⟨p, l, m, d⟩ := and_adj hAO hW hA hf hk h1 h2'
      obtain ⟨p', l', m', d'⟩ := and_adj hAO hW hA hf hk h1' h2
      unfold pr at hp hp'
      simp only at hp hp'
      have := p.isLt; have := p'.isLt; have := a.isLt; have := a'.isLt
      have hne' : a ≠ a' := hne
      have hv : a.val ≠ a'.val := fun h => hne' (Fin.ext h)
      rcases d with ⟨e1, f1⟩ | ⟨e1, f1⟩ <;> rcases d' with ⟨e2, f2⟩ | ⟨e2, f2⟩ <;>
        first
        | omega
        | exact twoF hI hne' hne' (hL a) (incF ⟨p, l, m, rfl, rfl⟩ a a' (by omega) (by omega))
            (incF ⟨p', l', m', rfl, rfl⟩ a' a (by omega) (by omega)) (hL a')
        | exact twoF hI hne' hne' (hL a) (incF ⟨p', l', m', rfl, rfl⟩ a a' (by omega) (by omega))
            (incF ⟨p, l, m, rfl, rfl⟩ a' a (by omega) (by omega)) (hL a'))
  simpa using c

lemma card_all {N : ℕ} {C : Circuit} {W : Finset ℕ} (hW : WH C N W) :
    (Aset C N W).card + (Tset C N W).card + (Oset C N W).card ≤ C.gates.length := by
  classical
  have d1 : Disjoint (Aset C N W) (Tset C N W) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    simp only [Aset, Tset, Finset.mem_filter] at h1 h2
    rw [h1.2.1] at h2
    exact GateOp.noConfusion h2.2.1
  have d2 : Disjoint (Aset C N W ∪ Tset C N W) (Oset C N W) := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    rcases Finset.mem_union.1 h1 with h | h
    · simp only [Aset, Finset.mem_filter] at h
      rw [oset_or hW h2] at h
      exact GateOp.noConfusion h.2.1
    · simp only [Tset, Finset.mem_filter] at h
      simp only [Oset, Finset.mem_filter] at h2
      exact h.2.2.1 h2.2
  have hs : Aset C N W ∪ Tset C N W ∪ Oset C N W ⊆ Finset.range C.gates.length := by
    intro k hk
    simp only [Finset.mem_union, Aset, Tset, Oset, Finset.mem_filter] at hk
    rcases hk with (h | h) | h <;> exact h.1
  have c := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1,
    Finset.card_range] at c
  exact c


lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.EdgeOwnership.coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.EdgeOwnership.coneStep n (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (PEqualNP.EdgeOwnership.coneStep n (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []).getD (w - n) []) := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (PEqualNP.EdgeOwnership.coneStep n (gs.foldl (PEqualNP.EdgeOwnership.coneStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.EdgeOwnership.coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    PEqualNP.EdgeOwnership.InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧
      n + k ∈ (gateAt C j).inputs ∧ (i = k ∨ PEqualNP.EdgeOwnership.InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold PEqualNP.EdgeOwnership.InCone PEqualNP.EdgeOwnership.cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (a : ℕ) : ∀ c,
    PEqualNP.EdgeOwnership.InCone n C a c → a < c ∧ c < C.gates.length := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hac
    obtain ⟨hc, k, hk, _, h3⟩ := (inCone_iff n C a c).1 hac
    rcases h3 with h | h
    · exact ⟨by omega, hc⟩
    · have := ih k hk h
      exact ⟨by omega, hc⟩

lemma inCone_trans (n : ℕ) (C : Circuit) (a b : ℕ) : ∀ c,
    PEqualNP.EdgeOwnership.InCone n C a b → PEqualNP.EdgeOwnership.InCone n C b c →
      PEqualNP.EdgeOwnership.InCone n C a c := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
    intro hab hbc
    obtain ⟨hc, k, hk, hw, h3⟩ := (inCone_iff n C b c).1 hbc
    refine (inCone_iff n C a c).2 ⟨hc, k, hk, hw, Or.inr ?_⟩
    rcases h3 with h | h
    · subst h; exact hab
    · exact ih k hk hab h

def Qg (N : ℕ) (C : Circuit) (g : ℕ) : Prop :=
  ∃ k, (gateAt C k).op = GateOp.and ∧ PEqualNP.EdgeOwnership.InCone N C g k

open Classical in
noncomputable def Wset (N : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range (N + C.gates.length)).filter (fun w => w < N ∨ Qg N C (w - N))

lemma below_of_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hj : PEqualNP.TopForm.junk G C = ∅) (j : ℕ) (hjl : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) : PEqualNP.TopForm.BelowF G C j := by
  intro x hx
  by_contra hF
  have hmem : j ∈ PEqualNP.TopForm.junk G C := by
    unfold PEqualNP.TopForm.junk PEqualNP.TopForm.gatesWhere
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr hjl, hop, hjl, x, hx, ?_⟩
    simpa using hF
  rw [hj] at hmem
  exact absurd hmem (Finset.notMem_empty j)

lemma W_props {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 N C) (htop : PEqualNP.TopForm.TopForm G C)
    (hj : PEqualNP.TopForm.junk G C = ∅) :
    WH C N (Wset N C) ∧
    (∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ i ∈ (gateAt C k).inputs,
      i ∈ Wset N C) := by
  classical
  obtain ⟨hAOnly, hRB, _⟩ := hAO
  have inp : ∀ k < C.gates.length, ∀ i ∈ (gateAt C k).inputs, N ≤ i →
      PEqualNP.EdgeOwnership.InCone N C (i - N) k := by
    intro k hk i hi hNi
    have hlt := hRB k hk i hi
    refine (inCone_iff N C (i - N) k).2 ⟨hk, i - N, by omega, ?_, Or.inl rfl⟩
    have : N + (i - N) = i := by omega
    rw [this]; exact hi
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [Wset, Finset.mem_filter, Finset.mem_range] at hw
    obtain ⟨hwr, hw2⟩ := hw
    by_cases hNw : w < N
    · exact Or.inl hNw
    rcases hw2 with h | ⟨k, hk, hc⟩
    · exact Or.inl h
    right
    have hlt2 := inCone_lt N C (w - N) k hc
    have hgl : w - N < C.gates.length := by omega
    have hor : (gateAt C (w - N)).op = GateOp.and ∨ (gateAt C (w - N)).op = GateOp.or := by
      have hm : gateAt C (w - N) ∈ C.gates := by
        rw [gateAt_eq hgl]; exact List.getElem_mem hgl
      exact hAOnly _ hm
    have hop : (gateAt C (w - N)).op = GateOp.or := by
      rcases hor with ho | ho
      · exact absurd hc (htop (w - N) hgl k hlt2.2 ho (below_of_junk G C hj _ hgl ho) hk)
      · exact ho
    refine ⟨w - N, hgl, by omega, hop, ?_⟩
    intro i hi
    have hil := hRB (w - N) hgl i hi
    simp only [Wset, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    by_cases hNi : i < N
    · exact Or.inl hNi
    · right
      exact ⟨k, hk, inCone_trans N C (i - N) (w - N) k (inp (w - N) hgl i hi (by omega)) hc⟩
  · intro k hk hop i hi
    have hil := hRB k hk i hi
    simp only [Wset, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    by_cases hNi : i < N
    · exact Or.inl hNi
    · exact Or.inr ⟨k, hop, inp k hk i hi (by omega)⟩

lemma card_n2 {n : ℕ} {L : Fin n → Finset (Fin n)} {C : Circuit} {W : Finset ℕ}
    (σ : Equiv.Perm (Fin n))
    (hL : ∀ a : Fin n, a ∈ L (σ a)) (hI : ∀ b b', b ≠ b' → (L b ∩ L b').card ≤ 1)
    (hAO : PEqualNP.TopForm.IsAO2 (n + n) C) (hW : WH C (n + n) W)
    (hA : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ∀ i ∈ (gateAt C k).inputs, i ∈ W)
    (hf : ∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = decide (∃ a b : Fin n, a ∈ L b ∧
      x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true)) :
    n ≤ (Aset C (n + n) W).card := by
  classical
  let P : Fin n → ℕ → Prop := fun a k => k ∈ Aset C (n + n) W ∧
    ∃ z1 ∈ S C (n + n) (in0 C k), ∃ z2 ∈ S C (n + n) (in1 C k), pr n (a, σ a) z1 z2
  have ex : ∀ a, ∃ k, P a k := by
    intro a
    obtain ⟨k, hk, z1, h1, z2, h2, hp⟩ := pick hAO hW hA hf (e := (a, σ a)) (hL a)
    exact ⟨k, hk, z1, h1, z2, h2, hp⟩
  let f : Fin n → ℕ := fun a => (ex a).choose
  have fp : ∀ a, P a (f a) := fun a => (ex a).choose_spec
  have c := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin n)))
    (t := Aset C (n + n) W) f (fun a _ => (fp a).1) (by
      intro a _ a2 _ haa
      by_contra hne
      obtain ⟨hk, z1, h1, z2, h2, hp⟩ := fp a
      obtain ⟨_, y1, g1, y2, g2, hq⟩ := fp a2
      rw [← haa] at g1 g2
      obtain ⟨p, l, m, d⟩ := and_adj hAO hW hA hf hk h1 g2
      obtain ⟨p2, l2, m2, d2⟩ := and_adj hAO hW hA hf hk g1 h2
      unfold pr at hp hq
      simp only at hp hq
      have := p.isLt; have := p2.isLt; have := a.isLt; have := a2.isLt
      have := (σ a).isLt; have := (σ a2).isLt
      have hne2 : a ≠ a2 := hne
      have hs : σ a ≠ σ a2 := fun h => hne2 (σ.injective h)
      rcases d with ⟨e1, f1⟩ | ⟨e1, f1⟩ <;> rcases d2 with ⟨e2, f2⟩ | ⟨e2, f2⟩ <;>
        first
        | omega
        | exact twoF hI hne2 hs (hL a) (incF ⟨p, l, m, rfl, rfl⟩ a (σ a2) (by omega) (by omega))
            (incF ⟨p2, l2, m2, rfl, rfl⟩ a2 (σ a) (by omega) (by omega)) (hL a2)
        | exact twoF hI hne2 hs (hL a) (incF ⟨p2, l2, m2, rfl, rfl⟩ a (σ a2) (by omega) (by omega))
            (incF ⟨p, l, m, rfl, rfl⟩ a2 (σ a) (by omega) (by omega)) (hL a2))
  simpa using c

lemma finish (n : ℕ) (E : Finset (Fin n × Fin n)) (σ : Equiv.Perm (Fin n))
    (G : SimpleGraph (Fin (n + n))) [DecidableRel G.Adj] (C : Circuit)
    (rect : ∀ (a b c d : Fin n), a ≠ b → c ≠ d →
      ¬((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E))
    (perm : ∀ a : Fin n, (a, σ a) ∈ E)
    (hadj : ∀ (u v : Fin (n + n)), G.Adj u v ↔ ∃ (p : Fin n) (l : Fin n), (p, l) ∈ E ∧
      (u = Fin.castAdd n p ∧ v = Fin.natAdd n l ∨ v = Fin.castAdd n p ∧ u = Fin.natAdd n l))
    (hAO : PEqualNP.TopForm.IsAO2 (n + n) C)
    (hfun : circuitFun (n + n) C = graphFun G ∅)
    (htop : PEqualNP.TopForm.TopForm G C)
    (hjunk : PEqualNP.TopForm.junk G C = ∅) :
    E.card + n ≤ C.size + 1 := by
  classical
  let L : Fin n → Finset (Fin n) := fun l => Finset.univ.filter (fun p => (p, l) ∈ E)
  have memL : ∀ p l, p ∈ L l ↔ (p, l) ∈ E := by intro p l; simp [L]
  have hf : ∀ x : Fin (n + n) → Bool, circuitFun (n + n) C x = decide (∃ a b : Fin n, a ∈ L b ∧
      x (Fin.castAdd n a) = true ∧ x (Fin.natAdd n b) = true) := by
    intro x
    rw [hfun]
    unfold graphFun
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false,
      false_or]
    constructor
    · rintro ⟨u, v, huv, hu, hv⟩
      obtain ⟨p, l, hpl, h⟩ := (hadj u v).1 huv
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨p, l, (memL p l).2 hpl, hu, hv⟩
      · exact ⟨p, l, (memL p l).2 hpl, hv, hu⟩
    · rintro ⟨a, b, hab, ha, hb⟩
      exact ⟨Fin.castAdd n a, Fin.natAdd n b,
        (hadj _ _).2 ⟨a, b, (memL a b).1 hab, Or.inl ⟨rfl, rfl⟩⟩, ha, hb⟩
  have hI : ∀ b b', b ≠ b' → (L b ∩ L b').card ≤ 1 := by
    intro b b2 hbb
    rw [Finset.card_le_one]
    intro p hp q hq
    by_contra hpq
    rw [Finset.mem_inter, memL, memL] at hp hq
    exact rect p q b b2 hpq hbb ⟨hp.1, hp.2, hq.1, hq.2⟩
  have hL : ∀ a : Fin n, a ∈ L (σ a) := fun a => (memL a (σ a)).2 (perm a)
  obtain ⟨hW, hA⟩ := W_props G C hAO htop hjunk
  have hinc : PEqualNP.HeptadCover.incidences L = E := by
    ext ⟨p, l⟩
    simp [PEqualNP.HeptadCover.incidences, L]
  have e1 := card_E hI hAO hW hA hf
  have e2 := card_n2 σ hL hI hAO hW hA hf
  have e3 := card_AT (W := Wset (n + n) C) hAO
  have e4 := Finset.card_union_le (Aset C (n + n) (Wset (n + n) C))
    (Oset C (n + n) (Wset (n + n) C))
  have e5 := card_all hW
  rw [hinc] at e1
  show _ ≤ C.gates.length + 1
  omega

end NoJunk


namespace NoJunk

open PEqualNP.CircuitLowerBounds

def planeEdges {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] :
    Finset (Fin N × Fin N) := Finset.univ.filter fun e => I e.1 e.2

lemma planeEdges_card {N q : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    (planeEdges I).card = N * (q + 1) := by
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
  have heq : planeEdges I = Finset.univ.biUnion F := by
    ext e
    simp only [planeEdges, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, hF]
    exact ⟨fun h => ⟨e.2, h, rfl⟩, fun ⟨l, hi, he⟩ => he ▸ hi⟩
  rw [heq, Finset.card_biUnion]
  · simp [F, hL]
  · intro l _ l' _ hne
    refine Finset.disjoint_left.mpr ?_
    intro e he he'
    exact hne (((hF l e).mp he).2.symm.trans ((hF l' e).mp he').2)

lemma plane_noJunk_lower {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (σ : Equiv.Perm (Fin N)) (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj]
    (C : Circuit)
    (hL : ∀ l, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hMatch : ∀ p, I p (σ p))
    (hAdj : ∀ u v, G.Adj u v ↔ ∃ p l : Fin N, I p l ∧
      (u = Fin.castAdd N p ∧ v = Fin.natAdd N l ∨
       v = Fin.castAdd N p ∧ u = Fin.natAdd N l))
    (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hfun : PEqualNP.MetaComplexity.circuitFun (N + N) C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅)
    (hTop : PEqualNP.TopForm.TopForm G C)
    (hJunk : PEqualNP.TopForm.junk G C = ∅) :
    N * (q + 2) - 1 ≤ C.size := by
  let E := planeEdges I
  have hmem (p l : Fin N) : (p,l) ∈ E ↔ I p l := by simp [E, planeEdges]
  have hRect : ∀ (p p' l l' : Fin N), p ≠ p' → l ≠ l' →
      ¬((p,l) ∈ E ∧ (p,l') ∈ E ∧ (p',l) ∈ E ∧ (p',l') ∈ E) := by
    intro p p' l l' hp hl ⟨hpl,hpl',hp'l,hp'l'⟩
    obtain ⟨w,_,hu⟩ := hU p p' hp
    exact hl ((hu l ⟨(hmem _ _).mp hpl,(hmem _ _).mp hp'l⟩).trans
      (hu l' ⟨(hmem _ _).mp hpl',(hmem _ _).mp hp'l'⟩).symm)
  have hCard : E.card = N * (q + 1) := planeEdges_card I hL
  have hBound := finish N E σ G C hRect (by simpa only [hmem] using hMatch)
    (by simpa only [hmem] using hAdj) hAO hfun hTop hJunk
  have hEq : N * (q + 2) = N * (q + 1) + N := by
    simp [Nat.mul_add, Nat.mul_two, Nat.add_assoc]
  rw [hCard] at hBound
  omega

end NoJunk

lemma normalization_of_topForm_noJunk
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hL : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hU : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hAO : PEqualNP.TopForm.IsAO2 (N + N) C)
    (hcompute : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true))
    (hAdj : ∀ u v, G.Adj u v ↔ ∃ p l : Fin N, I p l ∧
      (u = Fin.castAdd N p ∧ v = Fin.natAdd N l ∨
       v = Fin.castAdd N p ∧ u = Fin.natAdd N l))
    (hTop : PEqualNP.TopForm.TopForm G C)
    (hJunk : PEqualNP.TopForm.junk G C = ∅) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 (N + N) D ∧
      (∀ y : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) D y =
          decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧
            y (Fin.natAdd N l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  have hfun : PEqualNP.MetaComplexity.circuitFun (N + N) C =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
    funext z
    rw [hcompute z]
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
      false_and, exists_false, decide_false, Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨p, l, hI, hp, hl⟩
      exact ⟨Fin.castAdd N p, Fin.natAdd N l,
        (hAdj _ _).mpr ⟨p, l, hI, Or.inl ⟨rfl, rfl⟩⟩, hp, hl⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      obtain ⟨p, l, hI, h | h⟩ := (hAdj u v).mp huv
      · exact ⟨p, l, hI, h.1 ▸ hu, h.2 ▸ hv⟩
      · exact ⟨p, l, hI, h.1 ▸ hv, h.2 ▸ hu⟩
  obtain ⟨σ, hσ⟩ := plane_incidence_perm q N I hq hN hL hU
  exact normalization_of_size I C hL
    (NoJunk.plane_noJunk_lower I σ G C hL hU hσ hAdj hAO hfun hTop hJunk)

end PEqualNP.Outside.L_meta_2583
