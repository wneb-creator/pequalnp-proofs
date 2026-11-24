import Mathlib.Algebra.Order.BigOperators.Group.Finset
import PEqualNP.Defs.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_5324_aux

open PEqualNP.CircuitLowerBounds

def orStepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma or_append_relation (a b c : List Bool) (x y z : Bool)
    (hab : a.length = b.length) (hac : a.length = c.length)
    (h : ∀ i, c.getD i false = true ↔ a.getD i false = true ∨ b.getD i false = true)
    (hxyz : z = true ↔ x = true ∨ y = true) :
    ∀ i, (c ++ [z]).getD i false = true ↔
      (a ++ [x]).getD i false = true ∨ (b ++ [y]).getD i false = true := by
  intro i
  by_cases hi : i < a.length
  · have hib : i < b.length := hab ▸ hi
    have hic : i < c.length := hac ▸ hi
    simpa only [List.getD, List.getElem?_append_left hi,
      List.getElem?_append_left hib, List.getElem?_append_left hic] using h i
  · have hia : a.length ≤ i := Nat.le_of_not_gt hi
    have hib : b.length ≤ i := hab ▸ hia
    have hic : c.length ≤ i := hac ▸ hia
    simp only [List.getD, List.getElem?_append_right hia,
      List.getElem?_append_right hib, List.getElem?_append_right hic]
    rw [← hab, ← hac]
    by_cases he : i - a.length = 0
    · simp [he,hxyz]
    · have hge : 1 ≤ i - a.length := Nat.one_le_iff_ne_zero.mpr he
      have hx : ([x] : List Bool)[i - a.length]? = none :=
        List.getElem?_eq_none (by simpa using hge)
      have hy : ([y] : List Bool)[i - a.length]? = none :=
        List.getElem?_eq_none (by simpa using hge)
      have hz : ([z] : List Bool)[i - a.length]? = none :=
        List.getElem?_eq_none (by simpa using hge)
      simp [hx,hy,hz]

lemma or_fold_relation (gs : List Gate) (hall : ∀ g ∈ gs, g.op = .or)
    (a b c : List Bool) (hab : a.length = b.length) (hac : a.length = c.length)
    (h : ∀ i, c.getD i false = true ↔ a.getD i false = true ∨ b.getD i false = true) :
    ∀ i, (gs.foldl orStepWire c).getD i false = true ↔
      (gs.foldl orStepWire a).getD i false = true ∨
      (gs.foldl orStepWire b).getD i false = true := by
  induction gs generalizing a b c with
  | nil => exact h
  | cons g gs ih =>
    have hg : g.op = .or := hall g (by simp)
    have hgs : ∀ u ∈ gs, u.op = .or := fun u hu => hall u (by simp [hu])
    apply ih hgs (orStepWire a g) (orStepWire b g) (orStepWire c g)
      (by simp [orStepWire,hab]) (by simp [orStepWire,hac])
    apply or_append_relation a b c _ _ _ hab hac h
    simp only [hg, GateOp.eval, List.any_map, Function.comp_apply, id_eq, List.any_eq_true]
    constructor
    · rintro ⟨i,hi,hic⟩
      rcases (h i).mp hic with hia | hib
      · exact Or.inl ⟨i,hi,hia⟩
      · exact Or.inr ⟨i,hi,hib⟩
    · rintro (⟨i,hi,hia⟩ | ⟨i,hi,hib⟩)
      · exact ⟨i,hi,(h i).mpr (Or.inl hia)⟩
      · exact ⟨i,hi,(h i).mpr (Or.inr hib)⟩

lemma or_wires_join (n : ℕ) (C : Circuit) (hall : ∀ g ∈ C.gates, g.op = .or)
    (x y : Fin n → Bool) (w : ℕ) :
    (C.wires (List.ofFn fun i => x i || y i)).getD w false = true ↔
      (C.wires (List.ofFn x)).getD w false = true ∨
      (C.wires (List.ofFn y)).getD w false = true := by
  apply or_fold_relation C.gates hall (List.ofFn x) (List.ofFn y)
    (List.ofFn fun i => x i || y i) (by simp) (by simp)
  intro i
  by_cases hi : i < n
  · simp [List.getD,hi]
  · have hn : n ≤ i := Nat.le_of_not_gt hi
    simp [List.getD, List.getElem?_eq_none (by simpa using hn :
      (List.ofFn x).length ≤ i), List.getElem?_eq_none (by simpa using hn :
      (List.ofFn y).length ≤ i), List.getElem?_eq_none (by simpa using hn :
      (List.ofFn fun i => x i || y i).length ≤ i)]

lemma or_wires_pair (n : ℕ) (C : Circuit) (hall : ∀ g ∈ C.gates, g.op = .or)
    (a b : Fin n) (w : ℕ) :
    (C.wires (List.ofFn fun i => decide (i = a ∨ i = b))).getD w false = true ↔
      (C.wires (List.ofFn fun i => decide (i = a))).getD w false = true ∨
      (C.wires (List.ofFn fun i => decide (i = b))).getD w false = true := by
  simpa using or_wires_join n C hall (fun i => decide (i = a))
    (fun i => decide (i = b)) w

lemma left_right_ne {n m : ℕ} (a : Fin n) (b : Fin m) :
    Fin.castAdd m a ≠ Fin.natAdd n b := by
  intro h
  have hv := congrArg Fin.val h
  change a.val = n + b.val at hv
  have ha := a.isLt
  omega

lemma right_left_ne {n m : ℕ} (a : Fin n) (b : Fin m) :
    Fin.natAdd n b ≠ Fin.castAdd m a := (left_right_ne a b).symm

lemma pair_incidence {n m : ℕ} (E : Finset (Fin n × Fin m))
    (a : Fin n) (b : Fin m) :
    (∃ p l, (p,l) ∈ E ∧
      decide (Fin.castAdd m p = Fin.castAdd m a ∨ Fin.castAdd m p = Fin.natAdd n b) = true ∧
      decide (Fin.natAdd n l = Fin.castAdd m a ∨ Fin.natAdd n l = Fin.natAdd n b) = true) ↔
      (a,b) ∈ E := by
  simp only [decide_eq_true_eq]
  simp only [left_right_ne, right_left_ne, or_false, false_or]
  constructor
  · rintro ⟨p,l,he,hp,hl⟩
    have hp' : p = a := Fin.ext (congrArg (fun v : Fin (n+m) => v.val) hp)
    have hl' : l = b := Fin.ext (Nat.add_left_cancel (congrArg (fun v : Fin (n+m) => v.val) hl))
    simpa [hp',hl'] using he
  · intro he
    exact ⟨a,b,he,rfl,rfl⟩

lemma left_pair_no_incidence {n m : ℕ} (E : Finset (Fin n × Fin m))
    (a b : Fin n) :
    ¬ ∃ p l, (p,l) ∈ E ∧
      decide (Fin.castAdd m p = Fin.castAdd m a ∨ Fin.castAdd m p = Fin.castAdd m b) = true ∧
      decide (Fin.natAdd n l = Fin.castAdd m a ∨ Fin.natAdd n l = Fin.castAdd m b) = true := by
  simp [right_left_ne]

lemma right_pair_no_incidence {n m : ℕ} (E : Finset (Fin n × Fin m))
    (a b : Fin m) :
    ¬ ∃ p l, (p,l) ∈ E ∧
      decide (Fin.castAdd m p = Fin.natAdd n a ∨ Fin.castAdd m p = Fin.natAdd n b) = true ∧
      decide (Fin.natAdd n l = Fin.natAdd n a ∨ Fin.natAdd n l = Fin.natAdd n b) = true := by
  simp [left_right_ne]

lemma safe_pair_covers_at_most_one_matching {n m : ℕ}
    (E M : Finset (Fin n × Fin m))
    (h4 : ∀ a b : Fin n, ∀ c d : Fin m, a ≠ b → c ≠ d →
      ¬ ((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E))
    (hrow : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hcol : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (A C : Finset (Fin n)) (B D : Finset (Fin m))
    (hleft : ∀ a ∈ A, ∀ c ∈ C, False)
    (hAD : ∀ a ∈ A, ∀ d ∈ D, (a, d) ∈ E)
    (hCB : ∀ c ∈ C, ∀ b ∈ B, (c, b) ∈ E) :
    (M.filter fun e => (e.1 ∈ A ∧ e.2 ∈ D) ∨
      (e.1 ∈ C ∧ e.2 ∈ B)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨heM,he⟩ := Finset.mem_filter.mp he
  obtain ⟨hfM,hf⟩ := Finset.mem_filter.mp hf
  by_contra hef
  have hr : e.1 ≠ f.1 := fun h => hef (hrow e heM f hfM h)
  have hc : e.2 ≠ f.2 := fun h => hef (hcol e heM f hfM h)
  rcases he with ⟨hea,hed⟩ | ⟨hec,heb⟩
  · rcases hf with ⟨hfa,hfd⟩ | ⟨hfc,hfb⟩
    · exact h4 e.1 f.1 e.2 f.2 hr hc
        ⟨hAD _ hea _ hed,hAD _ hea _ hfd,hAD _ hfa _ hed,hAD _ hfa _ hfd⟩
    · exact hleft _ hea _ hfc
  · rcases hf with ⟨hfa,hfd⟩ | ⟨hfc,hfb⟩
    · exact hleft _ hfa _ hec
    · exact h4 e.1 f.1 e.2 f.2 hr hc
        ⟨hCB _ hec _ heb,hCB _ hec _ hfb,hCB _ hfc _ heb,hCB _ hfc _ hfb⟩

lemma safe_pair_family_matching_bound {n m : ℕ} {ι : Type*} [DecidableEq ι]
    (E M : Finset (Fin n × Fin m)) (T : Finset ι)
    (h4 : ∀ a b : Fin n, ∀ c d : Fin m, a ≠ b → c ≠ d →
      ¬ ((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E))
    (hrow : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hcol : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (A C : ι → Finset (Fin n)) (B D : ι → Finset (Fin m))
    (hleft : ∀ t ∈ T, ∀ a ∈ A t, ∀ c ∈ C t, False)
    (hAD : ∀ t ∈ T, ∀ a ∈ A t, ∀ d ∈ D t, (a, d) ∈ E)
    (hCB : ∀ t ∈ T, ∀ c ∈ C t, ∀ b ∈ B t, (c, b) ∈ E)
    (hcover : ∀ e ∈ M, ∃ t ∈ T,
      (e.1 ∈ A t ∧ e.2 ∈ D t) ∨ (e.1 ∈ C t ∧ e.2 ∈ B t)) :
    M.card ≤ T.card := by
  let U (t : ι) := M.filter fun e =>
    (e.1 ∈ A t ∧ e.2 ∈ D t) ∨ (e.1 ∈ C t ∧ e.2 ∈ B t)
  have hsub : M ⊆ T.biUnion U := by
    intro e he
    obtain ⟨t,ht,hcov⟩ := hcover e he
    exact Finset.mem_biUnion.mpr ⟨t,ht,Finset.mem_filter.mpr ⟨he,hcov⟩⟩
  have hcard : ∀ t ∈ T, (U t).card ≤ 1 := by
    intro t ht
    exact safe_pair_covers_at_most_one_matching E M h4 hrow hcol
      (A t) (C t) (B t) (D t) (hleft t ht) (hAD t ht) (hCB t ht)
  calc
    M.card ≤ (T.biUnion U).card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ T, (U t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ T, 1 := Finset.sum_le_sum hcard
    _ = T.card := by simp

lemma or_circuit_matching_bound {n m : ℕ}
    (E M : Finset (Fin n × Fin m)) (C : Circuit) (T : Finset (ℕ × ℕ))
    (h4 : ∀ a b : Fin n, ∀ c d : Fin m, a ≠ b → c ≠ d →
      ¬ ((a, c) ∈ E ∧ (a, d) ∈ E ∧ (b, c) ∈ E ∧ (b, d) ∈ E))
    (hall : ∀ g ∈ C.gates, g.op = .or)
    (hsafe : ∀ t ∈ T, ∀ x : Fin (n+m) → Bool,
      (C.wires (List.ofFn x)).getD t.1 false = true →
      (C.wires (List.ofFn x)).getD t.2 false = true →
      ∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd m a) = true ∧ x (Fin.natAdd n b) = true)
    (hrow : ∀ e ∈ M, ∀ f ∈ M, e.1 = f.1 → e = f)
    (hcol : ∀ e ∈ M, ∀ f ∈ M, e.2 = f.2 → e = f)
    (hcover : ∀ e ∈ M, ∃ t ∈ T,
      (C.wires (List.ofFn fun i => decide (i = Fin.castAdd m e.1 ∨
        i = Fin.natAdd n e.2))).getD t.1 false = true ∧
      (C.wires (List.ofFn fun i => decide (i = Fin.castAdd m e.1 ∨
        i = Fin.natAdd n e.2))).getD t.2 false = true) : M.card ≤ T.card := by
  let L (w : ℕ) : Finset (Fin n) := Finset.univ.filter fun a =>
    (C.wires (List.ofFn fun i => decide (i = Fin.castAdd m a))).getD w false = true
  let R (w : ℕ) : Finset (Fin m) := Finset.univ.filter fun a =>
    (C.wires (List.ofFn fun i => decide (i = Fin.natAdd n a))).getD w false = true
  have noLL : ∀ t ∈ T, ∀ a ∈ L t.1, ∀ b ∈ L t.2, False := by
    intro t ht a ha b hb
    have h1 := (Finset.mem_filter.mp ha).2
    have h2 := (Finset.mem_filter.mp hb).2
    apply left_pair_no_incidence E a b
    apply hsafe t ht (fun i => decide (i = Fin.castAdd m a ∨ i = Fin.castAdd m b))
    · exact (or_wires_pair (n+m) C hall _ _ t.1).mpr (Or.inl h1)
    · exact (or_wires_pair (n+m) C hall _ _ t.2).mpr (Or.inr h2)
  have noRR : ∀ t ∈ T, ∀ a ∈ R t.1, ∀ b ∈ R t.2, False := by
    intro t ht a ha b hb
    have h1 := (Finset.mem_filter.mp ha).2
    have h2 := (Finset.mem_filter.mp hb).2
    apply right_pair_no_incidence E a b
    apply hsafe t ht (fun i => decide (i = Fin.natAdd n a ∨ i = Fin.natAdd n b))
    · exact (or_wires_pair (n+m) C hall _ _ t.1).mpr (Or.inl h1)
    · exact (or_wires_pair (n+m) C hall _ _ t.2).mpr (Or.inr h2)
  apply safe_pair_family_matching_bound E M T h4 hrow hcol
    (fun t => L t.1) (fun t => L t.2) (fun t => R t.1) (fun t => R t.2) noLL
  · intro t ht a ha b hb
    have h1 := (Finset.mem_filter.mp ha).2
    have h2 := (Finset.mem_filter.mp hb).2
    apply (pair_incidence E a b).mp
    apply hsafe t ht (fun i => decide (i = Fin.castAdd m a ∨ i = Fin.natAdd n b))
    · exact (or_wires_pair (n+m) C hall _ _ t.1).mpr (Or.inl h1)
    · exact (or_wires_pair (n+m) C hall _ _ t.2).mpr (Or.inr h2)
  · intro t ht a ha b hb
    have h2 := (Finset.mem_filter.mp ha).2
    have h1 := (Finset.mem_filter.mp hb).2
    apply (pair_incidence E a b).mp
    apply hsafe t ht (fun i => decide (i = Fin.castAdd m a ∨ i = Fin.natAdd n b))
    · exact (or_wires_pair (n+m) C hall _ _ t.1).mpr (Or.inr h1)
    · exact (or_wires_pair (n+m) C hall _ _ t.2).mpr (Or.inl h2)
  · intro e he
    obtain ⟨t,ht,h1,h2⟩ := hcover e he
    refine ⟨t,ht,?_⟩
    rcases (or_wires_pair (n+m) C hall _ _ t.1).mp h1 with hL1 | hR1
    · have hL1' : e.1 ∈ L t.1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hL1⟩
      rcases (or_wires_pair (n+m) C hall _ _ t.2).mp h2 with hL2 | hR2
      · exact (noLL t ht e.1 hL1' e.1 (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,hL2⟩)).elim
      · exact Or.inl ⟨hL1',Finset.mem_filter.mpr ⟨Finset.mem_univ _,hR2⟩⟩
    · have hR1' : e.2 ∈ R t.1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hR1⟩
      rcases (or_wires_pair (n+m) C hall _ _ t.2).mp h2 with hL2 | hR2
      · exact Or.inr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hL2⟩,hR1'⟩
      · exact (noRR t ht e.2 hR1' e.2 (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,hR2⟩)).elim

end PEqualNP.Outside.L_meta_5324_aux
