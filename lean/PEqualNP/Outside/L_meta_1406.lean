import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_1406_aux
open PEqualNP.CircuitLowerBounds

lemma biclique_center {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (A B : Finset (Fin n)) (hA : A.Nonempty) (hB : B.Nonempty)
    (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    ∃ z : Fin n, ∀ a ∈ A, ∀ b ∈ B, a = z ∨ b = z := by
  classical
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  by_cases h : ∀ c ∈ A, c = a
  · exact ⟨a, fun c hc _ _ => Or.inl (h c hc)⟩
  · push_neg at h
    obtain ⟨c, hc, hca⟩ := h
    refine ⟨b, fun u hu v hv => Or.inr ?_⟩
    by_contra hvb
    exact h4 a b c v (Ne.symm hca) (Ne.symm hvb)
      ⟨hab a ha b hb, (hab c hc b hb).symm, hab c hc v hv, (hab a ha v hv).symm⟩

noncomputable def bareGate {n : ℕ} (w : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  by classical exact if g.op = GateOp.or then (g.inputs.map (fun i => w.getD i ∅)).foldr (· ∪ ·) ∅ else ∅

noncomputable def bareStep {n : ℕ} (w : List (Finset (Fin n))) (g : Gate) : List (Finset (Fin n)) :=
  w ++ [bareGate w g]

noncomputable def bareWires (n : ℕ) (gates : List Gate) : List (Finset (Fin n)) :=
  gates.foldl bareStep (List.ofFn (fun i : Fin n => {i}))

def realStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

lemma append_relation {α β : Type*} (xs : List α) (ys : List β) (da : α) (db : β)
    (R : α → β → Prop) (hlen : xs.length = ys.length)
    (h : ∀ i, R (xs.getD i da) (ys.getD i db)) (a : α) (b : β)
    (hab : R a b) (hdefault : R da db) :
    ∀ i, R ((xs ++ [a]).getD i da) ((ys ++ [b]).getD i db) := by
  intro i
  by_cases hil : i < xs.length
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_append, ← hlen, hil] using h i
  · by_cases hie : i = xs.length
    · subst i
      simpa [List.getD_eq_getElem?_getD, List.getElem?_append, ← hlen] using hab
    · simpa [List.getD_eq_getElem?_getD, List.getElem?_append, ← hlen, hil,
        List.getElem?_singleton, show i - xs.length ≠ 0 by omega] using hdefault

lemma real_length (gs : List Gate) (w : List Bool) :
    (gs.foldl realStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, realStep]; omega

lemma bare_length {n : ℕ} (gs : List Gate) (w : List (Finset (Fin n))) :
    (gs.foldl bareStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, bareStep]; omega

lemma mem_union_fold {n : ℕ} (ss : List (Finset (Fin n))) (u : Fin n) :
    u ∈ ss.foldr (· ∪ ·) ∅ ↔ ∃ A ∈ ss, u ∈ A := by
  induction ss with
  | nil => simp
  | cons A ss ih => simp [ih]

def supportValue {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ u ∈ A, x u = true)

lemma supportValue_true {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) :
    supportValue A x = true ↔ ∃ u ∈ A, x u = true := by simp [supportValue]

lemma supportValue_empty {n : ℕ} (x : Fin n → Bool) : supportValue ∅ x = false := by
  simp [supportValue]

lemma bare_gate_sound {n : ℕ} (s : List (Finset (Fin n))) (w : List Bool)
    (x : Fin n → Bool) (g : Gate)
    (h : ∀ i, ∀ u ∈ s.getD i ∅, x u = true → w.getD i false = true) :
    ∀ u ∈ bareGate s g, x u = true → g.op.eval (g.inputs.map (fun i => w.getD i false)) = true := by
  classical
  intro u hu hux
  by_cases hg : g.op = GateOp.or
  · simp only [bareGate, hg, if_true, mem_union_fold, List.mem_map] at hu
    obtain ⟨A, ⟨j, hj, rfl⟩, hu⟩ := hu
    simp only [hg, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    exact ⟨j, hj, h j u hu hux⟩
  · simp [bareGate, hg] at hu

lemma bare_fold_sound {n : ℕ} (gs : List Gate) (s : List (Finset (Fin n)))
    (w : List Bool) (x : Fin n → Bool) (hlen : s.length = w.length)
    (h : ∀ i, ∀ u ∈ s.getD i ∅, x u = true → w.getD i false = true) :
    ∀ i, ∀ u ∈ (gs.foldl bareStep s).getD i ∅,
      x u = true → (gs.foldl realStep w).getD i false = true := by
  induction gs generalizing s w with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    · simp [bareStep, realStep, hlen]
    · apply append_relation s w ∅ false
        (fun A b => ∀ u ∈ A, x u = true → b = true) hlen h
      · exact bare_gate_sound s w x g h
      · simp

lemma bare_sound {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    ∀ i, ∀ u ∈ (bareWires n gs).getD i ∅, x u = true →
      (gs.foldl realStep (List.ofFn x)).getD i false = true := by
  apply bare_fold_sound
  · simp
  · intro i
    by_cases hi : i < n
    · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi]
    · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi]

lemma real_read_old (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl realStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [realStep]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma real_split (gs : List Gate) (w : List Bool) (i : ℕ) :
    gs.foldl realStep w = (gs.drop i).foldl realStep ((gs.take i).foldl realStep w) := by
  simpa only [List.foldl_append] using
    congrArg (fun ls : List Gate => ls.foldl realStep w) (List.take_append_drop i gs).symm

lemma gate_read {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin gs.length) :
    (gs.foldl realStep (List.ofFn x)).getD (n + i.val) false =
      (gs.get i).op.eval ((gs.get i).inputs.map (fun j =>
        ((gs.take i.val).foldl realStep (List.ofFn x)).getD j false)) := by
  rw [real_split gs _ (i.val + 1), real_read_old]
  · rw [List.take_succ_eq_append_getElem i.isLt, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, realStep]
    have hl : ((gs.take i.val).foldl realStep (List.ofFn x)).length = n + i.val := by
      simp [real_length, Nat.min_eq_left (Nat.le_of_lt i.isLt)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, hl]
  · simp [real_length, Nat.min_eq_left (show i.val + 1 ≤ gs.length by omega)]

lemma singleton_no_edge {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) :
    ¬ ∃ a b, G.Adj a b ∧ decide (a = u) = true ∧ decide (b = u) = true := by
  simp

lemma pair_edge {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n)
    (h : ∃ a b, G.Adj a b ∧ decide (a = u ∨ a = v) = true ∧
      decide (b = u ∨ b = v) = true) : G.Adj u v := by
  simp only [decide_eq_true_eq] at h
  obtain ⟨a, b, hab, ha, hb⟩ := h
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (G.irrefl hab).elim
  · exact hab
  · exact hab.symm
  · exact (G.irrefl hab).elim

lemma support_center {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (ss : List (Finset (Fin n))) (hlen : ss.length ≤ 2)
    (hclean : ∀ x : Fin n → Bool, (ss.map (fun A => supportValue A x)).all id = true →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ z : Fin n, ∀ x, (ss.map (fun A => supportValue A x)).all id = true → x z = true := by
  classical
  obtain ⟨z⟩ := ‹Nonempty (Fin n)›
  cases ss with
  | nil =>
    obtain ⟨u, v, _, hu, _⟩ := hclean (fun _ => false) (by simp)
    contradiction
  | cons A ss =>
    cases ss with
    | nil =>
      refine ⟨z, fun x hx => ?_⟩
      have ha : supportValue A x = true := by simpa using hx
      obtain ⟨u, hu, _⟩ := (supportValue_true A x).mp ha
      exact (singleton_no_edge G u (hclean (fun a => decide (a = u)) (by
        simpa only [List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
          Bool.and_true] using (supportValue_true A _).mpr ⟨u, hu, by simp⟩))).elim
    | cons B ss =>
      cases ss with
      | cons C ss => simp at hlen
      | nil =>
        by_cases ha : A.Nonempty
        · by_cases hb : B.Nonempty
          · have hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b := by
              intro a ha b hb
              apply pair_edge G a b
              apply hclean (fun c => decide (c = a ∨ c = b))
              simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
                id_eq, Bool.and_true, Bool.and_eq_true]
              exact ⟨(supportValue_true A _).mpr ⟨a, ha, by simp⟩,
                (supportValue_true B _).mpr ⟨b, hb, by simp⟩⟩
            obtain ⟨c, hc⟩ := biclique_center G h4 A B ha hb hab
            refine ⟨c, fun x hx => ?_⟩
            simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
              id_eq, Bool.and_true, Bool.and_eq_true, supportValue_true] at hx
            obtain ⟨⟨a, ha, hax⟩, ⟨b, hb, hbx⟩⟩ := hx
            rcases hc a ha b hb with rfl | rfl <;> assumption
          · have hb : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
            exact ⟨z, by simp [hb, supportValue_empty]⟩
        · have ha : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
          exact ⟨z, by simp [ha, supportValue_empty]⟩

lemma union_value {n : ℕ} (ss : List (Finset (Fin n))) (x : Fin n → Bool) :
    supportValue (ss.foldr (· ∪ ·) ∅) x = (ss.map (fun A => supportValue A x)).any id := by
  apply Bool.eq_iff_iff.mpr
  simp only [supportValue_true, mem_union_fold, List.any_map, List.any_eq_true,
    Function.comp_apply, id_eq, supportValue_true]
  constructor
  · rintro ⟨u, ⟨A, hA, hu⟩, hx⟩
    exact ⟨A, hA, u, hu, hx⟩
  · rintro ⟨A, hA, u, hu, hx⟩
    exact ⟨u, ⟨A, hA, hu⟩, hx⟩

lemma circuit_center {n : ℕ} [Nonempty (Fin n)] (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (gs : List Gate) (i : Fin gs.length) (hg : (gs.get i).op = GateOp.and)
    (hlen : (gs.get i).inputs.length ≤ 2)
    (hclean : ∀ x : Fin n → Bool,
      (gs.foldl realStep (List.ofFn x)).getD (n + i.val) false = true →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ z : Fin n, ∀ x,
      ((gs.get i).inputs.map (fun j => supportValue
        ((bareWires n (gs.take i.val)).getD j ∅) x)).all id = true → x z = true := by
  have hc := support_center G h4 ((gs.get i).inputs.map
    (fun j => (bareWires n (gs.take i.val)).getD j ∅)) (by simpa using hlen)
  simp only [List.map_map, Function.comp_def] at hc
  apply hc
  intro x hx
  apply hclean x
  rw [gate_read, hg]
  simp only [GateOp.eval, List.all_map, Function.comp_apply, id_eq, List.all_eq_true]
  simp only [List.map_map, List.all_map, Function.comp_apply, id_eq, List.all_eq_true] at hx
  intro j hj
  obtain ⟨u, hu, hux⟩ := (supportValue_true _ x).mp (hx j hj)
  exact bare_sound (gs.take i.val) x j u hu hux

lemma agree_when_killed {n : ℕ} (gs : List Gate) (x : Fin n → Bool)
    (hbasis : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hkill : ∀ i : Fin gs.length, (gs.get i).op = GateOp.and →
      ((gs.get i).inputs.map (fun j => supportValue
        ((bareWires n (gs.take i.val)).getD j ∅) x)).all id = false) :
    ∀ k, k ≤ gs.length → ∀ j,
      supportValue ((bareWires n (gs.take k)).getD j ∅) x =
        ((gs.take k).foldl realStep (List.ofFn x)).getD j false := by
  intro k
  induction k with
  | zero =>
    intro _ j
    by_cases hj : j < n
    · simp [bareWires, List.getD_eq_getElem?_getD, hj, supportValue]
    · simp [bareWires, List.getD_eq_getElem?_getD, hj, supportValue]
  | succ k ih =>
    intro hk
    have hk' : k < gs.length := by omega
    let i : Fin gs.length := ⟨k, hk'⟩
    have heq := ih (by omega)
    rw [List.take_succ_eq_append_getElem hk']
    simp only [bareWires, List.foldl_append, List.foldl_cons, List.foldl_nil,
      bareStep, realStep]
    apply append_relation _ _ ∅ false (fun A b => supportValue A x = b)
    · simp [bare_length, real_length]
    · exact heq
    · have hmap : (gs.get i).inputs.map (fun j =>
          supportValue ((bareWires n (gs.take k)).getD j ∅) x) =
          (gs.get i).inputs.map (fun j =>
          ((gs.take k).foldl realStep (List.ofFn x)).getD j false) := by
        exact List.map_congr_left (fun j _ => heq j)
      change supportValue (bareGate (bareWires n (gs.take k)) (gs.get i)) x =
        (gs.get i).op.eval ((gs.get i).inputs.map (fun j =>
          ((gs.take k).foldl realStep (List.ofFn x)).getD j false))
      rcases hbasis (gs.get i) (List.get_mem _ _) with ha | ho
      ·
        have hz := hkill i ha
        change ((gs.get i).inputs.map (fun j => supportValue
          ((bareWires n (gs.take k)).getD j ∅) x)).all id = false at hz
        rw [hmap] at hz
        simp only [bareGate, ha, reduceCtorEq, ite_false, supportValue_empty, GateOp.eval]
        exact hz.symm
      · simp only [bareGate, ho, ite_true, union_value, List.map_map, Function.comp_def,
          GateOp.eval]
        exact congrArg (fun bs : List Bool => bs.any id) hmap
    · exact supportValue_empty x

end PEqualNP.Outside.L_meta_1406_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1406_aux in
theorem PEqualNP.Outside.L_meta_1406 :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
    ∀ (gates : List Gate) (out : ℕ),
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    (∀ x : Fin n → Bool, Circuit.eval ⟨gates, out⟩ (List.ofFn x) =
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
    (∀ (i : Fin gates.length) (x : Fin n → Bool), (gates.get i).op = GateOp.and →
      (Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (n + (i : ℕ)) false = true →
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) →
    ∀ I : Finset (Fin gates.length), (∀ i : Fin gates.length,
      (gates.get i).op = GateOp.and → i ∈ I) →
    ∃ T : Finset (Fin n), (∀ u v : Fin n, G.Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card ≤ I.card := by
  classical
  intro n G _ h4 gs out hbasis hcompute hclean I hI
  by_cases hn : n = 0
  · subst n
    exact ⟨∅, fun u => Fin.elim0 u, by simp⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hc : ∀ i : Fin gs.length, ∃ z : Fin n,
      (gs.get i).op = GateOp.and → ∀ x : Fin n → Bool,
      ((gs.get i).inputs.map (fun j => supportValue
        ((bareWires n (gs.take i.val)).getD j ∅) x)).all id = true → x z = true := by
    intro i
    by_cases hi : (gs.get i).op = GateOp.and
    · obtain ⟨z, hz⟩ := circuit_center G h4 gs i hi (hbasis _ (List.get_mem _ _)).2
        (fun x hx => hclean i x hi hx)
      exact ⟨z, fun _ => hz⟩
    · exact ⟨Classical.choice inferInstance, fun h => (hi h).elim⟩
  choose center hcenter using hc
  let T := I.image center
  have hout : (bareWires n gs).getD out ∅ = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro u hu
    have hv : Circuit.eval ⟨gs, out⟩ (List.ofFn (fun a => decide (a = u))) = true :=
      bare_sound gs (fun a => decide (a = u)) out u hu (by simp)
    have he := hcompute (fun a => decide (a = u))
    rw [hv] at he
    exact singleton_no_edge G u (of_decide_eq_true he.symm)
  refine ⟨T, ?_, Finset.card_image_le⟩
  intro u v huv
  by_contra hcover
  have hnu : u ∉ T := fun hu => hcover (Or.inl hu)
  have hnv : v ∉ T := fun hv => hcover (Or.inr hv)
  let x : Fin n → Bool := fun a => decide (a = u ∨ a = v)
  have havoid : ∀ t ∈ T, x t = false := by
    intro t ht
    simp only [x, decide_eq_false_iff_not]
    rintro (rfl | rfl)
    · exact hnu ht
    · exact hnv ht
  have hkill : ∀ i : Fin gs.length, (gs.get i).op = GateOp.and →
      ((gs.get i).inputs.map (fun j => supportValue
        ((bareWires n (gs.take i.val)).getD j ∅) x)).all id = false := by
    intro i hi
    apply Bool.eq_false_iff.mpr
    intro hx
    have ht := hcenter i hi x hx
    have hf := havoid (center i) (Finset.mem_image_of_mem center (hI i hi))
    rw [hf] at ht
    contradiction
  have hagree := agree_when_killed gs x (fun g hg => (hbasis g hg).1) hkill
    gs.length (Nat.le_refl _) out
  simp only [List.take_length, hout, supportValue_empty] at hagree
  have htrue : Circuit.eval ⟨gs, out⟩ (List.ofFn x) = true := by
    rw [hcompute]
    exact decide_eq_true (show ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true from
      ⟨u, v, huv, by simp [x], by simp [x]⟩)
  change (gs.foldl realStep (List.ofFn x)).getD out false = true at htrue
  rw [← hagree] at htrue
  contradiction
