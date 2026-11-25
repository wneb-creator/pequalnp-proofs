import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Bool.Basic
import Mathlib.Order.Preorder.Finite
import PEqualNP.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_1904_aux

def SupportMonotone {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, (∀ v, x v = true → y v = true) → f x = true → f y = true

lemma supportMonotone_of_monotone {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hf : Monotone f) : SupportMonotone f := by
  intro x y hxy hfx
  exact Bool.le_iff_imp.mp (hf (fun v => Bool.le_iff_imp.mpr (hxy v))) hfx

noncomputable def setInput {n : ℕ} (s : Set (Fin n)) : Fin n → Bool := by
  classical
  exact fun v => decide (v ∈ s)

def EdgeHolds {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

noncomputable def edgeFunction {n : ℕ} (G : SimpleGraph (Fin n))
    (x : Fin n → Bool) : Bool := by
  classical
  exact decide (EdgeHolds G x)

lemma setInput_true_iff {n : ℕ} (s : Set (Fin n)) (v : Fin n) :
    setInput s v = true ↔ v ∈ s := by
  classical
  simp [setInput]

lemma exists_maximal_independent_superset {n : ℕ} (G : SimpleGraph (Fin n))
    {s : Set (Fin n)} (hs : G.IsIndepSet s) :
    ∃ t, s ⊆ t ∧ Maximal G.IsIndepSet t := by
  exact Finite.exists_le_maximal hs

lemma independent_support_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (x : Fin n → Bool) :
    G.IsIndepSet {v | x v = true} ↔ ¬ EdgeHolds G x := by
  constructor
  · intro hs ⟨u, v, huv, hxu, hxv⟩
    exact hs hxu hxv huv.ne huv
  · intro h u hu v hv _ hadj
    exact h ⟨u, v, hadj, hu, hv⟩

lemma implies_edge_iff_rejects_maximal {n : ℕ} (G : SimpleGraph (Fin n))
    (f : (Fin n → Bool) → Bool) (hf : SupportMonotone f) :
    (∀ x, f x = true → EdgeHolds G x) ↔
      ∀ s, Maximal G.IsIndepSet s → f (setInput s) = false := by
  constructor
  · intro h s hs
    cases hfs : f (setInput s) with
    | false => rfl
    | true =>
      obtain ⟨u, v, huv, hu, hv⟩ := h _ hfs
      exact False.elim (hs.1 ((setInput_true_iff s u).mp hu)
        ((setInput_true_iff s v).mp hv) huv.ne huv)
  · intro h x hx
    by_contra he
    obtain ⟨s, hxs, hs⟩ := exists_maximal_independent_superset G
      ((independent_support_iff G x).mpr he)
    have htrue : f (setInput s) = true := hf x (setInput s)
      (fun v hv => (setInput_true_iff s v).mpr (hxs hv)) hx
    rw [h s hs] at htrue
    cases htrue

lemma equals_edge_iff_boundary {n : ℕ} (G : SimpleGraph (Fin n))
    (f : (Fin n → Bool) → Bool) (hf : SupportMonotone f) :
    (∀ x, f x = edgeFunction G x) ↔
      (∀ u v, G.Adj u v → f (setInput ({u, v} : Set (Fin n))) = true) ∧
      (∀ s, Maximal G.IsIndepSet s → f (setInput s) = false) := by
  constructor
  · intro h
    have himplies : ∀ x, f x = true → EdgeHolds G x := by
      intro x hx
      rw [h x] at hx
      simpa [edgeFunction] using hx
    refine ⟨?_, (implies_edge_iff_rejects_maximal G f hf).mp himplies⟩
    intro u v huv
    rw [h]
    simp only [edgeFunction, decide_eq_true_eq]
    exact ⟨u, v, huv, (setInput_true_iff _ _).mpr (by simp),
      (setInput_true_iff _ _).mpr (by simp)⟩
  · rintro ⟨hpairs, hmax⟩ x
    have himplies := (implies_edge_iff_rejects_maximal G f hf).mpr hmax
    have hiff : f x = true ↔ EdgeHolds G x := by
      refine ⟨himplies x, ?_⟩
      rintro ⟨u, v, huv, hu, hv⟩
      apply hf (setInput ({u, v} : Set (Fin n))) x ?_ (hpairs u v huv)
      intro w hw
      have hmem := (setInput_true_iff ({u, v} : Set (Fin n)) w).mp hw
      rcases hmem with hwu | hwv
      · simpa only [hwu] using hu
      · have hwv' : w = v := by simpa only [Set.mem_singleton_iff] using hwv
        simpa only [hwv'] using hv
    cases hfx : f x <;> cases hex : edgeFunction G x <;> try rfl
    · have he : EdgeHolds G x := by simpa [edgeFunction] using hex
      have := hiff.mpr he
      simp [hfx] at this
    · have he := hiff.mp hfx
      have : edgeFunction G x = true := by simpa [edgeFunction] using he
      simp [hex] at this

end PEqualNP.Outside.L_meta_1904_aux

namespace PEqualNP.Outside.L_meta_1904_aux.Frontier

open PEqualNP.CircuitLowerBounds

def IsAO (g : Gate) : Prop := g.op = .and ∨ g.op = .or

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wires (gs : List Gate) (x : List Bool) : List Bool := gs.foldl step x

theorem wires_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wires (gs ++ [g]) x = step (wires gs x) g := by
  simp [wires]

theorem wires_length (gs : List Gate) (x : List Bool) :
    (wires gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [wires]
  | append_singleton gs g ih => rw [wires_snoc, step]; simp [ih, Nat.add_assoc]

theorem wire_before (gs : List Gate) (g : Gate) (x : List Bool) {i : ℕ}
    (h : i < x.length + gs.length) :
    (wires (gs ++ [g]) x).getD i false = (wires gs x).getD i false := by
  rw [wires_snoc, step]
  have h' : i < (wires gs x).length := by simpa [wires_length] using h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h']

theorem wire_last (gs : List Gate) (g : Gate) (x : List Bool) :
    (wires (gs ++ [g]) x).getD (x.length + gs.length) false =
      g.op.eval (g.inputs.map fun i => (wires gs x).getD i false) := by
  rw [wires_snoc, step, ← wires_length]
  simp [List.getD_eq_getElem?_getD]

theorem wire_outside (gs : List Gate) (x : List Bool) {i : ℕ}
    (h : x.length + gs.length ≤ i) : (wires gs x).getD i false = false := by
  have h' : (wires gs x).length ≤ i := by simpa [wires_length] using h
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h']

theorem evalAO {g : Gate} (hg : IsAO g) {a b : ℕ → Bool}
    (le : ∀ i ∈ g.inputs, a i ≤ b i) :
    g.op.eval (g.inputs.map a) ≤ g.op.eval (g.inputs.map b) := by
  apply Bool.le_iff_imp.2
  rcases hg with h | h
  · simp only [h, GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    exact fun ha i hi => Bool.le_iff_imp.1 (le i hi) (ha i hi)
  · simp only [h, GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨i, hi, ha⟩
    exact ⟨i, hi, Bool.le_iff_imp.1 (le i hi) ha⟩

def next (k : ℕ) (P : Finset ℕ) (g : Gate) : Finset ℕ :=
  P.erase k ∪ (g.inputs.filter fun i => i < k).toFinset

theorem next_card (k : ℕ) (P : Finset ℕ) (g : Gate)
    (hk : k ∈ P) (hlen : g.inputs.length ≤ 2) : (next k P g).card ≤ P.card + 1 := by
  have h₁ := Finset.card_union_le (P.erase k) (g.inputs.filter fun i => i < k).toFinset
  have h₂ := List.toFinset_card_le (g.inputs.filter fun i => i < k)
  have h₃ := List.length_filter_le (fun i : ℕ => decide (i < k)) g.inputs
  have h₄ := Finset.card_erase_add_one hk
  unfold next
  omega

theorem next_include {k i : ℕ} {P : Finset ℕ} {g : Gate} (hi : i ∈ g.inputs)
    (hk : i < k) : i ∈ next k P g := by
  exact Finset.mem_union_right _ (List.mem_toFinset.2 (by simp [hi, hk]))

theorem frontier (n : ℕ) (gs : List Gate)
    (allowed : ∀ g ∈ gs, IsAO g ∧ g.inputs.length ≤ 2)
    (P : Finset ℕ) (bounded : ∀ i ∈ P, i < n + gs.length) :
    ∃ D : Finset ℕ, (∀ i ∈ D, i < n) ∧ D.card ≤ P.card + gs.length ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ D, x.getD i false ≤ y.getD i false) →
        ∀ i ∈ P, (wires gs x).getD i false ≤ (wires gs y).getD i false := by
  induction gs using List.reverseRecOn generalizing P with
  | nil =>
    refine ⟨P, ?_, by simp, ?_⟩
    · simpa using bounded
    · intro x y _ _ h
      simpa [wires] using h
  | append_singleton gs g ih =>
    have hpre : ∀ h ∈ gs, IsAO h ∧ h.inputs.length ≤ 2 :=
      fun h hh => allowed h (by simp [hh])
    have hg := allowed g (by simp)
    let k := n + gs.length
    have hp : ∀ i ∈ P, i ≠ k → i < k := by
      intro i hi hne
      have h := bounded i hi
      simp at h
      dsimp [k] at hne ⊢
      omega
    have he : ∀ i ∈ P.erase k, i < k := fun i hi =>
      hp i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)
    have sameBefore : ∀ x : List Bool, x.length = n → ∀ i < k,
        (wires (gs ++ [g]) x).getD i false = (wires gs x).getD i false := by
      intro x hx i hi
      apply wire_before
      simpa [k, hx] using hi
    have last : ∀ x : List Bool, x.length = n →
        (wires (gs ++ [g]) x).getD k false =
          g.op.eval (g.inputs.map fun i => (wires gs x).getD i false) := by
      intro x hx
      simpa [k, hx] using wire_last gs g x
    by_cases hk : k ∈ P
    · have he' : ∀ i ∈ next k P g, i < k := by
        intro i hi
        rcases Finset.mem_union.1 hi with hi | hi
        · exact he i hi
        · exact (List.mem_filter.1 (List.mem_toFinset.1 hi)).2 |> of_decide_eq_true
      obtain ⟨D, hD, hc, hcmp⟩ := ih hpre (next k P g) he'
      have count := next_card k P g hk hg.2
      refine ⟨D, hD, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro x y hx hy hxy i hi
        by_cases hi' : i = k
        · rw [hi', last x hx, last y hy]
          apply evalAO hg.1
          intro j hj
          by_cases hj' : j < k
          · exact hcmp x y hx hy hxy j (next_include hj hj')
          · rw [wire_outside gs x (by simpa [hx, k] using Nat.le_of_not_gt hj'),
              wire_outside gs y (by simpa [hy, k] using Nat.le_of_not_gt hj')]
        · have hiE : i ∈ P.erase k := Finset.mem_erase.2 ⟨hi', hi⟩
          rw [sameBefore x hx i (he i hiE), sameBefore y hy i (he i hiE)]
          exact hcmp x y hx hy hxy i (Finset.mem_union_left _ hiE)
    · have hp' : ∀ i ∈ P, i < k := fun i hi => hp i hi (fun e => hk (e ▸ hi))
      obtain ⟨D, hD, hc, hcmp⟩ := ih hpre P hp'
      refine ⟨D, hD, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · intro x y hx hy hxy i hi
        rw [sameBefore x hx i (hp' i hi), sameBefore y hy i (hp' i hi)]
        exact hcmp x y hx hy hxy i hi

theorem circuit_frontier (n : ℕ) (C : Circuit)
    (allowed : ∀ g ∈ C.gates, IsAO g ∧ g.inputs.length ≤ 2) :
    ∃ D : Finset ℕ, (∀ i ∈ D, i < n) ∧ D.card ≤ C.size + 1 ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ D, x.getD i false ≤ y.getD i false) → C.eval x ≤ C.eval y := by
  by_cases ho : C.output < n + C.gates.length
  · obtain ⟨D, hD, hc, hm⟩ := frontier n C.gates allowed {C.output} (by simpa)
    refine ⟨D, hD, ?_, ?_⟩
    · simpa [Circuit.size, Nat.add_comm] using hc
    · intro x y hx hy hxy
      exact hm x y hx hy hxy C.output (by simp)
  · refine ⟨∅, by simp, by simp, ?_⟩
    intro x y hx hy _
    change (wires C.gates x).getD C.output false ≤
      (wires C.gates y).getD C.output false
    rw [wire_outside _ _ (by omega), wire_outside _ _ (by omega)]

theorem circuit_frontier_monotone2 (n : ℕ) (C : Circuit)
    (allowed : PEqualNP.MetaComplexity.Monotone2 C) :
    ∃ D : Finset ℕ, (∀ i ∈ D, i < n) ∧ D.card ≤ C.size + 1 ∧
      ∀ x y : List Bool, x.length = n → y.length = n →
        (∀ i ∈ D, x.getD i false ≤ y.getD i false) → C.eval x ≤ C.eval y := by
  apply circuit_frontier n C
  intro g hg
  have h := allowed g hg
  exact ⟨by simpa [IsAO] using h.1, h.2⟩

theorem circuit_separating_frontier {A B : Type*} (n : ℕ) (C : Circuit)
    (allowed : PEqualNP.MetaComplexity.Monotone2 C)
    (positive : A → List Bool) (negative : B → List Bool)
    (plen : ∀ a, (positive a).length = n) (nlen : ∀ b, (negative b).length = n)
    (pos : ∀ a, C.eval (positive a) = true) (neg : ∀ b, C.eval (negative b) = false) :
    ∃ D : Finset ℕ, (∀ i ∈ D, i < n) ∧ D.card ≤ C.size + 1 ∧
      ∀ a b, ∃ i ∈ D,
        (positive a).getD i false = true ∧ (negative b).getD i false = false := by
  obtain ⟨D, hD, hc, hm⟩ := circuit_frontier_monotone2 n C allowed
  refine ⟨D, hD, hc, ?_⟩
  intro a b
  by_contra h
  have hle : ∀ i ∈ D, (positive a).getD i false ≤ (negative b).getD i false := by
    intro i hi
    apply Bool.le_iff_imp.mpr
    intro hp
    cases hn : (negative b).getD i false with
    | false => exact False.elim (h ⟨i, hi, hp, hn⟩)
    | true => rfl
  have hout := hm (positive a) (negative b) (plen a) (nlen b) hle
  rw [pos a, neg b] at hout
  have hfalse : false = true := Bool.le_iff_imp.mp hout rfl
  cases hfalse

end PEqualNP.Outside.L_meta_1904_aux.Frontier

namespace PEqualNP.Outside.L_meta_1904_aux.FiniteSourceCover

open scoped BigOperators

lemma finite_cover_card_bound {ι Ω : Type*} [Fintype Ω]
    (used : Finset ι) (covers : ι → Finset Ω) (capacity : ℕ)
    (hcover : ∀ x, ∃ i ∈ used, x ∈ covers i)
    (hcapacity : ∀ i ∈ used, (covers i).card ≤ capacity) :
    Fintype.card Ω ≤ used.card * capacity := by
  classical
  calc
    Fintype.card Ω = (Finset.univ : Finset Ω).card := by simp
    _ ≤ (used.biUnion covers).card := Finset.card_le_card (by
      intro x _
      exact Finset.mem_biUnion.mpr (hcover x))
    _ ≤ ∑ i ∈ used, (covers i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ used, capacity := Finset.sum_le_sum hcapacity
    _ = used.card * capacity := by simp

lemma finite_cover_source_lower_bound {ι Ω : Type*} [Fintype Ω]
    (used : Finset ι) (covers : ι → Finset Ω) (required capacity : ℕ)
    (hpositive : 0 < capacity)
    (hrows : Fintype.card Ω = required * capacity)
    (hcover : ∀ x, ∃ i ∈ used, x ∈ covers i)
    (hcapacity : ∀ i ∈ used, (covers i).card ≤ capacity) :
    required ≤ used.card := by
  have h := finite_cover_card_bound used covers capacity hcover hcapacity
  rw [hrows] at h
  nlinarith

def separatedRows {Ω : Type*} [Fintype Ω]
    (positive negative : Ω → List Bool) (source : ℕ) : Finset Ω :=
  Finset.univ.filter fun row =>
    (positive row).getD source false = true ∧ (negative row).getD source false = false

lemma frontier_separation_cover_bound {Ω : Type*} [Fintype Ω]
    (positive negative : Ω → List Bool) (frontier : Finset ℕ)
    (gateCount required capacity : ℕ)
    (hfrontier : frontier.card ≤ gateCount + 1)
    (hpositive : 0 < capacity)
    (hrows : Fintype.card Ω = required * capacity)
    (hseparates : ∀ row, ∃ source ∈ frontier,
      (positive row).getD source false = true ∧ (negative row).getD source false = false)
    (hcapacity : ∀ source ∈ frontier,
      (separatedRows positive negative source).card ≤ capacity) :
    required ≤ gateCount + 1 := by
  apply le_trans (finite_cover_source_lower_bound frontier
    (separatedRows positive negative) required capacity hpositive hrows ?_ hcapacity) hfrontier
  intro row
  obtain ⟨source, hsource, htrue, hfalse⟩ := hseparates row
  exact ⟨source, hsource, Finset.mem_filter.mpr ⟨Finset.mem_univ _, htrue, hfalse⟩⟩

lemma linear_times_binary_power_le (r k : ℕ) (hr : r ≤ k) :
    r * 2 ^ (k - r) ≤ 2 ^ (k - 1) := by
  have hsucc : ∀ t : ℕ, t + 1 ≤ 2 ^ t := by
    intro t
    induction t with
    | zero => norm_num
    | succ t ih =>
      rw [pow_succ]
      omega
  cases r with
  | zero => simp
  | succ r =>
    calc
      (r + 1) * 2 ^ (k - (r + 1)) ≤ 2 ^ r * 2 ^ (k - (r + 1)) :=
        Nat.mul_le_mul_right _ (hsucc r)
      _ = 2 ^ (r + (k - (r + 1))) := (pow_add 2 _ _).symm
      _ = 2 ^ (k - 1) := by congr 1; omega

def falseTransversals {k : ℕ} (selected : Finset (Fin k))
    (polarity : Fin k → Bool) : Finset (Fin k → Bool) :=
  Fintype.piFinset fun i => if i ∈ selected then {!(polarity i)} else Finset.univ

lemma mem_falseTransversals_iff {k : ℕ} (selected : Finset (Fin k))
    (polarity assignment : Fin k → Bool) :
    assignment ∈ falseTransversals selected polarity ↔
      ∀ i ∈ selected, assignment i = !(polarity i) := by
  simp only [falseTransversals, Fintype.mem_piFinset]
  constructor
  · intro h i hi
    simpa [hi] using h i
  · intro h i
    by_cases hi : i ∈ selected
    · simpa [hi] using h i hi
    · simp [hi]

lemma card_falseTransversals {k : ℕ} (selected : Finset (Fin k))
    (polarity : Fin k → Bool) :
    (falseTransversals selected polarity).card = 2 ^ (k - selected.card) := by
  classical
  calc
    (falseTransversals selected polarity).card =
        ∏ i : Fin k, if i ∈ selectedᶜ then 2 else 1 := by
      rw [falseTransversals, Fintype.card_piFinset]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ selected <;> simp [hi]
    _ = ∏ _i ∈ selectedᶜ, 2 := Finset.prod_ite_mem_eq _ _
    _ = 2 ^ (k - selected.card) := by simp [Finset.card_compl]

def clausePairs {k : ℕ} (selected : Finset (Fin k)) (polarity : Fin k → Bool) :
    Finset (Fin k × (Fin k → Bool)) := selected ×ˢ falseTransversals selected polarity

lemma mem_clausePairs_iff {k : ℕ} (selected : Finset (Fin k))
    (polarity assignment : Fin k → Bool) (positive : Fin k) :
    (positive, assignment) ∈ clausePairs selected polarity ↔
      positive ∈ selected ∧ ¬ ∃ i ∈ selected, assignment i = polarity i := by
  simp only [clausePairs, Finset.mem_product, mem_falseTransversals_iff]
  constructor
  · rintro ⟨hp, ht⟩
    refine ⟨hp, ?_⟩
    rintro ⟨i, hi, heq⟩
    have h := ht i hi
    rw [heq] at h
    cases hb : polarity i <;> simp [hb] at h
  · rintro ⟨hp, ht⟩
    refine ⟨hp, fun i hi => ?_⟩
    have hne : assignment i ≠ polarity i := fun h => ht ⟨i, hi, h⟩
    cases ha : assignment i <;> cases hb : polarity i <;> simp [ha, hb] at hne ⊢

lemma card_clausePairs {k : ℕ} (selected : Finset (Fin k)) (polarity : Fin k → Bool) :
    (clausePairs selected polarity).card = selected.card * 2 ^ (k - selected.card) := by
  simp [clausePairs, card_falseTransversals]

lemma card_clausePairs_le {k : ℕ} (selected : Finset (Fin k)) (polarity : Fin k → Bool) :
    (clausePairs selected polarity).card ≤ 2 ^ (k - 1) := by
  rw [card_clausePairs]
  apply linear_times_binary_power_le
  simpa using Finset.card_le_univ selected

lemma matching_pair_count (k : ℕ) :
    Fintype.card (Fin k × (Fin k → Bool)) = k * 2 ^ k := by
  simp

lemma matching_source_lower_bound {ι : Type*} (k : ℕ) (hk : 0 < k)
    (used : Finset ι) (selected : ι → Finset (Fin k)) (polarity : ι → Fin k → Bool)
    (hcover : ∀ x : Fin k × (Fin k → Bool),
      ∃ i ∈ used, x ∈ clausePairs (selected i) (polarity i)) :
    2 * k ≤ used.card := by
  apply finite_cover_source_lower_bound used
    (fun i => clausePairs (selected i) (polarity i)) (2 * k) (2 ^ (k - 1))
  · positivity
  · rw [matching_pair_count]
    have hpow : (2 : ℕ) ^ k = 2 * 2 ^ (k - 1) := by
      have hkeq : k = (k - 1) + 1 := by omega
      calc
        2 ^ k = 2 ^ ((k - 1) + 1) := congrArg (fun j => 2 ^ j) hkeq
        _ = 2 * 2 ^ (k - 1) := by rw [pow_succ]; omega
    rw [hpow]
    ring
  · exact hcover
  · intro i _
    exact card_clausePairs_le (selected i) (polarity i)

end PEqualNP.Outside.L_meta_1904_aux.FiniteSourceCover

namespace PEqualNP.Outside.L_meta_1904_aux.FiniteSourceCover

theorem monotone_circuit_separation_lower_bound {Ω : Type*} [Fintype Ω]
    (inputCount : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (allowed : PEqualNP.MetaComplexity.Monotone2 C)
    (positive negative : Ω → List Bool)
    (positive_length : ∀ row, (positive row).length = inputCount)
    (negative_length : ∀ row, (negative row).length = inputCount)
    (positive_output : ∀ row, C.eval (positive row) = true)
    (negative_output : ∀ row, C.eval (negative row) = false)
    (required capacity : ℕ) (capacity_pos : 0 < capacity)
    (pair_count : Fintype.card Ω = required * capacity)
    (source_capacity : ∀ source < inputCount,
      (separatedRows positive negative source).card ≤ capacity) :
    required ≤ C.size + 1 := by
  obtain ⟨D, hD, hcard, hseparates⟩ :=
    PEqualNP.Outside.L_meta_1904_aux.Frontier.circuit_separating_frontier
      inputCount C allowed positive negative positive_length negative_length
      positive_output negative_output
  exact frontier_separation_cover_bound positive negative D C.size required capacity
    hcard capacity_pos pair_count (fun row => hseparates row row)
    (fun source hsource => source_capacity source (hD source hsource))

end PEqualNP.Outside.L_meta_1904_aux.FiniteSourceCover
