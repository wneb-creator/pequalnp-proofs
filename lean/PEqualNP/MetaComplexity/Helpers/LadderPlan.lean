import PEqualNP.MetaComplexity.Helpers.SBase
import PEqualNP.MetaComplexity.Helpers.OneNotRelabel

/-!
# The ladder (row L-meta-1048): the plan module

Unverified, a conjecture until a checker accepts a row. The build plan
(the build plan) splits the proof into seven steps. This file states steps
1, 2 (`lp_PFreeze`, `lp_PConvex`), 4 (`lp_PDual`), 3 and 6 (`lp_PRun`, `lp_PCost`) as
Props, proves step 5 (`lp_interval`, from the checked rows L-meta-1041 and L-meta-681) and
step 7 (`lp_assembly`) from them. Every Prop is written with no local definitions, so a
proof of it may restate it verbatim.
-/

namespace PEqualNP.MetaComplexity.Ladder

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.OneNot

/-- Step 1, FREEZE THE NOTS: for every pattern `e` there is an AND/OR list of fan-in at most
two and the same length whose wires agree with those of `gates` on every input of the piece
`P_e` (the indexed gates' wires read `e`). -/
def lp_PFreeze : Prop :=
  ∀ (n t : ℕ) (gates : List Gate) (ι : Fin t → Fin gates.length) (e : Fin t → Bool),
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, (gates.get i).op = GateOp.not → ∃ j : Fin t, ι j = i) →
    ∃ gates' : List Gate, gates'.length = gates.length ∧
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ∀ x : Fin n → Bool,
        (∀ j : Fin t, Circuit.eval ⟨gates, n + (ι j : ℕ)⟩ (List.ofFn x) = e j) →
        ∀ o : ℕ, Circuit.eval ⟨gates', o⟩ (List.ofFn x) = Circuit.eval ⟨gates, o⟩ (List.ofFn x)

/-- Step 2, PIECES ARE CONVEX: `a ≤ x ≤ b` with `a, b` in `P_e` gives `x` in `P_e`. The
covering hypothesis is needed (an unindexed NOT gate breaks it). -/
def lp_PConvex : Prop :=
  ∀ (n t : ℕ) (gates : List Gate) (ι : Fin t → Fin gates.length) (e : Fin t → Bool),
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (∀ i : Fin gates.length, (gates.get i).op = GateOp.not → ∃ j : Fin t, ι j = i) →
    ∀ a x b : Fin n → Bool, (∀ i, a i = true → x i = true) → (∀ i, x i = true → b i = true) →
      (∀ j : Fin t, Circuit.eval ⟨gates, n + (ι j : ℕ)⟩ (List.ofFn a) = e j) →
      (∀ j : Fin t, Circuit.eval ⟨gates, n + (ι j : ℕ)⟩ (List.ofFn b) = e j) →
      ∀ j : Fin t, Circuit.eval ⟨gates, n + (ι j : ℕ)⟩ (List.ofFn x) = e j

/-- Step 3, RUN ARGUMENT: if the fibres of `f` on `range H` are intervals, the break set
`{u ≥ 1 : f u ≠ f (u - 1)}` has at most `2 ^ t - 1` elements, and levels with no break
between them have equal `f`. -/
def lp_PRun : Prop :=
  ∀ (H t : ℕ) (f : ℕ → Fin t → Bool),
    (∀ u v w : ℕ, u ≤ v → v ≤ w → w < H → f u = f w → f v = f u) →
    ((Finset.range H).filter (fun u => 1 ≤ u ∧ f u ≠ f (u - 1))).card + 1 ≤ 2 ^ t ∧
    ∀ u v : ℕ, u ≤ v → v < H →
      (∀ w ∈ (Finset.range H).filter (fun u => 1 ≤ u ∧ f u ≠ f (u - 1)), ¬ (u < w ∧ w ≤ v)) →
      f u = f v

/-- Step 4, DE MORGAN DUAL: an AND/OR list of fan-in at most two has a dual of the same length
and kind with `eval ⟨gd, o⟩ x = ! eval ⟨g, o⟩ (not x)` at every wire `o < n + g.length`. -/
def lp_PDual : Prop :=
  ∀ (n : ℕ) (g : List Gate),
    (∀ gt ∈ g, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2) →
    ∃ gd : List Gate, gd.length = g.length ∧
      (∀ gt ∈ gd, (gt.op = GateOp.and ∨ gt.op = GateOp.or) ∧ gt.inputs.length ≤ 2) ∧
      ∀ o : ℕ, o < n + g.length → ∀ x : Fin n → Bool,
        Circuit.eval ⟨gd, o⟩ (List.ofFn x) = !Circuit.eval ⟨g, o⟩ (List.ofFn (fun i => !x i))

/-- Step 6, CHAIN COSTS: with the levels (level 0 empty, level `u` in `1..h+1` is
`K (u - 1)`, level `h + 2` all points), for levels `uv.1 ≤ uv.2` the sum of step 5 is the
cost inside the row's statement, verbatim. -/
def lp_PCost : Prop :=
  ∀ (h q n : ℕ) (S : Fin n → Finset (Fin n)) (K : Fin (h + 1) → Finset (Fin n)), 1 ≤ h → q = 2 ^ h → n = q * q + q + 1 → (∀ i : Fin n, (S i).card = q + 1) → (∀ i j : Fin n, i ≠ j → (S i ∩ S j).card = 1) → (∀ p p' : Fin n, p ≠ p' → ∃ i : Fin n, p ∈ S i ∧ p' ∈ S i) → (∀ j : Fin (h + 1), (K j).card = (2 ^ (j : ℕ) - 1) * q + 2 ^ (j : ℕ)) → (∀ (j : Fin (h + 1)) (i : Fin n), (S i ∩ K j).card = 0 ∨ (S i ∩ K j).card = 2 ^ (j : ℕ)) → (∀ j j' : Fin (h + 1), j ≤ j' → K j ⊆ K j') →
    ∀ uv : ℕ × ℕ, uv.1 ≤ uv.2 → uv.2 < h + 3 →
      ∑ w ∈ Finset.univ.filter (fun w : Fin n =>
          Disjoint (S w) (if uv.1 = 0 then ∅ else if hu : uv.1 - 1 < h + 1 then K ⟨uv.1 - 1, hu⟩ else Finset.univ) ∧
          2 ≤ (S w ∩ (if uv.2 = 0 then ∅ else if hv : uv.2 - 1 < h + 1 then K ⟨uv.2 - 1, hv⟩ else Finset.univ)).card),
        ((S w ∩ (if uv.2 = 0 then ∅ else if hv : uv.2 - 1 < h + 1 then K ⟨uv.2 - 1, hv⟩ else Finset.univ)).card - 1)
      = ((if uv.1 = 0 then n else if uv.1 = h + 2 then 0 else q * (q + 1) / 2 ^ (uv.1 - 1) - q) - (if uv.2 = 0 then n else if uv.2 = h + 2 then 0 else q * (q + 1) / 2 ^ (uv.2 - 1) - q)) * (if uv.2 = h + 2 then q else 2 ^ (uv.2 - 1) - 1)

/-- Step 5, THE INTERVAL LEMMA: if `a ⊆ b` and both indicators lie in the piece `P_e`, the
lines missing `a` and meeting `b` in at least two points cost
`∑ (|S w ∩ b| - 1) ≤ gates.length`. -/
theorem lp_interval (hF : lp_PFreeze) (hC : lp_PConvex) (hD : lp_PDual) :
    ∀ (n m q t : ℕ) (S : Fin m → Finset (Fin n)) (gates : List Gate) (out : Fin m → ℕ)
      (ι : Fin t → Fin gates.length) (e : Fin t → Bool) (a b : Finset (Fin n)),
      2 ≤ q → (∀ i : Fin m, (S i).card = q + 1) →
      (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card = 1) →
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2) →
      (∀ i : Fin gates.length, (gates.get i).op = GateOp.not → ∃ j : Fin t, ι j = i) →
      (∀ (w : Fin m) (x : Fin n → Bool),
        Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) →
      a ⊆ b →
      (∀ j : Fin t, Circuit.eval ⟨gates, n + (ι j : ℕ)⟩
        (List.ofFn (fun i => decide (i ∈ a))) = e j) →
      (∀ j : Fin t, Circuit.eval ⟨gates, n + (ι j : ℕ)⟩
        (List.ofFn (fun i => decide (i ∈ b))) = e j) →
      ∑ w ∈ Finset.univ.filter (fun w : Fin m => Disjoint (S w) a ∧ 2 ≤ (S w ∩ b).card),
        ((S w ∩ b).card - 1) ≤ gates.length := by
  intro n m q t S gates out ι e a b hq hS hSS hops hcov hright hab ha hb
  obtain ⟨g1, hg1len, hg1ops, hg1eq⟩ := hF n t gates ι e hops hcov
  -- the frozen list is right on the interval [a, b]
  have hR1 : ∀ (w : Fin m) (x : Fin n → Bool), (∀ i ∈ a, x i = true) →
      (∀ i, x i = true → i ∈ b) →
      Circuit.eval ⟨g1, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true) := by
    intro w x hxa hxb
    have hP : ∀ j, Circuit.eval ⟨gates, n + (ι j : ℕ)⟩ (List.ofFn x) = e j :=
      hC n t gates ι e hops hcov (fun i => decide (i ∈ a)) x (fun i => decide (i ∈ b))
        (fun i hi => hxa i (by simpa using hi)) (fun i hi => by simpa using hxb i hi) ha hb
    rw [hg1eq x hP, hright]
  obtain ⟨g2, hg2len, hg2ops, hg2eq⟩ := hD n g1 hg1ops
  set T := Finset.univ.filter (fun w : Fin m => Disjoint (S w) a ∧ 2 ≤ (S w ∩ b).card) with hT
  -- the outputs of the lines of T are in range
  have hout : ∀ w ∈ T, out w < n + g1.length := by
    intro w hw
    by_contra hlt
    push_neg at hlt
    have h1 := hR1 w (fun i => decide (i ∈ b)) (fun i hi => by simpa using hab hi)
      (fun i hi => by simpa using hi)
    have h2 : Circuit.eval ⟨g1, out w⟩ (List.ofFn (fun i => decide (i ∈ b))) = false :=
      on1_getD_wires_of_ge _ _ _ (by simpa using hlt)
    obtain ⟨v, hv⟩ : (S w ∩ b).Nonempty := by
      rw [← Finset.card_pos]; have := (Finset.mem_filter.1 hw).2.2; omega
    rw [h2] at h1
    have h3 := h1.symm
    rw [decide_eq_false_iff_not] at h3
    exact h3 ⟨v, (Finset.mem_inter.1 hv).1, by simpa using (Finset.mem_inter.1 hv).2⟩
  -- the dual is the AND of each line of T on the interval [comp b, comp a]
  have hR2 : ∀ w ∈ T, ∀ z : Fin n → Bool, (∀ i, i ∉ b → z i = true) →
      (∀ i, z i = true → i ∉ a) →
      Circuit.eval ⟨g2, out w⟩ (List.ofFn z) = decide (∀ v ∈ S w, z v = true) := by
    intro w hw z hz1 hz2
    rw [hg2eq (out w) (hout w hw) z]
    rw [hR1 w (fun i => !z i)]
    · by_cases hc : ∀ v ∈ S w, z v = true
      · have hne : ¬ ∃ v ∈ S w, z v = false := by
          rintro ⟨v, hv, hzv⟩; simp [hc v hv] at hzv
        simpa [hne] using hc
      · push_neg at hc
        obtain ⟨v, hv, hzv⟩ := hc
        have : ∃ v ∈ S w, (!z v) = true := ⟨v, hv, by simpa using hzv⟩
        simp only [this, decide_true, Bool.not_true]
        symm
        rw [decide_eq_false_iff_not]
        intro hall
        exact hzv (hall v hv)
    · intro i hi
      have : z i = false := by
        by_contra hzi
        exact hz2 i (by simpa using hzi) hi
      simp [this]
    · intro i hi
      by_contra hib
      have := hz1 i hib
      simp [this] at hi
  -- restrict down to the complement of a
  obtain ⟨r, hr⟩ := on1_restrict_down n (Finset.univ \ a) g2
  set g3 := g2.map (fun g => ({ op := g.op, inputs := g.inputs.map r } : Gate)) with hg3
  have hg3len : g3.length = gates.length := by rw [hg3, List.length_map, hg2len, hg1len]
  have hg3ops : ∀ g ∈ g3, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    rw [hg3, List.mem_map] at hg
    obtain ⟨g', hg', rfl⟩ := hg
    obtain ⟨h1, h2⟩ := hg2ops g' hg'
    exact ⟨h1, by simpa using h2⟩
  -- re-index T
  set φ : Fin T.card ≃ T := T.equivFin.symm with hφ
  have hS' : ∀ i : Fin T.card, (S (φ i).1).card = q + 1 := fun i => hS _
  have hSS' : ∀ i j : Fin T.card, i ≠ j → (S (φ i).1 ∩ S (φ j).1).card = 1 := by
    intro i j hij
    apply hSS
    intro heq
    exact hij (φ.injective (Subtype.ext heq))
  have hright3 : ∀ (w : Fin T.card) (x : Fin n → Bool), (∀ v ∈ Finset.univ \ b, x v = true) →
      ((Finset.univ.filter (fun i : Fin n => x i = true)) \ (Finset.univ \ b)).card ≤ n →
      Circuit.eval ⟨g3, r (out (φ w).1)⟩ (List.ofFn x)
        = decide (∀ v ∈ S (φ w).1, x v = true) := by
    intro w x hx _
    have hwT := (φ w).2
    have hdisj : Disjoint (S (φ w).1) a := (Finset.mem_filter.1 hwT).2.1
    rw [hr, hR2 _ hwT]
    · apply decide_eq_decide.2
      constructor
      · intro hall v hv
        have := hall v hv
        simp only [Bool.and_eq_true] at this
        exact this.1
      · intro hall v hv
        have hva : v ∉ a := Finset.disjoint_left.1 hdisj hv
        simp [hall v hv, hva]
    · intro i hib
      have hia : i ∉ a := fun h => hib (hab h)
      simp [hx i (by simpa using hib), hia]
    · intro i hi
      simp only [Bool.and_eq_true, decide_eq_true_eq, Finset.mem_sdiff, Finset.mem_univ,
        true_and] at hi
      exact hi.2
  have key := PEqualNP.MetaComplexity.SBase.sbase q n T.card n (fun i => S (φ i).1)
    (Finset.univ \ b) hq hS' hSS' g3 (fun i => r (out (φ i).1)) hg3ops hright3 q le_rfl
    (Or.inr (by omega))
  have hdiff : ∀ i : Fin T.card, S (φ i).1 \ (Finset.univ \ b) = S (φ i).1 ∩ b := by
    intro i; ext v; simp
  simp only [hdiff] at key
  have hfil : Finset.univ.filter (fun i : Fin T.card => 2 ≤ (S (φ i).1 ∩ b).card)
      = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro i _
    exact (Finset.mem_filter.1 (φ i).2).2.2
  rw [hfil, Finset.card_univ, Fintype.card_fin] at key
  have hmin : ∀ i : Fin T.card, min (q + 1) (S (φ i).1 ∩ b).card = (S (φ i).1 ∩ b).card := by
    intro i
    apply min_eq_right
    rw [← hS (φ i).1]
    exact Finset.card_le_card Finset.inter_subset_left
  simp only [hmin] at key
  have hsum : ∑ i : Fin T.card, (S (φ i).1 ∩ b).card = ∑ w ∈ T, (S w ∩ b).card := by
    rw [← Finset.sum_coe_sort T (fun w => (S w ∩ b).card)]
    exact Equiv.sum_comp φ (fun w : T => (S w.1 ∩ b).card)
  rw [hsum, hg3len] at key
  have hsplit : ∑ w ∈ T, ((S w ∩ b).card - 1) + T.card = ∑ w ∈ T, (S w ∩ b).card := by
    rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    have := (Finset.mem_filter.1 hw).2.2
    omega
  omega

/-- The minimum over a finite image, read with `untopD 0`, is at most any member's value. -/
theorem lp_untop_le (s : Finset (Finset ℕ)) (F : Finset ℕ → ℕ) (P : Finset ℕ) (hP : P ∈ s)
    (L : ℕ) (hL : F P ≤ L) : WithTop.untopD 0 ((s.image F).min) ≤ L := by
  have hmem : F P ∈ s.image F := Finset.mem_image_of_mem F hP
  obtain ⟨m0, hm0⟩ := Finset.min_of_mem hmem
  have hle := Finset.min_le hmem
  rw [hm0] at hle
  rw [hm0, WithTop.untopD_coe]
  exact le_trans (WithTop.coe_le_coe.1 hle) hL

/-- Step 7, THE ASSEMBLY: the five pieces give the recorded statement of the row. -/
theorem lp_assembly (hF : lp_PFreeze) (hC : lp_PConvex) (hD : lp_PDual) (hR : lp_PRun)
    (hCo : lp_PCost) :
    ∀ (h q n t : ℕ) (S : Fin n → Finset (Fin n)) (K : Fin (h + 1) → Finset (Fin n)), 1 ≤ h → q = 2 ^ h → n = q * q + q + 1 → (∀ i : Fin n, (S i).card = q + 1) → (∀ i j : Fin n, i ≠ j → (S i ∩ S j).card = 1) → (∀ p p' : Fin n, p ≠ p' → ∃ i : Fin n, p ∈ S i ∧ p' ∈ S i) → (∀ j : Fin (h + 1), (K j).card = (2 ^ (j : ℕ) - 1) * q + 2 ^ (j : ℕ)) → (∀ (j : Fin (h + 1)) (i : Fin n), (S i ∩ K j).card = 0 ∨ (S i ∩ K j).card = 2 ^ (j : ℕ)) → (∀ j j' : Fin (h + 1), j ≤ j' → K j ⊆ K j') → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin n → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin t → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin t, ι j = i) → (∀ (w : Fin n) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → (WithTop.untopD 0 (((Finset.range (h + 3)).powerset.filter (fun P : Finset ℕ => P.card + 1 ≤ 2 ^ t)).image (fun P : Finset ℕ => ((Finset.range (h + 3) ×ˢ Finset.range (h + 3)).filter (fun uv : ℕ × ℕ => uv.1 ≤ uv.2 ∧ ∀ w ∈ P, ¬ (uv.1 < w ∧ w ≤ uv.2))).sup (fun uv : ℕ × ℕ => ((if uv.1 = 0 then n else if uv.1 = h + 2 then 0 else q * (q + 1) / 2 ^ (uv.1 - 1) - q) - (if uv.2 = 0 then n else if uv.2 = h + 2 then 0 else q * (q + 1) / 2 ^ (uv.2 - 1) - q)) * (if uv.2 = h + 2 then q else 2 ^ (uv.2 - 1) - 1)))).min) ≤ gates.length := by
  intro h q n t S K hh hq hn hS hSS hpts hKc hKm hKn gates out hops hι hright
  obtain ⟨ι, hcov⟩ := hι
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hh
  have hmono : ∀ u v : ℕ, u ≤ v →
      (if u = 0 then ∅ else if hu : u - 1 < h + 1 then K ⟨u - 1, hu⟩ else Finset.univ)
        ⊆ (if v = 0 then ∅ else if hv : v - 1 < h + 1 then K ⟨v - 1, hv⟩ else Finset.univ) := by
    intro u v huv
    split_ifs <;> first
      | exact Finset.empty_subset _
      | exact Finset.subset_univ _
      | omega
      | exact hKn _ _ (Fin.mk_le_mk.2 (by omega))
  have hint : ∀ u v w : ℕ, u ≤ v → v ≤ w → w < h + 3 →
      (fun u (j : Fin t) => Circuit.eval ⟨gates, n + (ι j : ℕ)⟩ (List.ofFn (fun i => decide (i ∈
        (if u = 0 then ∅ else if hu : u - 1 < h + 1 then K ⟨u - 1, hu⟩ else Finset.univ))))) u
      = (fun u (j : Fin t) => Circuit.eval ⟨gates, n + (ι j : ℕ)⟩ (List.ofFn (fun i => decide (i ∈
        (if u = 0 then ∅ else if hu : u - 1 < h + 1 then K ⟨u - 1, hu⟩ else Finset.univ))))) w →
      (fun u (j : Fin t) => Circuit.eval ⟨gates, n + (ι j : ℕ)⟩ (List.ofFn (fun i => decide (i ∈
        (if u = 0 then ∅ else if hu : u - 1 < h + 1 then K ⟨u - 1, hu⟩ else Finset.univ))))) v
      = (fun u (j : Fin t) => Circuit.eval ⟨gates, n + (ι j : ℕ)⟩ (List.ofFn (fun i => decide (i ∈
        (if u = 0 then ∅ else if hu : u - 1 < h + 1 then K ⟨u - 1, hu⟩ else Finset.univ))))) u := by
    intro u v w huv hvw _ hfuw
    funext j
    exact hC n t gates ι _ hops hcov _ _ _
      (fun i hi => by simp only [decide_eq_true_eq] at hi ⊢; exact hmono u v huv hi)
      (fun i hi => by simp only [decide_eq_true_eq] at hi ⊢; exact hmono v w hvw hi)
      (fun j => rfl) (fun j => (congrFun hfuw j).symm) j
  obtain ⟨hcard, hconst⟩ := hR (h + 3) t _ hint
  refine lp_untop_le _ _ ((Finset.range (h + 3)).filter (fun u => 1 ≤ u ∧
      (fun u (j : Fin t) => Circuit.eval ⟨gates, n + (ι j : ℕ)⟩ (List.ofFn (fun i => decide (i ∈
        (if u = 0 then ∅ else if hu : u - 1 < h + 1 then K ⟨u - 1, hu⟩ else Finset.univ))))) u
      ≠ (fun u (j : Fin t) => Circuit.eval ⟨gates, n + (ι j : ℕ)⟩ (List.ofFn (fun i => decide (i ∈
        (if u = 0 then ∅ else if hu : u - 1 < h + 1 then K ⟨u - 1, hu⟩ else Finset.univ))))) (u - 1))) ?_ _ ?_
  · rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.filter_subset _ _, hcard⟩
  · apply Finset.sup_le
    intro uv huv
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at huv
    obtain ⟨⟨_, h2lt⟩, h12, hnob⟩ := huv
    have heq := hconst uv.1 uv.2 h12 h2lt hnob
    exact le_trans (hCo h q n S K hh hq hn hS hSS hpts hKc hKm hKn uv h12 h2lt).ge
      (lp_interval hF hC hD n n q t S gates out ι _ _ _ hq2 hS hSS hops hcov hright
        (hmono _ _ h12) (fun j => rfl) (fun j => (congrFun heq j).symm))

end PEqualNP.MetaComplexity.Ladder
