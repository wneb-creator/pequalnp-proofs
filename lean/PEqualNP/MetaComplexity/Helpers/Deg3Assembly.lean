import PEqualNP.MetaComplexity.Helpers.Deg3Restrict
import PEqualNP.MetaComplexity.Helpers.Deg3R1

/-!
# Theorem A at line-degree 3 (product shape): the assembly, conjecture until checked

`theoremA_of` derives the recorded statement of the line-degree-3 Theorem A from one card of
the skeleton taken as a hypothesis, statement verbatim: card 04 (substitution of fixed inputs).
Card 05 (the sub-incidence is large) is proved here (`card05_count`). Card 01 (output
factorization) is not a hypothesis: it is `d3r_out_and`. Card 03 is used in its repaired form `card03_restrict_of_edge`; with no
incident pair the branch-1 bound is trivial, since the counted sub-incidence is then empty.
Cards 09 (`card09_R1`), 10, 11, 12 and 13 are proved.
-/

namespace PEqualNP.MetaComplexity.Deg3

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- CARD 01 (output factorization), the skeleton's statement, from `d3r_out_and`. -/
theorem card01_out : ∀ (n : ℕ) (C : Circuit) (a b : ℕ), n ≤ C.output →
    C.gates[C.output - n]? = some { op := GateOp.and, inputs := [a, b] } →
    ∀ z : Fin n → Bool, circuitFun n C z = true ↔
      (a < C.output ∧ circuitFun n ⟨C.gates, a⟩ z = true) ∧
      (b < C.output ∧ circuitFun n ⟨C.gates, b⟩ z = true) :=
  fun n C a b hout hgate z => d3r_out_and n C a b hout hgate z

/-- CARD 10 (every point is missed by some line): more lines than lines through a point. -/
theorem card10_missed : ∀ (N q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I], 2 ≤ q → q * q ≤ N →
    (∀ p : Fin N, (Finset.univ.filter (fun l : Fin N => I p l)).card ≤ q) →
    ∀ p : Fin N, ∃ u : Fin N, ¬ I p u := by
  intro N q I _ hq hN hdeg p
  by_contra h
  push Not at h
  have h1 : (Finset.univ.filter (fun l : Fin N => I p l)) = Finset.univ := by
    ext l; simp [h l]
  have := hdeg p
  rw [h1, Finset.card_univ, Fintype.card_fin] at this
  nlinarith

/-- CARD 11 (|E| = N q). -/
theorem card11_Ecount : ∀ (N q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
    (∀ l : Fin N, (Finset.univ.filter (fun p : Fin N => I p l)).card = q) →
    (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card = N * q := by
  intro N q I _ hl
  have : (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)) =
      (Finset.univ : Finset (Fin N)).biUnion
        (fun l => (Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))) := by
    ext ⟨p, l⟩; simp
  rw [this, Finset.card_biUnion]
  · have hterm : ∀ l : Fin N,
        ((Finset.univ.filter (fun p : Fin N => I p l)).image (fun p => (p, l))).card = q := by
      intro l
      rw [Finset.card_image_of_injective _ (fun x y h => by simpa using h)]
      exact hl l
    rw [Finset.sum_congr rfl (fun l _ => hterm l)]
    simp
  · intro l _ l' _ hll'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    simp only [Finset.mem_image, Finset.mem_filter] at he he'
    obtain ⟨_, _, rfl⟩ := he
    obtain ⟨_, _, h⟩ := he'
    exact hll' (congrArg Prod.snd h).symm

/-- CARD 05 (the sub-incidence of Lemma RESTRICT is large). Lines other than w missing T number at
least N - 1 - q |T|; each keeps at least q - 1 of its points (it meets w at most once). -/
theorem card05_count : ∀ (N q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (w : Fin N)
    (T : Finset (Fin N)),
    (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
    (∀ l : Fin N, (Finset.univ.filter (fun p : Fin N => I p l)).card = q) →
    (∀ p : Fin N, (Finset.univ.filter (fun l : Fin N => I p l)).card ≤ q) →
    (N - 1 - q * T.card) * (q - 1) ≤ (Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ e.1 ∉ T ∧ ¬ I e.1 w ∧ e.2 ≠ w ∧ ¬ ∃ p' ∈ T, I p' e.2)).card := by
  intro N q I _ w T hI hl hp
  set Lg := Finset.univ.filter (fun l : Fin N => l ≠ w ∧ ¬ ∃ p' ∈ T, I p' l) with hLg
  -- A: many good lines
  have hA : N - 1 - q * T.card ≤ Lg.card := by
    have hcov : (Finset.univ : Finset (Fin N)) ⊆
        (Lg ∪ {w}) ∪ T.biUnion (fun p => Finset.univ.filter (fun l : Fin N => I p l)) := by
      intro l _
      by_cases hw : l = w
      · simp [hw]
      · by_cases hT : ∃ p' ∈ T, I p' l
        · obtain ⟨p', hp'T, hp'l⟩ := hT
          exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨p', hp'T, by simp [hp'l]⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hw, hT⟩))
    have h1 := Finset.card_le_card hcov
    have h2 := Finset.card_union_le (Lg ∪ {w})
      (T.biUnion (fun p => Finset.univ.filter (fun l : Fin N => I p l)))
    have h3 := Finset.card_union_le Lg {w}
    have h4 := Finset.card_biUnion_le (s := T) (t := fun p => Finset.univ.filter (fun l : Fin N => I p l))
    have h5 : ∑ p ∈ T, (Finset.univ.filter (fun l : Fin N => I p l)).card ≤ T.card * q :=
      Finset.sum_le_card_nsmul _ _ _ (fun p _ => hp p)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    rw [Finset.card_singleton] at h3
    have : T.card * q = q * T.card := Nat.mul_comm _ _
    omega
  -- B: each good line keeps q - 1 points
  have hB : ∀ l ∈ Lg, q - 1 ≤ (Finset.univ.filter (fun p : Fin N => I p l ∧ ¬ I p w)).card := by
    intro l hlL
    have hlw : l ≠ w := (Finset.mem_filter.1 hlL).2.1
    have hsplit : Finset.univ.filter (fun p : Fin N => I p l) ⊆
        Finset.univ.filter (fun p : Fin N => I p l ∧ ¬ I p w) ∪
          Finset.univ.filter (fun p : Fin N => I p l ∧ I p w) := by
      intro p hp'
      by_cases h : I p w <;> simp_all
    have hle1 : (Finset.univ.filter (fun p : Fin N => I p l ∧ I p w)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      by_contra hxy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      exact hI x y l w hxy hlw ⟨hx.1, hx.2, hy.1, hy.2⟩
    have := Finset.card_le_card hsplit
    have := Finset.card_union_le (Finset.univ.filter (fun p : Fin N => I p l ∧ ¬ I p w))
      (Finset.univ.filter (fun p : Fin N => I p l ∧ I p w))
    rw [hl l] at *
    omega
  -- C: the pairs
  have hsub : Lg.biUnion (fun l => (Finset.univ.filter (fun p : Fin N => I p l ∧ ¬ I p w)).image
      (fun p => (p, l))) ⊆ Finset.univ.filter (fun e : Fin N × Fin N =>
        I e.1 e.2 ∧ e.1 ∉ T ∧ ¬ I e.1 w ∧ e.2 ≠ w ∧ ¬ ∃ p' ∈ T, I p' e.2) := by
    intro e he
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, hLg] at he
    obtain ⟨l, ⟨hlw, hlT⟩, p, ⟨hpl, hpw⟩, rfl⟩ := he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hpl, fun hpT => hlT ⟨p, hpT, hpl⟩, hpw, hlw, hlT⟩
  have hcard : (Lg.biUnion (fun l => (Finset.univ.filter (fun p : Fin N => I p l ∧ ¬ I p w)).image
      (fun p => (p, l)))).card = ∑ l ∈ Lg, (Finset.univ.filter (fun p : Fin N => I p l ∧ ¬ I p w)).card := by
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl (fun l _ => ?_)
      exact Finset.card_image_of_injective _ (fun x y h => by simpa using h)
    · intro l _ l' _ hll'
      rw [Function.onFun, Finset.disjoint_left]
      intro e he he'
      simp only [Finset.mem_image] at he he'
      obtain ⟨_, _, rfl⟩ := he
      obtain ⟨_, _, h⟩ := he'
      exact hll' (congrArg Prod.snd h).symm
  have hsum : Lg.card * (q - 1) ≤ ∑ l ∈ Lg, (Finset.univ.filter (fun p : Fin N => I p l ∧ ¬ I p w)).card := by
    have := Finset.card_nsmul_le_sum Lg _ (q - 1) hB
    simpa using this
  calc (N - 1 - q * T.card) * (q - 1) ≤ Lg.card * (q - 1) := Nat.mul_le_mul_right _ hA
    _ ≤ _ := hsum
    _ = _ := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-- CARD 12 (branch 1 arithmetic). -/
theorem card12_arith1 : ∀ (N q s E : ℕ), 2 ≤ q → q * q ≤ N → E = N * q →
    (N - 1 - q * (q / 2)) * (q - 1) ≤ 48 * s + 2 * N → E < 96 * s + 5 * N + 2 * q := by
  intro N q s E hq hN hE h
  subst hE
  have hk : 2 * (q / 2) ≤ q := Nat.mul_div_le q 2
  have h1 : 1 + q * (q / 2) ≤ N := by nlinarith
  obtain ⟨M, hM⟩ : ∃ M, N = M + 1 + q * (q / 2) := ⟨N - 1 - q * (q / 2), by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have e1 : N - 1 - q * (q / 2) = M := by omega
  have e2 : q - 1 = r := by omega
  rw [e1, e2] at h
  set k := q / 2 with hkdef
  subst hr
  subst hM
  nlinarith [Nat.zero_le (M * r), Nat.zero_le (k * r), Nat.zero_le s]

/-- CARD 13 (branch 2 arithmetic). -/
theorem card13_arith2 : ∀ (N q s E : ℕ), 2 ≤ q → q * q ≤ N → E = N * q →
    N * (q / 2) + N ≤ s + 1 → E < 96 * s + 5 * N + 2 * q := by
  intro N q s E hq hN hE h
  subst hE
  have hk : q ≤ 2 * (q / 2) + 1 := by omega
  have hN4 : 4 ≤ N := by nlinarith
  nlinarith

/-- Branch 1 of Theorem A, from card 04 (a hypothesis, statement verbatim from the skeleton),
card 05, the repaired card 03 and L-meta-649. -/
theorem branch1_of_cards
    (card04_subst : ∀ (n : ℕ) (marked : Finset ℕ) (C : Circuit) (D : ℕ) (fx : Fin n → Option Bool),
      Monotone2 C → 0 < C.size → HasLineDegree n marked C D →
      ∃ C' : Circuit, Monotone2 C' ∧ C'.size ≤ C.size ∧ HasLineDegree n marked C' D ∧
        ∀ x : Fin n → Bool, circuitFun n C' x = circuitFun n C (fun i => (fx i).getD (x i))) :
    ∀ (N q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (a b : ℕ) (w : Fin N) (T : Finset (Fin N)),
    (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
    (∀ l : Fin N, (Finset.univ.filter (fun p : Fin N => I p l)).card = q) →
    (∀ p : Fin N, (Finset.univ.filter (fun l : Fin N => I p l)).card ≤ q) →
    Monotone2 C → N + N ≤ C.output →
    C.gates[C.output - (N + N)]? = some { op := GateOp.and, inputs := [a, b] } →
    (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD a 0 ≤ 2 →
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    (∀ p ∈ T, ¬ I p w) →
    circuitFun (N + N) ⟨C.gates, b⟩
      (Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ T)) (fun l => decide (l = w))) = true →
    (N - 1 - q * T.card) * (q - 1) ≤ 48 * C.size + 2 * N := by
  intro N q I _ C a b w T hI hl hp hmono hout hgate hdeg hcorr hT hb
  have hc := card05_count N q I w T hI hl hp
  by_cases hedge : ∃ p l : Fin N, I p l
  · have hpos : 0 < (⟨C.gates, a⟩ : Circuit).size := by
      show 0 < C.gates.length
      rcases Nat.lt_or_ge (C.output - (N + N)) C.gates.length with h | h
      · omega
      · rw [List.getElem?_eq_none h] at hgate; exact absurd hgate (by simp)
    obtain ⟨C', hm', hs', hd', hf'⟩ := card04_subst (N + N) (Finset.Ico N (N + N)) ⟨C.gates, a⟩ 2
      (Fin.addCases (motive := fun _ => Option Bool)
        (fun p => if p ∈ T then some true else if I p w then some false else none)
        (fun l => if l = w then some true else if ∃ p' ∈ T, I p' l then some false else none))
      hmono hpos hdeg
    have hres := card03_restrict_of_edge N I C a b w T hedge hmono hout hgate hcorr hT hb
    have h649 := PEqualNP.MetaComplexity.L649 N
      (fun p l => I p l ∧ p ∉ T ∧ ¬ I p w ∧ l ≠ w ∧ ¬ ∃ p' ∈ T, I p' l) C'
      (fun p p' l l' hpp hll h => hI p p' l l' hpp hll ⟨h.1.1, h.2.1.1, h.2.2.1.1, h.2.2.2.1⟩)
      hm' hd' (fun z => by rw [hf' z]; exact hres z)
    have : C'.size ≤ C.size := hs'
    omega
  · push Not at hedge
    have h0 : (Finset.univ.filter (fun e : Fin N × Fin N =>
        I e.1 e.2 ∧ e.1 ∉ T ∧ ¬ I e.1 w ∧ e.2 ≠ w ∧ ¬ ∃ p' ∈ T, I p' e.2)) = ∅ := by
      ext e; simp [hedge e.1 e.2]
    rw [h0, Finset.card_empty] at hc
    omega

/-- Theorem A at line-degree 3 (product shape), from card 04 of the skeleton taken as a
hypothesis (statement verbatim). The conclusion is the recorded statement of L-meta-922. -/
theorem theoremA_of
    (card04_subst : ∀ (n : ℕ) (marked : Finset ℕ) (C : Circuit) (D : ℕ) (fx : Fin n → Option Bool),
      Monotone2 C → 0 < C.size → HasLineDegree n marked C D →
      ∃ C' : Circuit, Monotone2 C' ∧ C'.size ≤ C.size ∧ HasLineDegree n marked C' D ∧
        ∀ x : Fin n → Bool, circuitFun n C' x = circuitFun n C (fun i => (fx i).getD (x i))) :
    ∀ (N q : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit) (a b : ℕ), (∀ (n m k : ℕ) (S : Fin m → Finset (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin m → ℕ) (c : Fin m → ℕ), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → (∀ i : Fin m, 2 ≤ (S i).card) → (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) → (∀ (i : Fin m) (p : Fin n), (C.wires (List.ofFn (fun q : Fin n => decide (q = p)))).getD (o i) false = true ↔ p ∈ S i) → (∀ (i : Fin m) (x : Fin n → Bool), (Finset.univ.filter (fun q : Fin n => x q = true)).card ≤ k → (∀ q ∈ S i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false) → (∀ i : Fin m, c i ≤ k) → (∀ i : Fin m, c i + 1 ≤ (S i).card) → ∑ i : Fin m, c i ≤ C.size) → (∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (T Z : Finset (Fin n)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (r : ℕ → ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ gates'.length ≤ gates.length ∧ ∀ o : ℕ, (∃ x y : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i)) ≠ PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else y i))) → ∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', r o⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn (fun i => if i ∈ T then true else if i ∈ Z then false else x i))) → (∀ (P1 L1 : ℕ) (C1 : PEqualNP.CircuitLowerBounds.Circuit) (N1 : Finset (Fin L1)), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit C1 → (∀ g1 ∈ C1.gates, g1.inputs.length ≤ 2) → PEqualNP.CircuitLowerBounds.HasLineDegree (P1 + L1) (Finset.Ico P1 (P1 + L1)) C1 1 → (∀ j1 : Fin C1.gates.length, Relation.ReflTransGen (fun a1 b1 : ℕ => a1 < b1 ∧ ∃ i1 : Fin C1.gates.length, b1 = P1 + L1 + i1.val ∧ a1 ∈ (C1.gates.get i1).inputs) (P1 + L1 + j1.val) C1.output) → (∀ w1 : Fin L1, w1 ∈ N1 ↔ Relation.ReflTransGen (fun r1 s1 : ℕ => r1 < s1 ∧ ∃ k1 : Fin C1.gates.length, s1 = P1 + L1 + k1.val ∧ r1 ∈ (C1.gates.get k1).inputs) (P1 + w1.val) C1.output) → ∃ (D1 : PEqualNP.CircuitLowerBounds.Circuit) (T1 : Finset (Fin L1)) (o1 : Fin L1 → ℕ), PEqualNP.CircuitLowerBounds.IsMonotoneCircuit D1 ∧ (∀ h1 ∈ D1.gates, h1.inputs.length ≤ 2) ∧ D1.size + N1.card ≤ C1.size + 1 ∧ ∀ (x1 : Fin P1 → Bool) (y1 : Fin L1 → Bool), C1.eval (List.ofFn x1 ++ List.ofFn y1) = (C1.eval (List.ofFn x1 ++ List.ofFn (fun v1 : Fin L1 => false)) || decide (∃ u1 : Fin L1, y1 u1 = true ∧ (u1 ∈ T1 ∨ (D1.wires (List.ofFn x1)).getD (o1 u1) false = true)))) → (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → 2 ≤ q → q * q ≤ N → (∀ l : Fin N, (Finset.univ.filter (fun p : Fin N => I p l)).card = q) → (∀ p : Fin N, (Finset.univ.filter (fun l : Fin N => I p l)).card ≤ q) → PEqualNP.MetaComplexity.Monotone2 C → N + N ≤ C.output → C.gates[C.output - (N + N)]? = some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [a, b] } → (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD a 0 ≤ 2 → (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD b 0 ≤ 1 → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card < 96 * C.size + 5 * N + 2 * q := by
  intro N q I _ C a b h270 h669 h738 hI hq hN hl hp hmono hout hgate hdega hdegb hcorr
  have hE := card11_Ecount N q I hl
  have hfac := card01_out (N + N) C a b hout hgate
  by_cases hcase : ∃ (w : Fin N) (T : Finset (Fin N)), (∀ p ∈ T, ¬ I p w) ∧ T.card ≤ q / 2 ∧
      circuitFun (N + N) ⟨C.gates, b⟩
        (Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ T)) (fun l => decide (l = w))) = true
  · obtain ⟨w, T, hT, hTc, hb⟩ := hcase
    have h1 := branch1_of_cards card04_subst N q I C a b w T hI hl hp hmono hout
      hgate hdega hcorr hT hb
    have h2 : (N - 1 - q * (q / 2)) * (q - 1) ≤ (N - 1 - q * T.card) * (q - 1) :=
      Nat.mul_le_mul_right _ (by have := Nat.mul_le_mul_left q hTc; omega)
    exact card12_arith1 N q C.size _ hq hN hE (le_trans h2 h1)
  · push Not at hcase
    have hk1 : 1 ≤ q / 2 := by omega
    have hk2 : q / 2 + 1 ≤ q := by omega
    have hR := card09_R1 N q (q / 2) I ⟨C.gates, b⟩ h270 h669 h738 hI hq hk1 hk2 hl
      (card10_missed N q I hq hN hp) hmono hdegb (by
        intro w T hTc
        constructor
        · intro hb
          by_contra hno
          push Not at hno
          exact absurd hb (by simpa using hcase w T hno hTc)
        · rintro ⟨p, hpT, hpw⟩
          have hz := (hcorr (Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ T))
            (fun l => decide (l = w)))).2 ⟨p, w, hpw, by rw [Fin.addCases_left]; simpa using hpT, by rw [Fin.addCases_right]; simp⟩
          exact ((hfac _).1 hz).2.2)
    exact card13_arith2 N q C.size _ hq hN hE hR

end PEqualNP.MetaComplexity.Deg3
