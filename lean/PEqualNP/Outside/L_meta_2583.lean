import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

open PEqualNP.CircuitLowerBounds

lemma p4_identity (a b c d : Bool) :
    (((a || c) && (b || d)) && (b || c)) =
      ((a && b) || (b && c) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

def p4Block : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [1, 2]⟩,
    ⟨.and, [4, 5]⟩, ⟨.and, [7, 6]⟩], 8⟩

def p4Stars : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 4]⟩,
    ⟨.and, [2, 3]⟩, ⟨.or, [5, 6]⟩], 7⟩

def p4Fun (z : Fin 4 → Bool) : Bool :=
  (z 0 && z 1) || (z 1 && z 2) || (z 2 && z 3)

def p4Graph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun u v =>
    (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 3)

abbrev p4GraphDec : DecidableRel p4Graph.Adj := by
  unfold p4Graph
  infer_instance

lemma p4Graph_noFourCycle : @PEqualNP.TopForm.NoFourCycle 4 p4Graph p4GraphDec := by
  decide

lemma p4Graph_bipartite : ∀ u v : Fin 4, p4Graph.Adj u v →
    decide (u = 0 ∨ u = 2) ≠ decide (v = 0 ∨ v = 2) := by
  let := p4GraphDec
  decide

lemma p4Fun_graph : ∀ z : Fin 4 → Bool,
    @PEqualNP.MetaComplexity.NestedCover.graphFun 4 p4Graph p4GraphDec ∅ z = p4Fun z := by
  decide

lemma p4Block_ao2 : PEqualNP.TopForm.IsAO2 4 p4Block := by
  decide

lemma p4Stars_ao2 : PEqualNP.TopForm.IsAO2 4 p4Stars := by
  decide

lemma p4Block_eval : ∀ z : Fin 4 → Bool,
    PEqualNP.MetaComplexity.circuitFun 4 p4Block z = p4Fun z := by
  decide

lemma p4Stars_eval : ∀ z : Fin 4 → Bool,
    PEqualNP.MetaComplexity.circuitFun 4 p4Stars z = p4Fun z := by
  decide

lemma p4Block_not_readOne : ¬ PEqualNP.ReadK.IsReadK 4 p4Block 1 := by
  decide

lemma p4Stars_readOne : PEqualNP.ReadK.IsReadK 4 p4Stars 1 := by
  decide

lemma p4Block_size : p4Block.size = 5 := rfl

lemma p4Stars_size : p4Stars.size = 4 := rfl

lemma p4Block_internal_not_below : ∀ j : Fin 4, ∃ z : Fin 4 → Bool,
    PEqualNP.EdgeOwnership.gateVal 4 p4Block j z = true ∧ p4Fun z = false := by
  decide

def p4Bypass (j : Fin 5) (b : Fin 2) : Circuit :=
  let w := (p4Block.gates.getD j ⟨.or, []⟩).inputs.getD b 0
  ⟨p4Block.gates.set j ⟨.or, [w, w]⟩, p4Block.output⟩

lemma p4Block_no_bypass : ∀ j : Fin 5, ∀ b : Fin 2,
    ∃ z : Fin 4 → Bool,
      PEqualNP.MetaComplexity.circuitFun 4 (p4Bypass j b) z ≠ p4Fun z := by
  decide


namespace Additional

open PEqualNP.CircuitLowerBounds

def p4Mixed : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [2, 3]⟩,
    ⟨.or, [1, 5]⟩, ⟨.and, [4, 6]⟩], 7⟩

def p4Fun (z : Fin 4 → Bool) : Bool :=
  (z 0 && z 1) || (z 1 && z 2) || (z 2 && z 3)

lemma p4Mixed_ao2 : PEqualNP.TopForm.IsAO2 4 p4Mixed := by
  decide

lemma p4Mixed_eval : ∀ z : Fin 4 → Bool,
    PEqualNP.MetaComplexity.circuitFun 4 p4Mixed z = p4Fun z := by
  decide

lemma p4Mixed_not_readOne : ¬ PEqualNP.ReadK.IsReadK 4 p4Mixed 1 := by
  decide

lemma p4Mixed_size : p4Mixed.size = 4 := rfl

lemma p4Mixed_internal_below : ∀ z : Fin 4 → Bool,
    PEqualNP.EdgeOwnership.gateVal 4 p4Mixed 1 z = true → p4Fun z = true := by
  decide

lemma p4Mixed_internal_term : ∀ z : Fin 4 → Bool,
    PEqualNP.EdgeOwnership.gateVal 4 p4Mixed 1 z = (z 2 && z 3) := by
  decide

end Additional

namespace DoubleStar

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [3, 6]⟩,
    ⟨.and, [1, 7]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [8, 10]⟩], 11⟩

def disabled : Circuit :=
  ⟨circuit.gates.set 0 ⟨.or, []⟩, circuit.output⟩

def edgeFun (z : Fin 6 → Bool) : Bool :=
  (z 0 && z 1) || (z 0 && z 2) || (z 0 && z 3) ||
    (z 1 && z 4) || (z 1 && z 5)

def changedFun (z : Fin 6 → Bool) : Bool :=
  z 3 && (z 0 || (z 1 && (z 4 || z 5)))

lemma circuit_ao2 : PEqualNP.TopForm.IsAO2 6 circuit := by
  decide

lemma circuit_size : circuit.size = 6 := rfl

lemma circuit_eval : ∀ z : Fin 6 → Bool,
    PEqualNP.MetaComplexity.circuitFun 6 circuit z = edgeFun z := by
  decide

lemma disabled_eval : ∀ z : Fin 6 → Bool,
    PEqualNP.MetaComplexity.circuitFun 6 disabled z = changedFun z := by
  decide

lemma circuit_prime_iff : ∀ S : Finset (Fin 6),
    PEqualNP.ReadK.IsPrimeImplicant 6 circuit S ↔
      S = {0, 1} ∨ S = {0, 2} ∨ S = {0, 3} ∨ S = {1, 4} ∨ S = {1, 5} := by
  decide

lemma disabled_new_triple :
    PEqualNP.ReadK.IsPrimeImplicant 6 disabled {1, 3, 4} := by
  decide

lemma circuit_triple_not_prime :
    ¬ PEqualNP.ReadK.IsPrimeImplicant 6 circuit {1, 3, 4} := by
  decide

lemma disabled_prime_iff : ∀ S : Finset (Fin 6),
    PEqualNP.ReadK.IsPrimeImplicant 6 disabled S ↔
      S = {0, 3} ∨ S = {1, 3, 4} ∨ S = {1, 3, 5} := by
  decide

def pruned : Circuit :=
  ⟨[⟨.or, [4, 5]⟩, ⟨.and, [1, 6]⟩,
    ⟨.or, [0, 7]⟩, ⟨.and, [3, 8]⟩], 9⟩

lemma pruned_ao2 : PEqualNP.TopForm.IsAO2 6 pruned := by
  decide

lemma pruned_size : pruned.size = 4 := rfl

lemma pruned_eval : ∀ z : Fin 6 → Bool,
    PEqualNP.MetaComplexity.circuitFun 6 pruned z = changedFun z := by
  decide

lemma pruned_triple_prime :
    PEqualNP.ReadK.IsPrimeImplicant 6 pruned {1, 3, 4} := by
  decide

end DoubleStar

namespace PathDeletion

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [5, 1]⟩, ⟨.or, [3, 6]⟩,
    ⟨.or, [4, 0]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [4, 2]⟩,
    ⟨.or, [9, 10]⟩], 11⟩

def disabled : Circuit :=
  ⟨circuit.gates.set 5 ⟨.or, []⟩, circuit.output⟩

def edgeFun (z : Fin 5 → Bool) : Bool :=
  (z 0 && z 1) || (z 0 && z 3) || (z 3 && z 4) || (z 4 && z 2)

def changedFun (z : Fin 5 → Bool) : Bool :=
  (z 0 && z 1) || (z 0 && z 3) || (z 3 && z 4) || (z 1 && z 2 && z 4)

def graph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun u v =>
    (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 3) ∨ (u = 3 ∧ v = 4) ∨ (u = 4 ∧ v = 2)

abbrev graphDec : DecidableRel graph.Adj := by
  unfold graph
  infer_instance

lemma graph_noFourCycle : @PEqualNP.TopForm.NoFourCycle 5 graph graphDec := by
  decide

lemma graph_bipartite : ∀ u v : Fin 5, graph.Adj u v →
    decide (u = 0 ∨ u = 4) ≠ decide (v = 0 ∨ v = 4) := by
  let := graphDec
  decide

lemma circuit_ao2 : PEqualNP.TopForm.IsAO2 5 circuit := by
  decide

lemma circuit_size : circuit.size = 7 := rfl

lemma circuit_eval : ∀ z : Fin 5 → Bool,
    PEqualNP.MetaComplexity.circuitFun 5 circuit z = edgeFun z := by
  decide

lemma disabled_eval : ∀ z : Fin 5 → Bool,
    PEqualNP.MetaComplexity.circuitFun 5 disabled z = changedFun z := by
  decide

lemma graph_eval : ∀ z : Fin 5 → Bool,
    @PEqualNP.MetaComplexity.NestedCover.graphFun 5 graph graphDec ∅ z = edgeFun z := by
  decide

lemma circuit_topForm : @PEqualNP.TopForm.TopForm 5 graph graphDec circuit := by
  decide

lemma circuit_prime_iff : ∀ S : Finset (Fin 5),
    PEqualNP.ReadK.IsPrimeImplicant 5 circuit S ↔
      S = {0, 1} ∨ S = {0, 3} ∨ S = {3, 4} ∨ S = {2, 4} := by
  decide

lemma disabled_prime_iff : ∀ S : Finset (Fin 5),
    PEqualNP.ReadK.IsPrimeImplicant 5 disabled S ↔
      S = {0, 1} ∨ S = {0, 3} ∨ S = {3, 4} ∨ S = {1, 2, 4} := by
  decide

lemma disabled_new_triple :
    PEqualNP.ReadK.IsPrimeImplicant 5 disabled {1, 2, 4} := by
  decide

lemma circuit_triple_not_prime :
    ¬ PEqualNP.ReadK.IsPrimeImplicant 5 circuit {1, 2, 4} := by
  decide

def pruned : Circuit := ⟨circuit.gates.take 5, 9⟩

lemma pruned_ao2 : PEqualNP.TopForm.IsAO2 5 pruned := by
  decide

lemma pruned_size : pruned.size = 5 := rfl

lemma pruned_eval : ∀ z : Fin 5 → Bool,
    PEqualNP.MetaComplexity.circuitFun 5 pruned z = changedFun z := by
  decide

lemma pruned_triple_prime :
    PEqualNP.ReadK.IsPrimeImplicant 5 pruned {1, 2, 4} := by
  decide

end PathDeletion

lemma p4Mixed_not_topForm :
    ¬ @PEqualNP.TopForm.TopForm 4 p4Graph p4GraphDec Additional.p4Mixed := by
  decide



open scoped BigOperators

lemma plane_point_degree (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (p : Fin N) : (Finset.univ.filter (I p)).card = q + 1 := by
  classical
  let L := Finset.univ.filter (I p)
  have hsum : ∑ l ∈ L, (Finset.univ.filter (fun r => I r l)).card = L.card * (q + 1) := by
    simp_rw [hcol]
    simp
  have hcommon : ∀ r : Fin N, r ≠ p → (L.filter (I r)).card = 1 := by
    intro r hr
    obtain ⟨l, hl, huniq⟩ := hunique p r (Ne.symm hr)
    apply Finset.card_eq_one.mpr
    refine ⟨l, ?_⟩
    ext k
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hk => huniq k hk, fun hk => hk ▸ hl⟩
  have hself : (L.filter (I p)).card = L.card := by
    congr 1
    ext l
    simp [L]
  have hswap : ∑ l ∈ L, (Finset.univ.filter (fun r => I r l)).card =
      ∑ r : Fin N, (L.filter (I r)).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
  have hrow : ∑ r : Fin N, (L.filter (I r)).card = N - 1 + L.card := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ p), hself]
    have he : ∑ r ∈ Finset.univ.erase p, (L.filter (I r)).card = N - 1 := by
      calc
        _ = ∑ r ∈ Finset.univ.erase p, 1 := by
          apply Finset.sum_congr rfl
          intro r hr
          exact hcommon r (Finset.mem_erase.mp hr).1
        _ = _ := by simp
    rw [he]
  rw [hswap, hrow] at hsum
  have hNm : N - 1 = q ^ 2 + q := by omega
  rw [hNm] at hsum
  have hcancel : L.card * q = (q + 1) * q := by
    nlinarith
  exact Nat.eq_of_mul_eq_mul_right hq hcancel



open scoped BigOperators

lemma expansion_arithmetic (q s t : ℕ) (hs : 0 < s) (hsq : s ≤ q ^ 2)
    (h : (s * (q + 1)) ^ 2 ≤ t * (s * (q + s))) : s + q ≤ t := by
  have hcancel : s * (q + 1) ^ 2 ≤ t * (q + s) := by
    have hx : s * (s * (q + 1) ^ 2) ≤ s * (t * (q + s)) := by
      convert h using 1 <;> ring
    exact Nat.le_of_mul_le_mul_left hx hs
  have hsq_int : (s : ℤ) ≤ (q : ℤ) ^ 2 := by exact_mod_cast hsq
  have hprod : 0 ≤ ((s : ℤ) - 1) * ((q : ℤ) ^ 2 - s) := by
    apply mul_nonneg <;> omega
  have hc : (s : ℤ) * (q + 1) ^ 2 ≤ t * (q + s) := by
    exact_mod_cast hcancel
  by_contra ht
  have hlt : (t : ℤ) + 1 ≤ s + q := by omega
  have hspos : 0 < (s : ℤ) := by omega
  have hqpos : 0 ≤ (q : ℤ) := by omega
  nlinarith [mul_le_mul_of_nonneg_right hlt (by positivity : 0 ≤ (q : ℤ) + s)]

lemma incidence_moment_one {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (I : α → β → Prop) [DecidableRel I]
    (q : ℕ) (hrow : ∀ p ∈ S, (T.filter (I p)).card = q + 1) :
    ∑ l ∈ T, (S.filter (fun p => I p l)).card = S.card * (q + 1) := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    (∑ p ∈ S, ∑ l ∈ T, (if I p l then 1 else 0)) = ∑ p ∈ S, (q + 1) := by
      apply Finset.sum_congr rfl
      intro p hp
      simpa only [Finset.card_filter] using hrow p hp
    _ = _ := by simp

lemma incidence_moment_two {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (I : α → β → Prop) [DecidableRel I]
    (q : ℕ) (hrow : ∀ p ∈ S, (T.filter (I p)).card = q + 1)
    (hpair : ∀ p ∈ S, ∀ r ∈ S, p ≠ r →
      (T.filter (fun l => I p l ∧ I r l)).card = 1) :
    ∑ l ∈ T, (S.filter (fun p => I p l)).card ^ 2 = S.card * (q + S.card) := by
  classical
  have h_expand : ∀ l ∈ T, (S.filter (fun p => I p l)).card ^ 2 =
      ∑ p ∈ S, ∑ r ∈ S, if I p l ∧ I r l then 1 else 0 := by
    intro l hl
    rw [pow_two]
    simp only [Finset.card_filter, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro r hr
    by_cases hp' : I p l <;> by_cases hr' : I r l <;> simp [hp', hr']
  simp_rw [Finset.sum_congr rfl h_expand]
  rw [Finset.sum_comm]
  have h_each : ∀ p ∈ S,
      ∑ l ∈ T, ∑ r ∈ S, (if I p l ∧ I r l then 1 else 0) = q + S.card := by
    intro p hp
    rw [Finset.sum_comm]
    have h_inside : ∀ r ∈ S,
        ∑ l ∈ T, (if I p l ∧ I r l then 1 else 0) = if r = p then q + 1 else 1 := by
      intro r hr
      by_cases h : r = p
      · subst r
        simpa only [Finset.card_filter, and_self, ite_true] using hrow p hp
      · simpa only [Finset.card_filter, ite_eq_right h] using hpair p hp r hr (Ne.symm h)
    rw [Finset.sum_congr rfl h_inside]
    rw [← Finset.sum_erase_add _ _ hp]
    have he : ∑ r ∈ S.erase p, (if r = p then q + 1 else 1) = (S.erase p).card := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro r hr
      have hne := (Finset.mem_erase.mp hr).1
      simp [hne]
    rw [he]
    simp only [ite_true]
    have hcard := Finset.card_erase_add_one hp
    omega
  rw [Finset.sum_congr rfl h_each]
  simp

lemma incidence_neighborhood_expansion {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (I : α → β → Prop) [DecidableRel I]
    (q : ℕ) (hS : S.Nonempty) (hsq : S.card ≤ q ^ 2)
    (hrow : ∀ p ∈ S, (T.filter (I p)).card = q + 1)
    (hpair : ∀ p ∈ S, ∀ r ∈ S, p ≠ r →
      (T.filter (fun l => I p l ∧ I r l)).card = 1) :
    S.card + q ≤ T.card := by
  have hc := sq_sum_le_card_mul_sum_sq (s := T)
    (f := fun l => (S.filter (fun p => I p l)).card)
  rw [incidence_moment_one S T I q hrow, incidence_moment_two S T I q hrow hpair] at hc
  exact expansion_arithmetic q S.card T.card (Finset.card_pos.mpr hS) hsq hc

lemma plane_mixed_cover_bound (q N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hN : N = q ^ 2 + q + 1)
    (hrow : ∀ p : Fin N, (Finset.univ.filter (I p)).card = q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (A B : Finset (Fin N)) (hA : A ≠ Finset.univ) (hB : B ≠ Finset.univ)
    (hcover : ∀ p l : Fin N, I p l → p ∈ A ∨ l ∈ B) :
    N + q ≤ A.card + B.card := by
  classical
  let S := Finset.univ \ A
  have houtsideA : ∃ p : Fin N, p ∉ A := by
    by_contra! h
    exact hA (Finset.eq_univ_iff_forall.mpr h)
  have houtsideB : ∃ l : Fin N, l ∉ B := by
    by_contra! h
    exact hB (Finset.eq_univ_iff_forall.mpr h)
  have hS : S.Nonempty := by
    obtain ⟨p, hp⟩ := houtsideA
    exact ⟨p, by simp [S, hp]⟩
  have hnotA : ∀ p ∈ S, p ∉ A := by
    intro p hp
    exact (Finset.mem_sdiff.mp hp).2
  have hneigh : ∀ p ∈ S, ∀ l, I p l → l ∈ B := by
    intro p hp l hpl
    exact (hcover p l hpl).resolve_left (hnotA p hp)
  have hsquare : S.card ≤ q ^ 2 := by
    obtain ⟨l, hl⟩ := houtsideB
    let L := Finset.univ.filter (fun p => I p l)
    have hLcard : L.card = q + 1 := hcol l
    have hsub : S ⊆ Finset.univ \ L := by
      intro p hp
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hpL
      exact hl (hneigh p hp l (Finset.mem_filter.mp hpL).2)
    have hle := Finset.card_le_card hsub
    have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ L)
    simp only [Finset.card_univ, Fintype.card_fin, hLcard] at hsum
    omega
  have hrowB : ∀ p ∈ S, (B.filter (I p)).card = q + 1 := by
    intro p hp
    have heq : B.filter (I p) = Finset.univ.filter (I p) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨And.right, fun hpl => ⟨hneigh p hp l hpl, hpl⟩⟩
    rw [heq]
    exact hrow p
  have hpairB : ∀ p ∈ S, ∀ r ∈ S, p ≠ r →
      (B.filter (fun l => I p l ∧ I r l)).card = 1 := by
    intro p hp r hr hpr
    obtain ⟨l, hl, huniq⟩ := hunique p r hpr
    apply Finset.card_eq_one.mpr
    refine ⟨l, ?_⟩
    ext k
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hk
      exact huniq k hk.2
    · intro hk
      subst k
      exact ⟨hneigh p hp l hl.1, hl⟩
  have hexp := incidence_neighborhood_expansion S B I q hS hsquare hrowB hpairB
  have hpart : S.card + A.card = N := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  omega


namespace PartialCover

def uncovered {m n : ℕ} (E : Finset (Fin m × Fin n))
    (A : Finset (Fin m)) (B : Finset (Fin n)) : Finset (Fin m × Fin n) :=
  E.filter fun e => e.1 ∉ A ∧ e.2 ∉ B

lemma completion_avoiding {m n : ℕ} (E : Finset (Fin m × Fin n))
    (A : Finset (Fin m)) (B : Finset (Fin n))
    (p : Fin m) (l : Fin n) (hp : p ∉ A) (hl : l ∉ B) (hpl : (p, l) ∉ E) :
    ∃ A' : Finset (Fin m), ∃ B' : Finset (Fin n),
      p ∉ A' ∧ l ∉ B' ∧
      (∀ e ∈ E, e.1 ∈ A' ∨ e.2 ∈ B') ∧
      A'.card + B'.card ≤ A.card + B.card + (uncovered E A B).card := by
  let U := uncovered E A B
  let P := U.filter fun e => e.1 ≠ p
  let L := U.filter fun e => e.1 = p
  refine ⟨A ∪ P.image Prod.fst, B ∪ L.image Prod.snd, ?_, ?_, ?_, ?_⟩
  · simp only [Finset.mem_union, not_or]
    refine ⟨hp, ?_⟩
    intro h
    obtain ⟨e, he, hep⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp he).2 hep
  · simp only [Finset.mem_union, not_or]
    refine ⟨hl, ?_⟩
    intro h
    obtain ⟨e, he, hel⟩ := Finset.mem_image.mp h
    obtain ⟨heU, hep⟩ := Finset.mem_filter.mp he
    have heE : e ∈ E := (Finset.mem_filter.mp heU).1
    have heeq : e = (p, l) := Prod.ext hep hel
    exact hpl (heeq ▸ heE)
  · intro e he
    by_cases hA : e.1 ∈ A
    · exact Or.inl (Finset.mem_union_left _ hA)
    by_cases hB : e.2 ∈ B
    · exact Or.inr (Finset.mem_union_left _ hB)
    have heU : e ∈ U := Finset.mem_filter.mpr ⟨he, hA, hB⟩
    by_cases hep : e.1 = p
    · exact Or.inr (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨heU, hep⟩, rfl⟩))
    · exact Or.inl (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨heU, hep⟩, rfl⟩))
  · have hA := Finset.card_union_le A (P.image Prod.fst)
    have hB := Finset.card_union_le B (L.image Prod.snd)
    have hP := Finset.card_image_le (s := P) (f := Prod.fst)
    have hL := Finset.card_image_le (s := L) (f := Prod.snd)
    have hsum : L.card + P.card = U.card := by
      exact Finset.card_filter_add_card_filter_not (s := U) (fun e => e.1 = p)
    change (A ∪ P.image Prod.fst).card + (B ∪ L.image Prod.snd).card ≤
      A.card + B.card + U.card
    omega

lemma partial_cover_bound (N q : ℕ) (E : Finset (Fin N × Fin N))
    (hN : q + 1 ≤ N)
    (hfull : ∀ A B : Finset (Fin N), A ≠ Finset.univ → B ≠ Finset.univ →
      (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) → N + q ≤ A.card + B.card)
    (A B : Finset (Fin N)) (hA : A ≠ Finset.univ) (hB : B ≠ Finset.univ) :
    N + q ≤ A.card + B.card + (uncovered E A B).card := by
  classical
  by_cases h : ∃ p l : Fin N, p ∉ A ∧ l ∉ B ∧ (p, l) ∉ E
  · obtain ⟨p, l, hp, hl, hpl⟩ := h
    obtain ⟨A', B', hp', hl', hcov, hcost⟩ := completion_avoiding E A B p l hp hl hpl
    have hA' : A' ≠ Finset.univ := by intro heq; exact hp' (heq ▸ Finset.mem_univ p)
    have hB' : B' ≠ Finset.univ := by intro heq; exact hl' (heq ▸ Finset.mem_univ l)
    exact (hfull A' B' hA' hB' hcov).trans hcost
  · let S : Finset (Fin N) := Finset.univ \ A
    let T : Finset (Fin N) := Finset.univ \ B
    have hSpos : 0 < S.card := by
      apply Finset.card_pos.mpr
      obtain ⟨p, hp⟩ : ∃ p : Fin N, p ∉ A := by
        by_contra h
        apply hA
        ext p
        simp only [Finset.mem_univ, iff_true]
        exact not_not.mp (fun hp => h ⟨p, hp⟩)
      exact ⟨p, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hp⟩⟩
    have hTpos : 0 < T.card := by
      apply Finset.card_pos.mpr
      obtain ⟨l, hl⟩ : ∃ l : Fin N, l ∉ B := by
        by_contra h
        apply hB
        ext l
        simp only [Finset.mem_univ, iff_true]
        exact not_not.mp (fun hl => h ⟨l, hl⟩)
      exact ⟨l, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hl⟩⟩
    have hU : uncovered E A B = S ×ˢ T := by
      ext e
      simp only [uncovered, Finset.mem_filter, Finset.mem_product, S, T,
        Finset.mem_sdiff, Finset.mem_univ, true_and]
      constructor
      · exact fun he => he.2
      · intro he
        refine ⟨?_, he⟩
        by_contra heE
        exact h ⟨e.1, e.2, he.1, he.2, heE⟩
    have hScard : S.card + A.card = N := by
      simpa [S] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
    have hTcard : T.card + B.card = N := by
      simpa [T] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
    have hprod : S.card + T.card ≤ S.card * T.card + 1 := by
      have hmul : (0 : ℤ) ≤ ((S.card : ℤ) - 1) * ((T.card : ℤ) - 1) :=
        mul_nonneg (by omega) (by omega)
      exact_mod_cast (show (S.card : ℤ) + T.card ≤ (S.card : ℤ) * T.card + 1 by
        nlinarith)
    rw [hU, Finset.card_product]
    omega

end PartialCover

lemma plane_mixed_cover_bound_of_posted (q N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (A B : Finset (Fin N)) (hA : A ≠ Finset.univ) (hB : B ≠ Finset.univ)
    (hcover : ∀ p l : Fin N, I p l → p ∈ A ∨ l ∈ B) :
    N + q ≤ A.card + B.card := by
  exact plane_mixed_cover_bound q N I hN
    (plane_point_degree q N I (by omega) hN hcol hunique) hcol hunique A B hA hB hcover

lemma plane_partial_cover_bound (q N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (A B : Finset (Fin N)) (hA : A ≠ Finset.univ) (hB : B ≠ Finset.univ) :
    N + q ≤ A.card + B.card +
      (Finset.univ.filter (fun e : Fin N × Fin N =>
        I e.1 e.2 ∧ e.1 ∉ A ∧ e.2 ∉ B)).card := by
  let E := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  have hfull : ∀ A' B' : Finset (Fin N), A' ≠ Finset.univ → B' ≠ Finset.univ →
      (∀ e ∈ E, e.1 ∈ A' ∨ e.2 ∈ B') → N + q ≤ A'.card + B'.card := by
    intro A' B' hA' hB' hcov
    apply plane_mixed_cover_bound_of_posted q N I hq hN hcol hunique A' B' hA' hB'
    intro p l hpl
    exact hcov (p, l) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩)
  have h := PartialCover.partial_cover_bound N q E (by omega) hfull A B hA hB
  simpa only [PartialCover.uncovered, E, Finset.filter_filter, and_assoc] using h

lemma mixed_partial_cover_penalty (q N u t penalty : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (A B : Finset (Fin N)) (hA : A ≠ Finset.univ) (hB : B ≠ Finset.univ)
    (hsize : A.card + B.card ≤ t)
    (hmissing : (Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ e.1 ∉ A ∧ e.2 ∉ B)).card ≤ u)
    (hledger : t + penalty + 1 ≤ N + u) : q + penalty + 1 ≤ 2 * u := by
  have h := plane_partial_cover_bound q N I hq hN hcol hunique A B hA hB
  omega


namespace LowerBound

open PEqualNP.CircuitLowerBounds

def sel4 (i : BitVec 3) : BitVec 16 :=
  if i = 0 then 0xAAAA else if i = 1 then 0xCCCC else
    if i = 2 then 0xF0F0 else if i = 3 then 0xFF00 else 0

def sel5 (i : BitVec 3) (g0 : BitVec 16) : BitVec 16 :=
  if i = 4 then g0 else sel4 i

def sel6 (i : BitVec 3) (g0 g1 : BitVec 16) : BitVec 16 :=
  if i = 5 then g1 else sel5 i g0

def sel7 (i : BitVec 3) (g0 g1 g2 : BitVec 16) : BitVec 16 :=
  if i = 6 then g2 else sel6 i g0 g1

def tableGate (isAnd : Bool) (a b : BitVec 16) : BitVec 16 :=
  if isAnd then a &&& b else a ||| b

def target : BitVec 16 :=
  (0xAAAA &&& 0xCCCC) ||| (0xCCCC &&& 0xF0F0) ||| (0xF0F0 &&& 0xFF00)


set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma case_0_0_false : ∀ (o1 o2 : Bool)
    (a1 b1 : Fin 5), a1 ≤ b1 → ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate false (sel4 (BitVec.ofNat 3 0)) (sel4 (BitVec.ofNat 3 0))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1) (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma case_0_1_false : ∀ (o1 o2 : Bool)
    (a1 b1 : Fin 5), a1 ≤ b1 → ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate false (sel4 (BitVec.ofNat 3 0)) (sel4 (BitVec.ofNat 3 1))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1) (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma case_0_1_true : ∀ (o1 o2 : Bool)
    (a1 b1 : Fin 5), a1 ≤ b1 → ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate true (sel4 (BitVec.ofNat 3 0)) (sel4 (BitVec.ofNat 3 1))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1) (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma case_0_2_false : ∀ (o1 o2 : Bool)
    (a1 b1 : Fin 5), a1 ≤ b1 → ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate false (sel4 (BitVec.ofNat 3 0)) (sel4 (BitVec.ofNat 3 2))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1) (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma case_0_2_true : ∀ (o1 o2 : Bool)
    (a1 b1 : Fin 5), a1 ≤ b1 → ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate true (sel4 (BitVec.ofNat 3 0)) (sel4 (BitVec.ofNat 3 2))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1) (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma case_0_3_false : ∀ (o1 o2 : Bool)
    (a1 b1 : Fin 5), a1 ≤ b1 → ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate false (sel4 (BitVec.ofNat 3 0)) (sel4 (BitVec.ofNat 3 3))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1) (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma case_0_3_true : ∀ (o1 o2 : Bool)
    (a1 b1 : Fin 5), a1 ≤ b1 → ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate true (sel4 (BitVec.ofNat 3 0)) (sel4 (BitVec.ofNat 3 3))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1) (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma case_1_1_false : ∀ (o1 o2 : Bool)
    (a1 b1 : Fin 5), a1 ≤ b1 → ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate false (sel4 (BitVec.ofNat 3 1)) (sel4 (BitVec.ofNat 3 1))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1) (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma case_1_2_false : ∀ (o1 o2 : Bool)
    (a1 b1 : Fin 5), a1 ≤ b1 → ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate false (sel4 (BitVec.ofNat 3 1)) (sel4 (BitVec.ofNat 3 2))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1) (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma case_1_2_true : ∀ (o1 o2 : Bool)
    (a1 b1 : Fin 5), a1 ≤ b1 → ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate true (sel4 (BitVec.ofNat 3 1)) (sel4 (BitVec.ofNat 3 2))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1) (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma case_1_3_false : ∀ (o1 o2 : Bool)
    (a1 b1 : Fin 5), a1 ≤ b1 → ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate false (sel4 (BitVec.ofNat 3 1)) (sel4 (BitVec.ofNat 3 3))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1) (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma case_1_3_true : ∀ (o1 o2 : Bool)
    (a1 b1 : Fin 5), a1 ≤ b1 → ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate true (sel4 (BitVec.ofNat 3 1)) (sel4 (BitVec.ofNat 3 3))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1) (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma case_2_2_false : ∀ (o1 o2 : Bool)
    (a1 b1 : Fin 5), a1 ≤ b1 → ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate false (sel4 (BitVec.ofNat 3 2)) (sel4 (BitVec.ofNat 3 2))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1) (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma case_2_3_false : ∀ (o1 o2 : Bool)
    (a1 b1 : Fin 5), a1 ≤ b1 → ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate false (sel4 (BitVec.ofNat 3 2)) (sel4 (BitVec.ofNat 3 3))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1) (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma case_2_3_true : ∀ (o1 o2 : Bool)
    (a1 b1 : Fin 5), a1 ≤ b1 → ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate true (sel4 (BitVec.ofNat 3 2)) (sel4 (BitVec.ofNat 3 3))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1) (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
lemma case_3_3_false : ∀ (o1 o2 : Bool)
    (a1 b1 : Fin 5), a1 ≤ b1 → ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate false (sel4 (BitVec.ofNat 3 3)) (sel4 (BitVec.ofNat 3 3))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1) (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target := by
  decide +kernel

set_option maxHeartbeats 0 in
lemma threeGate_sorted_final : ∀ (o0 o1 o2 : Bool)
    (a0 b0 : Fin 4), a0 ≤ b0 → ∀ (a1 b1 : Fin 5), a1 ≤ b1 →
    ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate o0 (sel4 (BitVec.ofNat 3 a0.val)) (sel4 (BitVec.ofNat 3 b0.val))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1) (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target := by
  intro o0 o1 o2 a0 b0 h0 a1 b1 h1 a2 b2 h2
  fin_cases a0 <;> fin_cases b0 <;> cases o0
  all_goals first
    | omega
    | exact case_0_0_false o1 o2 a1 b1 h1 a2 b2 h2
    | exact case_0_1_false o1 o2 a1 b1 h1 a2 b2 h2
    | exact case_0_1_true o1 o2 a1 b1 h1 a2 b2 h2
    | exact case_0_2_false o1 o2 a1 b1 h1 a2 b2 h2
    | exact case_0_2_true o1 o2 a1 b1 h1 a2 b2 h2
    | exact case_0_3_false o1 o2 a1 b1 h1 a2 b2 h2
    | exact case_0_3_true o1 o2 a1 b1 h1 a2 b2 h2
    | exact case_1_1_false o1 o2 a1 b1 h1 a2 b2 h2
    | exact case_1_2_false o1 o2 a1 b1 h1 a2 b2 h2
    | exact case_1_2_true o1 o2 a1 b1 h1 a2 b2 h2
    | exact case_1_3_false o1 o2 a1 b1 h1 a2 b2 h2
    | exact case_1_3_true o1 o2 a1 b1 h1 a2 b2 h2
    | exact case_2_2_false o1 o2 a1 b1 h1 a2 b2 h2
    | exact case_2_3_false o1 o2 a1 b1 h1 a2 b2 h2
    | exact case_2_3_true o1 o2 a1 b1 h1 a2 b2 h2
    | exact case_3_3_false o1 o2 a1 b1 h1 a2 b2 h2

def inputTables : List (BitVec 16) := [0xAAAA, 0xCCCC, 0xF0F0, 0xFF00]

def clip (i : ℕ) : BitVec 3 := if i < 7 then BitVec.ofNat 3 i else 7

lemma sel4_getD (i : ℕ) : inputTables.getD i 0 = sel4 (clip i) := by
  by_cases h : i < 7
  · interval_cases i <;> rfl
  · have hn : inputTables.length ≤ i := by simp [inputTables]; omega
    simp [List.getD, List.getElem?_eq_none hn, clip, h, sel4]

lemma sel5_getD (i : ℕ) (g0 : BitVec 16) :
    (inputTables ++ [g0]).getD i 0 = sel5 (clip i) g0 := by
  by_cases h : i < 7
  · interval_cases i <;> rfl
  · have hn : (inputTables ++ [g0]).length ≤ i := by simp [inputTables]; omega
    simp [List.getD, List.getElem?_eq_none hn, clip, h, sel5, sel4]

lemma sel6_getD (i : ℕ) (g0 g1 : BitVec 16) :
    (inputTables ++ [g0, g1]).getD i 0 = sel6 (clip i) g0 g1 := by
  by_cases h : i < 7
  · interval_cases i <;> rfl
  · have hn : (inputTables ++ [g0, g1]).length ≤ i := by simp [inputTables]; omega
    simp [List.getD, List.getElem?_eq_none hn, clip, h, sel6, sel5, sel4]

lemma sel7_getD (i : ℕ) (g0 g1 g2 : BitVec 16) :
    (inputTables ++ [g0, g1, g2]).getD i 0 = sel7 (clip i) g0 g1 g2 := by
  by_cases h : i < 7
  · interval_cases i <;> rfl
  · have hn : (inputTables ++ [g0, g1, g2]).length ≤ i := by simp [inputTables]; omega
    simp [List.getD, List.getElem?_eq_none hn, clip, h, sel7, sel6, sel5, sel4]

lemma getD_map_eq {α β : Type} (f : α → β) (w : List α) (i : ℕ) (d : α) :
    (w.map f).getD i (f d) = f (w.getD i d) := by
  induction w generalizing i with
  | nil => simp [List.getD]
  | cons a w ih => cases i <;> simp_all [List.getD]

def inputOf (r : Fin 16) : Fin 4 → Bool := fun i => r.val.testBit i.val

def p4Fun (z : Fin 4 → Bool) : Bool :=
  (z 0 && z 1) || (z 1 && z 2) || (z 2 && z 3)

lemma inputTables_sem : ∀ r : Fin 16,
    inputTables.map (fun t => t.getLsbD r.val) = List.ofFn (inputOf r) := by
  decide

lemma target_sem : ∀ r : Fin 16, target.getLsbD r.val = p4Fun (inputOf r) := by
  decide

def gateFrom (o : Bool) (a b : ℕ) : Gate := ⟨if o then .and else .or, [a, b]⟩

def tableStep (w : List (BitVec 16)) (g : Gate) : List (BitVec 16) :=
  let a := w.getD (g.inputs.getD 0 0) 0
  let b := w.getD (g.inputs.getD 1 0) 0
  w ++ [match g.op with
    | .and => a &&& b
    | .or => a ||| b
    | _ => 0]

lemma tableStep_from (w : List (BitVec 16)) (o : Bool) (a b : ℕ) :
    tableStep w (gateFrom o a b) = w ++ [tableGate o (w.getD a 0) (w.getD b 0)] := by
  cases o <;> rfl

lemma tableStep_sem (w : List (BitVec 16)) (r : Fin 16) (o : Bool) (a b : ℕ) :
    (tableStep w (gateFrom o a b)).map (fun t => t.getLsbD r.val) =
      w.map (fun t => t.getLsbD r.val) ++
        [(gateFrom o a b).op.eval ((gateFrom o a b).inputs.map fun i =>
          (w.map (fun t => t.getLsbD r.val)).getD i false)] := by
  have hm (i : ℕ) : (w.map (fun t => t.getLsbD r.val)).getD i false =
      (w.getD i 0).getLsbD r.val := by
    simpa using getD_map_eq (fun t : BitVec 16 => t.getLsbD r.val) w i 0
  rw [tableStep_from]
  simp only [List.map_append, List.map_cons, List.map_nil, gateFrom]
  rw [hm a, hm b]
  cases o <;> simp [tableGate, GateOp.eval]

lemma gate_shape (g : Gate) (ho : g.op = .and ∨ g.op = .or)
    (hl : g.inputs.length = 2) : ∃ o a b, g = gateFrom o a b := by
  rcases g with ⟨op, inputs⟩
  rcases List.length_eq_two.mp hl with ⟨a, b, rfl⟩
  rcases ho with rfl | rfl
  · exact ⟨true, a, b, rfl⟩
  · exact ⟨false, a, b, rfl⟩

def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_sem (gs : List Gate) (w : List (BitVec 16)) (r : Fin 16)
    (h : ∀ g ∈ gs, ∃ o a b, g = gateFrom o a b) :
    (gs.foldl tableStep w).map (fun t => t.getLsbD r.val) =
      gs.foldl boolStep (w.map (fun t => t.getLsbD r.val)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨o, a, b, rfl⟩ := h g (by simp)
    have ht : ∀ g ∈ gs, ∃ o a b, g = gateFrom o a b := by
      intro g hg
      exact h g (by simp [hg])
    simp only [List.foldl_cons]
    rw [ih _ ht, tableStep_sem]
    rfl

lemma table_output_sem (C : Circuit) (r : Fin 16)
    (h : ∀ g ∈ C.gates, ∃ o a b, g = gateFrom o a b) :
    ((C.gates.foldl tableStep inputTables).getD C.output 0).getLsbD r.val =
      PEqualNP.MetaComplexity.circuitFun 4 C (inputOf r) := by
  have hm := getD_map_eq (fun t : BitVec 16 => t.getLsbD r.val)
    (C.gates.foldl tableStep inputTables) C.output 0
  rw [← hm, fold_sem C.gates inputTables r h, inputTables_sem]
  simp [PEqualNP.MetaComplexity.circuitFun, Circuit.eval, Circuit.wires]
  rfl

lemma table_of_function (C : Circuit)
    (h : ∀ g ∈ C.gates, ∃ o a b, g = gateFrom o a b)
    (hf : ∀ z : Fin 4 → Bool, PEqualNP.MetaComplexity.circuitFun 4 C z = p4Fun z) :
    (C.gates.foldl tableStep inputTables).getD C.output 0 = target := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  exact (table_output_sem C ⟨i, hi⟩ h).trans ((hf _).trans (target_sem ⟨i, hi⟩).symm)


def Certificate : Prop := ∀ (o0 o1 o2 : Bool)
    (a0 b0 : Fin 4) (a1 b1 : Fin 5) (a2 b2 : Fin 6) (out : Fin 7),
    let g0 := tableGate o0 (sel4 (BitVec.ofNat 3 a0.val)) (sel4 (BitVec.ofNat 3 b0.val))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    let g2 := tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1)
      (sel6 (BitVec.ofNat 3 b2.val) g0 g1)
    sel7 (BitVec.ofNat 3 out.val) g0 g1 g2 ≠ target

def FinalCertificate : Prop := ∀ (o0 o1 o2 : Bool)
    (a0 b0 : Fin 4) (a1 b1 : Fin 5) (a2 b2 : Fin 6),
    let g0 := tableGate o0 (sel4 (BitVec.ofNat 3 a0.val)) (sel4 (BitVec.ofNat 3 b0.val))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1)
      (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target

def SortedFinalCertificate : Prop := ∀ (o0 o1 o2 : Bool)
    (a0 b0 : Fin 4), a0 ≤ b0 → ∀ (a1 b1 : Fin 5), a1 ≤ b1 →
    ∀ (a2 b2 : Fin 6), a2 ≤ b2 →
    let g0 := tableGate o0 (sel4 (BitVec.ofNat 3 a0.val)) (sel4 (BitVec.ofNat 3 b0.val))
    let g1 := tableGate o1 (sel5 (BitVec.ofNat 3 a1.val) g0) (sel5 (BitVec.ofNat 3 b1.val) g0)
    tableGate o2 (sel6 (BitVec.ofNat 3 a2.val) g0 g1)
      (sel6 (BitVec.ofNat 3 b2.val) g0 g1) ≠ target

lemma gate_min_max {α : Type} [LinearOrder α] (o : Bool) (f : α → BitVec 16) (a b : α) :
    tableGate o (f (min a b)) (f (max a b)) = tableGate o (f a) (f b) := by
  rcases le_total a b with h | h
  · simp [min_eq_left h, max_eq_right h]
  · simp only [min_eq_right h, max_eq_left h]
    cases o <;> simp [tableGate, BitVec.and_comm, BitVec.or_comm]

lemma finalCertificate_of_sorted (hs : SortedFinalCertificate) : FinalCertificate := by
  intro o0 o1 o2 a0 b0 a1 b1 a2 b2
  have h := hs o0 o1 o2 (min a0 b0) (max a0 b0) min_le_max
    (min a1 b1) (max a1 b1) min_le_max (min a2 b2) (max a2 b2) min_le_max
  dsimp only at h ⊢
  rw [gate_min_max o0 (fun i : Fin 4 => sel4 (BitVec.ofNat 3 i.val)) a0 b0] at h
  rw [gate_min_max o1 (fun i : Fin 5 => sel5 (BitVec.ofNat 3 i.val) _) a1 b1] at h
  rw [gate_min_max o2 (fun i : Fin 6 => sel6 (BitVec.ofNat 3 i.val) _ _) a2 b2] at h
  exact h

lemma certificate_of_final (hf : FinalCertificate) : Certificate := by
  intro o0 o1 o2 a0 b0 a1 b1 a2 b2 out
  fin_cases out
  · change (0xAAAA : BitVec 16) ≠ target
    decide
  · change (0xCCCC : BitVec 16) ≠ target
    decide
  · change (0xF0F0 : BitVec 16) ≠ target
    decide
  · change (0xFF00 : BitVec 16) ≠ target
    decide
  · have h := hf o0 false false a0 b0 4 4 5 5
    simpa [sel7, sel6, sel5, tableGate] using h
  · have h := hf o0 o1 false a0 b0 a1 b1 5 5
    simpa [sel7, sel6, sel5, tableGate] using h
  · exact hf o0 o1 o2 a0 b0 a1 b1 a2 b2

lemma fold_length (gs : List Gate) (w : List (BitVec 16)) :
    (gs.foldl tableStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [tableStep, Nat.add_assoc, Nat.add_comm]

lemma getD_append_prefix (w v : List (BitVec 16)) (i : ℕ) (hi : i < w.length) :
    (w ++ v).getD i 0 = w.getD i 0 := by
  induction w generalizing i with
  | nil => simp at hi
  | cons a w ih => cases i <;> simp_all [List.getD]

lemma fold_preserve_getD (gs : List Gate) (w : List (BitVec 16)) (i : ℕ)
    (hi : i < w.length) :
    (gs.foldl tableStep w).getD i 0 = w.getD i 0 := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (tableStep w g) (by simp [tableStep]; omega)]
    exact getD_append_prefix w _ i hi

lemma threeGate_bounded_ne (hcert : Certificate) (o0 o1 o2 : Bool)
    (a0 b0 a1 b1 a2 b2 out : ℕ)
    (ha0 : a0 < 4) (hb0 : b0 < 4) (ha1 : a1 < 5) (hb1 : b1 < 5)
    (ha2 : a2 < 6) (hb2 : b2 < 6) (hout : out < 7) :
    ([gateFrom o0 a0 b0, gateFrom o1 a1 b1, gateFrom o2 a2 b2].foldl
      tableStep inputTables).getD out 0 ≠ target := by
  have hc := hcert o0 o1 o2 ⟨a0, ha0⟩ ⟨b0, hb0⟩ ⟨a1, ha1⟩ ⟨b1, hb1⟩
    ⟨a2, ha2⟩ ⟨b2, hb2⟩ ⟨out, hout⟩
  simpa only [List.foldl_cons, List.foldl_nil, tableStep_from,
    List.append_assoc, List.cons_append, List.nil_append,
    sel4_getD, sel5_getD, sel6_getD, sel7_getD, clip,
    ite_eq_left (show a0 < 7 by omega), ite_eq_left (show b0 < 7 by omega),
    ite_eq_left (show a1 < 7 by omega), ite_eq_left (show b1 < 7 by omega),
    ite_eq_left (show a2 < 7 by omega), ite_eq_left (show b2 < 7 by omega), ite_eq_left hout] using hc

lemma small_table_ne (hcert : Certificate) (gs : List Gate) (out : ℕ)
    (hs : gs.length ≤ 3) (hout : out < 4 + gs.length)
    (hb : PEqualNP.MetaComplexity.NestedCover.ReadsBack 4 ⟨gs, out⟩)
    (h : ∀ g ∈ gs, ∃ o a b, g = gateFrom o a b) :
    (gs.foldl tableStep inputTables).getD out 0 ≠ target := by
  have ho7 : out < 7 := by omega
  cases gs with
  | nil =>
    have hn := threeGate_bounded_ne hcert false false false 0 0 0 0 0 0 out
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ho7
    rw [fold_preserve_getD _ inputTables out (by simpa [inputTables] using hout)] at hn
    exact hn
  | cons g0 gs =>
    obtain ⟨o0, a0, b0, rfl⟩ := h g0 (by simp)
    have ha0 : a0 < 4 := by
      exact hb 0 (by simp) a0 (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt, gateFrom])
    have hb0 : b0 < 4 := by
      exact hb 0 (by simp) b0 (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt, gateFrom])
    cases gs with
    | nil =>
      have hn := threeGate_bounded_ne hcert o0 false false a0 b0 0 0 0 0 out
        ha0 hb0 (by decide) (by decide) (by decide) (by decide) ho7
      change (([gateFrom false 0 0, gateFrom false 0 0]).foldl tableStep
        (tableStep inputTables (gateFrom o0 a0 b0))).getD out 0 ≠ target at hn
      rw [fold_preserve_getD _ _ out (by simpa [tableStep, inputTables] using hout)] at hn
      exact hn
    | cons g1 gs =>
      obtain ⟨o1, a1, b1, rfl⟩ := h g1 (by simp)
      have ha1 : a1 < 5 := by
        exact hb 1 (by simp) a1 (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt, gateFrom])
      have hb1 : b1 < 5 := by
        exact hb 1 (by simp) b1 (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt, gateFrom])
      cases gs with
      | nil =>
        have hn := threeGate_bounded_ne hcert o0 o1 false a0 b0 a1 b1 0 0 out
          ha0 hb0 ha1 hb1 (by decide) (by decide) ho7
        change (([gateFrom false 0 0]).foldl tableStep
          (tableStep (tableStep inputTables (gateFrom o0 a0 b0)) (gateFrom o1 a1 b1))).getD out 0
          ≠ target at hn
        rw [fold_preserve_getD _ _ out (by simpa [tableStep, inputTables] using hout)] at hn
        exact hn
      | cons g2 gs =>
        have hnil : gs = [] := by
          apply List.length_eq_zero_iff.mp
          simp only [List.length_cons] at hs
          omega
        subst gs
        obtain ⟨o2, a2, b2, rfl⟩ := h g2 (by simp)
        have ha2 : a2 < 6 := by
          exact hb 2 (by simp) a2 (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt, gateFrom])
        have hb2 : b2 < 6 := by
          exact hb 2 (by simp) b2 (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt, gateFrom])
        exact threeGate_bounded_ne hcert o0 o1 o2 a0 b0 a1 b1 a2 b2 out ha0 hb0 ha1 hb1
          ha2 hb2 ho7

lemma p4_size_lower_bound_of_certificate (hcert : Certificate) (C : Circuit)
    (hAO : PEqualNP.TopForm.IsAO2 4 C)
    (hf : ∀ z : Fin 4 → Bool, PEqualNP.MetaComplexity.circuitFun 4 C z = p4Fun z) :
    4 ≤ C.size := by
  have hshape : ∀ g ∈ C.gates, ∃ o a b, g = gateFrom o a b := by
    intro g hg
    exact gate_shape g (hAO.1 g hg) (hAO.2.2 g hg)
  have ht := table_of_function C hshape hf
  have hout : C.output < 4 + C.gates.length := by
    by_contra hn
    have hh : (C.gates.foldl tableStep inputTables).length ≤ C.output := by
      rw [fold_length]
      simpa [inputTables] using Nat.le_of_not_gt hn
    rw [List.getD, List.getElem?_eq_none hh] at ht
    exact (by decide : (0 : BitVec 16) ≠ target) ht
  by_contra hn
  exact small_table_ne hcert C.gates C.output (by change ¬ 4 ≤ C.gates.length at hn; omega)
    hout hAO.2.1 hshape ht


lemma p4_size_lower_bound (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 4 C)
    (hf : ∀ z : Fin 4 → Bool, PEqualNP.MetaComplexity.circuitFun 4 C z = p4Fun z) :
    4 ≤ C.size := by
  exact p4_size_lower_bound_of_certificate
    (certificate_of_final (finalCertificate_of_sorted threeGate_sorted_final)) C hAO hf

end LowerBound

namespace PlaneP4

lemma induced_path (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∃ a c l m : Fin N, a ≠ c ∧ l ≠ m ∧ I a l ∧ I c l ∧ I c m ∧ ¬ I a m := by
  classical
  have hpos : 0 < N := by omega
  let l : Fin N := ⟨0, hpos⟩
  have hline : 1 < (Finset.univ.filter fun p => I p l).card := by
    rw [hcard l]
    omega
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.mp hline
  have hal : I a l := (Finset.mem_filter.mp ha).2
  have hcl : I c l := (Finset.mem_filter.mp hc).2
  have hout : ∃ x : Fin N, ¬ I x l := by
    by_contra hn
    push Not at hn
    have heq : (Finset.univ.filter fun p => I p l) = Finset.univ := by
      ext p
      simp [hn p]
    have hh := hcard l
    rw [heq] at hh
    simp only [Finset.card_univ, Fintype.card_fin] at hh
    nlinarith [sq_nonneg (q : ℤ)]
  obtain ⟨x, hx⟩ := hout
  have hcx : c ≠ x := by
    rintro rfl
    exact hx hcl
  obtain ⟨m, hm, _⟩ := huniq c x hcx
  have hlm : l ≠ m := by
    intro heq
    exact hx (heq ▸ hm.2)
  have hnot : ¬ I a m := by
    intro ham
    obtain ⟨u, _, hu⟩ := huniq a c hac
    have hmu := hu m ⟨ham, hm.1⟩
    have hlu := hu l ⟨hal, hcl⟩
    exact hlm (hlu.trans hmu.symm)
  exact ⟨a, c, l, m, hac, hlm, hal, hcl, hm.1, hnot⟩

lemma induced_five_path (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    ∃ a c d l m : Fin N, a ≠ c ∧ c ≠ d ∧ a ≠ d ∧ l ≠ m ∧
      I a l ∧ I c l ∧ I c m ∧ I d m ∧ ¬ I a m ∧ ¬ I d l := by
  obtain ⟨a, c, l, m, hac, hlm, hal, hcl, hcm, hnot⟩ :=
    induced_path q N I hq hN hcard huniq
  have hline : 1 < (Finset.univ.filter fun p => I p m).card := by
    rw [hcard m]
    omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hline
  have hd : ∃ d, I d m ∧ c ≠ d := by
    by_cases hcu : c = u
    · exact ⟨v, (Finset.mem_filter.mp hv).2, hcu ▸ huv⟩
    · exact ⟨u, (Finset.mem_filter.mp hu).2, hcu⟩
  obtain ⟨d, hdm, hcd⟩ := hd
  have had : a ≠ d := by
    rintro rfl
    exact hnot hdm
  have hdnot : ¬ I d l := by
    intro hdl
    obtain ⟨s, _, hs⟩ := huniq c d hcd
    exact hlm ((hs l ⟨hcl, hdl⟩).trans (hs m ⟨hcm, hdm⟩).symm)
  exact ⟨a, c, d, l, m, hac, hcd, had, hlm, hal, hcl, hcm, hdm, hnot, hdnot⟩

end PlaneP4

lemma p4Mixed_minimal (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 4 C)
    (hf : ∀ z : Fin 4 → Bool, PEqualNP.MetaComplexity.circuitFun 4 C z = p4Fun z) :
    Additional.p4Mixed.size ≤ C.size := by
  change 4 ≤ C.size
  exact LowerBound.p4_size_lower_bound C hAO hf

lemma p4Mixed_least :
    @PEqualNP.TopForm.IsLeastAO 4 p4Graph p4GraphDec Additional.p4Mixed := by
  refine ⟨Additional.p4Mixed_ao2, ?_, ?_⟩
  · funext z
    exact (Additional.p4Mixed_eval z).trans (p4Fun_graph z).symm
  · intro C hC hf
    apply p4Mixed_minimal C hC
    intro z
    rw [hf]
    exact p4Fun_graph z

lemma least_ao_not_read_one :
    @PEqualNP.TopForm.IsLeastAO 4 p4Graph p4GraphDec Additional.p4Mixed ∧
      ¬ PEqualNP.ReadK.IsReadK 4 Additional.p4Mixed 1 :=
  ⟨p4Mixed_least, Additional.p4Mixed_not_readOne⟩




lemma expansion_arithmetic_equality (q s t : ℕ) (hs : 0 < s)
    (hsq : s ≤ q ^ 2) (h : (s * (q + 1)) ^ 2 ≤ t * (s * (q + s)))
    (heq : t = s + q) : s = 1 ∨ s = q ^ 2 := by
  have hcancel : s * (q + 1) ^ 2 ≤ t * (q + s) := by
    have hx : s * (s * (q + 1) ^ 2) ≤ s * (t * (q + s)) := by
      convert h using 1 <;> ring
    exact Nat.le_of_mul_le_mul_left hx hs
  have hsq_int : (s : ℤ) ≤ (q : ℤ) ^ 2 := by exact_mod_cast hsq
  have hprod : 0 ≤ ((s : ℤ) - 1) * ((q : ℤ) ^ 2 - s) := by
    apply mul_nonneg <;> omega
  have hc : (s : ℤ) * (q + 1) ^ 2 ≤ (s + q) * (q + s) := by
    rw [heq] at hcancel
    exact_mod_cast hcancel
  have hz : ((s : ℤ) - 1) * ((q : ℤ) ^ 2 - s) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with hleft | hright
  · left
    omega
  · right
    have hx : (s : ℤ) = (q : ℤ) ^ 2 := by omega
    exact_mod_cast hx

lemma incidence_neighborhood_expansion_strict {α β : Type*} [DecidableEq α]
    [DecidableEq β] (S : Finset α) (T : Finset β) (I : α → β → Prop)
    [DecidableRel I] (q : ℕ) (hS : 1 < S.card) (hsq : S.card < q ^ 2)
    (hrow : ∀ p ∈ S, (T.filter (I p)).card = q + 1)
    (hpair : ∀ p ∈ S, ∀ r ∈ S, p ≠ r →
      (T.filter (fun l => I p l ∧ I r l)).card = 1) :
    S.card + q + 1 ≤ T.card := by
  have hc := sq_sum_le_card_mul_sum_sq (s := T)
    (f := fun l => (S.filter (fun p => I p l)).card)
  rw [incidence_moment_one S T I q hrow, incidence_moment_two S T I q hrow hpair] at hc
  have hpos : 0 < S.card := by omega
  have hle := expansion_arithmetic q S.card T.card hpos (by omega) hc
  by_contra hbad
  have heq : T.card = S.card + q := by omega
  rcases expansion_arithmetic_equality q S.card T.card hpos (by omega) hc heq with h | h <;> omega

lemma expansion_arithmetic_two (q s t : ℕ) (hs : 2 ≤ s)
    (hsq : s + q ≤ q ^ 2) (h : (s * (q + 1)) ^ 2 ≤ t * (s * (q + s))) :
    s + 2 * q ≤ t + 1 := by
  have hcancel : s * (q + 1) ^ 2 ≤ t * (q + s) := by
    have hx : s * (s * (q + 1) ^ 2) ≤ s * (t * (q + s)) := by
      convert h using 1 <;> ring
    exact Nat.le_of_mul_le_mul_left hx (by omega)
  have hsq_int : (s : ℤ) + q ≤ (q : ℤ) ^ 2 := by exact_mod_cast hsq
  have hprod : 0 ≤ ((s : ℤ) - 2) * ((q : ℤ) ^ 2 - q - s) := by
    apply mul_nonneg <;> omega
  have hc : (s : ℤ) * (q + 1) ^ 2 ≤ t * (q + s) := by exact_mod_cast hcancel
  by_contra hbad
  have hlt : (t : ℤ) ≤ s + 2 * q - 2 := by omega
  have hspos : 0 < (s : ℤ) := by omega
  have hqpos : 0 ≤ (q : ℤ) := by omega
  nlinarith [mul_le_mul_of_nonneg_right hlt (by positivity : 0 ≤ (q : ℤ) + s)]

lemma incidence_neighborhood_expansion_two {α β : Type*} [DecidableEq α]
    [DecidableEq β] (S : Finset α) (T : Finset β) (I : α → β → Prop)
    [DecidableRel I] (q : ℕ) (hS : 2 ≤ S.card) (hsq : S.card + q ≤ q ^ 2)
    (hrow : ∀ p ∈ S, (T.filter (I p)).card = q + 1)
    (hpair : ∀ p ∈ S, ∀ r ∈ S, p ≠ r →
      (T.filter (fun l => I p l ∧ I r l)).card = 1) :
    S.card + 2 * q ≤ T.card + 1 := by
  have hc := sq_sum_le_card_mul_sum_sq (s := T)
    (f := fun l => (S.filter (fun p => I p l)).card)
  rw [incidence_moment_one S T I q hrow, incidence_moment_two S T I q hrow hpair] at hc
  exact expansion_arithmetic_two q S.card T.card hS hsq hc

lemma plane_mixed_cover_bound_two (q N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hN : N = q ^ 2 + q + 1)
    (hrow : ∀ p : Fin N, (Finset.univ.filter (I p)).card = q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (A B : Finset (Fin N)) (hA : 2 ≤ (Finset.univ \ A).card)
    (hB : 2 ≤ (Finset.univ \ B).card)
    (hcover : ∀ p l : Fin N, I p l → p ∈ A ∨ l ∈ B) :
    N + 2 * q ≤ A.card + B.card + 1 := by
  classical
  let S := Finset.univ \ A
  have hnotA : ∀ p ∈ S, p ∉ A := by
    intro p hp
    exact (Finset.mem_sdiff.mp hp).2
  have hneigh : ∀ p ∈ S, ∀ l, I p l → l ∈ B := by
    intro p hp l hpl
    exact (hcover p l hpl).resolve_left (hnotA p hp)
  have hsquare : S.card + q ≤ q ^ 2 := by
    obtain ⟨l, hl, k, hk, hlk⟩ := Finset.one_lt_card.mp (show 1 < (Finset.univ \ B).card by omega)
    have hlB : l ∉ B := (Finset.mem_sdiff.mp hl).2
    have hkB : k ∉ B := (Finset.mem_sdiff.mp hk).2
    let L := Finset.univ.filter (fun p => I p l)
    let K := Finset.univ.filter (fun p => I p k)
    have hLcard : L.card = q + 1 := hcol l
    have hKcard : K.card = q + 1 := hcol k
    have hinter : (L ∩ K).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro p hp r hr
      by_contra hpr
      obtain ⟨j, hj, huniq⟩ := hunique p r hpr
      have hpL : I p l := (Finset.mem_filter.mp (Finset.mem_inter.mp hp).1).2
      have hpK : I p k := (Finset.mem_filter.mp (Finset.mem_inter.mp hp).2).2
      have hrL : I r l := (Finset.mem_filter.mp (Finset.mem_inter.mp hr).1).2
      have hrK : I r k := (Finset.mem_filter.mp (Finset.mem_inter.mp hr).2).2
      exact hlk ((huniq l ⟨hpL, hrL⟩).trans (huniq k ⟨hpK, hrK⟩).symm)
    have hu := Finset.card_union_add_card_inter L K
    have hsub : S ⊆ Finset.univ \ (L ∪ K) := by
      intro p hp
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hpLK
      rcases Finset.mem_union.mp hpLK with hpL | hpK
      · exact hlB (hneigh p hp l (Finset.mem_filter.mp hpL).2)
      · exact hkB (hneigh p hp k (Finset.mem_filter.mp hpK).2)
    have hle := Finset.card_le_card hsub
    have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (L ∪ K))
    simp only [Finset.card_univ, Fintype.card_fin] at hsum
    omega
  have hrowB : ∀ p ∈ S, (B.filter (I p)).card = q + 1 := by
    intro p hp
    have heq : B.filter (I p) = Finset.univ.filter (I p) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨And.right, fun hpl => ⟨hneigh p hp l hpl, hpl⟩⟩
    rw [heq]
    exact hrow p
  have hpairB : ∀ p ∈ S, ∀ r ∈ S, p ≠ r →
      (B.filter (fun l => I p l ∧ I r l)).card = 1 := by
    intro p hp r hr hpr
    obtain ⟨l, hl, huniq⟩ := hunique p r hpr
    apply Finset.card_eq_one.mpr
    refine ⟨l, ?_⟩
    ext k
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro hk
      exact huniq k hk.2
    · intro hk
      subst k
      exact ⟨hneigh p hp l hl.1, hl⟩
  have hexp := incidence_neighborhood_expansion_two S B I q hA hsquare hrowB hpairB
  have hpart : S.card + A.card = N := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  omega



open scoped BigOperators

def HitsEveryRectangle {α β : Type*} (S : Finset α) (T : Finset β)
    (E : Finset (α × β)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∀ l ∈ T, ∀ k ∈ T, l ≠ k →
    (a, l) ∈ E ∨ (a, k) ∈ E ∨ (b, l) ∈ E ∨ (b, k) ∈ E

lemma rectangle_hit_nonempty {α β : Type*} (S : Finset α) (T : Finset β)
    (E : Finset (α × β)) (hS : 2 ≤ S.card) (hT : 2 ≤ T.card)
    (hrect : HitsEveryRectangle S T E) : E.Nonempty := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (show 1 < S.card by omega)
  obtain ⟨l, hl, k, hk, hlk⟩ := Finset.one_lt_card.mp (show 1 < T.card by omega)
  rcases hrect a ha b hb hab l hl k hk hlk with h | h | h | h
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩
  · exact ⟨_, h⟩

lemma rectangle_density {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (T : Finset β) (E : Finset (α × β))
    (hsub : E ⊆ S ×ˢ T) (hS : 2 ≤ S.card) (hT : 2 ≤ T.card)
    (hrect : HitsEveryRectangle S T E) : S.card + T.card ≤ E.card + 3 := by
  classical
  have main : ∀ n : ℕ, ∀ (S : Finset α) (T : Finset β) (E : Finset (α × β)),
      S.card + T.card = n → E ⊆ S ×ˢ T → 2 ≤ S.card → 2 ≤ T.card →
      HitsEveryRectangle S T E → S.card + T.card ≤ E.card + 3 := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro S T E hn hsub hS hT hrect
      obtain ⟨e, he⟩ := rectangle_hit_nonempty S T E hS hT hrect
      have heS : e.1 ∈ S := (Finset.mem_product.mp (hsub he)).1
      have heT : e.2 ∈ T := (Finset.mem_product.mp (hsub he)).2
      by_cases hS2 : S.card = 2
      · by_cases hT2 : T.card = 2
        · have : 0 < E.card := Finset.card_pos.mpr ⟨e, he⟩
          omega
        · let T' := T.erase e.2
          let E' := E.filter (fun x => x.2 ≠ e.2)
          have hcardT : T'.card + 1 = T.card := Finset.card_erase_add_one heT
          have hsub' : E' ⊆ S ×ˢ T' := by
            intro x hx
            obtain ⟨hxE, hxne⟩ := Finset.mem_filter.mp hx
            obtain ⟨hxS, hxT⟩ := Finset.mem_product.mp (hsub hxE)
            exact Finset.mem_product.mpr ⟨hxS, Finset.mem_erase.mpr ⟨hxne, hxT⟩⟩
          have hEerase : E' ⊆ E.erase e := by
            intro x hx
            obtain ⟨hxE, hxne⟩ := Finset.mem_filter.mp hx
            refine Finset.mem_erase.mpr ⟨?_, hxE⟩
            intro hxe
            subst x
            exact hxne rfl
          have hcardE : E'.card + 1 ≤ E.card := by
            have hle := Finset.card_le_card hEerase
            have hecard := Finset.card_erase_add_one he
            omega
          have hrect' : HitsEveryRectangle S T' E' := by
            intro a ha b hb hab l hl k hk hlk
            obtain ⟨hlne, hlT⟩ := Finset.mem_erase.mp hl
            obtain ⟨hkne, hkT⟩ := Finset.mem_erase.mp hk
            rcases hrect a ha b hb hab l hlT k hkT hlk with h | h | h | h
            · exact Or.inl (Finset.mem_filter.mpr ⟨h, hlne⟩)
            · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨h, hkne⟩))
            · exact Or.inr (Or.inr (Or.inl (Finset.mem_filter.mpr ⟨h, hlne⟩)))
            · exact Or.inr (Or.inr (Or.inr (Finset.mem_filter.mpr ⟨h, hkne⟩)))
          have hrec := ih (S.card + T'.card) (by omega) S T' E' rfl hsub' hS
            (by omega) hrect'
          omega
      · let S' := S.erase e.1
        let E' := E.filter (fun x => x.1 ≠ e.1)
        have hcardS : S'.card + 1 = S.card := Finset.card_erase_add_one heS
        have hsub' : E' ⊆ S' ×ˢ T := by
          intro x hx
          obtain ⟨hxE, hxne⟩ := Finset.mem_filter.mp hx
          obtain ⟨hxS, hxT⟩ := Finset.mem_product.mp (hsub hxE)
          exact Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨hxne, hxS⟩, hxT⟩
        have hEerase : E' ⊆ E.erase e := by
          intro x hx
          obtain ⟨hxE, hxne⟩ := Finset.mem_filter.mp hx
          refine Finset.mem_erase.mpr ⟨?_, hxE⟩
          intro hxe
          subst x
          exact hxne rfl
        have hcardE : E'.card + 1 ≤ E.card := by
          have hle := Finset.card_le_card hEerase
          have hecard := Finset.card_erase_add_one he
          omega
        have hrect' : HitsEveryRectangle S' T E' := by
          intro a ha b hb hab l hl k hk hlk
          obtain ⟨hane, haS⟩ := Finset.mem_erase.mp ha
          obtain ⟨hbne, hbS⟩ := Finset.mem_erase.mp hb
          rcases hrect a haS b hbS hab l hl k hk hlk with h | h | h | h
          · exact Or.inl (Finset.mem_filter.mpr ⟨h, hane⟩)
          · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨h, hane⟩))
          · exact Or.inr (Or.inr (Or.inl (Finset.mem_filter.mpr ⟨h, hbne⟩)))
          · exact Or.inr (Or.inr (Or.inr (Finset.mem_filter.mpr ⟨h, hbne⟩)))
        have hrec := ih (S'.card + T.card) (by omega) S' T E' rfl hsub'
          (by omega) hT hrect'
        omega
  exact main _ S T E rfl hsub hS hT hrect


namespace CompletionSets

def uncovered {m n : ℕ} (E : Finset (Fin m × Fin n))
    (A : Finset (Fin m)) (B : Finset (Fin n)) : Finset (Fin m × Fin n) :=
  E.filter fun e => e.1 ∉ A ∧ e.2 ∉ B

lemma completion_avoiding_sets {m n : ℕ} (E : Finset (Fin m × Fin n))
    (A P : Finset (Fin m)) (B Q : Finset (Fin n))
    (hP : ∀ p ∈ P, p ∉ A) (hQ : ∀ l ∈ Q, l ∉ B)
    (hPQ : ∀ p ∈ P, ∀ l ∈ Q, (p, l) ∉ E) :
    ∃ A' : Finset (Fin m), ∃ B' : Finset (Fin n),
      (∀ p ∈ P, p ∉ A') ∧ (∀ l ∈ Q, l ∉ B') ∧
      (∀ e ∈ E, e.1 ∈ A' ∨ e.2 ∈ B') ∧
      A'.card + B'.card ≤ A.card + B.card + (uncovered E A B).card := by
  let U := uncovered E A B
  let X := U.filter fun e => e.1 ∉ P
  let Y := U.filter fun e => e.1 ∈ P
  refine ⟨A ∪ X.image Prod.fst, B ∪ Y.image Prod.snd, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_union, not_or]
    refine ⟨hP p hp, ?_⟩
    intro h
    obtain ⟨e, he, hep⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp he).2 (hep ▸ hp)
  · intro l hl
    simp only [Finset.mem_union, not_or]
    refine ⟨hQ l hl, ?_⟩
    intro h
    obtain ⟨e, he, hel⟩ := Finset.mem_image.mp h
    obtain ⟨heU, heP⟩ := Finset.mem_filter.mp he
    have heE : e ∈ E := (Finset.mem_filter.mp heU).1
    have heeq : e = (e.1, l) := Prod.ext rfl hel
    exact hPQ e.1 heP l hl (heeq ▸ heE)
  · intro e he
    by_cases hA : e.1 ∈ A
    · exact Or.inl (Finset.mem_union_left _ hA)
    by_cases hB : e.2 ∈ B
    · exact Or.inr (Finset.mem_union_left _ hB)
    have heU : e ∈ U := Finset.mem_filter.mpr ⟨he, hA, hB⟩
    by_cases hep : e.1 ∈ P
    · exact Or.inr (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨heU, hep⟩, rfl⟩))
    · exact Or.inl (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨heU, hep⟩, rfl⟩))
  · have hA := Finset.card_union_le A (X.image Prod.fst)
    have hB := Finset.card_union_le B (Y.image Prod.snd)
    have hX := Finset.card_image_le (s := X) (f := Prod.fst)
    have hY := Finset.card_image_le (s := Y) (f := Prod.snd)
    have hsum : Y.card + X.card = U.card :=
      Finset.card_filter_add_card_filter_not (s := U) (fun e => e.1 ∈ P)
    change (A ∪ X.image Prod.fst).card + (B ∪ Y.image Prod.snd).card ≤
      A.card + B.card + U.card
    omega

end CompletionSets


lemma partial_cover_bound_two (N q : ℕ) (E : Finset (Fin N × Fin N))
    (hN : 2 * q + 2 ≤ N)
    (hfull : ∀ A B : Finset (Fin N), 2 ≤ (Finset.univ \ A).card →
      2 ≤ (Finset.univ \ B).card → (∀ e ∈ E, e.1 ∈ A ∨ e.2 ∈ B) →
      N + 2 * q ≤ A.card + B.card + 1)
    (A B : Finset (Fin N)) (hA : 2 ≤ (Finset.univ \ A).card)
    (hB : 2 ≤ (Finset.univ \ B).card) :
    N + 2 * q ≤ A.card + B.card + (CompletionSets.uncovered E A B).card + 1 := by
  classical
  let S : Finset (Fin N) := Finset.univ \ A
  let T : Finset (Fin N) := Finset.univ \ B
  let U := CompletionSets.uncovered E A B
  have hnotA : ∀ p ∈ S, p ∉ A := fun p hp => (Finset.mem_sdiff.mp hp).2
  have hnotB : ∀ l ∈ T, l ∉ B := fun l hl => (Finset.mem_sdiff.mp hl).2
  by_cases hex : ∃ a b l k : Fin N, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      l ∈ T ∧ k ∈ T ∧ l ≠ k ∧ (a, l) ∉ E ∧ (a, k) ∉ E ∧
      (b, l) ∉ E ∧ (b, k) ∉ E
  · obtain ⟨a, b, l, k, ha, hb, hab, hl, hk, hlk, hal, hak, hbl, hbk⟩ := hex
    have hP : ∀ p ∈ ({a, b} : Finset (Fin N)), p ∉ A := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hnotA _ ha
      · exact hnotA _ hb
    have hQ : ∀ r ∈ ({l, k} : Finset (Fin N)), r ∉ B := by
      intro r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hr
      rcases hr with rfl | rfl
      · exact hnotB _ hl
      · exact hnotB _ hk
    have hPQ : ∀ p ∈ ({a, b} : Finset (Fin N)), ∀ r ∈ ({l, k} : Finset (Fin N)),
        (p, r) ∉ E := by
      intro p hp r hr
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp hr
      rcases hp with rfl | rfl <;> rcases hr with rfl | rfl <;> assumption
    obtain ⟨A', B', hP', hQ', hcover, hcost⟩ :=
      CompletionSets.completion_avoiding_sets E A {a, b} B {l, k} hP hQ hPQ
    have hA' : 2 ≤ (Finset.univ \ A').card := by
      have hs : ({a, b} : Finset (Fin N)) ⊆ Finset.univ \ A' := by
        intro p hp
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hP' p hp⟩
      have h := Finset.card_le_card hs
      rwa [Finset.card_pair hab] at h
    have hB' : 2 ≤ (Finset.univ \ B').card := by
      have hs : ({l, k} : Finset (Fin N)) ⊆ Finset.univ \ B' := by
        intro r hr
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hQ' r hr⟩
      have h := Finset.card_le_card hs
      rwa [Finset.card_pair hlk] at h
    have h := hfull A' B' hA' hB' hcover
    omega
  · have hsub : U ⊆ S ×ˢ T := by
      intro e he
      obtain ⟨_, hp, hl⟩ := Finset.mem_filter.mp he
      exact Finset.mem_product.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hp⟩,
         Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hl⟩⟩
    have hmem : ∀ p ∈ S, ∀ l ∈ T, (p, l) ∈ E → (p, l) ∈ U := by
      intro p hp l hl hpl
      exact Finset.mem_filter.mpr ⟨hpl, hnotA p hp, hnotB l hl⟩
    have hrect : HitsEveryRectangle S T U := by
      intro a ha b hb hab l hl k hk hlk
      by_contra hn
      simp only [not_or] at hn
      exact hex ⟨a, b, l, k, ha, hb, hab, hl, hk, hlk,
        fun he => hn.1 (hmem a ha l hl he),
        fun he => hn.2.1 (hmem a ha k hk he),
        fun he => hn.2.2.1 (hmem b hb l hl he),
        fun he => hn.2.2.2 (hmem b hb k hk he)⟩
    have h := rectangle_density S T U hsub hA hB hrect
    have hScard : S.card + A.card = N := by
      simpa [S] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
    have hTcard : T.card + B.card = N := by
      simpa [T] using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
    change N + 2 * q ≤ A.card + B.card + U.card + 1
    omega

lemma plane_partial_cover_bound_two (q N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (A B : Finset (Fin N)) (hA : 2 ≤ (Finset.univ \ A).card)
    (hB : 2 ≤ (Finset.univ \ B).card) :
    N + 2 * q ≤ A.card + B.card +
      (Finset.univ.filter (fun e : Fin N × Fin N =>
        I e.1 e.2 ∧ e.1 ∉ A ∧ e.2 ∉ B)).card + 1 := by
  let E := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  have hfull : ∀ A' B' : Finset (Fin N), 2 ≤ (Finset.univ \ A').card →
      2 ≤ (Finset.univ \ B').card → (∀ e ∈ E, e.1 ∈ A' ∨ e.2 ∈ B') →
      N + 2 * q ≤ A'.card + B'.card + 1 := by
    intro A' B' hA' hB' hcov
    apply plane_mixed_cover_bound_two q N I hN
      (plane_point_degree q N I (by omega) hN hcol hunique) hcol hunique A' B' hA' hB'
    intro p l hpl
    exact hcov (p, l) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpl⟩)
  have hdim : 2 * q + 2 ≤ N := by
    have hmul := Nat.mul_le_mul_right q hq
    nlinarith
  have h := partial_cover_bound_two N q E hdim hfull A B hA hB
  simpa only [CompletionSets.uncovered, E, Finset.filter_filter, and_assoc] using h

lemma mixed_partial_cover_penalty_two (q N u t penalty : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (A B : Finset (Fin N)) (hA : 2 ≤ (Finset.univ \ A).card)
    (hB : 2 ≤ (Finset.univ \ B).card) (hsize : A.card + B.card ≤ t)
    (hmissing : (Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ e.1 ∉ A ∧ e.2 ∉ B)).card ≤ u)
    (hledger : t + penalty + 1 ≤ N + u) : 2 * q + penalty ≤ 2 * u := by
  have h := plane_partial_cover_bound_two q N I hq hN hcol hunique A B hA hB
  omega

lemma near_minimum_partial_cover_pure (q N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (A B : Finset (Fin N)) (hsize : A.card + B.card = N - 1)
    (hmissing : (Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ e.1 ∉ A ∧ e.2 ∉ B)).card ≤ q + 1) : A = ∅ ∨ B = ∅ := by
  by_contra hn
  simp only [not_or] at hn
  have hApos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hn.1)
  have hBpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hn.2)
  have hAc : (Finset.univ \ A).card + A.card = N := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  have hBc : (Finset.univ \ B).card + B.card = N := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
  have h := plane_partial_cover_bound_two q N I hq hN hcol hunique A B
    (by omega) (by omega)
  omega

lemma near_minimum_partial_cover_single_star (q N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (A B : Finset (Fin N)) (hsize : A.card + B.card = N - 1)
    (hmissing : (Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ e.1 ∉ A ∧ e.2 ∉ B)).card ≤ q + 1) :
    (∃ p : Fin N, A = Finset.univ.erase p ∧ B = ∅) ∨
      ∃ l : Fin N, A = ∅ ∧ B = Finset.univ.erase l := by
  have hco : ∀ C : Finset (Fin N), C.card = N - 1 → ∃ p, C = Finset.univ.erase p := by
    intro C hC
    have hc : (Finset.univ \ C).card + C.card = N := by
      simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp (show (Finset.univ \ C).card = 1 by omega)
    refine ⟨p, ?_⟩
    calc
      C = Finset.univ \ (Finset.univ \ C) := by ext a; simp
      _ = Finset.univ \ {p} := congrArg (fun X : Finset (Fin N) => Finset.univ \ X) hp
      _ = Finset.univ.erase p := by ext a; simp
  rcases near_minimum_partial_cover_pure q N I hq hN hcol hunique A B hsize hmissing with hA | hB
  · obtain ⟨l, hl⟩ := hco B (by simpa [hA] using hsize)
    exact Or.inr ⟨l, hA, hl⟩
  · obtain ⟨p, hp⟩ := hco A (by simpa [hB] using hsize)
    exact Or.inl ⟨p, hp, hB⟩



namespace CircuitLedger

-- Circuit semantics copied from helper-9 commit 03d0e54e5 (Budget prefix only).
namespace Budget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Circuit evaluation and OR reachability follow L_meta_1490 and L_meta_4901.
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

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩
lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)
lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
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
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
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
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
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

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩
lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
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
      rw [orSets_len]; simp
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

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
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

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
lemma junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩
lemma binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))
lemma opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]
lemma opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)
lemma andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2
lemma andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩
lemma operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1
lemma operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
    (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
  have hlen := (orReaches_reach h _ hr).2
  have hnb : ¬ BelowF G C h :=
    fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
  have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
    by_contra hne
    apply hnb
    intro x hx
    by_contra hf
    exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩
lemma inputsAsOpnd (hAO : IsAO2 n C) {m z : ℕ} (hm : m < C.gates.length)
    (hz : z ∈ (gateAt C m).inputs) : ∃ b : Fin 2, z = opnd C m b := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO hm
  rcases List.mem_cons.mp (hpq ▸ hz) with rfl | hq
  · exact ⟨0, by simp [opnd, hpq]⟩
  · have e : z = q := List.mem_singleton.mp hq
    exact ⟨1, by simpa [opnd, hpq] using e⟩
lemma sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
    (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
    val C (List.ofFn x) (opnd C a b) = true :=
  reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
  (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

lemma topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  obtain ⟨hl, ho, hb⟩ := topData ha
  exact (graphFun_pair G u v).mp
    (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

lemma acceptedTop (hL : IsLeastAO G C) {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a ∈ tops G C, gateVal n C a (pairInput u v) = true := by
  have hout (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hL.2.1 x
  obtain ⟨a, hl, ho, hr, hv⟩ :=
    edge_trace G (graphFun G ∅) (fun k l => (graphFun_pair G k l).mp)
      hout u v ((graphFun_pair G u v).mpr hadj)
  have hand := (hL.1.1 _ (gateAt_mem hl)).resolve_right ho
  have hb : BelowF G C a := fun x hx =>
    below_of_reach (graphFun G ∅) hout a hr x (gateVal_eq_val n C a x ▸ hx)
  refine ⟨a, ?_, hv⟩
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    And.intro hl (And.intro hand hb)

lemma operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
    {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
    (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
        gateVal n C j (pairInput u v) = true := by
  rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
  · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
  · have hr' := reach_orReaches hr j rfl hj
    exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
      ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩


lemma andRawEmpty {j : ℕ} (hj : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with he | ⟨k, _, hr, ho, _⟩
  · have := v.isLt
    omega
  · rcases (orReaches_iff n C j k).mp hr with ⟨_, he | ⟨hof, _⟩⟩
    · subst k
      rw [hj] at ho
      cases ho
    · rw [hj] at hof
      cases hof

lemma lastOrBefore {j w : ℕ} (hr : Relation.ReflTransGen (OrStep n C) w (n + j)) :
    w = n + j ∨ ∃ m, m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧
      n + j ∈ (gateAt C m).inputs ∧ n + j < n + m ∧
      Relation.ReflTransGen (OrStep n C) w (n + m) := by
  rcases Relation.ReflTransGen.cases_tail hr with eq | ⟨z, hz, hstep⟩
  · exact .inl eq.symm
  · obtain ⟨m, hm, rfl, ho, hi, hb⟩ := hstep
    exact .inr ⟨m, hm, ho, hi, hb, hz⟩

lemma lastOrOutside {j m : ℕ} (hAO : IsAO2 n C) (hj : j ∈ junk G C)
    (hm : m < C.gates.length) (ho : (gateAt C m).op = GateOp.or)
    (hi : n + j ∈ (gateAt C m).inputs) (hb : n + j < n + m) :
    m ∈ orN G C \ lam G C := by
  obtain ⟨_, hjop, x, hjx, hx⟩ := junkData hj
  have hNotBelow : ¬ BelowF G C m := by
    intro h
    have hvm : gateVal n C m x = true := (val_or (n := n) (by simp) hm ho).mpr
      ⟨n + j, hi, hb, hjx⟩
    exact Bool.noConfusion (hx.symm.trans (h x hvm))
  apply Finset.mem_sdiff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hm (And.intro ho hNotBelow)
  · intro hl
    obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
    obtain ⟨b, be⟩ := inputsAsOpnd hAO hm hi
    have hnonempty : (orIn n C (opnd C m b)).Nonempty := by
      fin_cases b
      · exact h0
      · exact h1
    rw [← be, andRawEmpty (n := n) hjop] at hnonempty
    exact Finset.not_nonempty_empty hnonempty

lemma residualTrace (hL : IsLeastAO G C) (hT : TopForm G C) {u v : Fin n}
    (he : s(u,v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, ∃ b : Fin 2, ∃ j ∈ junk G C,
      gateVal n C a (pairInput u v) = true ∧ OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true := by
  obtain ⟨adj, miss⟩ := Finset.mem_sdiff.mp he
  have adj' : G.Adj u v := SimpleGraph.mem_edgeFinset.mp adj
  obtain ⟨a, ha, hv⟩ := acceptedTop hL adj'
  obtain ⟨hl, ho, _⟩ := topData ha
  have h := (andValOperands hL.1 hl ho _).mp hv
  rcases operandSupport hL.1 hT hl ho (b := 0) (h 0) with ⟨x, hx, hex⟩ | ⟨j, hj, hr, hjv⟩
  · rcases operandSupport hL.1 hT hl ho (b := 1) (h 1) with ⟨y, hy, hey⟩ | ⟨j, hj, hr, hjv⟩
    · have hxy : x ≠ y := (topAdj hL.1 ha hx hy).ne
      apply (miss ?_).elim
      unfold starEdges
      refine Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
        ⟨(x,y), Finset.mem_product.mpr ⟨hx,hy⟩, ?_⟩⟩
      rcases hex with rfl | rfl <;> rcases hey with rfl | rfl
      · exact (hxy rfl).elim
      · rfl
      · exact Sym2.eq_swap
      · exact (hxy rfl).elim
    · exact ⟨a, ha, 1, j, hj, hv, hr, hjv⟩
  · exact ⟨a, ha, 0, j, hj, hv, hr, hjv⟩


lemma opposite (b c : Fin 2) : c = b ∨ c = 1 - b := by
  revert b c
  decide

lemma topSides (empty : centreless G C = ∅) {a : ℕ} (ha : a ∈ tops G C)
    (b : Fin 2) : (side (n := n) C a b).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro he
  have hc : a ∈ centreless G C := by
    apply Finset.mem_filter.mpr
    refine ⟨ha, ?_⟩
    fin_cases b
    · exact Or.inl he
    · exact Or.inr he
  rw [empty] at hc
  exact Finset.notMem_empty _ hc

lemma orData {m : ℕ} (hm : m ∈ orN G C \ lam G C) :
    m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G C m := by
  simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    (Finset.mem_sdiff.mp hm).1

lemma emptyInputOutside (ao : IsAO2 n C) {j m : ℕ}
    (dirty : ¬ BelowF G C j) (empty : orIn n C (n + j) = ∅)
    (hm : m < C.gates.length) (hop : (gateAt C m).op = GateOp.or)
    (hin : n + j ∈ (gateAt C m).inputs) :
    m ∈ orN G C \ lam G C := by
  have hbad : ¬ BelowF G C m := by
    intro hb
    apply dirty
    intro x hx
    exact hb x ((val_or (n := n) (by simp) hm hop).mpr
      ⟨_, hin, ao.2.1 _ hm _ hin, hx⟩)
  refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
  · simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
      And.intro hm (And.intro hop hbad)
  · intro hl
    obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
    obtain ⟨b, hb⟩ := inputsAsOpnd ao hm hin
    have hne : (orIn n C (opnd C m b)).Nonempty := by
      fin_cases b
      · exact h0
      · exact h1
    rw [← hb, empty] at hne
    exact Finset.not_nonempty_empty hne

lemma residualPath (ao : IsAO2 n C) (empty : centreless G C = ∅)
    {a j : ℕ} {b : Fin 2} (ha : a ∈ tops G C) (hj : j ∈ junk G C)
    (path : OrReaches n C (opnd C a b) j) :
    ∃ m ∈ orN G C \ lam G C, n + j ∈ (gateAt C m).inputs ∧
      Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m) := by
  rcases lastOrBefore (orReaches_reach j _ path).1 with he | ⟨m, hm, hop, hin, hlt, hp⟩
  · have hne := topSides empty ha b
    change (orIn n C (opnd C a b)).Nonempty at hne
    rw [he, andRawEmpty (junkData hj).2.1] at hne
    exact (Finset.not_nonempty_empty hne).elim
  · exact ⟨m, lastOrOutside ao hj hm hop hin hlt, hin, hp⟩

lemma mixingRaw (ao : IsAO2 n C) (empty : centreless G C = ∅) {m a : ℕ} {b : Fin 2}
    (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
    (ha : a ∈ tops G C) (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m)) :
    (orIn n C (n + m)).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hz
  rcases lastOrBefore path with he | ⟨k, hk, hop, hin, hlt, _⟩
  · have hne := topSides empty ha b
    change (orIn n C (opnd C a b)).Nonempty at hne
    rw [he, hz] at hne
    exact Finset.not_nonempty_empty hne
  · have hk' := emptyInputOutside ao (orData hm).2.2 hz hk hop hin
    rw [only, Finset.mem_singleton] at hk'
    omega

lemma singleJunkInput (ao : IsAO2 n C) {m j k : ℕ}
    (hm : m ∈ orN G C \ lam G C) (hne : (orIn n C (n + m)).Nonempty)
    (hj : j ∈ junk G C) (hk : k ∈ junk G C)
    (hjin : n + j ∈ (gateAt C m).inputs) (hkin : n + k ∈ (gateAt C m).inputs) :
    j = k := by
  by_contra hjk
  obtain ⟨p, q, hpq⟩ := binaryInputs ao (orData hm).1
  have hinputs : ∀ w ∈ (gateAt C m).inputs, w = n + j ∨ w = n + k := by
    intro w hw
    simp only [hpq, List.mem_cons, List.not_mem_nil, or_false] at hjin hkin hw
    omega
  obtain ⟨t, ht⟩ := hne
  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach t ht) with he | ⟨w, hs, hrest⟩
  · have := t.isLt
    omega
  · obtain ⟨l, _, he, _, hin, _⟩ := hs
    have hl : l = m := by omega
    subst l
    have ht' := reach_mem_orIn t hrest
    rcases hinputs w hin with rfl | rfl
    · rw [andRawEmpty (junkData hj).2.1] at ht'
      exact Finset.notMem_empty _ ht'
    · rw [andRawEmpty (junkData hk).2.1] at ht'
      exact Finset.notMem_empty _ ht'

lemma cleanAdj (ao : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2)
    {t w : Fin n} (ht : t ∈ side C a b) (hw : w ∈ side C a (1 - b)) :
    (G.deleteEdges ↑(Ustar G C)).Adj t w := by
  have cross {u v : Fin n} (hu : u ∈ side C a 0) (hv : v ∈ side C a 1) :
      (G.deleteEdges ↑(Ustar G C)).Adj u v := by
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨topAdj ao ha hu hv, ?_⟩
    intro he
    apply (Finset.mem_sdiff.mp (show s(u, v) ∈ Ustar G C from he)).2
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_image.mpr
      ⟨(u, v), Finset.mem_product.mpr ⟨hu, hv⟩, rfl⟩⟩
  fin_cases b
  · exact cross ht hw
  · exact (cross hw ht).symm

lemma firingTop (ao : IsAO2 n C) {a m : ℕ} {b : Fin 2} {w : Fin n}
    (ha : a ∈ tops G C)
    (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m))
    (hw : w ∈ side C a (1 - b)) (x : Fin n → Bool)
    (hmx : gateVal n C m x = true) (hwx : x w = true) :
    graphFun G ∅ x = true := by
  obtain ⟨haLen, haOp, haBelow⟩ := topData ha
  apply haBelow x ((andValOperands ao haLen haOp x).mpr ?_)
  intro c
  rcases opposite b c with rfl | rfl
  · exact orStep_up (n := n) (by simp) path hmx
  · exact sideVal hw hwx

lemma oppositeEndpoint (least : IsLeastAO G C) (top : TopForm G C)
    (empty : centreless G C = ∅) {m a : ℕ} {b : Fin 2} {u v : Fin n}
    (only : orN G C \ lam G C = {m}) (hm : m ∈ orN G C \ lam G C)
    (ha : a ∈ tops G C) (hv : gateVal n C a (pairInput u v) = true)
    (path : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m)) :
    ∃ w ∈ side C a (1 - b), w = u ∨ w = v := by
  obtain ⟨al, aop, ab⟩ := topData ha
  have hv' := (andValOperands least.1 al aop _).mp hv (1 - b)
  rcases operandSupport least.1 top al aop hv' with h | ⟨j, hj, hr, _⟩
  · exact h
  · obtain ⟨k, hk, _, hp⟩ := residualPath least.1 empty ha hj hr
    rw [only, Finset.mem_singleton] at hk
    subst k
    exfalso
    apply (orData hm).2.2
    intro x hx
    apply ab x ((andValOperands least.1 al aop x).mpr ?_)
    intro c
    rcases opposite b c with rfl | rfl
    · exact orStep_up (n := n) (by simp) path hx
    · exact orStep_up (n := n) (by simp) hp hx

end Budget

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

lemma common_neighbors_unique_of_card_le_one {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfour : ∀ a b, a ≠ b →
      (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card ≤ 1) :
    ∀ a b, a ≠ b → ∀ l m,
      G.Adj a l → G.Adj b l → G.Adj a m → G.Adj b m → l = m := by
  intro a b hab l m hal hbl ham hbm
  apply Finset.card_le_one.mp (hfour a b hab) l _ m _
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hal, hbl⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨ham, hbm⟩

lemma one_extra_or_clean_pencil
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hleast : IsLeastAO G C) (htop : TopForm G C)
    (hempty : centreless G C = ∅)
    (m : ℕ) (honly : orN G C \ lam G C = {m})
    (hU : (Ustar G C).Nonempty) :
    ∃ t : Fin n, ∀ u v, s(u, v) ∈ Ustar G C →
      ∃ w, (w = u ∨ w = v) ∧ (G.deleteEdges ↑(Ustar G C)).Adj t w := by
  have hm : m ∈ orN G C \ lam G C := by simp [honly]
  obtain ⟨e, he⟩ := hU
  induction e using Sym2.ind with
  | h u v =>
    obtain ⟨a, ha, b, j, hj, _, hr, _⟩ := Budget.residualTrace hleast htop he
    obtain ⟨m', hm', _, path⟩ := Budget.residualPath hleast.1 hempty ha hj hr
    rw [honly, Finset.mem_singleton] at hm'
    subst m'
    obtain ⟨t, ht⟩ := Budget.mixingRaw hleast.1 hempty honly hm ha path
    refine ⟨t, ?_⟩
    intro p q hpq
    obtain ⟨a', ha', b', k, hk, hav, hr', _⟩ := Budget.residualTrace hleast htop hpq
    obtain ⟨l, hl, _, hp⟩ := Budget.residualPath hleast.1 hempty ha' hk hr'
    rw [honly, Finset.mem_singleton] at hl
    subst l
    obtain ⟨w, hw, hend⟩ := Budget.oppositeEndpoint hleast htop hempty honly hm ha' hav hp
    have ht' : t ∈ side C a' b' :=
      Budget.reach_mem_orIn t (hp.trans (Budget.mem_orIn_reach t ht))
    exact ⟨w, hend, Budget.cleanAdj hleast.1 ha' b' ht' hw⟩

lemma uncovered_card_eq_sum (N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (A B : Finset (Fin N)) :
    (Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ e.1 ∉ A ∧ e.2 ∉ B)).card =
      ∑ l ∈ Finset.univ \ B, ((Finset.univ \ A).filter (fun p => I p l)).card := by
  classical
  rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
  have hA : Finset.univ \ A = Finset.univ.filter (fun p => p ∉ A) := by
    ext p
    simp
  have hB : Finset.univ \ B = Finset.univ.filter (fun l => l ∉ B) := by
    ext l
    simp
  simp only [hA, hB, Finset.card_filter, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hlB : l ∈ B
  · simp [hlB]
  · simp only [hlB, not_false_eq_true, ite_true]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases hpA : p ∈ A <;> by_cases hpI : I p l <;> simp [hpA, hpI]

lemma finset_missing_one (N : ℕ) (A : Finset (Fin N)) (hsize : A.card + 1 = N) :
    ∃ p : Fin N, A = Finset.univ.erase p := by
  classical
  have hpart := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  simp only [Finset.card_univ, Fintype.card_fin] at hpart
  have hc : (Finset.univ \ A).card = 1 := by omega
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
  refine ⟨p, ?_⟩
  ext x
  have hx : x ∉ A ↔ x = p := by
    have h := Finset.ext_iff.mp hp x
    simpa using h
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

/-- A clean pencil cannot meet every edge of a residual full star of degree at least two. -/
lemma full_star_subset_clean_pencil_unique
    {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (U : Finset (Sym2 V)) (p t : V)
    (hstar : ∀ w, G.Adj p w → s(p, w) ∈ U)
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      G.Adj a l → G.Adj b l → G.Adj a m → G.Adj b m → l = m)
    (hpencil : ∀ u v, s(u, v) ∈ U →
      ∃ w, (w = u ∨ w = v) ∧ G.Adj t w ∧ s(t, w) ∉ U) :
    ∀ a b, G.Adj p a → G.Adj p b → a = b := by
  have leaf : ∀ a, G.Adj p a → G.Adj t a ∧ s(t, a) ∉ U := by
    intro a hpa
    obtain ⟨w, hw, htw, hclean⟩ := hpencil p a (hstar a hpa)
    rcases hw with rfl | rfl
    · exfalso
      apply hclean
      have hs := hstar t htw.symm
      rwa [Sym2.eq_swap] at hs
    · exact ⟨htw, hclean⟩
  intro a b hpa hpb
  obtain ⟨hta, hclean⟩ := leaf a hpa
  have hpt : p ≠ t := by
    intro h
    exact hclean (h ▸ hstar a hpa)
  exact hfour p t hpt a b hpa hta hpb (leaf b hpb).1

/-- Containment of a full star suffices: equality with `Ustar` is unnecessary. -/
lemma full_star_subset_extra_or_ge_two
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hleast : IsLeastAO G C) (htop : TopForm G C)
    (hfour : NoFourCycle G) (hempty : centreless G C = ∅)
    (p a b : Fin n) (hab : a ≠ b) (hpa : G.Adj p a) (hpb : G.Adj p b)
    (hstar : ∀ w, G.Adj p w → s(p, w) ∈ Ustar G C) :
    2 ≤ (orN G C \ lam G C).card := by
  classical
  have he := hstar a hpa
  obtain ⟨g, hg, side, j, hj, _, hr, _⟩ := Budget.residualTrace hleast htop he
  obtain ⟨m, hm, _, _⟩ := Budget.residualPath hleast.1 hempty hg hj hr
  have hpos : 0 < (orN G C \ lam G C).card := Finset.card_pos.mpr ⟨m, hm⟩
  by_contra hn
  have hone : (orN G C \ lam G C).card = 1 := by omega
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hone
  obtain ⟨t, ht⟩ := one_extra_or_clean_pencil n G C hleast htop hempty k hk ⟨s(p,a), he⟩
  apply hab
  apply full_star_subset_clean_pencil_unique G (Ustar G C) p t hstar
    (common_neighbors_unique_of_card_le_one G hfour) ?_ a b hpa hpb
  intro u v huv
  obtain ⟨w, hw, hclean⟩ := ht u v huv
  exact ⟨w, hw, (SimpleGraph.deleteEdges_adj.mp hclean).1,
    (SimpleGraph.deleteEdges_adj.mp hclean).2⟩

lemma full_star_subset_overhead_ge_two
    (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hleast : IsLeastAO G C) (htop : TopForm G C)
    (hfour : NoFourCycle G)
    (p a b : Fin n) (hab : a ≠ b) (hpa : G.Adj p a) (hpb : G.Adj p b)
    (hstar : ∀ w, G.Adj p w → s(p, w) ∈ Ustar G C) :
    2 ≤ 2 * (centreless G C).card + (orN G C \ lam G C).card := by
  by_cases hz : centreless G C = ∅
  · have hr := full_star_subset_extra_or_ge_two n G C hleast htop hfour hz
      p a b hab hpa hpb hstar
    omega
  · have hzpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hz)
    omega


lemma incidence_partial_cover_density
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hrow : ∀ p : Fin N, (Finset.univ.filter (I p)).card = q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (A B : Finset (Fin N)) :
    N * (q + 1) ≤ (q + 1) * (A.card + B.card) +
      (Finset.univ.filter (fun e : Fin N × Fin N =>
        I e.1 e.2 ∧ e.1 ∉ A ∧ e.2 ∉ B)).card := by
  classical
  let S := Finset.univ \ A
  let c : Fin N → ℕ := fun l => (S.filter (fun p => I p l)).card
  have hcap : ∀ l, c l ≤ q + 1 := by
    intro l
    rw [← hcol l]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ S))
  have hsum : ∑ l, c l = S.card * (q + 1) :=
    incidence_moment_one S Finset.univ I q (fun p _ => hrow p)
  have hB : ∑ l ∈ B, c l ≤ B.card * (q + 1) := by
    calc
      _ ≤ ∑ l ∈ B, (q + 1) := Finset.sum_le_sum (fun l _ => hcap l)
      _ = _ := by simp
  have hpart := Finset.sum_sdiff (f := c) (Finset.subset_univ B)
  have hS : S.card + A.card = N := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
  rw [uncovered_card_eq_sum]
  change N * (q + 1) ≤ (q + 1) * (A.card + B.card) + ∑ l ∈ Finset.univ \ B, c l
  nlinarith

lemma low_residual_cover_shape
    (q N t u P : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (A B : Finset (Fin N)) (hsize : A.card + B.card ≤ t)
    (hmissing : (Finset.univ.filter (fun e : Fin N × Fin N =>
      I e.1 e.2 ∧ e.1 ∉ A ∧ e.2 ∉ B)).card ≤ u)
    (hledger : t + P + 1 ≤ N + u) (hu : u < 2 * q) (hP : u ≤ P) :
    t + 1 = N ∧ A.card + B.card = t ∧ P = u ∧ q + 1 ≤ u ∧
      ((∃ p, A = Finset.univ.erase p ∧ B = ∅) ∨
        ∃ l, A = ∅ ∧ B = Finset.univ.erase l) := by
  classical
  have hrow := plane_point_degree q N I (by omega) hN hcol hunique
  have hdensity := incidence_partial_cover_density q N I hrow hcol A B
  have ht : t + 1 ≤ N := by omega
  have hkt : A.card + B.card = t := by
    by_contra hk
    have hgap : A.card + B.card + 2 ≤ N := by omega
    have hmul := Nat.mul_le_mul_right (q + 1) hgap
    nlinarith
  have htight : t + 1 = N := by
    by_contra hn
    have hgap : t + 2 ≤ N := by omega
    have hmul := Nat.mul_le_mul_right (q + 1) hgap
    nlinarith
  have hPu : P = u := by omega
  have hdegree : q + 1 ≤ u := by nlinarith
  have hpure : A = ∅ ∨ B = ∅ := by
    by_contra hn
    simp only [not_or] at hn
    have hAp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hn.1)
    have hBp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hn.2)
    have hAc : (Finset.univ \ A).card + A.card = N := by
      simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
    have hBc : (Finset.univ \ B).card + B.card = N := by
      simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
    have h := L_meta_2583.plane_partial_cover_bound_two q N I hq hN hcol hunique A B
      (by omega) (by omega)
    omega
  refine ⟨htight, hkt, hPu, hdegree, ?_⟩
  rcases hpure with hA | hB
  · obtain ⟨l, hl⟩ := finset_missing_one N B (by simp_all)
    exact Or.inr ⟨l, hA, hl⟩
  · obtain ⟨p, hp⟩ := finset_missing_one N A (by simp_all)
    exact Or.inl ⟨p, hp, hB⟩


end CircuitLedger


namespace Intersection

abbrev Assign := Fin 5 → Bool
abbrev Fun := Assign → Bool

def input (i : Fin 5) : Fun := fun z => z i
def zero : Fun := fun _ => false
def common : Fun := fun z => z 0 || z 1 || z 2
def ax : Fun := fun z => z 0 || z 3
def abx : Fun := fun z => z 0 || z 1 || z 3
def abcx : Fun := fun z => z 0 || z 1 || z 2 || z 3
def ay : Fun := fun z => z 0 || z 4
def aby : Fun := fun z => z 0 || z 1 || z 4
def abcy : Fun := fun z => z 0 || z 1 || z 2 || z 4

def required : Fin 7 → Fun := ![ax, abx, abcx, ay, aby, abcy, common]

def source : Fin 12 → Fun :=
  ![input 0, input 1, input 2, input 3, input 4,
    ax, abx, abcx, ay, aby, abcy, zero]

def catalogue : Finset Fun :=
  (Finset.univ.image input) ∪ (Finset.univ.image required)

lemma catalogue_card : catalogue.card = 12 := by
  decide +kernel

lemma required_ne_zero : ∀ i : Fin 7, required i ≠ zero := by
  decide +kernel

lemma common_eq_required : common = required 6 := rfl

lemma no_one_gate : ∀ (o : Bool) (i j : Fin 12),
    (fun z => if o then source i z && source j z else source i z || source j z) ≠ common := by
  decide +kernel

lemma catalogue_member_not_common : ∀ f ∈ catalogue, f ≠ common → ∃ i, source i = f := by
  intro f hf hne
  rcases Finset.mem_union.mp hf with hf | hf
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    fin_cases i
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨8, rfl⟩
    · exact ⟨9, rfl⟩
    · exact ⟨10, rfl⟩
    · exact False.elim (hne rfl)

open PEqualNP.CircuitLowerBounds

def original : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩,
    ⟨.or, [0, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [2, 9]⟩,
    ⟨.and, [7, 10]⟩], 11⟩

def replacement : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 6]⟩,
    ⟨.or, [0, 4]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [2, 9]⟩,
    ⟨.or, [0, 1]⟩, ⟨.or, [11, 2]⟩], 12⟩

lemma original_ao2 : PEqualNP.TopForm.IsAO2 5 original := by
  decide +kernel

lemma replacement_ao2 : PEqualNP.TopForm.IsAO2 5 replacement := by
  decide +kernel

lemma original_size : original.size = 7 := rfl

lemma replacement_size : replacement.size = 8 := rfl

lemma original_signals : ∀ (z : Assign) (i : Fin 6),
    (original.wires (List.ofFn z)).getD (5 + i.val) false = required i.castSucc z := by
  decide +kernel

lemma replacement_signals : ∀ (z : Assign) (i : Fin 6),
    (replacement.wires (List.ofFn z)).getD (5 + i.val) false = required i.castSucc z := by
  decide +kernel

lemma replacement_eval : ∀ z : Assign,
    PEqualNP.MetaComplexity.circuitFun 5 replacement z = common z := by
  decide +kernel

lemma original_eval : ∀ z : Assign,
    PEqualNP.MetaComplexity.circuitFun 5 original z = (common z || (z 3 && z 4)) := by
  decide +kernel

end Intersection


namespace IntersectionLower

open PEqualNP.CircuitLowerBounds

abbrev Assignment := Fin 5 → Bool
abbrev WireFun := Assignment → Bool

def zero : WireFun := fun _ => false
def inputList : List WireFun := List.ofFn fun i : Fin 5 => fun z => z i

def step (w : List WireFun) (g : Gate) : List WireFun :=
  w ++ [fun z => g.op.eval (g.inputs.map fun i => (w.getD i zero) z)]

def wires (C : Circuit) : List WireFun := C.gates.foldl step inputList

def binary (o : Bool) (a b : WireFun) : WireFun :=
  fun z => if o then a z && b z else a z || b z

def gate (o : Bool) (a b : ℕ) : Gate := ⟨if o then .and else .or, [a, b]⟩

lemma step_gate (w : List WireFun) (o : Bool) (a b : ℕ) :
    step w (gate o a b) = w ++ [binary o (w.getD a zero) (w.getD b zero)] := by
  cases o <;> simp [step, gate, GateOp.eval] <;> rfl

lemma gate_shape (g : Gate) (ho : g.op = .and ∨ g.op = .or)
    (hl : g.inputs.length = 2) : ∃ o a b, g = gate o a b := by
  rcases g with ⟨op, inputs⟩
  rcases List.length_eq_two.mp hl with ⟨a, b, rfl⟩
  rcases ho with rfl | rfl
  · exact ⟨true, a, b, rfl⟩
  · exact ⟨false, a, b, rfl⟩

lemma mem_fold (gs : List Gate) (w : List WireFun) (f : WireFun) (hf : f ∈ w) :
    f ∈ gs.foldl step w := by
  induction gs generalizing w with
  | nil => exact hf
  | cons g gs ih =>
    apply ih
    simp [step, hf]

lemma getD_mem_or (w : List WireFun) (i : ℕ) :
    w.getD i zero = zero ∨ w.getD i zero ∈ w := by
  induction w generalizing i with
  | nil => exact Or.inl rfl
  | cons a w ih =>
    cases i with
    | zero => exact Or.inr (by simp [List.getD])
    | succ i =>
      rcases ih i with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

lemma fold_length (gs : List Gate) (w : List WireFun) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step, Nat.add_assoc, Nat.add_comm]

lemma avoid_fold (K : Finset WireFun) (target : WireFun)
    (hzero : zero ≠ target)
    (hbinary : ∀ a b : WireFun, (a = zero ∨ a ∈ K) → (b = zero ∨ b ∈ K) →
      a ≠ target → b ≠ target → ∀ o : Bool, binary o a b ≠ target)
    (gs : List Gate) (w : List WireFun)
    (hshape : ∀ g ∈ gs, ∃ o a b, g = gate o a b)
    (hglobal : ∀ f ∈ gs.foldl step w, f ∈ K)
    (hstart : ∀ f ∈ w, f ≠ target) :
    ∀ f ∈ gs.foldl step w, f ≠ target := by
  induction gs generalizing w with
  | nil => exact hstart
  | cons g gs ih =>
    obtain ⟨o, a, b, rfl⟩ := hshape g (by simp)
    have hwK : ∀ f ∈ w, f ∈ K := by
      intro f hf
      exact hglobal f (mem_fold _ w f hf)
    have hread (i : ℕ) :
        (w.getD i zero = zero ∨ w.getD i zero ∈ K) ∧ w.getD i zero ≠ target := by
      rcases getD_mem_or w i with h | h
      · exact ⟨Or.inl h, fun heq => hzero (h.symm.trans heq)⟩
      · exact ⟨Or.inr (hwK _ h), hstart _ h⟩
    have hnew := hbinary _ _ (hread a).1 (hread b).1 (hread a).2 (hread b).2 o
    have hnext : ∀ f ∈ step w (gate o a b), f ≠ target := by
      rw [step_gate]
      intro f hf
      simp only [List.mem_append, List.mem_singleton] at hf
      rcases hf with hf | rfl
      · exact hstart f hf
      · exact hnew
    exact ih _ (fun g hg => hshape g (by simp [hg])) hglobal hnext

lemma catalogue_lower_bound (C : Circuit) (K : Finset WireFun) (target : WireFun)
    (hAO : PEqualNP.TopForm.IsAO2 5 C) (hcard : K.card = 12)
    (hzero : zero ≠ target) (htarget : target ∈ K)
    (hinputs : ∀ f ∈ inputList, f ≠ target)
    (hbinary : ∀ a b : WireFun, (a = zero ∨ a ∈ K) → (b = zero ∨ b ∈ K) →
      a ≠ target → b ≠ target → ∀ o : Bool, binary o a b ≠ target)
    (hcover : K ⊆ (wires C).toFinset) : 8 ≤ C.size := by
  classical
  by_contra hn
  have hlen : (wires C).length ≤ 12 := by
    rw [wires, fold_length]
    simp only [inputList, List.length_ofFn, Circuit.size] at hn ⊢
    omega
  have heq : K = (wires C).toFinset := Finset.eq_of_subset_of_card_le hcover
    (by rw [hcard]; exact (List.toFinset_card_le _).trans hlen)
  have hglobal : ∀ f ∈ wires C, f ∈ K := by
    intro f hf
    rw [heq]
    exact List.mem_toFinset.mpr hf
  have hshape : ∀ g ∈ C.gates, ∃ o a b, g = gate o a b := by
    intro g hg
    exact gate_shape g (hAO.1 g hg) (hAO.2.2 g hg)
  have havoid := avoid_fold K target hzero hbinary C.gates inputList hshape hglobal hinputs
  have hmem : target ∈ wires C := List.mem_toFinset.mp (hcover htarget)
  exact havoid target hmem rfl

lemma map_getD {α β : Type} (f : α → β) (w : List α) (i : ℕ) (d : α) :
    (w.map f).getD i (f d) = f (w.getD i d) := by
  induction w generalizing i with
  | nil => simp [List.getD]
  | cons a w ih => cases i <;> simp_all [List.getD]

def boolStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_sem (w : List WireFun) (g : Gate) (z : Assignment) :
    (step w g).map (fun f => f z) = boolStep (w.map (fun f => f z)) g := by
  have hm (i : ℕ) : (w.map (fun f => f z)).getD i false = (w.getD i zero) z :=
    map_getD (fun f : WireFun => f z) w i zero
  simp only [step, boolStep, List.map_append, List.map_cons, List.map_nil]
  simp only [hm]

lemma fold_sem (gs : List Gate) (w : List WireFun) (z : Assignment) :
    (gs.foldl step w).map (fun f => f z) = gs.foldl boolStep (w.map (fun f => f z)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih, step_sem]

lemma wires_sem (C : Circuit) (z : Assignment) :
    (wires C).map (fun f => f z) = C.wires (List.ofFn z) := by
  rw [wires, fold_sem]
  simp only [inputList, List.map_ofFn]
  rfl

lemma getD_sem (C : Circuit) (i : ℕ) (z : Assignment) :
    (wires C).getD i zero z = (C.wires (List.ofFn z)).getD i false := by
  rw [← wires_sem]
  exact (map_getD (fun f : WireFun => f z) (wires C) i zero).symm

end IntersectionLower

namespace Intersection

open PEqualNP.CircuitLowerBounds

lemma extraction_lower_bound (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 5 C)
    (hout : ∀ i : Fin 7, ∃ w : ℕ, ∀ z : Assign,
      (C.wires (List.ofFn z)).getD w false = required i z) : 8 ≤ C.size := by
  apply IntersectionLower.catalogue_lower_bound C catalogue common hAO catalogue_card
  · exact Ne.symm (required_ne_zero 6)
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · intro f hf
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
    have hn : ∀ i : Fin 5, input i ≠ common := by decide +kernel
    exact hn i
  · intro a b ha hb hna hnb o
    have hs (f : Fun) (hf : f = IntersectionLower.zero ∨ f ∈ catalogue)
        (hne : f ≠ common) : ∃ i, source i = f := by
      rcases hf with hf | hf
      · exact ⟨11, hf.symm⟩
      · exact catalogue_member_not_common f hf hne
    obtain ⟨i, rfl⟩ := hs a ha hna
    obtain ⟨j, rfl⟩ := hs b hb hnb
    exact no_one_gate o i j
  · intro f hf
    apply List.mem_toFinset.mpr
    rcases Finset.mem_union.mp hf with hf | hf
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
      apply IntersectionLower.mem_fold
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
      obtain ⟨w, hw⟩ := hout i
      have heq : (IntersectionLower.wires C).getD w IntersectionLower.zero = required i := by
        funext z
        rw [IntersectionLower.getD_sem]
        exact hw z
      rcases IntersectionLower.getD_mem_or (IntersectionLower.wires C) w with hz | hm
      · exact False.elim (required_ne_zero i (heq.symm.trans hz))
      · simpa only [heq] using hm

lemma replacement_all_signals : ∀ i : Fin 7, ∃ w : ℕ, ∀ z : Assign,
    (replacement.wires (List.ofFn z)).getD w false = required i z := by
  intro i
  fin_cases i
  · exact ⟨5, fun z => replacement_signals z 0⟩
  · exact ⟨6, fun z => replacement_signals z 1⟩
  · exact ⟨7, fun z => replacement_signals z 2⟩
  · exact ⟨8, fun z => replacement_signals z 3⟩
  · exact ⟨9, fun z => replacement_signals z 4⟩
  · exact ⟨10, fun z => replacement_signals z 5⟩
  · exact ⟨12, fun z => replacement_eval z⟩

lemma no_cost_free_extraction : ¬ ∃ D : Circuit,
    PEqualNP.TopForm.IsAO2 5 D ∧ D.size ≤ original.size ∧
      ∀ i : Fin 7, ∃ w : ℕ, ∀ z : Assign,
        (D.wires (List.ofFn z)).getD w false = required i z := by
  rintro ⟨D, hAO, hsize, hout⟩
  have hmin := extraction_lower_bound D hAO hout
  rw [original_size] at hsize
  omega

end Intersection




namespace ProductiveBudget

lemma support_family_bound {α : Type} [DecidableEq α]
    (n m : ℕ) (s : ℕ → Finset α) (a : ℕ → Finset ℕ) (cost : ℕ → ℕ)
    (hinput : ∀ i < n, (s i).card ≤ 1)
    (hback : ∀ k < m, a k ⊆ Finset.range (n + k))
    (hcost : ∀ k < m, (a k).card ≤ cost k + 1)
    (hcover : ∀ k < m, s (n + k) ⊆ (a k).biUnion s) :
    ∀ t : Finset ℕ, t ⊆ Finset.range (n + m) →
      (t.biUnion s).card ≤ (Finset.range m).sum cost + t.card := by
  induction m with
  | zero =>
    intro t ht
    have h1 := Finset.card_biUnion_le (s := t) (t := s)
    have h2 : ∑ i ∈ t, (s i).card ≤ t.card := by
      calc
        ∑ i ∈ t, (s i).card ≤ ∑ i ∈ t, 1 := Finset.sum_le_sum fun i hi =>
          hinput i (by have := ht hi; simpa using this)
        _ = t.card := by simp
    simpa using h1.trans h2
  | succ m ih =>
    intro t ht
    have hb : ∀ k < m, a k ⊆ Finset.range (n + k) := fun k hk => hback k (by omega)
    have hc : ∀ k < m, (a k).card ≤ cost k + 1 := fun k hk => hcost k (by omega)
    have hv : ∀ k < m, s (n + k) ⊆ (a k).biUnion s := fun k hk => hcover k (by omega)
    by_cases hm : n + m ∈ t
    · let u := t.erase (n + m) ∪ a m
      have hu : u ⊆ Finset.range (n + m) := by
        intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · obtain ⟨hne, hit⟩ := Finset.mem_erase.mp hi
          have hi' := Finset.mem_range.mp (ht hit)
          exact Finset.mem_range.mpr (by omega)
        · exact hback m (by omega) hi
      have hsub : t.biUnion s ⊆ u.biUnion s := by
        intro x hx
        obtain ⟨i, hit, hxi⟩ := Finset.mem_biUnion.mp hx
        by_cases him : i = n + m
        · subst i
          obtain ⟨j, hja, hxj⟩ := Finset.mem_biUnion.mp (hcover m (by omega) hxi)
          exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_union_right _ hja, hxj⟩
        · exact Finset.mem_biUnion.mpr ⟨i,
            Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨him, hit⟩), hxi⟩
      have huc : u.card ≤ t.card + cost m := by
        have h1 := Finset.card_union_le (t.erase (n + m)) (a m)
        have h2 := Finset.card_erase_add_one hm
        have h3 := hcost m (by omega)
        dsimp only [u]
        omega
      have hbound := ih hb hc hv u hu
      have hsmall := Finset.card_le_card hsub
      rw [Finset.sum_range_succ]
      change (t.biUnion s).card ≤ (Finset.range m).sum cost + cost m + t.card
      omega
    · have ht' : t ⊆ Finset.range (n + m) := by
        intro i hi
        have hi' := Finset.mem_range.mp (ht hi)
        have hne : i ≠ n + m := by intro h; subst i; exact hm hi
        exact Finset.mem_range.mpr (by omega)
      have hbound := ih hb hc hv t ht'
      rw [Finset.sum_range_succ]
      change (t.biUnion s).card ≤ (Finset.range m).sum cost + cost m + t.card
      omega


lemma small_union {α : Type} [DecidableEq α] (A B : Finset α)
    (h : (A ∪ B).card ≤ 1) : A ∪ B = A ∨ A ∪ B = B := by
  by_cases ha : A = ∅
  · exact Or.inr (by simp [ha])
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr ha
  apply Or.inl
  apply Finset.union_eq_left.mpr
  intro b hb
  have hba := Finset.card_le_one.mp h b (Finset.mem_union_right _ hb)
    a (Finset.mem_union_left _ ha)
  simpa [hba] using ha

lemma productive_support_budget {α : Type} [DecidableEq α]
    (n m : ℕ) (s : ℕ → Finset α) (a b : ℕ → ℕ)
    (hinput : ∀ i < n, (s i).card ≤ 1)
    (ha : ∀ k < m, a k < n + k) (hb : ∀ k < m, b k < n + k)
    (hstep : ∀ k < m, s (n + k) = s (a k) ∪ s (b k) ∨ s (n + k) = ∅)
    (T : Finset ℕ) (hT : T ⊆ Finset.range (n + m)) :
    (T.biUnion s).card ≤
      ((Finset.range m).filter fun k => 2 ≤ (s (n + k)).card ∧
        (s (a k)).Nonempty ∧ (s (b k)).Nonempty).card + T.card := by
  classical
  let cost : ℕ → ℕ := fun k =>
    if 2 ≤ (s (n + k)).card ∧ (s (a k)).Nonempty ∧ (s (b k)).Nonempty then 1 else 0
  have hparents : ∀ k < m, ∃ P : Finset ℕ,
      P ⊆ Finset.range (n + k) ∧ P.card ≤ cost k + 1 ∧
        s (n + k) ⊆ P.biUnion s := by
    intro k hk
    by_cases hz : s (n + k) = ∅
    · exact ⟨∅, Finset.empty_subset _, by simp, by simp [hz]⟩
    have hu : s (n + k) = s (a k) ∪ s (b k) := (hstep k hk).resolve_right hz
    have left_parent (hleft : s (a k) ∪ s (b k) = s (a k)) :
        ∃ P : Finset ℕ, P ⊆ Finset.range (n + k) ∧ P.card ≤ cost k + 1 ∧
          s (n + k) ⊆ P.biUnion s := by
      refine ⟨{a k}, ?_, by simp, ?_⟩
      · simpa using ha k hk
      · simpa only [Finset.singleton_biUnion] using Finset.subset_of_eq (hu.trans hleft)
    have right_parent (hright : s (a k) ∪ s (b k) = s (b k)) :
        ∃ P : Finset ℕ, P ⊆ Finset.range (n + k) ∧ P.card ≤ cost k + 1 ∧
          s (n + k) ⊆ P.biUnion s := by
      refine ⟨{b k}, ?_, by simp, ?_⟩
      · simpa using hb k hk
      · simpa only [Finset.singleton_biUnion] using Finset.subset_of_eq (hu.trans hright)
    by_cases hane : (s (a k)).Nonempty
    · by_cases hbne : (s (b k)).Nonempty
      · by_cases hcard : 2 ≤ (s (n + k)).card
        · refine ⟨{a k, b k}, ?_, ?_, ?_⟩
          · intro w hw
            simp only [Finset.mem_insert, Finset.mem_singleton] at hw
            rcases hw with rfl | rfl
            · exact Finset.mem_range.mpr (ha k hk)
            · exact Finset.mem_range.mpr (hb k hk)
          · simpa [cost, hcard, hane, hbne] using
              (Finset.card_le_two : ({a k, b k} : Finset ℕ).card ≤ 2)
          · simpa only [Finset.biUnion_insert, Finset.singleton_biUnion, hu] using
              (Finset.Subset.refl (s (a k) ∪ s (b k)))
        · have hsmall : (s (a k) ∪ s (b k)).card ≤ 1 := by rw [← hu]; omega
          exact (small_union _ _ hsmall).elim left_parent right_parent
      · exact left_parent (by simp [Finset.not_nonempty_iff_eq_empty.mp hbne])
    · exact right_parent (by simp [Finset.not_nonempty_iff_eq_empty.mp hane])
  let parents : ℕ → Finset ℕ := fun k => if hk : k < m then (hparents k hk).choose else ∅
  have hp : ∀ k < m, parents k ⊆ Finset.range (n + k) := by
    intro k hk
    simpa [parents, hk] using (hparents k hk).choose_spec.1
  have hc : ∀ k < m, (parents k).card ≤ cost k + 1 := by
    intro k hk
    simpa [parents, hk] using (hparents k hk).choose_spec.2.1
  have hv : ∀ k < m, s (n + k) ⊆ (parents k).biUnion s := by
    intro k hk
    simpa [parents, hk] using (hparents k hk).choose_spec.2.2
  have h := support_family_bound n m s parents cost hinput hp hc hv T hT
  have hsum : (Finset.range m).sum cost =
      ((Finset.range m).filter fun k => 2 ≤ (s (n + k)).card ∧
        (s (a k)).Nonempty ∧ (s (b k)).Nonempty).card := by
    simp only [cost, Finset.sum_boole]
    rfl
  rwa [hsum] at h

end ProductiveBudget


namespace CircuitLedger
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def falseSide (C : Circuit) (p : Fin n) (j : ℕ) : Fin 2 :=
  if Budget.val C (List.ofFn (pairInput p p)) (opnd C j 0) = false then 0 else 1

lemma falseSide_correct (hAO : IsAO2 n C) (p : Fin n) {j : ℕ}
    (hj : j ∈ junk G C) (hfalse : gateVal n C j (pairInput p p) = false) :
    Budget.val C (List.ofFn (pairInput p p)) (opnd C j (falseSide C p j)) = false := by
  obtain ⟨hlen, hop, _⟩ := Budget.junkData hj
  by_cases hz : Budget.val C (List.ofFn (pairInput p p)) (opnd C j 0) = false
  · simp [falseSide, hz]
  · have h0 : Budget.val C (List.ofFn (pairInput p p)) (opnd C j 0) = true :=
      Bool.eq_true_of_not_eq_false hz
    have h1 : Budget.val C (List.ofFn (pairInput p p)) (opnd C j 1) = false := by
      by_contra h
      have h1 := Bool.eq_true_of_not_eq_false h
      have htrue := (Budget.andValBoth hAO hlen hop (pairInput p p)).mpr ⟨h0, h1⟩
      exact Bool.false_ne_true (hfalse.symm.trans htrue)
    simpa [falseSide, hz] using h1

lemma operand_reachable_lt (hAO : IsAO2 n C) {j k : ℕ} {b : Fin 2}
    (hj : j < C.gates.length) (hr : OrReaches n C (opnd C j b) k) : k < j := by
  have hle := Budget.orStep_le (Budget.orReaches_reach k _ hr).1
  have hlt := Budget.opndBound hAO hj b
  omega

lemma false_root_raw_leaf (hAO : IsAO2 n C) (hT : TopForm G C)
    (p l : Fin n) {j : ℕ} (hj : j ∈ junk G C)
    (hf : gateVal n C j (pairInput p p) = false)
    (hon : gateVal n C j (pairInput p l) = true)
    (hmin : ∀ k ∈ junk G C, k < j →
      gateVal n C k (pairInput p p) = false → gateVal n C k (pairInput p l) = false) :
    l ∈ orIn n C (opnd C j (falseSide C p j)) := by
  let b := falseSide C p j
  change l ∈ side (n := n) C j b
  have hb := falseSide_correct hAO p hj hf
  change Budget.val C (List.ofFn (pairInput p p)) (opnd C j b) = false at hb
  obtain ⟨hlen, hop, _⟩ := Budget.junkData hj
  have hval := (Budget.andValOperands hAO hlen hop (pairInput p l)).mp hon b
  rcases Budget.operandSupport hAO hT hlen hop hval with ⟨t, ht, htp | htl⟩ | ⟨k, hk, hr, hkv⟩
  · subst t
    have hpval : Budget.val C (List.ofFn (pairInput p p)) (opnd C j b) = true :=
      Budget.sideVal ht (Budget.pairInput_left p p)
    exact (Bool.false_ne_true (hb.symm.trans hpval)).elim
  · simpa only [htl] using ht
  · have hklt := operand_reachable_lt hAO hlen hr
    have hkfalse : gateVal n C k (pairInput p p) = false := by
      by_contra hn
      have hkt := Bool.eq_true_of_not_eq_false hn
      have ht : Budget.val C (List.ofFn (pairInput p p)) (opnd C j b) = true :=
        Budget.orStep_up (n := n) (by simp) (Budget.orReaches_reach k _ hr).1 hkt
      exact Bool.false_ne_true (hb.symm.trans ht)
    exact (Bool.false_ne_true ((hmin k hk hklt hkfalse).symm.trans hkv)).elim

lemma false_junk_roots_cover (hAO : IsAO2 n C) (hT : TopForm G C) (p l : Fin n)
    (hex : ∃ j ∈ junk G C, gateVal n C j (pairInput p p) = false ∧
      gateVal n C j (pairInput p l) = true) :
    ∃ j ∈ junk G C, gateVal n C j (pairInput p p) = false ∧
      l ∈ orIn n C (opnd C j (falseSide C p j)) := by
  classical
  let S := (junk G C).filter fun j => gateVal n C j (pairInput p p) = false ∧
    gateVal n C j (pairInput p l) = true
  have hS : S.Nonempty := by
    obtain ⟨j, hj, hf, hon⟩ := hex
    exact ⟨j, Finset.mem_filter.mpr ⟨hj, hf, hon⟩⟩
  let j := S.min' hS
  obtain ⟨hj, hf, hon⟩ := Finset.mem_filter.mp (S.min'_mem hS)
  refine ⟨j, hj, hf, false_root_raw_leaf hAO hT p l hj hf hon ?_⟩
  intro k hk hkj hkfalse
  by_contra hn
  have hkon := Bool.eq_true_of_not_eq_false hn
  have hkS : k ∈ S := Finset.mem_filter.mpr ⟨hk, hkfalse, hkon⟩
  have hle : j ≤ k := S.min'_le k hkS
  omega


noncomputable def falseJunkRoots (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (p : Fin n) : Finset ℕ :=
  ((junk G C).filter fun j => gateVal n C j (pairInput p p) = false).image
    (fun j => opnd C j (falseSide C p j))

lemma falseJunkRoots_card_le (p : Fin n) :
    (falseJunkRoots G C p).card ≤
      ((junk G C).filter fun j => gateVal n C j (pairInput p p) = false).card :=
  Finset.card_image_le

lemma falseJunkRoots_bound (hAO : IsAO2 n C) (p : Fin n) :
    falseJunkRoots G C p ⊆ Finset.range (n + C.size) := by
  intro w hw
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
  have hlen := (Budget.junkData (Finset.mem_filter.mp hj).1).1
  have hb := Budget.opndBound hAO hlen (falseSide C p j)
  exact Finset.mem_range.mpr (by change _ < n + C.gates.length; omega)

lemma falseJunkRoots_cover (hAO : IsAO2 n C) (hT : TopForm G C) (p l : Fin n)
    (hex : ∃ j ∈ junk G C, gateVal n C j (pairInput p p) = false ∧
      gateVal n C j (pairInput p l) = true) :
    l ∈ (falseJunkRoots G C p).biUnion (orIn n C) := by
  obtain ⟨j, hj, hf, hl⟩ := false_junk_roots_cover hAO hT p l hex
  exact Finset.mem_biUnion.mpr ⟨_,
    Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hf⟩, rfl⟩, hl⟩

end CircuitLedger


namespace CircuitLedger
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover Budget

lemma raw_orIn_iff_reach {n : ℕ} {C : Circuit} (p : ℕ) (u : Fin n) :
    u ∈ orIn n C p ↔ Relation.ReflTransGen (Budget.OrStep n C) p u.val :=
  ⟨Budget.mem_orIn_reach u, Budget.reach_mem_orIn u⟩

lemma orIn_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    (PEqualNP.TopForm.orIn n C w).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [raw_orIn_iff_reach] at ha hb
  have h1 : ∀ c : Fin n, Relation.ReflTransGen (OrStep n C) w c.val → c.val = w := by
    intro c hc
    rcases Relation.ReflTransGen.cases_head hc with h | ⟨d, hd, _⟩
    · exact h.symm
    · obtain ⟨k, _, h3, _⟩ := hd
      omega
  exact Fin.ext ((h1 a ha).trans (h1 b hb).symm)

lemma orIn_gate {n : ℕ} (C : Circuit) (k : ℕ) (u : Fin n) :
    u ∈ PEqualNP.TopForm.orIn n C (n + k) ↔ k < C.gates.length ∧
      (gateAt C k).op = GateOp.or ∧ ∃ w ∈ (gateAt C k).inputs, w < n + k ∧
        u ∈ PEqualNP.TopForm.orIn n C w := by
  rw [raw_orIn_iff_reach]
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_head h with h | ⟨d, hd, hr⟩
    · have := u.isLt
      omega
    · obtain ⟨k', hk', he, hop, hin, hlt⟩ := hd
      have hkk : k' = k := by omega
      subst hkk
      exact ⟨hk', hop, d, hin, hlt, (raw_orIn_iff_reach d u).2 hr⟩
  · rintro ⟨hk, hop, w, hw, hlt, hu⟩
    exact Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hw, hlt⟩ ((raw_orIn_iff_reach w u).1 hu)

lemma orIn_binary {n : ℕ} {C : Circuit} (hAO : PEqualNP.TopForm.IsAO2 n C)
    (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.TopForm.orIn n C (n + k) =
        PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 0) ∪
          PEqualNP.TopForm.orIn n C (PEqualNP.TopForm.opnd C k 1) ∨
      PEqualNP.TopForm.orIn n C (n + k) = ∅ := by
  classical
  by_cases hop : (gateAt C k).op = GateOp.or
  · left
    obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem hk))
    have hp : p < n + k := hAO.2.1 k hk p (by rw [hin]; simp)
    have hq : q < n + k := hAO.2.1 k hk q (by rw [hin]; simp)
    have e0 : PEqualNP.TopForm.opnd C k 0 = p := by simp [PEqualNP.TopForm.opnd, hin]
    have e1 : PEqualNP.TopForm.opnd C k 1 = q := by simp [PEqualNP.TopForm.opnd, hin]
    rw [e0, e1]
    ext u
    rw [Finset.mem_union, orIn_gate]
    simp only [hk, hop, true_and, hin, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro ⟨w, (rfl | rfl), _, hu⟩
      · exact Or.inl hu
      · exact Or.inr hu
    · rintro (hu | hu)
      · exact ⟨p, Or.inl rfl, hp, hu⟩
      · exact ⟨q, Or.inr rfl, hq, hu⟩
  · right
    ext u
    simp only [Finset.notMem_empty, iff_false]
    intro hu
    exact hop ((orIn_gate C k u).mp hu).2.1

lemma raw_star_forest_budget
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (hfour : NoFourCycle G)
    (p : Fin n) (X : Finset (Fin n)) (hX : ∀ x ∈ X, G.Adj p x)
    (hstar : ∀ w ∈ X, s(p,w) ∈ Ustar G C)
    (R : Finset ℕ) (hR : R ⊆ Finset.range (n + C.size)) :
    (R.biUnion (fun w => orIn n C w ∩ X)).card ≤
      ((orN G C \ lam G C) \ mixing G C).card + R.card := by
  classical
  let ss : ℕ → Finset (Fin n) := fun w => orIn n C w ∩ X
  let a : ℕ → ℕ := fun k => opnd C k 0
  let b : ℕ → ℕ := fun k => opnd C k 1
  let P := (Finset.range C.gates.length).filter fun k => 2 ≤ (ss (n+k)).card ∧
    (ss (a k)).Nonempty ∧ (ss (b k)).Nonempty
  have hinput : ∀ i < n, (ss i).card ≤ 1 := by
    intro i hi
    exact (Finset.card_le_card Finset.inter_subset_left).trans (orIn_input C i hi)
  have hstep : ∀ k < C.gates.length, ss (n+k) = ss (a k) ∪ ss (b k) ∨ ss (n+k) = ∅ := by
    intro k hk
    rcases orIn_binary hAO k hk with hu | hz
    · left
      simp only [ss, a, b, hu, Finset.union_inter_distrib_right]
    · right
      simp [ss, hz]
  have hb := ProductiveBudget.productive_support_budget n C.gates.length ss a b hinput
    (fun k hk => Budget.opndBound hAO hk 0)
    (fun k hk => Budget.opndBound hAO hk 1) hstep R hR
  have hP : P ⊆ (orN G C \ lam G C) \ mixing G C := by
    intro k hk
    obtain ⟨hklen, hmany, hleft, hright⟩ := Finset.mem_filter.mp hk
    have hklen' := Finset.mem_range.mp hklen
    obtain ⟨u, v, hu, hv, huv⟩ := Finset.one_lt_card_iff.mp (show 1 < (ss (n+k)).card by omega)
    obtain ⟨huraw, huX⟩ := Finset.mem_inter.mp hu
    obtain ⟨hvraw, hvX⟩ := Finset.mem_inter.mp hv
    have hop : (gateAt C k).op = GateOp.or := ((orIn_gate C k u).mp huraw).2.1
    have hn : ¬ BelowF G C k := by
      intro hbelow
      have hg : gateVal n C k (pairInput u u) = true :=
        Budget.reach_var_val (pairInput u u) (n+k) u (Budget.mem_orIn_reach u huraw)
          (Budget.pairInput_left u u)
      exact G.irrefl ((Budget.graphFun_pair G u u).mp (hbelow _ hg))
    have hkn : k ∈ orN G C := by
      simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using ⟨hklen', hop, hn⟩
    have hnotlam : k ∉ lam G C := by
      intro hlam
      obtain ⟨_, _, _, g, hg, c, hsingle, hr⟩ := Finset.mem_filter.mp hlam
      obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hsingle
      have htmem : t ∈ side (n := n) C g (1-c) := by simp [ht]
      have rawside : ∀ x ∈ orIn n C (n+k), x ∈ side (n := n) C g c := by
        intro x hx
        exact Budget.reach_mem_orIn x
          ((Budget.orReaches_reach k _ hr).1.trans (Budget.mem_orIn_reach x hx))
      have htu := (Budget.cleanAdj hAO hg c (rawside u huraw) htmem).symm
      have htv := (Budget.cleanAdj hAO hg c (rawside v hvraw) htmem).symm
      have hpt : p ≠ t := by
        intro heq
        exact (SimpleGraph.deleteEdges_adj.mp htu).2 (heq ▸ hstar u huX)
      exact huv (common_neighbors_unique_of_card_le_one G hfour p t hpt u v
        (hX u huX) (SimpleGraph.deleteEdges_adj.mp htu).1
        (hX v hvX) (SimpleGraph.deleteEdges_adj.mp htv).1)
    have hnotmix : k ∉ mixing G C := by
      intro hmix
      have hx := (Finset.mem_filter.mp hmix).2
      have hn0 : orIn n C (opnd C k 0) ≠ ∅ := by
        obtain ⟨x, hx⟩ := hleft
        exact Finset.nonempty_iff_ne_empty.mp ⟨x, (Finset.mem_inter.mp hx).1⟩
      have hn1 : orIn n C (opnd C k 1) ≠ ∅ := by
        obtain ⟨x, hx⟩ := hright
        exact Finset.nonempty_iff_ne_empty.mp ⟨x, (Finset.mem_inter.mp hx).1⟩
      exact hx (propext (iff_of_false hn0 hn1))
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hkn, hnotlam⟩, hnotmix⟩
  exact hb.trans (Nat.add_le_add_right (Finset.card_le_card hP) _)

end CircuitLedger


namespace CircuitLedger
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge

noncomputable def falseServed {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (p : Fin n) (X : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact X.filter fun l => ∃ j ∈ junk G C, gateVal n C j (pairInput p p) = false ∧
    gateVal n C j (pairInput p l) = true

lemma false_served_budget
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (p : Fin n) (X : Finset (Fin n)) (hX : ∀ x ∈ X, G.Adj p x)
    (hstar : ∀ w ∈ X, s(p,w) ∈ Ustar G C) :
    (falseServed G C p X).card ≤
      ((orN G C \ lam G C) \ mixing G C).card +
        ((junk G C).filter fun j => gateVal n C j (pairInput p p) = false).card := by
  classical
  have hcover : falseServed G C p X ⊆
      (falseJunkRoots G C p).biUnion (fun w => orIn n C w ∩ X) := by
    intro l hl
    obtain ⟨hlX, hex⟩ := Finset.mem_filter.mp hl
    obtain ⟨w, hw, hlw⟩ := Finset.mem_biUnion.mp (falseJunkRoots_cover hAO hT p l hex)
    exact Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_inter.mpr ⟨hlw, hlX⟩⟩
  have hf := raw_star_forest_budget G C hAO hfour p X hX hstar
    (falseJunkRoots G C p) (falseJunkRoots_bound hAO p)
  have hr := falseJunkRoots_card_le (G := G) (C := C) p
  exact (Finset.card_le_card hcover).trans (hf.trans (Nat.add_le_add_left hr _))

end CircuitLedger


namespace CircuitLedger
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.MetaComplexity.NestedCover

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma falseSide_and_correct (hAO : IsAO2 n C) (p : Fin n) {j : ℕ}
    (hlen : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hfalse : gateVal n C j (pairInput p p) = false) :
    Budget.val C (List.ofFn (pairInput p p)) (opnd C j (falseSide C p j)) = false := by
  by_cases hz : Budget.val C (List.ofFn (pairInput p p)) (opnd C j 0) = false
  · simp [falseSide, hz]
  · have h0 := Bool.eq_true_of_not_eq_false hz
    have h1 : Budget.val C (List.ofFn (pairInput p p)) (opnd C j 1) = false := by
      by_contra h
      have h1 := Bool.eq_true_of_not_eq_false h
      have htrue := (Budget.andValBoth hAO hlen hop (pairInput p p)).mpr ⟨h0, h1⟩
      exact Bool.false_ne_true (hfalse.symm.trans htrue)
    simpa [falseSide, hz] using h1

lemma top_unserved_leaf_in_falseSide (hAO : IsAO2 n C) (hT : TopForm G C)
    (p l : Fin n) {a : ℕ} (ha : a ∈ tops G C)
    (haccept : gateVal n C a (pairInput p l) = true)
    (hnofalse : ∀ j ∈ junk G C, gateVal n C j (pairInput p p) = false →
      gateVal n C j (pairInput p l) = false) :
    l ∈ orIn n C (opnd C a (falseSide C p a)) := by
  obtain ⟨hlen, hop, hbelow⟩ := Budget.topData ha
  have hfalse : gateVal n C a (pairInput p p) = false := by
    by_contra h
    exact G.irrefl ((Budget.graphFun_pair G p p).mp (hbelow _ (Bool.eq_true_of_not_eq_false h)))
  let b := falseSide C p a
  change l ∈ side (n := n) C a b
  have hb : Budget.val C (List.ofFn (pairInput p p)) (opnd C a b) = false :=
    falseSide_and_correct hAO p hlen hop hfalse
  have hpair := (Budget.andValOperands hAO hlen hop (pairInput p l)).mp haccept b
  rcases Budget.operandSupport hAO hT hlen hop hpair with
    ⟨t, ht, htp | htl⟩ | ⟨k, hk, hr, hkv⟩
  · subst t
    exact (Bool.false_ne_true (hb.symm.trans (Budget.sideVal ht (Budget.pairInput_left p p)))).elim
  · simpa only [htl] using ht
  · have hkcentre : gateVal n C k (pairInput p p) = true := by
      by_contra h
      exact Bool.false_ne_true ((hnofalse k hk (Bool.eq_false_of_not_eq_true h)).symm.trans hkv)
    have hwire : Budget.val C (List.ofFn (pairInput p p)) (opnd C a b) = true :=
      Budget.orStep_up (n := n) (by simp) (Budget.orReaches_reach k _ hr).1 hkcentre
    exact (Bool.false_ne_true (hb.symm.trans hwire)).elim

noncomputable def centrelessFalseRoots (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (p : Fin n) : Finset ℕ :=
  (centreless G C).image (fun a => opnd C a (falseSide C p a))

lemma centrelessFalseRoots_card_le (p : Fin n) :
    (centrelessFalseRoots G C p).card ≤ (centreless G C).card := Finset.card_image_le

lemma centrelessFalseRoots_bound (hAO : IsAO2 n C) (p : Fin n) :
    centrelessFalseRoots G C p ⊆ Finset.range (n + C.size) := by
  intro w hw
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
  have hlen := (Budget.topData (Finset.mem_filter.mp ha).1).1
  have hb := Budget.opndBound hAO hlen (falseSide C p a)
  exact Finset.mem_range.mpr (by change _ < n + C.gates.length; omega)

noncomputable def centrelessServed (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (p : Fin n) (X : Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact X.filter fun l => ∃ a ∈ centreless G C, gateVal n C a (pairInput p l) = true

lemma false_or_centreless_roots_cover (hAO : IsAO2 n C) (hT : TopForm G C)
    (p : Fin n) (X : Finset (Fin n)) :
    falseServed G C p X ∪ centrelessServed G C p X ⊆
      (falseJunkRoots G C p ∪ centrelessFalseRoots G C p).biUnion
        (fun w => orIn n C w ∩ X) := by
  classical
  intro l hl
  by_cases hf : l ∈ falseServed G C p X
  · obtain ⟨hlX, hex⟩ := Finset.mem_filter.mp hf
    obtain ⟨w, hw, hraw⟩ := Finset.mem_biUnion.mp (falseJunkRoots_cover hAO hT p l hex)
    exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_union_left _ hw, Finset.mem_inter.mpr ⟨hraw, hlX⟩⟩
  · have hc : l ∈ centrelessServed G C p X := (Finset.mem_union.mp hl).resolve_left hf
    obtain ⟨hlX, a, ha, hpair⟩ := Finset.mem_filter.mp hc
    have hno : ∀ j ∈ junk G C, gateVal n C j (pairInput p p) = false →
        gateVal n C j (pairInput p l) = false := by
      intro j hj hjfalse
      by_contra hn
      exact hf (Finset.mem_filter.mpr ⟨hlX, j, hj, hjfalse, Bool.eq_true_of_not_eq_false hn⟩)
    have hraw := top_unserved_leaf_in_falseSide hAO hT p l
      (Finset.mem_filter.mp ha).1 hpair hno
    exact Finset.mem_biUnion.mpr ⟨_, Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨a, ha, rfl⟩), Finset.mem_inter.mpr ⟨hraw, hlX⟩⟩

lemma false_or_centreless_served_budget
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (p : Fin n) (X : Finset (Fin n)) (hX : ∀ x ∈ X, G.Adj p x)
    (hstar : ∀ w ∈ X, s(p,w) ∈ Ustar G C) :
    (falseServed G C p X ∪ centrelessServed G C p X).card ≤
      ((orN G C \ lam G C) \ mixing G C).card +
        ((junk G C).filter fun j => gateVal n C j (pairInput p p) = false).card +
          (centreless G C).card := by
  classical
  let R := falseJunkRoots G C p ∪ centrelessFalseRoots G C p
  have hR : R ⊆ Finset.range (n + C.size) :=
    Finset.union_subset (falseJunkRoots_bound hAO p) (centrelessFalseRoots_bound hAO p)
  have hcover := false_or_centreless_roots_cover hAO hT p X
  have hforest := raw_star_forest_budget G C hAO hfour p X hX hstar R hR
  have hroots := Finset.card_union_le (falseJunkRoots G C p) (centrelessFalseRoots G C p)
  have hf := falseJunkRoots_card_le (G := G) (C := C) p
  have hz := centrelessFalseRoots_card_le (G := G) (C := C) p
  have hc := Finset.card_le_card hcover
  dsimp only [R] at hforest
  omega

end CircuitLedger


namespace FirstMixing

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge CircuitLedger.Budget

lemma raw_nonempty_child
    {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {k : ℕ}
    (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or)
    (hn : (orIn n C (n + k)).Nonempty) :
    ∃ b : Fin 2, (orIn n C (opnd C k b)).Nonempty := by
  obtain ⟨v, hv⟩ := hn
  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach v hv) with he | ⟨w, hs, hr⟩
  · have := v.isLt
    omega
  · obtain ⟨j, hj, hkj, hjop, hin, hlt⟩ := hs
    have hje : j = k := by omega
    subst j
    obtain ⟨b, hb⟩ := inputsAsOpnd ao hk hin
    refine ⟨b, v, ?_⟩
    rw [← hb]
    exact reach_mem_orIn v hr

lemma first_mixing
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (ao : IsAO2 n C) {j : ℕ}
    (hj : j ∈ junk G C) :
    ∀ w, (orIn n C w).Nonempty →
      Relation.ReflTransGen (OrStep n C) w (n + j) →
      ∃ m ∈ mixing G C, (orIn n C (n + m)).Nonempty ∧
        Relation.ReflTransGen (OrStep n C) w (n + m) ∧
        Relation.ReflTransGen (OrStep n C) (n + m) (n + j) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hn path
    rcases Relation.ReflTransGen.cases_head path with he | ⟨v, hs, hr⟩
    · rw [he, andRawEmpty (junkData hj).2.1] at hn
      exact (Finset.not_nonempty_empty hn).elim
    · obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hs
      by_cases hv : (orIn n C v).Nonempty
      · obtain ⟨m, hm, hmn, hvm, hmj⟩ := ih v hlt hv hr
        exact ⟨m, hm, hmn, Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hvm, hmj⟩
      · have hve : orIn n C v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hv
        obtain ⟨b, hb⟩ := inputsAsOpnd ao hk hin
        obtain ⟨c, hc⟩ := raw_nonempty_child ao hk hop hn
        have hbe : orIn n C (opnd C k b) = ∅ := by rwa [hb] at hve
        have hbc : b ≠ c := by
          intro he
          subst c
          rw [hbe] at hc
          exact Finset.not_nonempty_empty hc
        have hbad : ¬ BelowF G C k := by
          intro hbelow
          obtain ⟨_, _, x, hjx, hFx⟩ := junkData hj
          have hkx : gateVal n C k x = true :=
            orStep_up (n := n) (by simp) path hjx
          exact Bool.noConfusion (hFx.symm.trans (hbelow x hkx))
        have hkN : k ∈ orN G C := by
          simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using
            And.intro hk (And.intro hop hbad)
        have hmix : k ∈ mixing G C := by
          apply Finset.mem_filter.mpr
          refine ⟨hkN, ?_⟩
          have hce := Finset.nonempty_iff_ne_empty.mp hc
          fin_cases b <;> fin_cases c <;> simp_all
        exact ⟨k, hmix, hn, Relation.ReflTransGen.refl, path⟩

lemma raw_pencil_leaf_unique
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (ao : IsAO2 n C) (hfour : NoFourCycle G)
    (p : Fin n)
    {m a a' : ℕ} {b b' : Fin 2} {l l' : Fin n}
    (hedge : s(p,l) ∈ Ustar G C)
    (hm : (orIn n C (n + m)).Nonempty)
    (ha : a ∈ tops G C) (ha' : a' ∈ tops G C)
    (hp : Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m))
    (hp' : Relation.ReflTransGen (OrStep n C) (opnd C a' b') (n + m))
    (hl : l ∈ side C a (1-b)) (hl' : l' ∈ side C a' (1-b'))
    (hpl : G.Adj p l) (hpl' : G.Adj p l') : l = l' := by
  obtain ⟨t, ht⟩ := hm
  have hta : t ∈ side C a b :=
    reach_mem_orIn t (hp.trans (mem_orIn_reach t ht))
  have hta' : t ∈ side C a' b' :=
    reach_mem_orIn t (hp'.trans (mem_orIn_reach t ht))
  have htl := SimpleGraph.deleteEdges_adj.mp (cleanAdj ao ha b hta hl)
  have htl' := SimpleGraph.deleteEdges_adj.mp (cleanAdj ao ha' b' hta' hl')
  have hpt : p ≠ t := by
    intro he
    subst t
    exact htl.2 hedge
  exact CircuitLedger.common_neighbors_unique_of_card_le_one G hfour
    p t hpt l l' hpl htl.1 hpl' htl'.1

end FirstMixing


namespace FirstMixing

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge CircuitLedger.Budget

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma true_leaf_mixing_of_no_centreless (hL : IsLeastAO G C) (hT : TopForm G C)
    {p l : Fin n} (he : s(p,l) ∈ Ustar G C)
    (hncentre : ∀ a ∈ centreless G C, gateVal n C a (pairInput p l) = false)
    (hnofalse : ∀ j ∈ junk G C, gateVal n C j (pairInput p p) = false →
      gateVal n C j (pairInput p l) = false) :
    ∃ m ∈ mixing G C, (orIn n C (n + m)).Nonempty ∧
      ∃ a ∈ tops G C, ∃ b : Fin 2,
        Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m) ∧
        l ∈ side C a (1 - b) := by
  obtain ⟨a, ha, b, j, hj, hv, hr, hjv⟩ := residualTrace hL hT he
  obtain ⟨hlen, hop, hbelow⟩ := topData ha
  have hjcentre : gateVal n C j (pairInput p p) = true := by
    by_contra h
    have hf := Bool.eq_false_of_not_eq_true h
    exact Bool.false_ne_true ((hnofalse j hj hf).symm.trans hjv)
  have hbcentre : val C (List.ofFn (pairInput p p)) (opnd C a b) = true :=
    orStep_up (n := n) (by simp) (orReaches_reach j _ hr).1 hjcentre
  have hotherfalse : val C (List.ofFn (pairInput p p)) (opnd C a (1 - b)) = false := by
    by_contra h
    have ht := Bool.eq_true_of_not_eq_false h
    have htop : gateVal n C a (pairInput p p) = true := by
      apply (andValOperands hL.1 hlen hop _).mpr
      intro c
      rcases opposite b c with rfl | rfl
      · exact hbcentre
      · exact ht
    exact G.irrefl ((graphFun_pair G p p).mp (hbelow _ htop))
  have hotherpair := (andValOperands hL.1 hlen hop _).mp hv (1 - b)
  have hl : l ∈ side C a (1 - b) := by
    rcases operandSupport hL.1 hT hlen hop hotherpair with
      ⟨t, ht, htp | htl⟩ | ⟨k, hk, hkr, hkv⟩
    · subst t
      have ht := sideVal ht (pairInput_left p p)
      exact (Bool.false_ne_true (hotherfalse.symm.trans ht)).elim
    · simpa only [htl] using ht
    · have hkcentre : gateVal n C k (pairInput p p) = true := by
        by_contra h
        have hf := Bool.eq_false_of_not_eq_true h
        exact Bool.false_ne_true ((hnofalse k hk hf).symm.trans hkv)
      have ht : val C (List.ofFn (pairInput p p)) (opnd C a (1 - b)) = true :=
        orStep_up (n := n) (by simp) (orReaches_reach k _ hkr).1 hkcentre
      exact (Bool.false_ne_true (hotherfalse.symm.trans ht)).elim
  have hrawb : (side (n := n) C a b).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hac : a ∈ centreless G C := by
      apply Finset.mem_filter.mpr
      refine ⟨ha, ?_⟩
      fin_cases b
      · exact Or.inl hempty
      · exact Or.inr hempty
    exact Bool.false_ne_true ((hncentre a hac).symm.trans hv)
  obtain ⟨m, hm, hraw, hpath, _⟩ :=
    first_mixing hL.1 hj (opnd C a b) hrawb (orReaches_reach j _ hr).1
  exact ⟨m, hm, hraw, a, ha, b, hpath, hl⟩

lemma true_leaf_mixing (hL : IsLeastAO G C) (hT : TopForm G C)
    (empty : centreless G C = ∅) {p l : Fin n} (he : s(p,l) ∈ Ustar G C)
    (hnofalse : ∀ j ∈ junk G C, gateVal n C j (pairInput p p) = false →
      gateVal n C j (pairInput p l) = false) :
    ∃ m ∈ mixing G C, (orIn n C (n + m)).Nonempty ∧
      ∃ a ∈ tops G C, ∃ b : Fin 2,
        Relation.ReflTransGen (OrStep n C) (opnd C a b) (n + m) ∧
        l ∈ side C a (1 - b) := by
  apply true_leaf_mixing_of_no_centreless hL hT he _ hnofalse
  intro a ha
  simpa [empty] using ha

end FirstMixing


namespace FirstMixing

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge CircuitLedger.Budget

def PencilAt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (m : ℕ) (l : Fin n) : Prop :=
  (orIn n C (n+m)).Nonempty ∧ ∃ a ∈ tops G C, ∃ b : Fin 2,
    Relation.ReflTransGen (OrStep n C) (opnd C a b) (n+m) ∧
      l ∈ side C a (1-b)

lemma pencil_count
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (hfour : NoFourCycle G)
    (p : Fin n) (L : Finset (Fin n))
    (hstar : ∀ l ∈ L, s(p,l) ∈ Ustar G C) (hL : ∀ l ∈ L, G.Adj p l)
    (hcover : ∀ l ∈ L, ∃ m ∈ mixing G C, PencilAt G C m l) :
    L.card ≤ (mixing G C).card := by
  classical
  let pick (l : Fin n) : ℕ := if h : l ∈ L then (hcover l h).choose else 0
  have hpick (l : Fin n) (hl : l ∈ L) :
      pick l ∈ mixing G C ∧ PencilAt G C (pick l) l := by
    simpa only [pick, dif_pos hl] using (hcover l hl).choose_spec
  apply Finset.card_le_card_of_injOn pick (fun l hl => (hpick l hl).1)
  intro l hl k hk he
  obtain ⟨hn, a, ha, b, hp, hside⟩ := (hpick l hl).2
  obtain ⟨_, a', ha', b', hp', hside'⟩ := (hpick k hk).2
  rw [← he] at hp'
  exact raw_pencil_leaf_unique ao hfour p (hstar l hl) hn ha ha' hp hp'
    hside hside' (hL l hl) (hL k hk)

lemma mixing_subset_extra
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    mixing G C ⊆ orN G C \ lam G C := by
  intro m hm
  obtain ⟨hm, hx⟩ := Finset.mem_filter.mp hm
  refine Finset.mem_sdiff.mpr ⟨hm, ?_⟩
  intro hl
  obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
  have h0' := Finset.nonempty_iff_ne_empty.mp h0
  have h1' := Finset.nonempty_iff_ne_empty.mp h1
  simp_all

end FirstMixing

namespace FirstMixing

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge CircuitLedger CircuitLedger.Budget

lemma unserved_mixing_count
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hz : centreless G C = ∅) (hfour : NoFourCycle G)
    (p : Fin n) (X : Finset (Fin n)) (hX : ∀ l ∈ X, G.Adj p l)
    (hstar : ∀ l ∈ X, s(p,l) ∈ Ustar G C) :
    (X \ falseServed G C p X).card ≤ (mixing G C).card := by
  classical
  apply pencil_count G C hL.1 hfour p _
    (fun l hl => hstar l (Finset.mem_sdiff.mp hl).1)
    (fun l hl => hX l (Finset.mem_sdiff.mp hl).1)
  intro l hl
  obtain ⟨hlX, hlf⟩ := Finset.mem_sdiff.mp hl
  apply true_leaf_mixing hL hT hz (hstar l hlX)
  intro j hj hjp
  apply Bool.eq_false_of_not_eq_true
  intro hjl
  exact hlf (Finset.mem_filter.mpr ⟨hlX, j, hj, hjp, hjl⟩)

lemma full_star_zero_centreless_penalty
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hz : centreless G C = ∅) (hfour : NoFourCycle G)
    (p : Fin n) (X : Finset (Fin n)) (hXne : X.Nonempty)
    (hX : ∀ l ∈ X, G.Adj p l)
    (hstar : ∀ l ∈ X, s(p,l) ∈ Ustar G C) :
    X.card + 1 ≤ (junk G C).card + (orN G C \ lam G C).card := by
  classical
  let J := (junk G C).filter fun j => gateVal n C j (pairInput p p) = false
  have hJsub : J ⊆ junk G C := Finset.filter_subset _ _
  have hfalse := false_served_budget G C hL.1 hT hfour p X hX hstar
  have hrest := unserved_mixing_count G C hL hT hz hfour p X hX hstar
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (show falseServed G C p X ⊆ X from Finset.filter_subset _ _)
  have hmixsplit := Finset.card_sdiff_add_card_eq_card (mixing_subset_extra G C)
  change (falseServed G C p X).card ≤
    ((orN G C \ lam G C) \ mixing G C).card + J.card at hfalse
  by_cases hJ : J = junk G C
  · have hall : falseServed G C p X = X := by
      apply Finset.Subset.antisymm (Finset.filter_subset _ _)
      intro l hl
      obtain ⟨a, ha, b, j, hj, _, _, hjl⟩ := residualTrace hL hT (hstar l hl)
      have hjp : gateVal n C j (pairInput p p) = false :=
        (Finset.mem_filter.mp (show j ∈ J by rw [hJ]; exact hj)).2
      exact Finset.mem_filter.mpr ⟨hl, j, hj, hjp, hjl⟩
    have hmix : 0 < (mixing G C).card := by
      obtain ⟨l, hl⟩ := hXne
      obtain ⟨a, ha, b, j, hj, _, hr, _⟩ := residualTrace hL hT (hstar l hl)
      obtain ⟨m, hm, _⟩ := first_mixing hL.1 hj _ (topSides hz ha b)
        (orReaches_reach j _ hr).1
      exact Finset.card_pos.mpr ⟨m, hm⟩
    rw [hall, hJ] at hfalse
    omega
  · have hlt : J.card < (junk G C).card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hJsub, hJ⟩)
    omega

end FirstMixing

namespace FirstMixing

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge CircuitLedger CircuitLedger.Budget

lemma other_served_mixing_count
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hfour : NoFourCycle G) (p : Fin n) (X : Finset (Fin n))
    (hX : ∀ l ∈ X, G.Adj p l)
    (hstar : ∀ l ∈ X, s(p,l) ∈ Ustar G C) :
    (X \ (falseServed G C p X ∪ centrelessServed G C p X)).card ≤
      (mixing G C).card := by
  classical
  apply pencil_count G C hL.1 hfour p _
    (fun l hl => hstar l (Finset.mem_sdiff.mp hl).1)
    (fun l hl => hX l (Finset.mem_sdiff.mp hl).1)
  intro l hl
  obtain ⟨hlX, hlf⟩ := Finset.mem_sdiff.mp hl
  apply true_leaf_mixing_of_no_centreless hL hT (hstar l hlX)
  · intro a ha
    apply Bool.eq_false_of_not_eq_true
    intro hav
    exact hlf (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hlX, a, ha, hav⟩))
  · intro j hj hjp
    apply Bool.eq_false_of_not_eq_true
    intro hjl
    exact hlf (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hlX, j, hj, hjp, hjl⟩))

lemma residual_pencil_penalty
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hfour : NoFourCycle G) (p : Fin n) (X : Finset (Fin n))
    (hXne : X.Nonempty) (hX : ∀ l ∈ X, G.Adj p l)
    (hstar : ∀ l ∈ X, s(p,l) ∈ Ustar G C) :
    X.card + 1 ≤ 2 * (centreless G C).card + (junk G C).card +
      (orN G C \ lam G C).card := by
  classical
  by_cases hz : centreless G C = ∅
  · have h := full_star_zero_centreless_penalty G C hL hT hz hfour p X hXne hX hstar
    simpa only [hz, Finset.card_empty, Nat.mul_zero, Nat.zero_add] using h
  · have hzpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hz)
    have hraw := false_or_centreless_served_budget G C hL.1 hT hfour p X hX hstar
    have hrest := other_served_mixing_count G C hL hT hfour p X hX hstar
    have hsubset : falseServed G C p X ∪ centrelessServed G C p X ⊆ X :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hsplit := Finset.card_sdiff_add_card_eq_card hsubset
    have hmixsplit := Finset.card_sdiff_add_card_eq_card (mixing_subset_extra G C)
    have hjle := Finset.card_le_card
      (Finset.filter_subset (fun j => gateVal n C j (pairInput p p) = false) (junk G C))
    omega

lemma full_star_penalty
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hfour : NoFourCycle G) (p : Fin n) (X : Finset (Fin n))
    (hXne : X.Nonempty) (hX : ∀ l ∈ X, G.Adj p l)
    (hstar : ∀ l, G.Adj p l → s(p,l) ∈ Ustar G C) :
    X.card + 1 ≤ 2 * (centreless G C).card + (junk G C).card +
      (orN G C \ lam G C).card :=
  residual_pencil_penalty G C hL hT hfour p X hXne hX (fun l hl => hstar l (hX l hl))

end FirstMixing



namespace FirstMixing
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

lemma full_star_ledger_lower_bound
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hfour : NoFourCycle G) (p : Fin n) (X : Finset (Fin n))
    (hXne : X.Nonempty) (hX : ∀ l ∈ X, G.Adj p l)
    (hstar : ∀ l, G.Adj p l → s(p,l) ∈ Ustar G C)
    (hresidual : (Ustar G C).card ≤ X.card)
    (N : ℕ) (hcentres : N ≤ (tops G C \ centreless G C).card + 1)
    (hledger : G.edgeFinset.card + (tops G C \ centreless G C).card +
      2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card ≤
        C.size + (Ustar G C).card + 1) :
    G.edgeFinset.card + N ≤ C.size + 1 := by
  have hP := full_star_penalty G C hL hT hfour p X hXne hX hstar
  omega

lemma full_star_equal_penalty_degree_gap
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hfour : NoFourCycle G) (p : Fin n) (X : Finset (Fin n))
    (hXne : X.Nonempty) (hX : ∀ l ∈ X, G.Adj p l)
    (hstar : ∀ l, G.Adj p l → s(p,l) ∈ Ustar G C)
    (q : ℕ) (hdegree : q + 1 ≤ X.card)
    (hbudget : 2 * (centreless G C).card + (junk G C).card +
      (orN G C \ lam G C).card ≤ (Ustar G C).card) :
    q + 2 ≤ (Ustar G C).card := by
  have hP := full_star_penalty G C hL hT hfour p X hXne hX hstar
  omega

end FirstMixing



namespace GlobalMixing

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge
open CircuitLedger CircuitLedger.Budget FirstMixing

lemma getD_snoc (W : List Bool) (v : Bool) (i : ℕ) :
    (W ++ [v]).getD i false = if i = W.length then v else W.getD i false := by
  rcases lt_trichotomy i W.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h
    simp [List.getD_eq_getElem?_getD]
  · rw [ite_eq_right (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma op_eval_mono {op : GateOp} (hop : op = .and ∨ op = .or) (l : List ℕ)
    (f f' : ℕ → Bool) (hff : ∀ a ∈ l, f a = true → f' a = true)
    (h : op.eval (l.map f) = true) : op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at h ⊢
    intro a ha
    exact hff a ha (h a ha)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at h ⊢
    obtain ⟨a, ha, hfa⟩ := h
    exact ⟨a, ha, hff a ha hfa⟩

lemma fold_mono (gs : List Gate) : ∀ W1 W2 : List Bool,
    W1.length = W2.length →
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) →
    (∀ i, W1.getD i false = true → W2.getD i false = true) →
    ∀ i, (gs.foldl stepWire W1).getD i false = true →
      (gs.foldl stepWire W2).getD i false = true := by
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (stepWire W1 g) (stepWire W2 g) (by simp [stepWire, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [stepWire, getD_snoc, hl]
    split_ifs
    · exact op_eval_mono (hop g List.mem_cons_self) _ _ _ (fun k _ => H k)
    · exact H i

lemma gateVal_mono {n : ℕ} {C : Circuit} (ao : IsAO2 n C)
    {x y : Fin n → Bool} (hxy : ∀ v, x v = true → y v = true)
    (j : ℕ) (h : gateVal n C j x = true) : gateVal n C j y = true := by
  apply fold_mono C.gates (List.ofFn x) (List.ofFn y) (by simp) ao.1 ?_ (n+j) h
  intro i hi
  by_cases hin : i < n
  · simpa [List.getD_eq_getElem?_getD, hin] using
      hxy ⟨i,hin⟩ (by simpa [List.getD_eq_getElem?_getD, hin] using hi)
  · have hge : (List.ofFn x).length ≤ i := by simpa using Nat.le_of_not_gt hin
    rw [getD_ge _ _ hge] at hi
    cases hi

lemma singleton_to_pair {n : ℕ} {C : Circuit} (ao : IsAO2 n C)
    (p l : Fin n) (m : ℕ) (hm : gateVal n C m (pairInput p p) = true) :
    gateVal n C m (pairInput p l) = true := by
  apply gateVal_mono ao _ m hm
  intro v hv
  have hp : v = p := by simpa only [pairInput_true, or_self] using hv
  subst v
  exact pairInput_left p l

lemma true_leaf_mixing_true
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hT : TopForm G C) {p l : Fin n}
    (he : s(p,l) ∈ Ustar G C)
    (hncentre : ∀ a ∈ centreless G C, gateVal n C a (pairInput p l) = false)
    (hnofalse : ∀ j ∈ junk G C, gateVal n C j (pairInput p p) = false →
      gateVal n C j (pairInput p l) = false) :
    ∃ m ∈ mixing G C, gateVal n C m (pairInput p p) = true ∧ PencilAt G C m l := by
  obtain ⟨a, ha, b, j, hj, hv, hr, hjv⟩ := residualTrace hL hT he
  obtain ⟨hlen, hop, hbelow⟩ := topData ha
  have hjcentre : gateVal n C j (pairInput p p) = true := by
    by_contra h
    exact Bool.false_ne_true ((hnofalse j hj (Bool.eq_false_of_not_eq_true h)).symm.trans hjv)
  have hbcentre : val C (List.ofFn (pairInput p p)) (opnd C a b) = true :=
    orStep_up (n := n) (by simp) (orReaches_reach j _ hr).1 hjcentre
  have htopfalse : gateVal n C a (pairInput p p) = false := by
    by_contra h
    exact G.irrefl ((graphFun_pair G p p).mp (hbelow _ (Bool.eq_true_of_not_eq_false h)))
  have hselectedfalse := falseSide_and_correct hL.1 p hlen hop htopfalse
  have hselectedraw := top_unserved_leaf_in_falseSide hL.1 hT p l ha hv hnofalse
  have hl : l ∈ side C a (1-b) := by
    rcases opposite b (falseSide C p a) with heq | heq
    · rw [heq] at hselectedfalse
      exact (Bool.false_ne_true (hselectedfalse.symm.trans hbcentre)).elim
    · simpa only [side, heq] using hselectedraw
  have hrawb : (side (n := n) C a b).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hac : a ∈ centreless G C := by
      apply Finset.mem_filter.mpr
      refine ⟨ha, ?_⟩
      fin_cases b
      · exact Or.inl hempty
      · exact Or.inr hempty
    exact Bool.false_ne_true ((hncentre a hac).symm.trans hv)
  obtain ⟨m, hm, hraw, hpath, hmj⟩ :=
    first_mixing hL.1 hj (opnd C a b) hrawb (orReaches_reach j _ hr).1
  have hmcentre : gateVal n C m (pairInput p p) = true :=
    orStep_up (n := n) (by simp) hmj hjcentre
  exact ⟨m, hm, hmcentre, hraw, a, ha, b, hpath, hl⟩

lemma global_opposite_leaf_unique
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) (hfour : NoFourCycle G) {p l l' : Fin n} {m : ℕ}
    (hedge : s(p,l) ∈ Ustar G C)
    (hmcentre : gateVal n C m (pairInput p p) = true)
    (hpencil : PencilAt G C m l) (hpencil' : PencilAt G C m l') : l' = l := by
  obtain ⟨hraw, a, ha, b, hp, hl⟩ := hpencil
  obtain ⟨_, a', ha', b', hp', hl'⟩ := hpencil'
  obtain ⟨u, hu⟩ := hraw
  have hua : u ∈ side C a b := reach_mem_orIn u (hp.trans (mem_orIn_reach u hu))
  have hua' : u ∈ side C a' b' := reach_mem_orIn u (hp'.trans (mem_orIn_reach u hu))
  have hul := SimpleGraph.deleteEdges_adj.mp (cleanAdj ao ha b hua hl)
  have hul' := SimpleGraph.deleteEdges_adj.mp (cleanAdj ao ha' b' hua' hl')
  have hpu : p ≠ u := by
    intro heq
    subst u
    exact hul.2 hedge
  have hpl : G.Adj p l := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hedge).1
  have hpl' : G.Adj p l' := (graphFun_pair G p l').mp
    (firingTop ao ha' hp' hl' (pairInput p l')
      (singleton_to_pair ao p l' m hmcentre) (pairInput_right p l'))
  exact (common_neighbors_unique_of_card_le_one G hfour p u hpu l l'
    hpl hul.1 hpl' hul'.1).symm

end GlobalMixing


namespace CertificateCover

lemma cover_of_unique_labels
    {V M : Type} [DecidableEq V] [DecidableEq M]
    (U : Finset (Sym2 V)) (labels : Finset M) (Cert : M → Sym2 V → V → Prop)
    (hcover : ∀ e ∈ U, ∃ m ∈ labels, ∃ v, v ∈ e ∧ Cert m e v)
    (hunique : ∀ m ∈ labels, ∀ e ∈ U, ∀ f ∈ U, ∀ v w,
      Cert m e v → Cert m f w → v = w) :
    ∃ S : Finset V, S.card ≤ labels.card ∧ ∀ e ∈ U, ∃ v ∈ S, v ∈ e := by
  classical
  let used := labels.filter fun m => ∃ e ∈ U, ∃ v, v ∈ e ∧ Cert m e v
  have hex : ∀ m : {m // m ∈ used}, ∃ v, ∃ e ∈ U, v ∈ e ∧ Cert m.val e v := by
    intro m
    obtain ⟨_, e, he, v, hv, hc⟩ := Finset.mem_filter.mp m.property
    exact ⟨v, e, he, hv, hc⟩
  choose leaf hleaf using hex
  let S := used.attach.image leaf
  refine ⟨S, ?_, ?_⟩
  · have hcard : S.card ≤ used.card := by
      exact Finset.card_image_le.trans_eq Finset.card_attach
    exact hcard.trans (Finset.card_le_card (Finset.filter_subset _ _))
  · intro e he
    obtain ⟨m, hm, v, hv, hc⟩ := hcover e he
    have hused : m ∈ used := Finset.mem_filter.mpr ⟨hm, e, he, v, hv, hc⟩
    let mm : {m // m ∈ used} := ⟨m, hused⟩
    obtain ⟨f, hf, hlf, hcert⟩ := hleaf mm
    have heq : leaf mm = v := hunique m hm f hf e he (leaf mm) v hcert hc
    refine ⟨leaf mm, Finset.mem_image.mpr ⟨mm, Finset.mem_attach _ _, rfl⟩, ?_⟩
    simpa only [heq] using hv

end CertificateCover


namespace GlobalMixing
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open FirstMixing

/-- Only selected residual edges satisfying the displayed orientation conditions are covered. -/
lemma selected_true_edges_cover
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (U : Finset (Sym2 (Fin n))) (hU : U ⊆ Ustar G C)
    (heligible : ∀ e ∈ U, ∃ p l : Fin n, e = s(p,l) ∧
      (∀ a ∈ centreless G C, gateVal n C a (pairInput p l) = false) ∧
      (∀ j ∈ junk G C, gateVal n C j (pairInput p p) = false →
        gateVal n C j (pairInput p l) = false)) :
    ∃ S : Finset (Fin n), S.card ≤ (mixing G C).card ∧
      ∀ e ∈ U, ∃ v ∈ S, v ∈ e := by
  classical
  let Cert : ℕ → Sym2 (Fin n) → Fin n → Prop := fun m e l =>
    ∃ p : Fin n, e = s(p,l) ∧ gateVal n C m (pairInput p p) = true ∧ PencilAt G C m l
  apply CertificateCover.cover_of_unique_labels U (mixing G C) Cert
  · intro e he
    obtain ⟨p, l, heq, hncentre, hnofalse⟩ := heligible e he
    have hres : s(p,l) ∈ Ustar G C := by rw [← heq]; exact hU he
    obtain ⟨m, hm, hmtrue, hpencil⟩ := true_leaf_mixing_true hL hT hres hncentre hnofalse
    refine ⟨m, hm, l, ?_, p, heq, hmtrue, hpencil⟩
    rw [heq]
    exact Sym2.mem_iff.mpr (Or.inr rfl)
  · intro m hm e he f hf l l' hecert hfcert
    obtain ⟨p, heq, hmtrue, hpencil⟩ := hecert
    obtain ⟨p', hfeq, _, hpencil'⟩ := hfcert
    have hres : s(p,l) ∈ Ustar G C := by rw [← heq]; exact hU he
    exact (global_opposite_leaf_unique hL.1 hfour hres hmtrue hpencil hpencil').symm

/-- Residual edges admitting an orientation with no accepting centreless top and no
  accepting dirty gate that is false on the singleton centre. Other residual edges are excluded. -/
noncomputable def trueEligibleEdges
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    Finset (Sym2 (Fin n)) := by
  classical
  exact (Ustar G C).filter fun e => ∃ p l : Fin n, e = s(p,l) ∧
    (∀ a ∈ centreless G C, gateVal n C a (pairInput p l) = false) ∧
    (∀ j ∈ junk G C, gateVal n C j (pairInput p p) = false →
      gateVal n C j (pairInput p l) = false)

lemma true_eligible_edges_cover
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G) :
    ∃ S : Finset (Fin n), S.card ≤ (mixing G C).card ∧
      ∀ e ∈ trueEligibleEdges G C, ∃ v ∈ S, v ∈ e := by
  apply selected_true_edges_cover G C hL hT hfour (trueEligibleEdges G C)
    (Finset.filter_subset _ _)
  intro e he
  exact (Finset.mem_filter.mp he).2

end GlobalMixing

end PEqualNP.Outside.L_meta_2583
