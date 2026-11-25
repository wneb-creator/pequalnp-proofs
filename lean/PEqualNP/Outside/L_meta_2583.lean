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

lemma false_source_raw_leaf (hAO : IsAO2 n C) (hT : TopForm G C)
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
  refine ⟨j, hj, hf, false_source_raw_leaf hAO hT p l hj hf hon ?_⟩
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


namespace GlobalMixing
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open FirstMixing

lemma opposite_raw_support_subset_singleton
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) (hfour : NoFourCycle G) {p l : Fin n} {m a : ℕ} {b : Fin 2}
    (hedge : s(p,l) ∈ Ustar G C)
    (hmcentre : gateVal n C m (pairInput p p) = true)
    (hpencil : PencilAt G C m l) (ha : a ∈ tops G C)
    (hpath : Relation.ReflTransGen (CircuitLedger.Budget.OrStep n C)
      (opnd C a b) (n + m)) :
    side C a (1-b) ⊆ {l} := by
  intro l' hl'
  apply Finset.mem_singleton.mpr
  exact global_opposite_leaf_unique ao hfour hedge hmcentre hpencil
    ⟨hpencil.1, a, ha, b, hpath, hl'⟩

end GlobalMixing

namespace GlobalMixing
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open FirstMixing

lemma selected_mixing_certificates_cover
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (hfour : NoFourCycle G)
    (U : Finset (Sym2 (Fin n))) (hU : U ⊆ Ustar G C)
    (hcert : ∀ e ∈ U, ∃ m ∈ mixing G C, ∃ p l : Fin n,
      e = s(p,l) ∧ gateVal n C m (pairInput p p) = true ∧ PencilAt G C m l) :
    ∃ S : Finset (Fin n), S.card ≤ (mixing G C).card ∧
      ∀ e ∈ U, ∃ v ∈ S, v ∈ e := by
  classical
  let Cert : ℕ → Sym2 (Fin n) → Fin n → Prop := fun m e l =>
    ∃ p : Fin n, e = s(p,l) ∧ gateVal n C m (pairInput p p) = true ∧ PencilAt G C m l
  apply CertificateCover.cover_of_unique_labels U (mixing G C) Cert
  · intro e he
    obtain ⟨m, hm, p, l, heq, hmtrue, hpencil⟩ := hcert e he
    refine ⟨m, hm, l, ?_, p, heq, hmtrue, hpencil⟩
    rw [heq]
    exact Sym2.mem_iff.mpr (Or.inr rfl)
  · intro m hm e he f hf l l' hecert hfcert
    obtain ⟨p, heq, hmtrue, hpencil⟩ := hecert
    obtain ⟨p', hfeq, _, hpencil'⟩ := hfcert
    have hres : s(p,l) ∈ Ustar G C := by rw [← heq]; exact hU he
    exact (global_opposite_leaf_unique hAO hfour hres hmtrue hpencil hpencil').symm

end GlobalMixing


namespace Relative603
open Finset
variable {V : Type*} [DecidableEq V]

def edgeAt (G : SimpleGraph V) (X : Finset V) : Prop :=
  ∃ u ∈ X, ∃ v ∈ X, G.Adj u v

def bit (A B X : Finset V) : Prop := A ⊆ X ∨ B ⊆ X

def factors (F : Finset V → Prop) (S A B : Finset V) : Prop :=
  ∀ X ⊆ S, ∀ Y ⊆ S, (bit A B X ↔ bit A B Y) →
    ∀ T : Finset V, Disjoint T S → (F (X ∪ T) ↔ F (Y ∪ T))

lemma edgeAt_pair (G : SimpleGraph V) (u v : V) : edgeAt G {u,v} ↔ G.Adj u v := by
  simp only [edgeAt, mem_insert, mem_singleton]
  constructor
  · rintro ⟨a,rfl|rfl,b,rfl|rfl,h⟩
    · exact (G.irrefl h).elim
    · exact h
    · exact h.symm
    · exact (G.irrefl h).elim
  · intro h
    exact ⟨u,Or.inl rfl,v,Or.inr rfl,h⟩

lemma pair_minimal {G : SimpleGraph V} {Y : Finset V} {p q : V}
    (hY : edgeAt G Y) (hs : Y ⊆ {p,q}) : Y = {p,q} := by
  obtain ⟨a,ha,b,hb,hab⟩ := hY
  have ha' := hs ha
  have hb' := hs hb
  simp only [mem_insert,mem_singleton] at ha' hb'
  apply subset_antisymm hs
  intro i hi
  simp only [mem_insert,mem_singleton] at hi
  have hne := hab.ne
  grind

/-- The module obstruction only needs pair completeness for H and safety for a no-four G.
  The Boolean predicate may accept additional ambient edges and higher prime implicants. -/
lemma no_relative_module
    (H G : SimpleGraph V) (F : Finset V → Prop) (S A B : Finset V)
    (safe : ∀ X, F X → edgeAt G X)
    (complete : ∀ p q, H.Adj p q → F {p,q})
    (hAS : A ⊆ S) (hBS : B ⊆ S) (hA : A.Nonempty) (hB : B.Nonempty)
    (two : ∃ p ∈ S, ∃ q ∈ S, p ≠ q)
    (degree : ∀ p ∈ S, ∃ q r, q ≠ r ∧ H.Adj p q ∧ H.Adj p r)
    (noFour : ∀ p q, p ≠ q → ∀ a b,
      G.Adj p a → G.Adj q a → G.Adj p b → G.Adj q b → a = b) :
    ¬ factors F S A B := by
  classical
  intro fac
  have emptyFalse : ¬ F ∅ := fun h => by simpa [edgeAt] using safe ∅ h
  have singletonFalse (p : V) : ¬ F {p} := fun h => by simpa [edgeAt] using safe {p} h
  have emptyBit : ¬ bit A B ∅ := by simpa [bit, hA.ne_empty, hB.ne_empty]
  have fullBit : bit A B S := Or.inl hAS
  have hg {p q : V} (h : H.Adj p q) : G.Adj p q :=
    (edgeAt_pair G p q).mp (safe _ (complete p q h))
  obtain ⟨p, hp, q, hq, hpq⟩ := two
  by_cases inside : F S
  · have encode : ∀ X ⊆ S, F X ↔ bit A B X := by
      intro X hX
      constructor
      · intro hx
        by_contra hb
        have hh := fac X hX ∅ (empty_subset _) (iff_of_false hb emptyBit) ∅ (by simp)
        exact emptyFalse (by simpa using hh.mp (by simpa using hx))
      · intro hb
        have hh := fac X hX S (subset_refl _) (iff_of_true hb fullBit) ∅ (by simp)
        simpa using hh.mpr (by simpa using inside)
    have closed : ∀ p ∈ S, ∀ q, H.Adj p q → q ∈ S := by
      intro p hp q hpq
      by_contra hq
      have singleBit : ¬ bit A B {p} := by
        rw [← encode {p} (singleton_subset_iff.mpr hp)]
        exact singletonFalse p
      have hh := fac {p} (singleton_subset_iff.mpr hp) ∅ (empty_subset _)
        (iff_of_false singleBit emptyBit) {q} (by simpa using hq)
      exact singletonFalse q (by simpa using hh.mp (by simpa using complete p q hpq))
    have atmost : ∀ p ∈ S, ∀ q ∈ S, H.Adj p q → ({p,q} : Finset V) = A ∨ {p,q} = B := by
      intro p hp q hq hpq
      have hpair : ({p,q} : Finset V) ⊆ S := by
        intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl <;> assumption
      rcases (encode _ hpair).mp (complete p q hpq) with h | h
      · exact Or.inl (pair_minimal (safe _ ((encode A hAS).mpr (Or.inl (subset_refl _)))) h).symm
      · exact Or.inr (pair_minimal (safe _ ((encode B hBS).mpr (Or.inr (subset_refl _)))) h).symm
    obtain ⟨a,b,hab,hpa,hpb⟩ := degree p hp
    have ha := closed p hp a hpa
    have hb := closed p hp b hpb
    obtain ⟨c,d,hcd,hac,had⟩ := degree a ha
    obtain ⟨z,hzp,haz⟩ : ∃ z, z ≠ p ∧ H.Adj a z := by
      by_cases hc : c = p
      · exact ⟨d,fun he => hcd (hc.trans he.symm),had⟩
      · exact ⟨c,hc,hac⟩
    have hz := closed a ha z haz
    have h1 := atmost p hp a ha hpa
    have h2 := atmost p hp b hb hpb
    have h3 := atmost a ha z hz haz
    have hpna := hpa.ne
    have hpnb := hpb.ne
    have hanz := haz.ne
    have diff12 : ({p,a}:Finset V) ≠ {p,b} := by
      intro heq
      have : a ∈ ({p,b}:Finset V) := heq ▸ (by simp : a ∈ ({p,a}:Finset V))
      simpa [Ne.symm hpna,hab] using this
    have diff13 (x : V) : ({p,x}:Finset V) ≠ {a,z} := by
      intro heq
      have : p ∈ ({a,z}:Finset V) := heq ▸ (by simp : p ∈ ({p,x}:Finset V))
      simpa [hpna,Ne.symm hzp] using this
    rcases h1 with h1|h1 <;> rcases h2 with h2|h2 <;> rcases h3 with h3|h3 <;> grind
  · have noInside : ∀ X ⊆ S, ¬ F X := by
      intro X hX hx
      by_cases hb : bit A B X
      · have hh := fac X hX S (subset_refl _) (iff_of_true hb fullBit) ∅ (by simp)
        exact inside (by simpa using hh.mp (by simpa using hx))
      · have hh := fac X hX ∅ (empty_subset _) (iff_of_false hb emptyBit) ∅ (by simp)
        exact emptyFalse (by simpa using hh.mp (by simpa using hx))
    have outside : ∀ p ∈ S, ∀ a, H.Adj p a → a ∉ S := by
      intro p hp a hpa ha
      exact noInside {p,a} (by
        intro w hw
        simp only [mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl <;> assumption) (complete p a hpa)
    have singleBit : ∀ p ∈ S, bit A B {p} := by
      intro p hp
      obtain ⟨a,b,hab,hpa,hpb⟩ := degree p hp
      by_contra hn
      have ha := outside p hp a hpa
      have hh := fac {p} (singleton_subset_iff.mpr hp) ∅ (empty_subset _)
        (iff_of_false hn emptyBit) {a} (by simpa using ha)
      exact singletonFalse a (by simpa using hh.mp (by simpa using complete p a hpa))
    obtain ⟨a,b,hab,hpa,hpb⟩ := degree p hp
    have transfer : ∀ t, H.Adj p t → G.Adj q t := by
      intro t hpt
      have ht := outside p hp t hpt
      have hh := fac {p} (singleton_subset_iff.mpr hp) {q} (singleton_subset_iff.mpr hq)
        (iff_of_true (singleBit p hp) (singleBit q hq)) {t} (by simpa using ht)
      apply (edgeAt_pair G q t).mp
      exact safe _ (by simpa using hh.mp (by simpa using complete p t hpt))
    exact hab (noFour p q hpq a b (hg hpa) (transfer a hpa) (hg hpb) (transfer b hpb))

end Relative603


namespace RelativeOrBound

namespace GraphInduction603
open SimpleGraph
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def sparse (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, {e : Sym2 V | e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S}.ncard ≤ S.card

def noFour (G : SimpleGraph V) : Prop :=
  ∀ v (c : G.Walk v v), c.IsCycle → c.length ≠ 4

omit [DecidableEq V] in
lemma sparse_subgraph {H G : SimpleGraph V} (h : H ≤ G) (hG : sparse G) : sparse H := by
  intro S
  apply le_trans _ (hG S)
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro e he
  exact ⟨SimpleGraph.edgeSet_mono h he.1, he.2⟩

omit [Fintype V] [DecidableEq V] in
lemma noFour_subgraph {H G : SimpleGraph V} (h : H ≤ G) (hG : noFour G) : noFour H := by
  intro v c hc
  simpa only [Walk.length_mapLe] using hG v (c.mapLe h) (hc.mapLe h)

omit [DecidableEq V] in
lemma count_eq (G : SimpleGraph V) : G.edgeSet.ncard = G.edgeFinset.card := by
  exact Set.ncard_eq_toFinset_card' _

omit [DecidableEq V] in
lemma support_count (G : SimpleGraph V) (hs : sparse G) :
    G.edgeFinset.card ≤ G.support.toFinset.card := by
  rw [← count_eq]
  let S := G.support.toFinset
  apply le_trans _ (hs S)
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  intro e he
  refine ⟨he, ?_⟩
  induction e using Sym2.inductionOn with
  | _ a b =>
    have hab : G.Adj a b := he
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact Set.mem_toFinset.mpr hab.mem_support_left
    · exact Set.mem_toFinset.mpr hab.mem_support_right

omit [DecidableEq V] in

lemma regular_of_no_leaf (G : SimpleGraph V) (hs : sparse G)
    (hl : ∀ v, G.degree v ≠ 1) (v : V) (hv : v ∈ G.support) : G.degree v = 2 := by
  classical
  have hmin : ∀ i ∈ G.support.toFinset, 2 ≤ G.degree i := by
    intro i hi
    have hi' := (G.degree_pos_iff_mem_support i).mpr (Set.mem_toFinset.mp hi)
    have := hl i
    omega
  by_contra hn
  have hv' := Set.mem_toFinset.mpr hv
  have hd := hmin v hv'
  have hsum := Finset.sum_lt_sum hmin (⟨v,hv',by omega⟩ :
    ∃ i ∈ G.support.toFinset, 2 < G.degree i)
  have hmax := support_count G hs
  have hhand := G.sum_degrees_support_eq_twice_card_edges
  simp only [Finset.sum_const, smul_eq_mul] at hsum
  omega

lemma count_after_delete (G : SimpleGraph V) (v : V) :
    (G.deleteIncidenceSet v).edgeSet.ncard + G.degree v = G.edgeSet.ncard := by
  have h := G.card_edgeFinset_deleteIncidenceSet v
  have hle := G.degree_le_card_edgeFinset v
  simpa only [SimpleGraph.edgeFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] using (h ▸ Nat.sub_add_cancel hle :
      (G.deleteIncidenceSet v).edgeFinset.card + G.degree v = G.edgeFinset.card)


lemma of_paid_deletions (cost : SimpleGraph V → ℕ)
    (leaf : ∀ G : SimpleGraph V, sparse G → noFour G → cost G + 1 < G.edgeSet.ncard →
      ∀ v, G.degree v = 1 → cost (G.deleteIncidenceSet v) + 1 ≤ cost G)
    (core : ∀ G : SimpleGraph V, sparse G → noFour G → cost G + 1 < G.edgeSet.ncard →
      (∀ v ∈ G.support, G.degree v = 2) →
      ∃ v ∈ G.support, cost (G.deleteIncidenceSet v) + 2 ≤ cost G)
    (G : SimpleGraph V) (hs : sparse G) (hf : noFour G) :
    G.edgeSet.ncard ≤ cost G + 1 := by
  induction h : G.edgeSet.ncard using Nat.strong_induction_on generalizing G with
  | ind k ih =>
    by_cases hb : G.edgeSet.ncard ≤ cost G + 1
    · omega
    have hg : cost G + 1 < G.edgeSet.ncard := by omega
    have paid : ∃ v, 0 < G.degree v ∧
        cost (G.deleteIncidenceSet v) + G.degree v ≤ cost G := by
      by_cases hleaf : ∃ v, G.degree v = 1
      · obtain ⟨v,hv⟩ := hleaf
        exact ⟨v,by omega, by simpa only [hv] using leaf G hs hf hg v hv⟩
      · have hreg := regular_of_no_leaf G hs (fun v e => hleaf ⟨v,e⟩)
        obtain ⟨v,hv,hp⟩ := core G hs hf hg hreg
        have hd := hreg v hv
        exact ⟨v,by omega,by omega⟩
    obtain ⟨v,hpos,hpay⟩ := paid
    have hc := count_after_delete G v
    have hlt : (G.deleteIncidenceSet v).edgeSet.ncard < k := by omega
    have H := G.deleteIncidenceSet_le v
    have hrec := ih _ hlt _ (sparse_subgraph H hs) (noFour_subgraph H hf) rfl
    omega

end GraphInduction603

namespace Leaf603
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def readGate (g : Gate) (w : ℕ → Bool) : Bool := g.op.eval (g.inputs.map w)
private def run (gs : List Gate) (input : List Bool) : List Bool :=
  gs.foldl (fun wires g => wires ++ [readGate g (fun j => wires.getD j false)]) input

private lemma run_append (gs : List Gate) (g : Gate) (s : List Bool) :
    run (gs ++ [g]) s = run gs s ++ [readGate g (fun j => (run gs s).getD j false)] := by
  simp [run,List.foldl_append]

private lemma run_len (gs : List Gate) (s : List Bool) : (run gs s).length=s.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => simp [run_append,ih,Nat.add_assoc]

private def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run gs (List.ofFn x)).getD w false

private lemma new_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    val (gs++[g]) x (n+gs.length) = readGate g (val gs x) := by
  have hl : (run gs (List.ofFn x)).length=n+gs.length := by simp [run_len]
  unfold val
  rw [run_append,←hl]
  simp

private lemma other_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) {w : ℕ}
    (h : w ≠ n+gs.length) : val (gs++[g]) x w = val gs x w := by
  have hl : (run gs (List.ofFn x)).length=n+gs.length := by simp [run_len]
  unfold val
  rw [run_append]
  by_cases hw : w < (run gs (List.ofFn x)).length
  · exact List.getD_append _ _ _ _ hw
  · rw [List.getD_eq_default _ _ (by simp [hl]; omega),List.getD_eq_default _ _ (by omega)]

private def release {n : ℕ} (gs : List Gate) (v : Fin n) : Prop :=
  ∃ (j : ℕ) (g : Gate) (i : ℕ), gs[j]?=some g ∧ g.op=.or ∧ i∈g.inputs ∧ i<n+j ∧
    ∀ z : Fin n → Bool, z v=false → val gs z i=false

private lemma release_prefix {n : ℕ} {gs : List Gate} {v : Fin n} (g : Gate)
    (h : release gs v) : release (gs++[g]) v := by
  obtain ⟨j,q,i,hj,hop,hi,hlt,hz⟩ := h
  have hjl := (List.getElem?_eq_some_iff.mp hj).1
  refine ⟨j,q,i,(List.getElem?_append_left hjl).trans hj,hop,hi,hlt,?_⟩
  intro z hv
  exact (other_val gs g z (by omega)).trans (hz z hv)

private lemma sensitive_or_dominated {n : ℕ} (v : Fin n) (x : Fin n → Bool) (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op=.and ∨ g.op=.or) (no : ¬release gs v) (w : ℕ)
    (hd : val gs x w ≠ val gs (Function.update x v true) w) :
    ∀ z : Fin n → Bool, z v=false → val gs z w=false := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    intro z hz
    change (List.ofFn x).getD w false ≠ (List.ofFn (Function.update x v true)).getD w false at hd
    change (List.ofFn z).getD w false = false
    by_cases hw : w<n
    · rw [List.getD_eq_getElem _ _ (by simpa using hw),List.getD_eq_getElem _ _ (by simpa using hw)] at hd
      rw [List.getD_eq_getElem _ _ (by simpa using hw)]
      simp only [List.getElem_ofFn] at hd ⊢
      by_cases hv : (⟨w,hw⟩ : Fin n)=v
      · exact hv ▸ hz
      · exact (hd (Function.update_of_ne hv true x).symm).elim
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hw)]
  | append_singleton gs g ih =>
    have hm' : ∀ q ∈ gs, q.op=.and ∨ q.op=.or := fun q h => hm q (List.mem_append_left _ h)
    have no' : ¬ release gs v := fun h => no (release_prefix g h)
    by_cases hw : w=n+gs.length
    · subst w
      rw [new_val,new_val] at hd
      obtain ⟨a,ha,hdif⟩ : ∃ a ∈ g.inputs, val gs x a ≠ val gs (Function.update x v true) a := by
        by_contra! h
        exact hd (congrArg g.op.eval (List.map_congr_left h))
      have bound : a<n+gs.length := by
        by_contra! h
        exact hdif (by
          unfold val
          rw [List.getD_eq_default _ _ (by simpa [run_len] using h),
            List.getD_eq_default _ _ (by simpa [run_len] using h)])
      have hf := ih hm' no' a hdif
      rcases hm g (by simp) with hop | hop
      · intro z hz
        rw [new_val]
        have he := hf z hz
        change (g.op.eval _) = false
        rw [hop]
        apply List.all_eq_false.mpr
        exact ⟨_,List.mem_map.mpr ⟨a,ha,rfl⟩,by simp [he]⟩
      · exact (no ⟨gs.length,g,a,by simp,hop,ha,bound,fun z hz =>
          (other_val _ _ _ (Nat.ne_of_lt bound)).trans (hf z hz)⟩).elim
    · rw [other_val _ _ _ hw,other_val _ _ _ hw] at hd
      intro z hz
      exact (other_val _ _ _ hw).trans (ih hm' no' w hd z hz)


lemma release_exists {n : ℕ} (C : Circuit) (v : Fin n) (hm : Monotone2 C)
    (on : ∃ x : Fin n → Bool, x v=false ∧ C.eval (List.ofFn x)=false ∧
      C.eval (List.ofFn (Function.update x v true))=true)
    (other : ∃ z : Fin n → Bool, z v=false ∧ C.eval (List.ofFn z)=true) :
    ∃ (j : ℕ) (g : Gate) (i : ℕ), C.gates[j]?=some g ∧ g.op=.or ∧ i∈g.inputs ∧ i<n+j ∧
      ∀ z : Fin n → Bool, z v=false → (C.wires (List.ofFn z)).getD i false=false := by
  change release C.gates v
  by_contra h
  obtain ⟨x,_,hx,hy⟩ := on
  obtain ⟨z,hz,ho⟩ := other
  have hd : val C.gates x C.output ≠ val C.gates (Function.update x v true) C.output := by
    change C.eval (List.ofFn x) ≠ _
    exact fun eq => Bool.false_ne_true (hx.symm.trans (eq.trans hy))
  have hf := sensitive_or_dominated v x C.gates (fun g hg => (hm g hg).1) h C.output hd z hz
  exact Bool.false_ne_true (hf.symm.trans ho)

private lemma val_prefix {n : ℕ} (a b : List Gate) (x : Fin n → Bool) (w : ℕ) (hw : w<n+a.length) :
    val (a++b) x w=val a x w := by
  induction b using List.reverseRecOn with
  | nil => simp
  | append_singleton b g ih =>
    rw [←List.append_assoc,other_val _ _ _ (by simp; omega),ih]

private def pick (dead i : ℕ) : List ℕ → ℕ
  | a::b::_ => if a=i then b else a
  | _ => dead

private def copyOf (dead i : ℕ) (g : Gate) : Gate := ⟨.and,[pick dead i g.inputs]⟩

private lemma copy_value (dead i : ℕ) (g : Gate) (w : ℕ → Bool)
    (hz : w dead=false) (hi : w i=false) (hop : g.op=.or) (hin : i∈g.inputs)
    (hl : g.inputs.length≤2) : readGate (copyOf dead i g) w = readGate g w := by
  obtain ⟨op,l⟩ := g
  change op=.or at hop
  subst op
  change i∈l at hin
  change l.length≤2 at hl
  rcases l with _|⟨a,_|⟨b,_|⟨c,t⟩⟩⟩
  · simp at hin
  · have e : i=a := by simpa using hin
    subst a
    simp [readGate,copyOf,pick,GateOp.eval,hz,hi]
  · have e : i=a ∨ i=b := by simpa using hin
    rcases e with rfl|rfl
    · simp [readGate,copyOf,pick,GateOp.eval,hi]
    · by_cases eq : a=i <;> simp [readGate,copyOf,pick,GateOp.eval,hi,eq]
  · simp at hl

private lemma patch_val {n : ℕ} (C : Circuit) (f : ℕ → Gate → Gate) (z : Fin n → Bool)
    (same : ∀ (a : List Gate) (g : Gate), (∃ b, C.gates=(a++[g])++b) →
      readGate (f a.length g) (val a z)=readGate g (val a z))
    (gs : List Gate) (pre : ∃ b, C.gates=gs++b) (w : ℕ) :
    val (gs.mapIdx f) z w=val gs z w := by
  induction gs using List.reverseRecOn generalizing w with
  | nil => rfl
  | append_singleton gs g ih =>
    have pre' : ∃ b, C.gates=gs++b := by
      obtain ⟨b,hb⟩ := pre
      exact ⟨[g]++b,hb.trans (List.append_assoc _ _ _)⟩
    rw [List.mapIdx_concat]
    by_cases hw : w=n+gs.length
    · subst w
      have e : n+gs.length=n+(gs.mapIdx f).length := by simp
      rw [e,new_val,←e,new_val,show val (gs.mapIdx f) z=val gs z from funext (ih pre')]
      exact same gs g pre
    · rw [other_val _ _ _ (by simpa using hw),other_val _ _ _ hw]
      exact ih pre' w

private def pin (v dead w : ℕ) := if w=v then dead else w
private def reroute (v dead : ℕ) (g : Gate) : Gate := ⟨g.op,g.inputs.map (pin v dead)⟩

private lemma pin_eval {n : ℕ} (v : Fin n) (dead : ℕ) (x : Fin n → Bool)
    (gs : List Gate) (hd : n+gs.length≤dead) (w : ℕ) :
    val (gs.map (reroute v dead)) x (pin v dead w) = val gs (Function.update x v false) w := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    by_cases hw : w=v.val
    · subst w
      simp only [pin,ite_true,List.map_nil,val,run,List.foldl_nil]
      rw [List.getD_eq_default _ _ (by simpa using hd),List.getD_eq_getElem _ _ (by simp)]
      simp
    · rw [show pin v dead w=w by simp [pin,hw]]
      simp only [List.map_nil,val,run,List.foldl_nil]
      by_cases h : w<n
      · rw [List.getD_eq_getElem _ _ (by simpa using h),List.getD_eq_getElem _ _ (by simpa using h)]
        simp only [List.getElem_ofFn]
        exact (Function.update_of_ne (show (⟨w,h⟩ : Fin n) ≠ v from fun e => hw (congrArg Fin.val e)) false x).symm
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt h)]
  | append_singleton gs g ih =>
    have hlen : n+gs.length<dead := by simp at hd; omega
    have hv := v.isLt
    simp only [List.map_append,List.map_cons,List.map_nil]
    by_cases hw : w=n+gs.length
    · subst w
      rw [show pin v dead (n+gs.length)=n+(gs.map (reroute v dead)).length by simp [pin,show n+gs.length≠v.val by omega],
        new_val,new_val]
      unfold readGate
      simp only [reroute,List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact ih hlen.le j
    · have hne : pin v dead w ≠ n+(gs.map (reroute v dead)).length := by
        simp only [pin,List.length_map]
        split <;> omega
      rw [other_val _ _ _ hne,other_val _ _ _ hw]
      exact ih hlen.le w


def Charged {n : ℕ} (C : Circuit) (v : Fin n) (j : ℕ) : Prop :=
  ∃ (i : ℕ) (g : Gate), C.gates[j]?=some g ∧ g.op=.or ∧ i∈g.inputs ∧ i<n+j ∧
    ∀ z : Fin n → Bool, z v=false → (C.wires (List.ofFn z)).getD i false=false


lemma restrict_many {n : ℕ} (C : Circuit) (v : Fin n) (A S : Finset ℕ) (hm : Monotone2 C)
    (cover : ∀ j g, C.gates[j]?=some g → g.op=.or → j∈A) (charges : ∀ j∈S, Charged C v j) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.gates.length=C.gates.length ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x)=C.eval (List.ofFn (Function.update x v false))) ∧
      ∀ j g, C'.gates[j]?=some g → g.op=.or → j∈A\S := by
  classical
  let dead := n+C.gates.length
  let operand (j : ℕ) : ℕ := if hj : j∈S then (charges j hj).choose else 0
  let change (j : ℕ) (g : Gate) := if j∈S then copyOf dead (operand j) g else g
  let gs := C.gates.mapIdx change
  let C' : Circuit := ⟨gs.map (reroute v dead),pin v dead C.output⟩
  have atGate (j : ℕ) (g : Gate) (h : C'.gates[j]?=some g) :
      ∃ q, C.gates[j]?=some q ∧ g=reroute v dead (change j q) := by
    change (gs.map (reroute v dead))[j]?=some g at h
    simp only [gs,List.getElem?_map,List.getElem?_mapIdx] at h
    cases eq : C.gates[j]? with
    | none => simp [eq] at h
    | some q => exact ⟨q,rfl,by simpa [eq] using h.symm⟩
  refine ⟨C',?_,by simp [C',gs],?_,?_⟩
  · intro g hg
    obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
    obtain ⟨q,hq,rfl⟩ := atGate j g hj
    have good := hm q (List.mem_of_getElem? hq)
    by_cases h : j∈S
    · simp [change,h,copyOf,reroute]
    · simpa [change,h,reroute] using good
  · intro x
    let z := Function.update x v false
    have hz : z v=false := by simp [z]
    have hstep (a : List Gate) (g : Gate) (pre : ∃ b, C.gates=(a++[g])++b) :
        readGate (change a.length g) (val a z) = readGate g (val a z) := by
      by_cases h : a.length∈S
      · obtain ⟨b,hb⟩ := pre
        have hh := (charges a.length h).choose_spec
        change ∃ (q : Gate), C.gates[a.length]?=some q ∧ q.op=.or ∧ _ at hh
        obtain ⟨q,hq,hop,hin,hi,hzero⟩ := hh
        have hhg : C.gates[a.length]?=some g := by simp [hb,List.append_assoc]
        obtain rfl : q=g := Option.some.inj (hq.symm.trans hhg)
        let i := (charges a.length h).choose
        have hlen : a.length ≤ C.gates.length := by simp [hb]
        have hdead : val a z dead=false := by
          unfold val
          apply List.getD_eq_default
          simp only [run_len,List.length_ofFn]
          dsimp [dead]
          omega
        have hfull : val C.gates z i=false := hzero z hz
        have ha : val a z i=false := by
          rw [hb,List.append_assoc] at hfull
          exact (val_prefix a ([q]++b) z i hi).symm.trans hfull
        have hep : change a.length q=copyOf dead i q := by
          unfold change operand
          simp only [h,↓reduceIte,↓reduceDIte]
          rfl
        rw [hep]
        exact copy_value dead i q (val a z) hdead ha hop hin (hm q (List.mem_of_getElem? hhg)).2
      · simp [change,h]
    have hp := patch_val C change z hstep C.gates ⟨[],by simp⟩ C.output
    have hpin := pin_eval v dead x gs (by simp [gs,dead]) C.output
    exact hpin.trans hp
  · intro j g hg hop
    obtain ⟨q,hq,rfl⟩ := atGate j g hg
    by_cases h : j∈S
    · simp [reroute,change,h,copyOf] at hop
    · refine Finset.mem_sdiff.mpr ⟨cover j q hq ?_,h⟩
      simpa [reroute,change,h] using hop


lemma restrict_charged {n : ℕ} (C : Circuit) (v : Fin n) (A S : Finset ℕ) (hm : Monotone2 C)
    (cover : ∀ j g, C.gates[j]?=some g → g.op=.or → j∈A) (charges : ∀ j∈S, Charged C v j) :
    ∃ (C' : Circuit) (B : Finset ℕ), B.card+S.card=A.card ∧ Monotone2 C' ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x)=C.eval (List.ofFn (Function.update x v false))) ∧
      ∀ j g, C'.gates[j]?=some g → g.op=.or → j∈B := by
  have sub : S⊆A := by
    intro j hj
    obtain ⟨_,g,hg,hop,_⟩ := charges j hj
    exact cover j g hg hop
  obtain ⟨C',hM,_,hF,hB⟩ := restrict_many C v A S hm cover charges
  exact ⟨C',A\S,Finset.card_sdiff_add_card_eq_card sub,hM,hF,hB⟩


lemma restrict_one {n : ℕ} (C : Circuit) (v : Fin n) (A : Finset ℕ) (hm : Monotone2 C)
    (cover : ∀ j g, C.gates[j]?=some g → g.op=.or → j∈A)
    (on : ∃ x : Fin n → Bool, x v=false ∧ C.eval (List.ofFn x)=false ∧
      C.eval (List.ofFn (Function.update x v true))=true)
    (other : ∃ z : Fin n → Bool, z v=false ∧ C.eval (List.ofFn z)=true) :
    ∃ (C' : Circuit) (B : Finset ℕ), B.card+1=A.card ∧ Monotone2 C' ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x)=C.eval (List.ofFn (Function.update x v false))) ∧
      ∀ j g, C'.gates[j]?=some g → g.op=.or → j∈B := by
  obtain ⟨j,g,i,hg,hop,hin,hi,hv⟩ := release_exists C v hm on other
  have hp : Charged C v j := ⟨i,g,hg,hop,hin,hi,hv⟩
  simpa only [Finset.card_singleton] using restrict_charged C v A {j} hm cover
    (fun k hk => Finset.mem_singleton.mp hk ▸ hp)


lemma discard_redundant_or {n : ℕ} (C : Circuit) (A : Finset ℕ) (j : ℕ) (g : Gate)
    (hm : Monotone2 C) (cover : ∀ k h, C.gates[k]?=some h → h.op=.or → k∈A)
    (hg : C.gates[j]?=some g) (hop : g.op=.or)
    (same : (∃ w<n+j, ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n+j) false = (C.wires (List.ofFn x)).getD w false) ∨
      ∃ b : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n+j) false=b) :
    ∃ C' : Circuit, Monotone2 C' ∧ C'.gates.length=C.gates.length ∧
      (∀ x : Fin n → Bool, C'.eval (List.ofFn x)=C.eval (List.ofFn x)) ∧
      (∀ k h, C'.gates[k]?=some h → h.op=.or → k∈A.erase j) ∧ (A.erase j).card+1=A.card := by
  let dead := n+C.gates.length
  obtain ⟨l,hl,allowed,glob⟩ : ∃ l : List ℕ, l.length≤1 ∧
      (∀ w∈l, w<n+j ∨ w=dead) ∧
      ∀ x : Fin n → Bool, readGate ⟨.and,l⟩ (val C.gates x)=val C.gates x (n+j) := by
    rcases same with ⟨w,hw,eq⟩ | ⟨b,eq⟩
    · refine ⟨[w],by simp,fun z hz => (List.mem_singleton.mp hz) ▸ (Or.inl hw),?_⟩
      intro x
      have hx : val C.gates x w=val C.gates x (n+j) := (eq x).symm
      simpa [readGate,GateOp.eval] using hx
    · cases b
      · refine ⟨[dead],by simp,fun w hw => Or.inr (List.mem_singleton.mp hw),?_⟩
        intro x
        have hd : val C.gates x dead=false := by
          unfold val
          exact List.getD_eq_default _ _ (by simp [run_len,dead])
        have hx : false=val C.gates x (n+j) := (eq x).symm
        simpa [readGate,GateOp.eval,hd] using hx
      · exact ⟨[],by simp,by simp,fun x => (eq x).symm⟩
  let f (k : ℕ) (h : Gate) : Gate := if k=j then ⟨.and,l⟩ else h
  let C' : Circuit := ⟨C.gates.mapIdx f,C.output⟩
  have source (k : ℕ) (h : Gate) (hh : C'.gates[k]?=some h) :
      ∃ h', C.gates[k]?=some h' ∧ h=f k h' := by
    change (C.gates.mapIdx f)[k]?=some h at hh
    rw [List.getElem?_mapIdx] at hh
    cases h0 : C.gates[k]? with
    | none => simp [h0] at hh
    | some h' => exact ⟨h',rfl,by simpa [h0] using hh.symm⟩
  refine ⟨C',?_,by simp [C'],?_,?_,?_⟩
  · intro h hh
    obtain ⟨k,hk⟩ := List.mem_iff_getElem?.mp hh
    obtain ⟨h',h0,rfl⟩ := source k h hk
    by_cases hk : k=j
    · simp [f,hk]; omega
    · simpa [f,hk] using hm h' (List.mem_of_getElem? h0)
  · intro x
    apply patch_val C f x _ C.gates ⟨[],by simp⟩ C.output
    intro a h ⟨b,hb⟩
    by_cases ha : a.length=j
    · have hout : val C.gates x (n+j)=readGate h (val a x) := by
        rw [hb,← ha,val_prefix (a++[h]) b x _ (by simp),new_val]
      have hdata : l.map (val a x)=l.map (val C.gates x) := by
        apply List.map_congr_left
        intro w hw
        rcases allowed w hw with h|rfl
        · rw [hb,List.append_assoc]
          exact (val_prefix a ([_]++b) x w (by omega)).symm
        · have ha' : a.length≤C.gates.length := by simp [hb]
          unfold val
          rw [List.getD_eq_default _ _ (by simp [run_len,dead];omega),
            List.getD_eq_default _ _ (by simp [run_len,dead])]
      have hval : readGate ⟨.and,l⟩ (val a x)=readGate ⟨.and,l⟩ (val C.gates x) :=
        congrArg GateOp.and.eval hdata
      simpa [f,ha] using hval.trans ((glob x).trans hout)
    · simp [f,ha]
  · intro k h hh ha
    obtain ⟨h',h0,rfl⟩ := source k h hh
    by_cases hk : k=j
    · simp [f,hk] at ha
    · exact Finset.mem_erase.mpr ⟨hk,cover k h' h0 (by simpa [f,hk] using ha)⟩
  · exact Finset.card_erase_add_one (cover j g hg hop)


end Leaf603

namespace CycleModule603

open Finset
variable {V : Type*} [DecidableEq V]

def bit (A B X : Finset V) : Prop := A ⊆ X ∨ B ⊆ X

lemma twins_force_square {G : SimpleGraph V} {p q : V} (hpq : p≠q)
    {a b : V} (hab : a≠b) (hpa : G.Adj p a) (hpb : G.Adj p b)
    (hqa : G.Adj q a) (hqb : G.Adj q b) :
    ∃ W : G.Walk p p, W.IsCycle ∧ W.length=4 := by
  let W : G.Walk p p := .cons hpa (.cons hqa.symm (.cons hqb (.cons hpb.symm .nil)))
  have hlen : W.length=4 := rfl
  refine ⟨W,SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨?_,by omega⟩,hlen⟩
  simp only [W,SimpleGraph.Walk.tail_cons,SimpleGraph.Walk.isPath_copy,
    SimpleGraph.Walk.isPath_def,SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil]
  simp [hab,hpa.ne.symm,hqa.ne.symm,hqb.ne,hpb.ne.symm,hpq.symm]

end CycleModule603

namespace CycleCut603
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def readGate (g : Gate) (w : ℕ → Bool) : Bool := g.op.eval (g.inputs.map w)
private def run (gs : List Gate) (input : List Bool) : List Bool :=
  gs.foldl (fun wires g => wires ++ [readGate g (fun j => wires.getD j false)]) input

private lemma run_append (gs : List Gate) (g : Gate) (s : List Bool) :
    run (gs ++ [g]) s = run gs s ++ [readGate g (fun j => (run gs s).getD j false)] := by
  simp [run,List.foldl_append]

private lemma run_len (gs : List Gate) (s : List Bool) : (run gs s).length=s.length+gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => simp [run_append,ih,Nat.add_assoc]

private def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run gs (List.ofFn x)).getD w false

private lemma new_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    val (gs++[g]) x (n+gs.length) = readGate g (val gs x) := by
  have hl : (run gs (List.ofFn x)).length=n+gs.length := by simp [run_len]
  unfold val
  rw [run_append,←hl]
  simp

private lemma other_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) {w : ℕ}
    (h : w ≠ n+gs.length) : val (gs++[g]) x w = val gs x w := by
  have hl : (run gs (List.ofFn x)).length=n+gs.length := by simp [run_len]
  unfold val
  rw [run_append]
  by_cases hw : w < (run gs (List.ofFn x)).length
  · exact List.getD_append _ _ _ _ hw
  · rw [List.getD_eq_default _ _ (by simp [hl]; omega),List.getD_eq_default _ _ (by omega)]

def releaseAt {n : ℕ} (gs : List Gate) (v : Fin n) (j : ℕ) : Prop :=
  ∃ g i, gs[j]?=some g ∧ g.op=.or ∧ i∈g.inputs ∧ i<n+j ∧
    ∀ z : Fin n → Bool, z v=false → ((⟨gs,0⟩ : Circuit).wires (List.ofFn z)).getD i false=false

private lemma push_release {n j : ℕ} {gs : List Gate} {v : Fin n} (g : Gate)
    (h : releaseAt gs v j) : releaseAt (gs++[g]) v j := by
  obtain ⟨q,i,hj,hop,hi,hlt,hz⟩ := h
  have hjl := (List.getElem?_eq_some_iff.mp hj).1
  refine ⟨q,i,(List.getElem?_append_left hjl).trans hj,hop,hi,hlt,?_⟩
  intro z hv
  exact (other_val gs g z (by omega)).trans (hz z hv)

private lemma changed_dominated {n : ℕ} (S : Finset (Fin n)) (x y : Fin n → Bool)
    (agree : ∀ i, i ∉ S → x i = y i) (p : ℕ) (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op=.and ∨ g.op=.or)
    (only : ∀ v ∈ S, ∀ j, releaseAt gs v j → j=p)
    (same : p<gs.length → val gs x (n+p)=val gs y (n+p)) (w : ℕ)
    (hd : val gs x w ≠ val gs y w) :
    ∃ v∈S, ∀ z : Fin n → Bool, z v=false → val gs z w=false := by
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    change (List.ofFn x).getD w false ≠ (List.ofFn y).getD w false at hd
    by_cases hw : w<n
    · let i : Fin n := ⟨w,hw⟩
      have hx : ∀ t : Fin n → Bool, val [] t w = t i := by
        intro t; change (List.ofFn t).getD w false=t i
        rw [List.getD_eq_getElem _ _ (by simpa using hw)]
        simp [i]
      refine ⟨i,by
        by_contra hi
        exact hd ((hx x).trans ((agree i hi).trans (hx y).symm)),?_⟩
      intro z hz
      exact (hx z).trans hz
    · exact (hd (by rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hw),
          List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hw)])).elim
  | append_singleton gs g ih =>
    have hm' : ∀ q∈gs, q.op=.and ∨ q.op=.or := fun q h => hm q (List.mem_append_left _ h)
    have only' : ∀ v∈S, ∀ j, releaseAt gs v j → j=p :=
      fun v hv j hj => only v hv j (push_release g hj)
    have same' (h : p<gs.length) : val gs x (n+p)=val gs y (n+p) := by
      have he := same (by simp; omega)
      simpa only [other_val gs g _ (by omega : n+p ≠ n+gs.length)] using he
    by_cases hw : w=n+gs.length
    · subst w
      have hd' := hd
      rw [new_val,new_val] at hd'
      obtain ⟨a,ha,had⟩ : ∃ a∈g.inputs, val gs x a ≠ val gs y a := by
        by_contra! h
        exact hd' (congrArg g.op.eval (List.map_congr_left h))
      have bound : a<n+gs.length := by
        by_contra! h
        unfold val at had
        exact had (by rw [List.getD_eq_default _ _ (by simpa [run_len] using h),
          List.getD_eq_default _ _ (by simpa [run_len] using h)])
      obtain ⟨v,hv,below⟩ := ih hm' only' same' a had
      rcases hm g (by simp) with hand|hor
      · refine ⟨v,hv,fun z hz => ?_⟩
        rw [new_val]
        change (g.op.eval _) = false
        rw [hand]
        apply List.all_eq_false.mpr
        exact ⟨_,List.mem_map.mpr ⟨a,ha,rfl⟩,by simp [below z hz]⟩
      · have atGate : releaseAt (gs++[g]) v gs.length := by
          refine ⟨g,a,by simp,hor,ha,bound,fun z hz => ?_⟩
          exact (other_val _ _ _ (Nat.ne_of_lt bound)).trans (below z hz)
        have e := only v hv _ atGate
        subst p
        exact (hd (same (by simp))).elim
    · rw [other_val _ _ _ hw,other_val _ _ _ hw] at hd
      obtain ⟨v,hv,below⟩ := ih hm' only' same' w hd
      exact ⟨v,hv,fun z hz => (other_val _ _ _ hw).trans (below z hz)⟩

lemma factor_gate {n : ℕ} (S : Finset (Fin n)) (C : Circuit) (p : ℕ) (hm : Monotone2 C)
    (only : ∀ v∈S, ∀ j, releaseAt C.gates v j → j=p)
    (free : ∀ v∈S, ∃ z : Fin n → Bool, z v=false ∧ C.eval (List.ofFn z)=true)
    (x y : Fin n → Bool) (agree : ∀ i, i∉S → x i=y i)
    (same : (C.wires (List.ofFn x)).getD (n+p) false=(C.wires (List.ofFn y)).getD (n+p) false) :
    C.eval (List.ofFn x)=C.eval (List.ofFn y) := by
  by_contra hd
  obtain ⟨v,hv,below⟩ := changed_dominated S x y agree p C.gates (fun g hg => (hm g hg).1)
    only (fun _ => same) C.output hd
  obtain ⟨z,hz,ho⟩ := free v hv
  exact Bool.false_ne_true ((below z hz).symm.trans ho)

def mask {n : ℕ} (X : Finset (Fin n)) (i : Fin n) : Bool := decide (i∈X)


private lemma val_prefix {n : ℕ} (a b : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : w<n+a.length) : val (a++b) x w=val a x w := by
  induction b using List.reverseRecOn with
  | nil => simp
  | append_singleton b g ih => rw [←List.append_assoc,other_val _ _ _ (by simp; omega),ih]

private lemma out_val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ)
    (hw : n+gs.length ≤ w) : val gs x w=false := by
  exact List.getD_eq_default _ _ (by simpa [run_len] using hw)

def monomial {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) := ∀ v∈A, x v=true

def principal {n : ℕ} (f : (Fin n → Bool) → Bool) :=
  (∀ x, f x=false) ∨ ∃ A : Finset (Fin n), ∀ x, f x=true ↔ monomial A x

private lemma principal_all {n : ℕ} (l : List ℕ) (z : (Fin n → Bool) → ℕ → Bool)
    (h : ∀ j∈l, principal (fun x => z x j)) : principal (fun x => (l.map (z x)).all id) := by
  induction l with
  | nil => right; exact ⟨∅,by simp [monomial]⟩
  | cons a l ih =>
    rcases h a (by simp) with ha|⟨A,ha⟩
    · left; intro x; simp [ha]
    rcases ih (fun j hj => h j (by simp [hj])) with hl|⟨B,hB⟩
    · left; intro x; simp [hl]
    right; refine ⟨A∪B,fun x => ?_⟩
    simp only [List.map_cons,List.all_cons,id_eq,Bool.and_eq_true]
    rw [ha,hB]
    simp [monomial,Finset.mem_union,or_imp,forall_and]

lemma all_and_principal {n : ℕ} (gs : List Gate)
    (hall : ∀g∈gs, g.op=.and) (w : ℕ) :
    principal (fun x : Fin n → Bool => ((⟨gs,0⟩ : Circuit).wires (List.ofFn x)).getD w false) := by
  change principal (fun x : Fin n → Bool => val gs x w)
  induction gs using List.reverseRecOn generalizing w with
  | nil =>
    by_cases h : w<n
    · right; refine ⟨{⟨w,h⟩},fun x => ?_⟩
      change (List.ofFn x).getD w false=true ↔ _
      rw [List.getD_eq_getElem _ _ (by simpa using h)]
      simp [monomial]
    · left; exact fun x => out_val _ _ _ (by simp; omega)
  | append_singleton gs g ih =>
    have h : ∀q∈gs, q.op=.and := fun q hq => hall q (List.mem_append_left _ hq)
    by_cases hw : w=n+gs.length
    · subst w
      simp only [new_val,readGate,hall g (by simp),GateOp.eval]
      exact principal_all _ _ (fun j _ => ih h j)
    · simpa only [other_val gs g _ hw] using ih h w

private lemma mono_antitone {n : ℕ} {A B : Finset (Fin n)} (h : A⊆B) {x : Fin n → Bool}
    (hx : monomial B x) : monomial A x := fun v hv => hx v (h hv)

lemma prefix_decision {n : ℕ} (pre post : List Gate) (g : Gate)
    (hall : ∀q∈pre, q.op=.and) (hop : g.op=.or) (hlen : g.inputs.length≤2) :
    let gs := (pre++[g])++post
    (∃ w, ∀ x : Fin n → Bool,
      ((⟨gs,0⟩ : Circuit).wires (List.ofFn x)).getD (n+pre.length) false =
      ((⟨pre,0⟩ : Circuit).wires (List.ofFn x)).getD w false) ∨
    (∃ A B : Finset (Fin n), ¬ A⊆B ∧ ¬ B⊆A ∧
      (∀ v∈A∪B, releaseAt gs v pre.length) ∧
      (∀ U : Finset (Fin n), ((⟨gs,0⟩ : Circuit).wires (List.ofFn (mask U))).getD
        (n+pre.length) false=true ↔ CycleModule603.bit A B U)) := by
  dsimp only
  let gs := (pre++[g])++post
  have thisGate (x : Fin n → Bool) : val gs x (n+pre.length)=readGate g (val pre x) :=
    (val_prefix (pre++[g]) post x _ (by simp)).trans (new_val pre g x)
  cases hi : g.inputs with
  | nil =>
    left; refine ⟨n+pre.length,fun x => ?_⟩
    change val gs x _=val pre x _
    rw [thisGate,out_val _ _ _ (by omega)]
    simp [readGate,hop,hi,GateOp.eval]
  | cons a l =>
    cases hj : l with
    | nil =>
      left; refine ⟨a,fun x => ?_⟩
      change val gs x _=val pre x _
      rw [thisGate]; simp [readGate,hop,hi,hj,GateOp.eval]
    | cons b tail =>
      have ht : tail=[] := by apply List.length_eq_zero_iff.mp; rw [hi,hj] at hlen; simp only [List.length_cons] at hlen; omega
      subst tail
      have ins : g.inputs=[a,b] := by rw [hi,hj]
      have gate (x : Fin n → Bool) : val gs x (n+pre.length) = (val pre x a || val pre x b) := by
        rw [thisGate]; simp [readGate,hop,ins,GateOp.eval]
      have pure (w : ℕ) : principal (fun x : Fin n → Bool => val pre x w) := all_and_principal pre hall w
      rcases pure a with ha|⟨A,ha⟩
      · left; exact ⟨b,fun x => by change val gs x _=val pre x _; rw [gate,show val pre x a=false from ha x]; simp⟩
      rcases pure b with hb|⟨B,hb⟩
      · left; exact ⟨a,fun x => by change val gs x _=val pre x _; rw [gate,show val pre x b=false from hb x]; simp⟩
      by_cases hab : A⊆B
      · left; refine ⟨a,fun x => ?_⟩
        change val gs x _=val pre x _
        apply Bool.eq_iff_iff.mpr
        rw [gate,Bool.or_eq_true,ha,hb]
        exact or_iff_left_of_imp (mono_antitone hab)
      by_cases hba : B⊆A
      · left; refine ⟨b,fun x => ?_⟩
        change val gs x _=val pre x _
        apply Bool.eq_iff_iff.mpr
        rw [gate,Bool.or_eq_true,ha,hb]
        exact or_iff_right_of_imp (mono_antitone hba)
      right
      have charge (w : ℕ) (L : Finset (Fin n)) (hin : w∈g.inputs)
          (rep : ∀ x : Fin n → Bool, val pre x w=true ↔ monomial L x) (v : Fin n) (hv : v∈L) :
          releaseAt gs v pre.length := by
        have valid : w<n+pre.length := by
          by_contra! h
          have yes := (rep (fun _ => true)).mpr (by intro i _; rfl)
          rw [out_val _ _ _ h] at yes
          contradiction
        refine ⟨g,w,?_,hop,hin,valid,fun x hx => ?_⟩
        · rw [List.getElem?_append_left (by simp)]; simp
        · change val ((pre++[g])++post) x w=false
          rw [List.append_assoc,val_prefix _ _ _ _ valid]
          cases e : val pre x w with
          | false => rfl
          | true => exact (Bool.false_ne_true (hx.symm.trans ((rep x).mp e v hv))).elim
      refine ⟨A,B,hab,hba,?_,fun U => ?_⟩
      · intro v hv
        rcases Finset.mem_union.mp hv with hv|hv
        · exact charge a A (by simp [ins]) ha v hv
        · exact charge b B (by simp [ins]) hb v hv
      · change val gs (mask U) _=true ↔ _
        rw [gate,Bool.or_eq_true,ha,hb]
        simp only [monomial,mask,decide_eq_true_eq,CycleModule603.bit]; rfl

lemma global_copy {n : ℕ} (pre post : List Gate) (g : Gate)
    (copy : ∃ w, ∀ x : Fin n → Bool, ((⟨(pre++[g])++post,0⟩ : Circuit).wires
      (List.ofFn x)).getD (n+pre.length) false = ((⟨pre,0⟩ : Circuit).wires (List.ofFn x)).getD w false) :
    let C : Circuit := ⟨(pre++[g])++post,0⟩
    (∃ w<n+pre.length, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n+pre.length) false =
      (C.wires (List.ofFn x)).getD w false) ∨
      ∃ b : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n+pre.length) false=b := by
  obtain ⟨w,eq⟩ := copy
  by_cases h : w<n+pre.length
  · left; refine ⟨w,h,fun x => (eq x).trans ?_⟩
    change val pre x w=val ((pre++[g])++post) x w
    rw [List.append_assoc,val_prefix _ _ _ _ h]
  · right; exact ⟨false,fun x => (eq x).trans (out_val pre x w (by omega))⟩

end CycleCut603

namespace Leaf603
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private lemma split_first_or (gs : List Gate)
    (hm : ∀ q ∈ gs, (q.op=.and ∨ q.op=.or) ∧ q.inputs.length≤2)
    (present : ∃ q ∈ gs, q.op=.or) :
    ∃ (pre : List Gate) (g : Gate) (post : List Gate), gs=(pre++[g])++post ∧
      (∀ q ∈ pre, q.op=.and) ∧ g.op=.or ∧ g.inputs.length≤2 := by
  induction gs with
  | nil => simp at present
  | cons h t ih =>
    obtain ⟨hop,hlen⟩ := hm h List.mem_cons_self
    rcases hop with hand|hor
    · have tail : ∃ q ∈ t, q.op=.or := by
        obtain ⟨q,hq,hor⟩ := present
        rcases List.mem_cons.mp hq with rfl|hq
        · rw [hand] at hor
          cases hor
        · exact ⟨q,hq,hor⟩
      obtain ⟨a,g,b,eq,ha,hg,hl⟩ := ih (fun q hq => hm q (List.mem_cons_of_mem _ hq)) tail
      refine ⟨h::a,g,b,congrArg (List.cons h) eq,?_,hg,hl⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl|hq
      · exact hand
      · exact ha q hq
    · exact ⟨[],h,t,rfl,by simp,hor,hlen⟩


lemma first_or {n : ℕ} (C : Circuit) (v : Fin n) (hm : Monotone2 C)
    (on : ∃ x : Fin n → Bool, x v=false ∧ C.eval (List.ofFn x)=false ∧
      C.eval (List.ofFn (Function.update x v true))=true)
    (other : ∃ z : Fin n → Bool, z v=false ∧ C.eval (List.ofFn z)=true) :
    ∃ (pre : List Gate) (g : Gate) (post : List Gate), C.gates=(pre++[g])++post ∧
      (∀ q ∈ pre, q.op=.and) ∧ g.op=.or ∧ g.inputs.length≤2 := by
  obtain ⟨j,g,_,hg,hop,_⟩ := release_exists C v hm on other
  exact split_first_or C.gates hm ⟨g,List.mem_of_getElem? hg,hop⟩

end Leaf603

namespace GraphCircuit603

open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped Classical

variable {n : ℕ}

def detects (K G : SimpleGraph (Fin n)) (C : Circuit) : Prop :=
  (∀ x : Fin n → Bool,
    (∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) → C.eval (List.ofFn x) = true) ∧
  (∀ x : Fin n → Bool, C.eval (List.ofFn x) = true →
    ∃ u v, K.Adj u v ∧ x u = true ∧ x v = true)

def covers (C : Circuit) (A : Finset ℕ) : Prop :=
  ∀ j g, C.gates[j]? = some g → g.op = .or → j ∈ A

def feasible (K G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ C A, Monotone2 C ∧ detects K G C ∧ covers C A ∧ A.card = k

private lemma exists_budget (K G : SimpleGraph (Fin n)) :
    ∃ k, k = G.edgeSet.ncard ∨ feasible K G k := ⟨_, Or.inl rfl⟩

noncomputable def best (K G : SimpleGraph (Fin n)) : ℕ := Nat.find (exists_budget K G)

lemma best_le {K G : SimpleGraph (Fin n)} {k : ℕ} (h : feasible K G k) :
    best K G ≤ k :=
  Nat.find_min' (exists_budget K G) (Or.inr h)

lemma represents {K G : SimpleGraph (Fin n)} (h : best K G < G.edgeSet.ncard) :
    feasible K G (best K G) :=
  (Nat.find_spec (exists_budget K G)).resolve_left (Nat.ne_of_lt h)

lemma target_le_ambient {K G : SimpleGraph (Fin n)} {C : Circuit}
    (h : detects K G C) : G ≤ K := by
  intro u v huv
  let x : Fin n → Bool := fun i => decide (i = u ∨ i = v)
  have hx : C.eval (List.ofFn x) = true :=
    h.1 x ⟨u, v, huv, by simp [x], by simp [x]⟩
  obtain ⟨a, b, hab, ha, hb⟩ := h.2 x hx
  rcases of_decide_eq_true ha with rfl | rfl
  · rcases of_decide_eq_true hb with rfl | rfl
    · exact (K.irrefl hab).elim
    · exact hab
  · rcases of_decide_eq_true hb with rfl | rfl
    · exact hab.symm
    · exact (K.irrefl hab).elim

lemma one_bit {K G : SimpleGraph (Fin n)} {C : Circuit} (h : detects K G C)
    {v : Fin n} (hv : v ∈ G.support) :
    ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = false ∧
      C.eval (List.ofFn (Function.update x v true)) = true := by
  obtain ⟨u, hu⟩ := G.mem_support.mp hv
  let x : Fin n → Bool := fun i => decide (i = u)
  have hne : v ≠ u := hu.ne
  refine ⟨x, by simp [x, hne], ?_, ?_⟩
  · rw [Bool.eq_false_iff]
    intro ht
    obtain ⟨i, j, hij, hi, hj⟩ := h.2 x ht
    exact hij.ne ((of_decide_eq_true hi).trans (of_decide_eq_true hj).symm)
  · apply h.1
    exact ⟨v, u, hu, by simp, by simp [x, Function.update_of_ne hne.symm]⟩

lemma deletion_eval (G : SimpleGraph (Fin n)) (v : Fin n) (x : Fin n → Bool) :
    (∃ a b, G.Adj a b ∧ Function.update x v false a = true ∧
        Function.update x v false b = true) ↔
      ∃ a b, (G.deleteIncidenceSet v).Adj a b ∧ x a = true ∧ x b = true := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have hav : a ≠ v := by rintro rfl; simp at ha
    have hbv : b ≠ v := by rintro rfl; simp at hb
    exact ⟨a, b, (G.deleteIncidenceSet_adj).mpr ⟨hab, hav, hbv⟩,
      (Function.update_of_ne hav _ _).symm.trans ha,
      (Function.update_of_ne hbv _ _).symm.trans hb⟩
  · rintro ⟨a, b, hab, ha, hb⟩
    obtain ⟨hab, hav, hbv⟩ := G.deleteIncidenceSet_adj.mp hab
    exact ⟨a, b, hab, (Function.update_of_ne hav _ _).trans ha,
      (Function.update_of_ne hbv _ _).trans hb⟩

lemma restrict_detects {K G : SimpleGraph (Fin n)} {C C' : Circuit} {v : Fin n}
    (h : detects K G C)
    (heq : ∀ x : Fin n → Bool,
      C'.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v false))) :
    detects K (G.deleteIncidenceSet v) C' := by
  constructor
  · intro x hx
    rw [heq]
    exact h.1 _ ((deletion_eval G v x).mpr hx)
  · intro x hx
    rw [heq] at hx
    obtain ⟨a, b, hab, ha, hb⟩ := h.2 _ hx
    have hav : a ≠ v := by rintro rfl; simp at ha
    have hbv : b ≠ v := by rintro rfl; simp at hb
    exact ⟨a, b, hab, (Function.update_of_ne hav _ _).symm.trans ha,
      (Function.update_of_ne hbv _ _).symm.trans hb⟩

lemma accepts_without {K G : SimpleGraph (Fin n)} {C : Circuit}
    (h : detects K G C) (v : Fin n) (hd : G.degree v < G.edgeSet.ncard) :
    ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = true := by
  have hc : (G.deleteIncidenceSet v).edgeSet.ncard + G.degree v = G.edgeSet.ncard := by
    have he := G.card_edgeFinset_deleteIncidenceSet v
    have hle := G.degree_le_card_edgeFinset v
    simpa only [SimpleGraph.edgeFinset, Set.toFinset_card, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq] using (he ▸ Nat.sub_add_cancel hle :
        (G.deleteIncidenceSet v).edgeFinset.card + G.degree v = G.edgeFinset.card)
  have hcard : 0 < (G.deleteIncidenceSet v).edgeSet.ncard := by omega
  obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt hcard)
  have hex : ∃ a b, (G.deleteIncidenceSet v).Adj a b := by
    induction e using Sym2.inductionOn with
    | _ a b => exact ⟨a, b, he⟩
  obtain ⟨a, b, hab⟩ := hex
  let x : Fin n → Bool := Function.update (fun _ => true) v false
  apply Exists.intro x
  refine ⟨by simp [x], h.1 x ?_⟩
  exact (deletion_eval G v (fun _ => true)).mpr ⟨a, b, hab, rfl, rfl⟩

lemma delete_isolated {G : SimpleGraph (Fin n)} {v : Fin n} (hv : v ∉ G.support) :
    G.deleteIncidenceSet v = G := by
  ext a b
  rw [G.deleteIncidenceSet_adj]
  refine ⟨fun h => h.1, fun hab => ⟨hab, ?_, ?_⟩⟩
  · rintro rfl
    exact hv hab.mem_support_left
  · rintro rfl
    exact hv hab.mem_support_right

lemma two_neighbors {G : SimpleGraph (Fin n)} {v : Fin n} (hd : 2 ≤ G.degree v) :
    ∃ a b, a ≠ b ∧ G.Adj v a ∧ G.Adj v b := by
  have h : 1 < (G.neighborFinset v).card := hd
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h
  exact ⟨a, b, hab, (G.mem_neighborFinset _ _).mp ha, (G.mem_neighborFinset _ _).mp hb⟩

lemma accepts_core_without {K G : SimpleGraph (Fin n)} {C : Circuit}
    (h : detects K G C)
    (degrees : ∀ u ∈ G.support, G.degree u = 2) {v : Fin n} (hv : v ∈ G.support) :
    ∃ x : Fin n → Bool, x v = false ∧ C.eval (List.ofFn x) = true := by
  obtain ⟨u, hvu⟩ := G.mem_support.mp hv
  obtain ⟨a, b, hab, ha, hb⟩ := two_neighbors (le_of_eq (degrees u hvu.mem_support_right).symm)
  have hex : ∃ w, G.Adj u w ∧ w ≠ v := by
    by_cases he : a = v
    · exact ⟨b, hb, fun h => hab (he.trans h.symm)⟩
    · exact ⟨a, ha, he⟩
  obtain ⟨w, hw, hwv⟩ := hex
  let x : Fin n → Bool := Function.update (fun _ => true) v false
  exact ⟨x, by simp [x], h.1 x ⟨u, w, hw,
    by simp [x, Function.update_of_ne hvu.ne.symm],
    by simp [x, Function.update_of_ne hwv]⟩⟩

lemma support_nonempty {G : SimpleGraph (Fin n)} (hg : 0 < G.edgeSet.ncard) :
    G.support.Nonempty := by
  obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero hg.ne'
  induction e using Sym2.inductionOn with
  | _ a b =>
    have hab : G.Adj a b := he
    exact ⟨a, hab.mem_support_left⟩

end GraphCircuit603

namespace PaidGraph603
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity GraphCircuit603
open scoped Classical
variable {n : ℕ} {K G : SimpleGraph (Fin n)} {C : Circuit} {A : Finset ℕ}

lemma after_restriction {v : Fin n} {C' : Circuit} (h : detects K G C)
    (heq : ∀ x : Fin n → Bool,
      C'.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v false))) :
    detects K (G.deleteIncidenceSet v) C' := by
  exact GraphCircuit603.restrict_detects h heq

lemma charged_saving (hm : Monotone2 C) (h : detects K G C) (hc : covers C A)
    (v : Fin n) (S : Finset ℕ) (charged : ∀ j∈S, Leaf603.Charged C v j) :
    best K (G.deleteIncidenceSet v) + S.card ≤ A.card := by
  obtain ⟨C',B,hB,hM,heq,hcov⟩ := Leaf603.restrict_charged C v A S hm hc charged
  have hb := best_le (show feasible K (G.deleteIncidenceSet v) B.card from
    ⟨C',B,hM,after_restriction h heq,hcov,rfl⟩)
  omega

lemma charge_is_active (hm : Monotone2 C) (h : detects K G C) (hc : covers C A)
    (hmin : A.card = best K G) {v : Fin n} {j : ℕ} (hj : Leaf603.Charged C v j) :
    v ∈ G.support := by
  by_contra hv
  have hh := charged_saving hm h hc v {j} (fun k hk => Finset.mem_singleton.mp hk ▸ hj)
  simp only [delete_isolated hv,Finset.card_singleton,hmin,Nat.not_succ_le_self] at hh

lemma double_saving (hm : Monotone2 C) (h : detects K G C) (hc : covers C A)
    (v : Fin n) {i j : ℕ} (hne : i ≠ j) (hi : Leaf603.Charged C v i)
    (hj : Leaf603.Charged C v j) : best K (G.deleteIncidenceSet v) + 2 ≤ A.card := by
  have hh := charged_saving hm h hc v {i,j} (fun k hk => by
    rcases Finset.mem_insert.mp hk with he|he
    · exact he ▸ hi
    · exact Finset.mem_singleton.mp he ▸ hj)
  simpa [hne] using hh

lemma leaf_paid (hg : best K G + 1 < G.edgeSet.ncard) (v : Fin n) (degree : G.degree v = 1) :
    best K (G.deleteIncidenceSet v) + 1 ≤ best K G := by
  obtain ⟨C,A,hm,h,hc,hmin⟩ := represents (show best K G < G.edgeSet.ncard by omega)
  have hv := (G.degree_pos_iff_mem_support v).mp (show 0 < G.degree v by omega)
  obtain ⟨C',B,hB,hM,heq,hcov⟩ := Leaf603.restrict_one C v A hm hc (one_bit h hv)
    (accepts_without h v (by omega))
  have hb := best_le (show feasible K (G.deleteIncidenceSet v) B.card from
    ⟨C',B,hM,after_restriction h heq,hcov,rfl⟩)
  omega

def corePaid (K : SimpleGraph (Fin n)) : Prop :=
  ∀ G : SimpleGraph (Fin n), GraphInduction603.sparse G → GraphInduction603.noFour G →
    best K G + 1 < G.edgeSet.ncard → (∀ v ∈ G.support, G.degree v = 2) →
    ∃ v ∈ G.support, best K (G.deleteIncidenceSet v) + 2 ≤ best K G

lemma edge_bound (core : corePaid K) (hs : GraphInduction603.sparse G)
    (hf : GraphInduction603.noFour G) (hm : Monotone2 C) (h : detects K G C)
    (hc : covers C A) : G.edgeSet.ncard ≤ A.card + 1 := by
  have hb := best_le (show feasible K G A.card from ⟨C,A,hm,h,hc,rfl⟩)
  exact (GraphInduction603.of_paid_deletions (best K) (fun _ _ _ hg => leaf_paid hg)
    core G hs hf).trans (by omega)

end PaidGraph603

namespace CycleCut603
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma predicate_factors {n : ℕ} (S A B : Finset (Fin n))
    (C : Circuit) (p : ℕ) (hm : Monotone2 C)
    (hAS : A ⊆ S) (hBS : B ⊆ S)
    (only : ∀ v∈S, ∀ j, releaseAt C.gates v j → j=p)
    (free : ∀ v∈S, ∃ z : Fin n → Bool, z v=false ∧ C.eval (List.ofFn z)=true)
    (bit_eq : ∀ U : Finset (Fin n), (C.wires (List.ofFn (mask U))).getD (n+p) false=true ↔
      CycleModule603.bit A B U) :
    Relative603.factors (fun U => C.eval (List.ofFn (mask U)) = true) S A B := by
  intro X hX Y hY bits T ht
  have part (U Q : Finset (Fin n)) (hU : U⊆S) : U⊆Q∪T ↔ U⊆Q := by
    constructor
    · intro h i hi
      exact (Finset.mem_union.mp (h hi)).resolve_right
        (fun he => Finset.disjoint_left.mp ht he (hU hi))
    · intro h i hi
      exact Finset.mem_union_left _ (h hi)
  have beq : CycleModule603.bit A B (X∪T) ↔ CycleModule603.bit A B (Y∪T) := by
    simpa only [CycleModule603.bit, Relative603.bit, part A _ hAS, part B _ hBS] using bits
  have eq := factor_gate S C p hm only free (mask (X∪T)) (mask (Y∪T)) (by
    intro i hi
    have hx : i∉X := fun h => hi (hX h)
    have hy : i∉Y := fun h => hi (hY h)
    simp [mask,hx,hy]) (Bool.eq_iff_iff.mpr ((bit_eq _).trans (beq.trans (bit_eq _).symm)))
  exact iff_of_eq (congrArg (fun b => b = true) eq)

end CycleCut603

namespace CoreFacts603
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity GraphCircuit603 PaidGraph603
open scoped Classical
variable {n : ℕ} {K G : SimpleGraph (Fin n)} {C : Circuit} {A : Finset ℕ}

lemma forbids_copy (hm : Monotone2 C) (h : detects K G C) (hc : covers C A)
    (hmin : A.card = best K G) {p : ℕ} {g : Gate}
    (hg : C.gates[p]? = some g) (hop : g.op = .or)
    (same : (∃ w<n+p, ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n+p) false = (C.wires (List.ofFn x)).getD w false) ∨
      ∃ b : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n+p) false=b) : False := by
  obtain ⟨C',hm',_,heq,cover,hcard⟩ := Leaf603.discard_redundant_or C A p g hm hc hg hop same
  have hdet : detects K G C' := by
    constructor
    · intro x hx
      rw [heq]
      exact h.1 x hx
    · intro x hx
      exact h.2 x (by rwa [heq] at hx)
  have hh := best_le (show feasible K G (A.erase p).card from ⟨C',A.erase p,hm',hdet,cover,rfl⟩)
  omega

lemma charged_iff_release (v : Fin n) (j : ℕ) :
    Leaf603.Charged C v j ↔ CycleCut603.releaseAt C.gates v j := by
  constructor
  · rintro ⟨i,g,hg,hop,hi,hij,hz⟩
    exact ⟨g,i,hg,hop,hi,hij,hz⟩
  · rintro ⟨g,i,hg,hop,hi,hij,hz⟩
    exact ⟨i,g,hg,hop,hi,hij,hz⟩


lemma pay_from_bit (hm : Monotone2 C) (h : detects K G C) (hc : covers C A)
    (hmin : A.card = best K G) (hf : GraphInduction603.noFour K)
    (degrees : ∀ u∈G.support, G.degree u = 2) (p : ℕ)
    (X Y : Finset (Fin n)) (hx : ¬ X ⊆ Y) (hy : ¬ Y ⊆ X)
    (hp : ∀ v∈X∪Y, Leaf603.Charged C v p)
    (bit_eq : ∀ U : Finset (Fin n), (C.wires (List.ofFn (CycleCut603.mask U))).getD (n+p) false=true ↔
      CycleModule603.bit X Y U) :
    ∃ v ∈ G.support, best K (G.deleteIncidenceSet v) + 2 ≤ best K G := by
  let S := X ∪ Y
  have active : ∀ v∈S, v ∈ G.support := fun v hv => charge_is_active hm h hc hmin (hp v hv)
  by_contra hn
  have only : ∀ v∈S, ∀ j, CycleCut603.releaseAt C.gates v j → j=p := by
    intro v hv j hj
    by_contra hne
    have pay := double_saving hm h hc v hne (charged_iff_release v j |>.mpr hj) (hp v hv)
    exact hn ⟨v,active v hv,hmin ▸ pay⟩
  have free := fun v hv => accepts_core_without h degrees (active v hv)
  have hXS : X ⊆ S := Finset.subset_union_left
  have hYS : Y ⊆ S := Finset.subset_union_right
  obtain ⟨u,hu,huy⟩ := Finset.not_subset.mp hx
  obtain ⟨v,hv,hvx⟩ := Finset.not_subset.mp hy
  have neq : u ≠ v := fun e => hvx (e ▸ hu)
  have ff := CycleCut603.predicate_factors S X Y C p hm hXS hYS only free bit_eq
  apply Relative603.no_relative_module G K
    (fun U => C.eval (List.ofFn (CycleCut603.mask U)) = true) S X Y
    ?_ ?_ hXS hYS ⟨u,hu⟩ ⟨v,hv⟩ ⟨u,hXS hu,v,hYS hv,neq⟩
    (fun w hw => two_neighbors (le_of_eq (degrees w (active w hw)).symm)) ?_ ff
  · intro U hU
    obtain ⟨a,b,hab,ha,hb⟩ := h.2 _ hU
    exact ⟨a,of_decide_eq_true ha,b,of_decide_eq_true hb,hab⟩
  · intro a b hab
    apply h.1
    exact ⟨a,b,hab,by simp [CycleCut603.mask],by simp [CycleCut603.mask]⟩
  · intro a b hab x y hax hbx hay hby
    by_contra hxy
    obtain ⟨c,hc,hlen⟩ := CycleModule603.twins_force_square hab hxy hax hay hbx hby
    exact hf a c hc hlen

end CoreFacts603

namespace Pseudoforest603
open SimpleGraph PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open GraphCircuit603 PaidGraph603 CoreFacts603
open scoped Classical

lemma pay_core {n : ℕ} (K : SimpleGraph (Fin n))
    (hK : GraphInduction603.noFour K) : corePaid K := by
  intro G _ _ hg degrees
  obtain ⟨C,A,hm,h,hc,hmin⟩ := represents (show best K G < G.edgeSet.ncard by omega)
  obtain ⟨v,hv⟩ := support_nonempty (show 0 < G.edgeSet.ncard by omega)
  obtain ⟨pre,g,post,shape,ands,hor,hlen⟩ :=
    Leaf603.first_or C v hm (one_bit h hv) (accepts_core_without h degrees hv)
  cases C with
  | mk gs out =>
    dsimp at shape
    subst gs
    have hj : (((pre++[g])++post)[pre.length]?) = some g := by
      rw [List.getElem?_append_left (by simp)]
      simp
    rcases CycleCut603.prefix_decision (n:=n) pre post g ands hor hlen with copy | choice
    · exact False.elim (forbids_copy hm h hc hmin hj hor (CycleCut603.global_copy pre post g copy))
    · obtain ⟨X,Y,hx,hy,charges,bits⟩ := choice
      exact pay_from_bit hm h hc hmin hK degrees pre.length X Y hx hy
        (fun w hw => (charged_iff_release w pre.length).mpr (charges w hw)) bits

end Pseudoforest603

namespace OrBound603
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity GraphCircuit603

lemma relative_or_bound {n : ℕ} (K G : SimpleGraph (Fin n)) (C : Circuit) (A : Finset ℕ)
    (hs : GraphInduction603.sparse G) (hf : GraphInduction603.noFour K)
    (hm : Monotone2 C) (h : detects K G C) (hc : covers C A) :
    G.edgeSet.ncard ≤ A.card + 1 := by
  have hGfour := GraphInduction603.noFour_subgraph (target_le_ambient h) hf
  exact PaidGraph603.edge_bound (Pseudoforest603.pay_core K hf) hs hGfour hm h hc

end OrBound603

namespace InputMonotonicity
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

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
    ∀ i, (gs.foldl step W1).getD i false = true →
      (gs.foldl step W2).getD i false = true := by
  induction gs with
  | nil => intro W1 W2 _ _ H; simpa using H
  | cons g gs ih =>
    intro W1 W2 hl hop H
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (step W1 g) (step W2 g) (by simp [step, hl])
      (fun g' hg' => hop g' (List.mem_cons_of_mem _ hg'))
    intro i
    simp only [step, getD_snoc, hl]
    split_ifs
    · exact op_eval_mono (hop g List.mem_cons_self) _ _ _ (fun k _ => H k)
    · exact H i

lemma eval_mono {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {x y : Fin n → Bool} (hxy : ∀ v, x v = true → y v = true)
    (h : C.eval (List.ofFn x) = true) : C.eval (List.ofFn y) = true := by
  apply fold_mono C.gates (List.ofFn x) (List.ofFn y) (by simp)
    (fun g hg => (hm g hg).1) ?_ C.output h
  intro i hi
  by_cases hin : i < n
  · simpa [List.getD_eq_getElem?_getD, hin] using
      hxy ⟨i,hin⟩ (by simpa [List.getD_eq_getElem?_getD, hin] using hi)
  · have hge : (List.ofFn x).length ≤ i := by simpa using Nat.le_of_not_gt hin
    have he : (List.ofFn x).getD i false = false := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]
    rw [he] at hi
    cases hi

end InputMonotonicity

namespace OrBound603
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open GraphCircuit603

/-- A relative OR bound: the output may accept extra ambient edges and higher prime implicants. -/
lemma relative_or_bound_of_pairs {n : ℕ}
    (K G : SimpleGraph (Fin n)) (C : Circuit) (A : Finset ℕ)
    (hs : GraphInduction603.sparse G) (hf : GraphInduction603.noFour K)
    (hm : Monotone2 C)
    (accepts : ∀ u v, G.Adj u v → C.eval (List.ofFn (pairInput u v)) = true)
    (safe : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true →
      ∃ u v, K.Adj u v ∧ x u = true ∧ x v = true)
    (hc : covers C A) : G.edgeSet.ncard ≤ A.card + 1 := by
  apply relative_or_bound K G C A hs hf hm ?_ hc
  refine ⟨?_, safe⟩
  intro x hx
  obtain ⟨u,v,huv,hu,hv⟩ := hx
  apply InputMonotonicity.eval_mono hm _ (accepts u v huv)
  intro w hw
  simp only [pairInput, decide_eq_true_eq] at hw
  rcases hw with rfl | rfl
  · exact hu
  · exact hv

lemma relative_or_bound_AO2 {n : ℕ}
    (K G : SimpleGraph (Fin n)) (C : Circuit) (A : Finset ℕ)
    (hs : GraphInduction603.sparse G) (hf : GraphInduction603.noFour K)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (accepts : ∀ u v, G.Adj u v → C.eval (List.ofFn (pairInput u v)) = true)
    (safe : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true →
      ∃ u v, K.Adj u v ∧ x u = true ∧ x v = true)
    (hc : covers C A) : G.edgeSet.ncard ≤ A.card + 1 := by
  apply relative_or_bound_of_pairs K G C A hs hf _ accepts safe hc
  intro g hg
  exact ⟨hAO.1 g hg, le_of_eq (hAO.2.2 g hg)⟩

end OrBound603

end RelativeOrBound



namespace IncidenceCoverTransport

open PEqualNP.MetaComplexity.NestedCover

lemma finite_min_cover_exists
    (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ K : Finset (Fin n), IsMinCover G K := by
  classical
  let P : ℕ → Prop := fun k => ∃ K : Finset (Fin n),
    G.IsVertexCover (K : Set (Fin n)) ∧ K.card = k
  have hex : ∃ k, P k := by
    refine ⟨n, Finset.univ, ?_, by simp⟩
    simp
  obtain ⟨K, hK, hcard⟩ := Nat.find_spec hex
  refine ⟨K, hK, ?_⟩
  intro K' hK'
  rw [hcard]
  exact Nat.find_min' hex ⟨K', hK', rfl⟩

lemma pair_embedding_injective {N n : ℕ}
    (P L : Fin N → Fin n) (hP : Function.Injective P) (hL : Function.Injective L)
    (hdis : ∀ p l, P p ≠ L l) :
    Function.Injective (fun e : Fin N × Fin N => s(P e.1, L e.2)) := by
  rintro ⟨p,l⟩ ⟨p',l'⟩ he
  rcases Sym2.eq_iff.mp he with h | h
  · exact Prod.ext (hP h.1) (hL h.2)
  · exact False.elim (hdis p l' h.1)

lemma of_deleted_cover {N n : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n)))
    (P L : Fin N → Fin n) (hP : Function.Injective P) (hL : Function.Injective L)
    (hdis : ∀ p l, P p ≠ L l)
    (hI : ∀ p l, I p l → G.Adj (P p) (L l))
    (K : Finset (Fin n))
    (hK : (G.deleteEdges (U : Set (Sym2 (Fin n)))).IsVertexCover
      (K : Set (Fin n))) :
    ∃ A B : Finset (Fin N),
      A.card + B.card ≤ K.card ∧
      (∀ p, p ∈ A ↔ P p ∈ K) ∧ (∀ l, l ∈ B ↔ L l ∈ K) ∧
      (∀ p l, I p l → p ∉ A → l ∉ B → s(P p,L l) ∈ U) ∧
      (Finset.univ.filter (fun e : Fin N × Fin N =>
        I e.1 e.2 ∧ e.1 ∉ A ∧ e.2 ∉ B)).card ≤ U.card := by
  classical
  let A := Finset.univ.filter (fun p => P p ∈ K)
  let B := Finset.univ.filter (fun l => L l ∈ K)
  have hA : ∀ p, p ∈ A ↔ P p ∈ K := by simp [A]
  have hB : ∀ l, l ∈ B ↔ L l ∈ K := by simp [B]
  have hAB : Disjoint (A.image P) (B.image L) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨l,_,he⟩ := Finset.mem_image.mp hy
    exact hdis p l he.symm
  have hsub : A.image P ∪ B.image L ⊆ K := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      exact (hA p).mp hp
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hx
      exact (hB l).mp hl
  have hsize := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hAB,
    Finset.card_image_of_injective A hP, Finset.card_image_of_injective B hL] at hsize
  have hmiss : ∀ p l, I p l → p ∉ A → l ∉ B → s(P p,L l) ∈ U := by
    intro p l hi hp hl
    by_contra hu
    have he : (G.deleteEdges (U : Set (Sym2 (Fin n)))).Adj (P p) (L l) := by
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨hI p l hi, hu⟩
    rcases hK he with hk | hk
    · exact hp ((hA p).mpr hk)
    · exact hl ((hB l).mpr hk)
  refine ⟨A,B,hsize,hA,hB,hmiss,?_⟩
  let M := Finset.univ.filter (fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ e.1 ∉ A ∧ e.2 ∉ B)
  have hMU : M.image (fun e => s(P e.1,L e.2)) ⊆ U := by
    intro e he
    obtain ⟨⟨p,l⟩,hm,rfl⟩ := Finset.mem_image.mp he
    have hm' := (Finset.mem_filter.mp hm).2
    exact hmiss p l hm'.1 hm'.2.1 hm'.2.2
  have hc := Finset.card_le_card hMU
  rwa [Finset.card_image_of_injective M (pair_embedding_injective P L hP hL hdis)] at hc

lemma of_min_deleted_cover_budget {N n t : ℕ}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (G : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n)))
    (P L : Fin N → Fin n) (hP : Function.Injective P) (hL : Function.Injective L)
    (hdis : ∀ p l, P p ≠ L l)
    (hI : ∀ p l, I p l → G.Adj (P p) (L l))
    (hbudget : ∀ K : Finset (Fin n),
      IsMinCover (G.deleteEdges (U : Set (Sym2 (Fin n)))) K → K.card ≤ t) :
    ∃ A B : Finset (Fin N), A.card + B.card ≤ t ∧
      (∀ p l, I p l → p ∉ A → l ∉ B → s(P p,L l) ∈ U) ∧
      (Finset.univ.filter (fun e : Fin N × Fin N =>
        I e.1 e.2 ∧ e.1 ∉ A ∧ e.2 ∉ B)).card ≤ U.card := by
  obtain ⟨K,hK⟩ := finite_min_cover_exists n (G.deleteEdges (U : Set (Sym2 (Fin n))))
  obtain ⟨A,B,hs,_,_,hm,hc⟩ := of_deleted_cover I G U P L hP hL hdis hI K hK.1
  exact ⟨A,B,hs.trans (hbudget K hK),hm,hc⟩

end IncidenceCoverTransport


namespace IncidenceCoverTransport

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

lemma small_residual_plane_exclusion
    {n : ℕ} (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pi li : Fin N → Fin n) (hpi : Function.Injective pi) (hli : Function.Injective li)
    (hdis : ∀ p l, pi p ≠ li l)
    (hI : ∀ p l, I p l → G.Adj (pi p) (li l))
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hfour : NoFourCycle G)
    (hbudget : ∀ K : Finset (Fin n),
      IsMinCover (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))) K →
        K.card ≤ (tops G C \ centreless G C).card)
    (hcounter : (tops G C \ centreless G C).card +
      (2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) + 1 ≤
        N + (Ustar G C).card)
    (hpaid : (Ustar G C).card ≤
      2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card)
    (hsmall : (Ustar G C).card ≤ q + 1) : False := by
  classical
  obtain ⟨A,B,hs,hm,hc⟩ := of_min_deleted_cover_budget I G (Ustar G C)
    pi li hpi hli hdis hI hbudget
  obtain ⟨_,_,hQ,_,shape⟩ := CircuitLedger.low_residual_cover_shape q N
    (tops G C \ centreless G C).card (Ustar G C).card
    (2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card)
    I hq hN hcol hunique A B hs hc hcounter (by omega) hpaid
  rcases shape with ⟨p,hA,hB⟩ | ⟨l,hA,hB⟩
  · let X := (Finset.univ.filter (I p)).image li
    have hXcard : X.card = q + 1 := by
      rw [Finset.card_image_of_injective _ hli]
      exact plane_point_degree q N I (by omega) hN hcol hunique p
    have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
    have hX : ∀ v ∈ X, G.Adj (pi p) v := by
      intro v hv
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv
      exact hI p l (Finset.mem_filter.mp hl).2
    have hstar : ∀ v ∈ X, s(pi p,v) ∈ Ustar G C := by
      intro v hv
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv
      exact hm p l (Finset.mem_filter.mp hl).2 (by simp [hA]) (by simp [hB])
    have hpen := FirstMixing.residual_pencil_penalty G C hL hT hfour (pi p)
      X hXne hX hstar
    omega
  · let X := (Finset.univ.filter (fun p => I p l)).image pi
    have hXcard : X.card = q + 1 := by
      rw [Finset.card_image_of_injective _ hpi]
      exact hcol l
    have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
    have hX : ∀ v ∈ X, G.Adj (li l) v := by
      intro v hv
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
      exact (hI p l (Finset.mem_filter.mp hp).2).symm
    have hstar : ∀ v ∈ X, s(li l,v) ∈ Ustar G C := by
      intro v hv
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
      rw [Sym2.eq_swap]
      exact hm p l (Finset.mem_filter.mp hp).2 (by simp [hA]) (by simp [hB])
    have hpen := FirstMixing.residual_pencil_penalty G C hL hT hfour (li l)
      X hXne hX hstar
    omega

end IncidenceCoverTransport




namespace PureProvider
open SimpleGraph
open scoped Classical
variable {V : Type*}

/-- A free provider is a raw input, or a pure OR of clean neighbors of one centre. -/
def Provider (K : SimpleGraph V) (U : Finset (Sym2 V)) (S : Finset V) : Prop :=
  S.card ≤ 1 ∨ ∃ c, ∀ v ∈ S, K.Adj c v ∧ s(c,v) ∉ U

/-- Acceptance by a conjunction of pure provider clauses on a two-point assignment. -/
def HitPair (Q : Finset (Finset V)) (p q : V) : Prop :=
  ∀ S ∈ Q, p ∈ S ∨ q ∈ S

lemma hitPair_swap {Q : Finset (Finset V)} {p q : V} (h : HitPair Q p q) :
    HitPair Q q p := fun S hS => (h S hS).symm

lemma bool_eq_of_ne_common (a b c : Bool) (ha : a ≠ c) (hb : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

lemma provider_monochromatic (K : SimpleGraph V) (U : Finset (Sym2 V))
    (color : V → Bool) (hbip : ∀ a b, K.Adj a b → color a ≠ color b)
    {S : Finset V} (hS : Provider K U S) {u v : V} (hu : u ∈ S) (hv : v ∈ S) :
    color u = color v := by
  rcases hS with hsmall | ⟨c,hc⟩
  · exact congrArg color (Finset.card_le_one.mp hsmall u hu v hv)
  · exact bool_eq_of_ne_common _ _ _ (hbip u c (hc u hu).1.symm)
      (hbip v c (hc v hv).1.symm)

lemma shared_endpoint_unique (K : SimpleGraph V) (U : Finset (Sym2 V))
    (Q : Finset (Finset V))
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      K.Adj a l → K.Adj b l → K.Adj a m → K.Adj b m → l = m)
    (hprovider : ∀ S ∈ Q, Provider K U S)
    (hsafe : ∀ p q, HitPair Q p q → K.Adj p q)
    {p l m : V} (he : s(p,l) ∈ U)
    (hl : HitPair Q p l) (hm : HitPair Q p m) : l = m := by
  classical
  have hn : ¬ HitPair Q p p := fun h => K.irrefl (hsafe p p h)
  obtain ⟨S,hSQ,hp⟩ : ∃ S ∈ Q, p ∉ S := by
    by_contra h
    apply hn
    intro S hS
    left
    by_contra hp
    exact h ⟨S,hS,hp⟩
  have hlS : l ∈ S := (hl S hSQ).resolve_left hp
  have hmS : m ∈ S := (hm S hSQ).resolve_left hp
  rcases hprovider S hSQ with hsmall | ⟨c,hc⟩
  · exact Finset.card_le_one.mp hsmall l hlS m hmS
  · have hpc : p ≠ c := by
      intro h
      exact (hc l hlS).2 (h ▸ he)
    exact hfour p c hpc l m (hsafe p l hl) (hc l hlS).1
      (hsafe p m hm) (hc m hmS).1

lemma cross_accepted (K : SimpleGraph V) (U : Finset (Sym2 V))
    (Q : Finset (Finset V)) (color : V → Bool)
    (hbip : ∀ a b, K.Adj a b → color a ≠ color b)
    (hprovider : ∀ S ∈ Q, Provider K U S)
    {p l q m : V} (hcol : color p = color q) (hop : color p ≠ color l)
    (hl : HitPair Q p l) (hm : HitPair Q q m) : HitPair Q p m := by
  intro S hS
  rcases hl S hS with hpS | hlS
  · exact Or.inl hpS
  · rcases hm S hS with hqS | hmS
    · have he := provider_monochromatic K U color hbip (hprovider S hS) hqS hlS
      exact False.elim (hop (hcol.trans he))
    · exact Or.inr hmS

lemma oriented_edges_unique (K : SimpleGraph V) (U : Finset (Sym2 V))
    (Q : Finset (Finset V)) (color : V → Bool)
    (hbip : ∀ a b, K.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      K.Adj a l → K.Adj b l → K.Adj a m → K.Adj b m → l = m)
    (hprovider : ∀ S ∈ Q, Provider K U S)
    (hsafe : ∀ p q, HitPair Q p q → K.Adj p q)
    {p l q m : V} (hcol : color p = color q)
    (he : s(p,l) ∈ U) (hf : s(q,m) ∈ U)
    (hl : HitPair Q p l) (hm : HitPair Q q m) : p = q ∧ l = m := by
  have hpm := cross_accepted K U Q color hbip hprovider hcol
    (hbip p l (hsafe p l hl)) hl hm
  have hlm := shared_endpoint_unique K U Q hfour hprovider hsafe he hl hpm
  subst m
  have hep : s(l,p) ∈ U := by simpa only [Sym2.eq_swap] using he
  have hpq := shared_endpoint_unique K U Q hfour hprovider hsafe hep
    (hitPair_swap hl) (hitPair_swap hm)
  exact ⟨hpq,rfl⟩

/-- A safe conjunction of pure clean providers accepts at most one residual edge.
  Only safety on two-point assignments (including singletons) is needed. -/
lemma residual_card_le_one (K : SimpleGraph V) (U : Finset (Sym2 V))
    (Q : Finset (Finset V)) (color : V → Bool)
    (hbip : ∀ a b, K.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      K.Adj a l → K.Adj b l → K.Adj a m → K.Adj b m → l = m)
    (hprovider : ∀ S ∈ Q, Provider K U S)
    (hsafe : ∀ p q, HitPair Q p q → K.Adj p q)
    (haccept : ∀ p q, s(p,q) ∈ U → HitPair Q p q) : U.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  induction e using Sym2.ind with
  | h p l =>
    induction f using Sym2.ind with
    | h q m =>
      have hl := haccept p l he
      have hm := haccept q m hf
      by_cases hc : color p = color q
      · obtain ⟨rfl,rfl⟩ := oriented_edges_unique K U Q color hbip hfour hprovider hsafe hc he hf hl hm
        rfl
      · have hcm : color p = color m :=
          bool_eq_of_ne_common _ _ _ hc (hbip m q (hsafe q m hm).symm)
        have hf' : s(m,q) ∈ U := by simpa only [Sym2.eq_swap] using hf
        obtain ⟨rfl,rfl⟩ := oriented_edges_unique K U Q color hbip hfour hprovider hsafe hcm he hf' hl (hitPair_swap hm)
        exact Sym2.eq_swap

end PureProvider


namespace PureProvider
open SimpleGraph
open scoped Classical
variable {V : Type*}

/-- The Boolean semantics of a conjunction of pure provider clauses. -/
def Hits (Q : Finset (Finset V)) (X : Set V) : Prop :=
  ∀ S ∈ Q, ∃ v ∈ S, v ∈ X

lemma singleton_clause (K : SimpleGraph V) (U : Finset (Sym2 V))
    (Q : Finset (Finset V)) (color : V → Bool)
    (hbip : ∀ a b, K.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      K.Adj a l → K.Adj b l → K.Adj a m → K.Adj b m → l = m)
    (hprovider : ∀ S ∈ Q, Provider K U S)
    (hsafe : ∀ X : Set V, Hits Q X → ∃ u ∈ X, ∃ v ∈ X, K.Adj u v)
    {p l : V} (he : s(p,l) ∈ U) (haccept : HitPair Q p l) : {p} ∈ Q := by
  classical
  by_contra hsingle
  let X : Set V := {v | v = l ∨ (color v = color p ∧ ¬ K.Adj l v)}
  have hhit : Hits Q X := by
    intro S hS
    by_cases hlS : l ∈ S
    · exact ⟨l,hlS,Or.inl rfl⟩
    have hpS : p ∈ S := (haccept S hS).resolve_right hlS
    have hnsub : ¬ (∀ v ∈ S, K.Adj l v) := by
      intro hsub
      have hsmall : ∀ v ∈ S, v = p := by
        rcases hprovider S hS with hcard | ⟨c,hc⟩
        · intro v hv
          exact Finset.card_le_one.mp hcard v hv p hpS
        · have hcl : c ≠ l := by
            intro hcl
            have hclean := (hc p hpS).2
            apply hclean
            rw [hcl]
            simpa only [Sym2.eq_swap] using he
          intro v hv
          exact hfour c l hcl v p (hc v hv).1 (hsub v hv)
            (hc p hpS).1 (hsub p hpS)
      have heq : S = {p} := by
        ext v
        simp only [Finset.mem_singleton]
        exact ⟨hsmall v,fun h => h ▸ hpS⟩
      exact hsingle (heq ▸ hS)
    obtain ⟨v,hv,hnv⟩ : ∃ v ∈ S, ¬ K.Adj l v := by
      by_contra hn
      apply hnsub
      intro v hv
      by_contra hnv
      exact hn ⟨v,hv,hnv⟩
    exact ⟨v,hv,Or.inr ⟨provider_monochromatic K U color hbip (hprovider S hS) hv hpS,hnv⟩⟩
  obtain ⟨u,hu,v,hv,huv⟩ := hsafe X hhit
  rcases hu with rfl | ⟨hu,hnlu⟩
  · rcases hv with rfl | ⟨_,hnlv⟩
    · exact K.irrefl huv
    · exact hnlv huv
  · rcases hv with rfl | ⟨hv,_⟩
    · exact hnlu huv.symm
    · exact hbip u v huv (hu.trans hv.symm)

/-- A fully safe pure-provider term accepting a residual edge is exactly that edge term. -/
lemma hits_iff_edge (K : SimpleGraph V) (U : Finset (Sym2 V))
    (Q : Finset (Finset V)) (color : V → Bool)
    (hbip : ∀ a b, K.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      K.Adj a l → K.Adj b l → K.Adj a m → K.Adj b m → l = m)
    (hprovider : ∀ S ∈ Q, Provider K U S)
    (hsafe : ∀ X : Set V, Hits Q X → ∃ u ∈ X, ∃ v ∈ X, K.Adj u v)
    {p l : V} (he : s(p,l) ∈ U) (haccept : HitPair Q p l) (X : Set V) :
    Hits Q X ↔ p ∈ X ∧ l ∈ X := by
  classical
  have hp := singleton_clause K U Q color hbip hfour hprovider hsafe he haccept
  have he' : s(l,p) ∈ U := by simpa only [Sym2.eq_swap] using he
  have hl := singleton_clause K U Q color hbip hfour hprovider hsafe he' (hitPair_swap haccept)
  constructor
  · intro h
    obtain ⟨u,hu,huX⟩ := h {p} hp
    obtain ⟨v,hv,hvX⟩ := h {l} hl
    simp only [Finset.mem_singleton] at hu hv
    exact ⟨hu ▸ huX,hv ▸ hvX⟩
  · rintro ⟨hpX,hlX⟩ S hS
    rcases haccept S hS with hpS | hlS
    · exact ⟨p,hpS,hpX⟩
    · exact ⟨l,hlS,hlX⟩

end PureProvider


namespace PureProvider
open SimpleGraph
open scoped Classical
variable {V ι : Type*}

lemma provider_mono_residual (K : SimpleGraph V) {U W : Finset (Sym2 V)}
    (hsub : W ⊆ U) {S : Finset V} (h : Provider K U S) : Provider K W S := by
  rcases h with hsmall | ⟨c,hc⟩
  · exact Or.inl hsmall
  · exact Or.inr ⟨c,fun v hv => ⟨(hc v hv).1,fun he => (hc v hv).2 (hsub he)⟩⟩

/-- A finite family of safe pure-provider conjunctions covers at most one residual edge per term.
  This is a term-count bound and asserts no conversion from circuit OR counts to term counts. -/
lemma family_residual_card_le (K : SimpleGraph V) (U : Finset (Sym2 V))
    (I : Finset ι) (W : ι → Finset (Sym2 V)) (Q : ι → Finset (Finset V))
    (color : V → Bool)
    (hbip : ∀ a b, K.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      K.Adj a l → K.Adj b l → K.Adj a m → K.Adj b m → l = m)
    (hsub : ∀ i ∈ I, W i ⊆ U)
    (hcover : ∀ e ∈ U, ∃ i ∈ I, e ∈ W i)
    (hprovider : ∀ i ∈ I, ∀ S ∈ Q i, Provider K U S)
    (hsafe : ∀ i ∈ I, ∀ p q, HitPair (Q i) p q → K.Adj p q)
    (haccept : ∀ i ∈ I, ∀ p q, s(p,q) ∈ W i → HitPair (Q i) p q) :
    U.card ≤ I.card := by
  classical
  have hsmall : ∀ i ∈ I, (W i).card ≤ 1 := by
    intro i hi
    exact residual_card_le_one K (W i) (Q i) color hbip hfour
      (fun S hS => provider_mono_residual K (hsub i hi) (hprovider i hi S hS))
      (hsafe i hi) (haccept i hi)
  calc
    U.card ≤ (I.biUnion W).card := Finset.card_le_card (by
      intro e he
      obtain ⟨i,hi,hei⟩ := hcover e he
      exact Finset.mem_biUnion.mpr ⟨i,hi,hei⟩)
    _ ≤ ∑ i ∈ I, (W i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, 1 := Finset.sum_le_sum hsmall
    _ = I.card := by simp

end PureProvider




namespace FirstMixing

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge CircuitLedger CircuitLedger.Budget

lemma residual_pencil_refined_budget
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hfour : NoFourCycle G) (p : Fin n) (X : Finset (Fin n))
    (hX : ∀ l ∈ X, G.Adj p l)
    (hstar : ∀ l ∈ X, s(p,l) ∈ Ustar G C) :
    X.card ≤ (orN G C \ lam G C).card +
      ((junk G C).filter fun j => gateVal n C j (pairInput p p) = false).card +
        (centreless G C).card := by
  classical
  have hraw := false_or_centreless_served_budget G C hL.1 hT hfour p X hX hstar
  have hrest := other_served_mixing_count G C hL hT hfour p X hX hstar
  have hsubset : falseServed G C p X ∪ centrelessServed G C p X ⊆ X :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsplit := Finset.card_sdiff_add_card_eq_card hsubset
  have hmixsplit := Finset.card_sdiff_add_card_eq_card (mixing_subset_extra G C)
  omega

lemma tight_residual_pencil_shape
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hfour : NoFourCycle G) (p : Fin n) (X : Finset (Fin n))
    (hX : ∀ l ∈ X, G.Adj p l)
    (hstar : ∀ l ∈ X, s(p,l) ∈ Ustar G C)
    (htight : 2 * (centreless G C).card + (junk G C).card +
      (orN G C \ lam G C).card = X.card + 1) :
    (centreless G C).card +
      ((junk G C).filter fun j => gateVal n C j (pairInput p p) = true).card ≤ 1 := by
  classical
  have href := residual_pencil_refined_budget G C hL hT hfour p X hX hstar
  let J := (junk G C).filter fun j => gateVal n C j (pairInput p p) = false
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (show J ⊆ junk G C from Finset.filter_subset _ _)
  have heq : junk G C \ J =
      (junk G C).filter (fun j => gateVal n C j (pairInput p p) = true) := by
    ext j
    simp only [J, Finset.mem_sdiff, Finset.mem_filter]
    cases gateVal n C j (pairInput p p) <;> simp
  rw [heq] at hsplit
  change X.card ≤ (orN G C \ lam G C).card + J.card + (centreless G C).card at href
  omega

end FirstMixing


namespace ActualTopCentres

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open CircuitLedger CircuitLedger.Budget

lemma singleton_side_of_top
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfour : NoFourCycle G)
    {a : ℕ} (ha : a ∈ tops G C \ centreless G C) :
    ∃ c : Fin n, side (n := n) C a 0 = {c} ∨ side (n := n) C a 1 = {c} := by
  classical
  obtain ⟨hat,haz⟩ := Finset.mem_sdiff.mp ha
  have hn : side (n := n) C a 0 ≠ ∅ ∧ side (n := n) C a 1 ≠ ∅ := by
    simpa only [centreless, Finset.mem_filter, hat, true_and, not_or] using haz
  have hsmall : (side (n := n) C a 0).card ≤ 1 ∨ (side (n := n) C a 1).card ≤ 1 := by
    by_cases h0 : (side (n := n) C a 0).card ≤ 1
    · exact Or.inl h0
    · right
      have hex : ∃ u ∈ side (n := n) C a 0, ∃ v ∈ side (n := n) C a 0, u ≠ v := by
        by_contra he
        push Not at he
        exact h0 (Finset.card_le_one.mpr he)
      obtain ⟨u,hu,v,hv,huv⟩ := hex
      apply le_trans (Finset.card_le_card ?_) (hfour u v huv)
      intro w hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        topAdj hAO hat hu hw, topAdj hAO hat hv hw⟩
  rcases hsmall with h0 | h1
  · have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hn.1)
    obtain ⟨c,hc⟩ := Finset.card_eq_one.mp (show (side (n := n) C a 0).card = 1 by omega)
    exact ⟨c,Or.inl hc⟩
  · have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hn.2)
    obtain ⟨c,hc⟩ := Finset.card_eq_one.mp (show (side (n := n) C a 1).card = 1 by omega)
    exact ⟨c,Or.inr hc⟩

lemma selected_centres_cover
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a}) :
    (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).IsVertexCover
      (((tops G C \ centreless G C).attach.image c) : Set (Fin n)) := by
  classical
  intro u v huv
  rw [SimpleGraph.deleteEdges_adj] at huv
  have he : s(u,v) ∈ starEdges G C := by
    by_contra hn
    exact huv.2 (Finset.mem_sdiff.mpr ⟨by simpa using huv.1,hn⟩)
  simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product] at he
  obtain ⟨a,ha,⟨x,y⟩,⟨hx,hy⟩,he⟩ := he
  have hat : a ∈ tops G C \ centreless G C := by
    refine Finset.mem_sdiff.mpr ⟨ha,?_⟩
    intro hz
    have hz' := (Finset.mem_filter.mp hz).2
    rcases hz' with hz' | hz'
    · rw [hz'] at hx
      exact Finset.notMem_empty _ hx
    · rw [hz'] at hy
      exact Finset.notMem_empty _ hy
  let aa : {a // a ∈ tops G C \ centreless G C} := ⟨a,hat⟩
  have hmem : c aa ∈ (tops G C \ centreless G C).attach.image c :=
    Finset.mem_image.mpr ⟨aa,Finset.mem_attach _ _,rfl⟩
  have hxy : x ∈ (tops G C \ centreless G C).attach.image c ∨
      y ∈ (tops G C \ centreless G C).attach.image c := by
    rcases hc aa with hs | hs
    · have hx' : x = c aa := Finset.mem_singleton.mp (hs ▸ hx)
      exact Or.inl (hx' ▸ hmem)
    · have hy' : y = c aa := Finset.mem_singleton.mp (hs ▸ hy)
      exact Or.inr (hy' ▸ hmem)
  rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact hxy
  · exact hxy.symm

lemma exists_selected_centres
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hfour : NoFourCycle G) :
    ∃ c : {a // a ∈ tops G C \ centreless G C} → Fin n,
      (∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a}) ∧
      ((tops G C \ centreless G C).attach.image c).card ≤
        (tops G C \ centreless G C).card ∧
      (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).IsVertexCover
        (((tops G C \ centreless G C).attach.image c) : Set (Fin n)) := by
  classical
  let c : {a // a ∈ tops G C \ centreless G C} → Fin n :=
    fun a => Classical.choose (singleton_side_of_top G C hAO hfour a.property)
  have hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a} :=
    fun a => Classical.choose_spec (singleton_side_of_top G C hAO hfour a.property)
  refine ⟨c,hc,?_,selected_centres_cover G C c hc⟩
  exact le_trans (Finset.card_image_le) (by simp)

end ActualTopCentres




namespace ProviderGrid
open SimpleGraph
open scoped Classical
variable {V : Type*}

/-- A two-vertex support carrying one graph edge. -/
def EdgeSupport (K : SimpleGraph V) (S : Finset V) : Prop :=
  S.card = 2 ∧ ∀ u ∈ S, ∀ v ∈ S, u ≠ v → K.Adj u v

lemma common_part_card_le_one {S A B : Finset V}
    (hSA : S ⊆ A) (hSB : S ⊆ B) (hA : A.card = 2) (hB : B.card = 2)
    (hne : A ≠ B) : S.card ≤ 1 := by
  by_contra hn
  have ha : S = A := Finset.eq_of_subset_of_card_le hSA (by omega)
  have hb : S = B := Finset.eq_of_subset_of_card_le hSB (by omega)
  exact hne (ha.symm.trans hb)

lemma union_component_nonempty {R S T : Finset V}
    (hcard : (R ∪ T).card = (S ∪ T).card) (hne : R ∪ T ≠ S ∪ T) :
    R.Nonempty := by
  classical
  by_contra hn
  have hz : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  have hsub : R ∪ T ⊆ S ∪ T := by simp only [hz, Finset.empty_union]; exact Finset.subset_union_right
  exact hne (Finset.eq_of_subset_of_card_le hsub (Nat.le_of_eq hcard.symm))

lemma edgeSupport_pair_adj (K : SimpleGraph V) {a b : V}
    (h : EdgeSupport K {a,b}) : K.Adj a b := by
  classical
  have hab : a ≠ b := by
    intro heq
    have hc := h.1
    simp only [heq, Finset.insert_eq_of_mem (Finset.mem_singleton_self b), Finset.card_singleton] at hc
    omega
  exact h.2 a (by simp) b (by simp) hab

/-- Four distinct adjacent cells in a grid of two-element unions force a four-cycle. -/
lemma two_element_union_grid_impossible (K : SimpleGraph V)
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      K.Adj a l → K.Adj b l → K.Adj a m → K.Adj b m → l = m)
    (R0 R1 B0 B1 : Finset V)
    (h00 : EdgeSupport K (R0 ∪ B0)) (h01 : EdgeSupport K (R0 ∪ B1))
    (h10 : EdgeSupport K (R1 ∪ B0)) (h11 : EdgeSupport K (R1 ∪ B1))
    (hr0 : R0 ∪ B0 ≠ R0 ∪ B1) (hr1 : R1 ∪ B0 ≠ R1 ∪ B1)
    (hc0 : R0 ∪ B0 ≠ R1 ∪ B0) (hc1 : R0 ∪ B1 ≠ R1 ∪ B1) : False := by
  classical
  have r0small := common_part_card_le_one (S := R0)
    Finset.subset_union_left Finset.subset_union_left h00.1 h01.1 hr0
  have r1small := common_part_card_le_one (S := R1)
    Finset.subset_union_left Finset.subset_union_left h10.1 h11.1 hr1
  have b0small := common_part_card_le_one (S := B0)
    Finset.subset_union_right Finset.subset_union_right h00.1 h10.1 hc0
  have b1small := common_part_card_le_one (S := B1)
    Finset.subset_union_right Finset.subset_union_right h01.1 h11.1 hc1
  have r0pos := Finset.card_pos.mpr (union_component_nonempty (h00.1.trans h10.1.symm) hc0)
  have r1pos := Finset.card_pos.mpr (union_component_nonempty (h10.1.trans h00.1.symm) (Ne.symm hc0))
  have b0ne : B0.Nonempty := union_component_nonempty (R := B0) (S := B1) (T := R0) (by simpa only [Finset.union_comm] using h00.1.trans h01.1.symm)
    (by simpa only [Finset.union_comm] using hr0)
  have b1ne : B1.Nonempty := union_component_nonempty (R := B1) (S := B0) (T := R0) (by simpa only [Finset.union_comm] using h01.1.trans h00.1.symm)
    (by simpa only [Finset.union_comm] using Ne.symm hr0)
  have b0pos := Finset.card_pos.mpr b0ne
  have b1pos := Finset.card_pos.mpr b1ne
  obtain ⟨a0,ha0⟩ := Finset.card_eq_one.mp (show R0.card = 1 by omega)
  obtain ⟨a1,ha1⟩ := Finset.card_eq_one.mp (show R1.card = 1 by omega)
  obtain ⟨b0,hb0⟩ := Finset.card_eq_one.mp (show B0.card = 1 by omega)
  obtain ⟨b1,hb1⟩ := Finset.card_eq_one.mp (show B1.card = 1 by omega)
  have haa : a0 ≠ a1 := by
    intro heq
    exact hc0 (by rw [ha0,ha1,heq])
  have hbb : b0 ≠ b1 := by
    intro heq
    exact hr0 (by rw [hb0,hb1,heq])
  have h00' : K.Adj a0 b0 := edgeSupport_pair_adj K (by simpa [ha0,hb0] using h00)
  have h01' : K.Adj a0 b1 := edgeSupport_pair_adj K (by simpa [ha0,hb1] using h01)
  have h10' : K.Adj a1 b0 := edgeSupport_pair_adj K (by simpa [ha1,hb0] using h10)
  have h11' : K.Adj a1 b1 := edgeSupport_pair_adj K (by simpa [ha1,hb1] using h11)
  exact hbb (hfour a0 a1 haa b0 b1 h00' h10' h01' h11')

end ProviderGrid


namespace PureProvider
open SimpleGraph
open scoped Classical
variable {V : Type*}

/-- Variables occurring as full singleton clauses, not merely after restricting an assignment. -/
noncomputable def units (Q : Finset (Finset V)) : Finset V :=
  Q.biUnion fun S => if S.card = 1 then S else ∅

lemma mem_units {Q : Finset (Finset V)} {v : V} : v ∈ units Q ↔ {v} ∈ Q := by
  classical
  constructor
  · intro hv
    obtain ⟨S,hS,hv⟩ := Finset.mem_biUnion.mp hv
    split_ifs at hv with hc
    · obtain ⟨w,rfl⟩ := Finset.card_eq_one.mp hc
      have hvw : v = w := Finset.mem_singleton.mp hv
      simpa only [hvw] using hS
    · exact (Finset.notMem_empty v hv).elim
  · intro hv
    apply Finset.mem_biUnion.mpr
    exact ⟨{v},hv,by simp⟩

lemma units_union (A B : Finset (Finset V)) : units (A ∪ B) = units A ∪ units B := by
  classical
  ext v
  simp only [mem_units,Finset.mem_union]

lemma hits_union {A B : Finset (Finset V)} {X : Set V} :
    Hits (A ∪ B) X ↔ Hits A X ∧ Hits B X := by
  constructor
  · intro h
    exact ⟨fun S hS => h S (Finset.mem_union_left B hS),
      fun S hS => h S (Finset.mem_union_right A hS)⟩
  · rintro ⟨hA,hB⟩ S hS
    rcases Finset.mem_union.mp hS with ha | hb
    · exact hA S ha
    · exact hB S hb

lemma units_eq_pair (K : SimpleGraph V) (U : Finset (Sym2 V))
    (Q : Finset (Finset V)) (color : V → Bool)
    (hbip : ∀ a b, K.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      K.Adj a l → K.Adj b l → K.Adj a m → K.Adj b m → l = m)
    (hprovider : ∀ S ∈ Q, Provider K U S)
    (hsafe : ∀ X : Set V, Hits Q X → ∃ u ∈ X, ∃ v ∈ X, K.Adj u v)
    {p l : V} (he : s(p,l) ∈ U) (ha : HitPair Q p l) : units Q = {p,l} := by
  classical
  have hp := singleton_clause K U Q color hbip hfour hprovider hsafe he ha
  have he' : s(l,p) ∈ U := by simpa only [Sym2.eq_swap] using he
  have hl := singleton_clause K U Q color hbip hfour hprovider hsafe he' (hitPair_swap ha)
  ext v
  rw [mem_units]
  constructor
  · intro hv
    have h := ha {v} hv
    simpa only [Finset.mem_singleton,Finset.mem_insert,eq_comm] using h
  · intro hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hp
    · exact (Finset.mem_singleton.mp hv) ▸ hl

lemma pair_support_eq_sym2 {p q r s : V} (hne : p ≠ q)
    (h : ({p,q} : Finset V) = {r,s}) : s(p,q) = s(r,s) := by
  classical
  have hp : p = r ∨ p = s := by
    have hmem : p ∈ ({r,s} : Finset V) := h ▸ (by simp)
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hmem
  have hq : q = r ∨ q = s := by
    have hmem : q ∈ ({r,s} : Finset V) := h ▸ (by simp)
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hmem
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact (hne rfl).elim
  · rfl
  · exact Sym2.eq_swap
  · exact (hne rfl).elim

lemma edgeSupport_pair (K : SimpleGraph V) {p q : V} (h : K.Adj p q) :
    ProviderGrid.EdgeSupport K {p,q} := by
  classical
  refine ⟨by simp [h.ne],?_⟩
  intro a ha b hb hab
  simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hab rfl).elim
  · exact h
  · exact h.symm
  · exact (hab rfl).elim

/-- Four safe provider-CNF grid terms cannot accept four distinct residual edges. -/
lemma no_four_grid_edges (K : SimpleGraph V) (U : Finset (Sym2 V))
    (E : Finset (Finset V)) (A B : Fin 2 → Finset (Finset V)) (color : V → Bool)
    (hbip : ∀ a b, K.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      K.Adj a l → K.Adj b l → K.Adj a m → K.Adj b m → l = m)
    (hU : ∀ p q, s(p,q) ∈ U → K.Adj p q)
    (hprovider : ∀ i j, ∀ S ∈ E ∪ A i ∪ B j, Provider K U S)
    (hsafe : ∀ X : Set V,
      Hits E X ∧ (Hits (A 0) X ∨ Hits (A 1) X) ∧
        (Hits (B 0) X ∨ Hits (B 1) X) → ∃ u ∈ X, ∃ v ∈ X, K.Adj u v)
    (p q : Fin 2 → Fin 2 → V)
    (he : ∀ i j, s(p i j,q i j) ∈ U)
    (ha : ∀ i j, HitPair (E ∪ A i ∪ B j) (p i j) (q i j))
    (hinj : Function.Injective (fun ij : Fin 2 × Fin 2 => s(p ij.1 ij.2,q ij.1 ij.2))) : False := by
  classical
  have hsafe' : ∀ i j, ∀ X : Set V, Hits (E ∪ A i ∪ B j) X →
      ∃ u ∈ X, ∃ v ∈ X, K.Adj u v := by
    intro i j X h
    obtain ⟨⟨hE,hA⟩,hB⟩ := hits_union.mp h |>.imp_left hits_union.mp
    apply hsafe X
    refine ⟨hE,?_,?_⟩
    · fin_cases i <;> simp_all
    · fin_cases j <;> simp_all
  have heq : ∀ i j, (units E ∪ units (A i)) ∪ units (B j) = {p i j,q i j} := by
    intro i j
    simpa only [units_union] using units_eq_pair K U (E ∪ A i ∪ B j) color hbip hfour
      (hprovider i j) (hsafe' i j) (he i j) (ha i j)
  have hedge : ∀ i j, ProviderGrid.EdgeSupport K ((units E ∪ units (A i)) ∪ units (B j)) := by
    intro i j
    rw [heq i j]
    exact edgeSupport_pair K (hU _ _ (he i j))
  have hne : ∀ i j k l : Fin 2, (i,j) ≠ (k,l) →
      (units E ∪ units (A i)) ∪ units (B j) ≠ (units E ∪ units (A k)) ∪ units (B l) := by
    intro i j k l hij hij'
    have hs : ({p i j,q i j} : Finset V) = {p k l,q k l} := by
      rw [← heq i j,← heq k l]
      exact hij'
    exact hij (hinj (pair_support_eq_sym2 (hU _ _ (he i j)).ne hs))
  exact ProviderGrid.two_element_union_grid_impossible K hfour
    (units E ∪ units (A 0)) (units E ∪ units (A 1)) (units (B 0)) (units (B 1))
    (hedge 0 0) (hedge 0 1) (hedge 1 0) (hedge 1 1)
    (hne 0 0 0 1 (by decide)) (hne 1 0 1 1 (by decide))
    (hne 0 0 1 0 (by decide)) (hne 0 1 1 1 (by decide))

end PureProvider


namespace PureProvider
open SimpleGraph
open scoped Classical
variable {V : Type*}

lemma hitPair_union {A B : Finset (Finset V)} {p q : V} :
    HitPair (A ∪ B) p q ↔ HitPair A p q ∧ HitPair B p q := by
  constructor
  · intro h
    exact ⟨fun S hS => h S (Finset.mem_union_left B hS),
      fun S hS => h S (Finset.mem_union_right A hS)⟩
  · rintro ⟨hA,hB⟩ S hS
    rcases Finset.mem_union.mp hS with ha | hb
    · exact hA S ha
    · exact hB S hb

lemma safe_pairs_of_safe (K : SimpleGraph V) (Q : Finset (Finset V))
    (hsafe : ∀ X : Set V, Hits Q X → ∃ u ∈ X, ∃ v ∈ X, K.Adj u v)
    {p q : V} (ha : HitPair Q p q) : K.Adj p q := by
  obtain ⟨u,hu,v,hv,huv⟩ := hsafe {p,q} (by
    intro S hS
    rcases ha S hS with hp | hq
    · exact ⟨p,hp,by simp⟩
    · exact ⟨q,hq,by simp⟩)
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact (K.irrefl huv).elim
  · exact huv
  · exact huv.symm
  · exact (K.irrefl huv).elim

lemma accepted_edges_unique (K : SimpleGraph V) (U : Finset (Sym2 V))
    (Q : Finset (Finset V)) (color : V → Bool)
    (hbip : ∀ a b, K.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      K.Adj a l → K.Adj b l → K.Adj a m → K.Adj b m → l = m)
    (hprovider : ∀ S ∈ Q, Provider K U S)
    (hsafe : ∀ p q, HitPair Q p q → K.Adj p q)
    {p l q m : V} (he : s(p,l) ∈ U) (hf : s(q,m) ∈ U)
    (ha : HitPair Q p l) (hb : HitPair Q q m) : s(p,l) = s(q,m) := by
  by_cases hc : color p = color q
  · obtain ⟨rfl,rfl⟩ := oriented_edges_unique K U Q color hbip hfour hprovider hsafe hc he hf ha hb
    rfl
  · have hcm : color p = color m := bool_eq_of_ne_common _ _ _ hc (hbip m q (hsafe q m hb).symm)
    have hf' : s(m,q) ∈ U := by simpa only [Sym2.eq_swap] using hf
    obtain ⟨rfl,rfl⟩ := oriented_edges_unique K U Q color hbip hfour hprovider hsafe hcm he hf' ha (hitPair_swap hb)
    exact Sym2.eq_swap

/-- A fully safe two-by-two grid of pure-provider CNF terms accepts at most three residual edges. -/
lemma grid_residual_card_le_three (K : SimpleGraph V) (U : Finset (Sym2 V))
    (E : Finset (Finset V)) (A B : Fin 2 → Finset (Finset V)) (color : V → Bool)
    (hbip : ∀ a b, K.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l m,
      K.Adj a l → K.Adj b l → K.Adj a m → K.Adj b m → l = m)
    (hU : ∀ p q, s(p,q) ∈ U → K.Adj p q)
    (hprovider : ∀ i j, ∀ S ∈ E ∪ A i ∪ B j, Provider K U S)
    (hsafe : ∀ X : Set V,
      Hits E X ∧ (Hits (A 0) X ∨ Hits (A 1) X) ∧
        (Hits (B 0) X ∨ Hits (B 1) X) → ∃ u ∈ X, ∃ v ∈ X, K.Adj u v)
    (haccept : ∀ p q, s(p,q) ∈ U →
      HitPair E p q ∧ (HitPair (A 0) p q ∨ HitPair (A 1) p q) ∧
        (HitPair (B 0) p q ∨ HitPair (B 1) p q)) : U.card ≤ 3 := by
  classical
  have hsafe' : ∀ i j, ∀ X : Set V, Hits (E ∪ A i ∪ B j) X →
      ∃ u ∈ X, ∃ v ∈ X, K.Adj u v := by
    intro i j X h
    obtain ⟨⟨hE,hA⟩,hB⟩ := hits_union.mp h |>.imp_left hits_union.mp
    apply hsafe X
    refine ⟨hE,?_,?_⟩
    · fin_cases i <;> simp_all
    · fin_cases j <;> simp_all
  have hsel : ∀ e : {e // e ∈ U}, ∃ ij : Fin 2 × Fin 2, ∃ p q,
      e.val = s(p,q) ∧ HitPair (E ∪ A ij.1 ∪ B ij.2) p q := by
    rintro ⟨e,he⟩
    induction e using Sym2.ind with
    | h p q =>
      obtain ⟨hE,hA,hB⟩ := haccept p q he
      rcases hA with hA | hA <;> rcases hB with hB | hB
      · exact ⟨(0,0),p,q,rfl,hitPair_union.mpr ⟨hitPair_union.mpr ⟨hE,hA⟩,hB⟩⟩
      · exact ⟨(0,1),p,q,rfl,hitPair_union.mpr ⟨hitPair_union.mpr ⟨hE,hA⟩,hB⟩⟩
      · exact ⟨(1,0),p,q,rfl,hitPair_union.mpr ⟨hitPair_union.mpr ⟨hE,hA⟩,hB⟩⟩
      · exact ⟨(1,1),p,q,rfl,hitPair_union.mpr ⟨hitPair_union.mpr ⟨hE,hA⟩,hB⟩⟩
  choose lab p q heq ha using hsel
  have he : ∀ e, s(p e,q e) ∈ U := fun e => heq e ▸ e.property
  have hinj : Function.Injective lab := by
    intro e f h
    apply Subtype.ext
    rw [heq e,heq f]
    apply accepted_edges_unique K U (E ∪ A (lab e).1 ∪ B (lab e).2) color hbip hfour
      (hprovider _ _) (fun p q h => safe_pairs_of_safe K _ (hsafe' _ _) h) (he e) (he f) (ha e)
    simpa only [h] using ha f
  by_contra hlarge
  have hsurj : Function.Surjective lab := by
    by_contra hn
    have hlt := Fintype.card_lt_of_injective_not_surjective lab hinj hn
    have hcard : Fintype.card (Fin 2 × Fin 2) = 4 := by decide
    rw [Fintype.card_coe,hcard] at hlt
    omega
  choose g hg using hsurj
  let p' : Fin 2 → Fin 2 → V := fun i j => p (g (i,j))
  let q' : Fin 2 → Fin 2 → V := fun i j => q (g (i,j))
  apply no_four_grid_edges K U E A B color hbip hfour hU hprovider hsafe p' q'
    (fun i j => he (g (i,j))) ?_ ?_
  · intro i j
    have h := ha (g (i,j))
    simpa only [hg,p',q'] using h
  · intro ij kl h
    have hgf : g ij = g kl := by
      apply Subtype.ext
      rw [heq (g ij),heq (g kl)]
      exact h
    have hlabel := congrArg lab hgf
    simpa only [hg] using hlabel

lemma hits_pair_iff {Q : Finset (Finset V)} {p q : V} :
    Hits Q ({p,q} : Set V) ↔ HitPair Q p q := by
  constructor
  · intro h S hS
    obtain ⟨v,hv,hvp⟩ := h S hS
    rcases hvp with rfl | hvq
    · exact Or.inl hv
    · exact Or.inr (hvq ▸ hv)
  · intro h S hS
    rcases h S hS with hp | hq
    · exact ⟨p,hp,by simp⟩
    · exact ⟨q,hq,by simp⟩

/-- An indexed family of pair-safe pure-provider terms covers at most one residual edge per term. -/
lemma cnf_family_residual_card_le (K : SimpleGraph V) (U : Finset (Sym2 V))
    {m : ℕ} (Q : Fin m → Finset (Finset V)) (color : V → Bool)
    (hbip : ∀ a b, K.Adj a b → color a ≠ color b)
    (hfour : ∀ a b, a ≠ b → ∀ l k,
      K.Adj a l → K.Adj b l → K.Adj a k → K.Adj b k → l = k)
    (hprovider : ∀ i, ∀ S ∈ Q i, Provider K U S)
    (hsafe : ∀ i, ∀ p q, HitPair (Q i) p q → K.Adj p q)
    (haccept : ∀ p q, s(p,q) ∈ U → ∃ i, HitPair (Q i) p q) : U.card ≤ m := by
  classical
  have hsel : ∀ e : {e // e ∈ U}, ∃ i : Fin m, ∃ p q,
      e.val = s(p,q) ∧ HitPair (Q i) p q := by
    rintro ⟨e,he⟩
    induction e using Sym2.ind with
    | h p q =>
      obtain ⟨i,hi⟩ := haccept p q he
      exact ⟨i,p,q,rfl,hi⟩
  choose lab p q heq ha using hsel
  have he : ∀ e, s(p e,q e) ∈ U := fun e => heq e ▸ e.property
  have hinj : Function.Injective lab := by
    intro e f h
    apply Subtype.ext
    rw [heq e,heq f]
    apply accepted_edges_unique K U (Q (lab e)) color hbip hfour (hprovider _) (hsafe _)
      (he e) (he f) (ha e)
    simpa only [h] using ha f
  simpa only [Fintype.card_coe,Fintype.card_fin] using Fintype.card_le_of_injective lab hinj

end PureProvider


namespace ActualTopCentres

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

lemma low_residual_selected_centres_rigid
    {n : ℕ} (q N P : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (pi li : Fin N → Fin n) (hpi : Function.Injective pi) (hli : Function.Injective li)
    (hdis : ∀ p l, pi p ≠ li l)
    (hI : ∀ p l, I p l → G.Adj (pi p) (li l))
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hcounter : (tops G C \ centreless G C).card + P + 1 ≤ N + (Ustar G C).card)
    (hpaid : (Ustar G C).card ≤ P)
    (hsmall : (Ustar G C).card < 2 * q) :
    Function.Injective c ∧
      ((tops G C \ centreless G C).attach.image c).card =
        (tops G C \ centreless G C).card ∧
      (tops G C \ centreless G C).card + 1 = N ∧ P = (Ustar G C).card ∧
      ((∃ p, (tops G C \ centreless G C).attach.image c =
          (Finset.univ.erase p).image pi) ∨
       ∃ l, (tops G C \ centreless G C).attach.image c =
          (Finset.univ.erase l).image li) := by
  classical
  let T := tops G C \ centreless G C
  let K := T.attach.image c
  have hKle : K.card ≤ T.card := Finset.card_image_le.trans_eq Finset.card_attach
  have hKcover := selected_centres_cover G C c hc
  obtain ⟨A,B,hsize,hA,hB,_,hmissing⟩ :=
    IncidenceCoverTransport.of_deleted_cover I G (Ustar G C) pi li hpi hli hdis hI K hKcover
  have hsizeT : A.card + B.card ≤ T.card := hsize.trans hKle
  obtain ⟨ht,hab,hPu,_,hshape⟩ := CircuitLedger.low_residual_cover_shape
    q N T.card (Ustar G C).card P I hq hN hcol hunique A B hsizeT hmissing
    hcounter hsmall hpaid
  have hKcard : K.card = T.card := by omega
  have hinj : Function.Injective c := by
    have hh : (T.attach.image c).card = T.attach.card := by simpa only [Finset.card_attach] using hKcard
    have hi := Finset.card_image_iff.mp hh
    intro a b heq
    exact hi (Finset.mem_attach T a) (Finset.mem_attach T b) heq
  have hABdis : Disjoint (A.image pi) (B.image li) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨l,_,he⟩ := Finset.mem_image.mp hy
    exact hdis p l he.symm
  have hsub : A.image pi ∪ B.image li ⊆ K := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
      exact (hA p).mp hp
    · obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hx
      exact (hB l).mp hl
  have heq : K = A.image pi ∪ B.image li := by
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_union_of_disjoint hABdis,
      Finset.card_image_of_injective A hpi, Finset.card_image_of_injective B hli,
      hab, hKcard]
  refine ⟨hinj,hKcard,ht,hPu,?_⟩
  change (∃ p, K = (Finset.univ.erase p).image pi) ∨
    ∃ l, K = (Finset.univ.erase l).image li
  rcases hshape with ⟨p,hAp,hB0⟩ | ⟨l,hA0,hBl⟩
  · left
    refine ⟨p,?_⟩
    simpa only [hAp,hB0,Finset.image_empty,Finset.union_empty] using heq
  · right
    refine ⟨l,?_⟩
    simpa only [hA0,hBl,Finset.image_empty,Finset.empty_union] using heq

end ActualTopCentres

namespace ActualTopCentres

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

lemma plane_embeddings_monochromatic
    {n : ℕ} (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (G : SimpleGraph (Fin n)) (pi li : Fin N → Fin n)
    (hI : ∀ p l, I p l → G.Adj (pi p) (li l))
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b) :
    (∀ p r, color (pi p) = color (pi r)) ∧
      (∀ l k, color (li l) = color (li k)) := by
  classical
  have hbool : ∀ a b c : Bool, a ≠ c → b ≠ c → a = b := by decide
  have hp : ∀ p r, color (pi p) = color (pi r) := by
    intro p r
    by_cases hpr : p = r
    · rw [hpr]
    obtain ⟨l,hl,_⟩ := hunique p r hpr
    exact hbool _ _ _ (hbip _ _ (hI p l hl.1)) (hbip _ _ (hI r l hl.2))
  refine ⟨hp,?_⟩
  intro l k
  obtain ⟨p,hpI⟩ := Finset.card_pos.mp
    (show 0 < (Finset.univ.filter (fun p => I p l)).card by rw [hcol]; omega)
  obtain ⟨r,hrI⟩ := Finset.card_pos.mp
    (show 0 < (Finset.univ.filter (fun p => I p k)).card by rw [hcol]; omega)
  have hpl := hI p l (Finset.mem_filter.mp hpI).2
  have hrk := hI r k (Finset.mem_filter.mp hrI).2
  apply hbool _ _ (color (pi p)) (hbip _ _ hpl.symm)
  simpa only [hp r p] using hbip _ _ hrk.symm

lemma no_double_singleton_of_monochromatic_choices
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C)
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hcard : 2 ≤ (tops G C \ centreless G C).card)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hmono : ∀ d : {a // a ∈ tops G C \ centreless G C} → Fin n,
      (∀ a, side (n := n) C a.val 0 = {d a} ∨ side (n := n) C a.val 1 = {d a}) →
      ∀ a b, color (d a) = color (d b))
    {a : ℕ} (ha : a ∈ tops G C \ centreless G C) {x y : Fin n}
    (hx : side (n := n) C a 0 = {x}) (hy : side (n := n) C a 1 = {y}) : False := by
  classical
  let aa : {a // a ∈ tops G C \ centreless G C} := ⟨a,ha⟩
  obtain ⟨b,hb,hba⟩ := Finset.exists_mem_ne (show 1 < (tops G C \ centreless G C).card by omega) a
  let bb : {a // a ∈ tops G C \ centreless G C} := ⟨b,hb⟩
  have hne : bb ≠ aa := fun he => hba (congrArg Subtype.val he)
  let d := Function.update c aa x
  let e := Function.update c aa y
  have hd : ∀ k, side (n := n) C k.val 0 = {d k} ∨ side (n := n) C k.val 1 = {d k} := by
    intro k
    by_cases hk : k = aa
    · subst k
      exact Or.inl (by simpa only [d,Function.update_self] using hx)
    · simpa only [d,Function.update_of_ne hk] using hc k
  have he : ∀ k, side (n := n) C k.val 0 = {e k} ∨ side (n := n) C k.val 1 = {e k} := by
    intro k
    by_cases hk : k = aa
    · subst k
      exact Or.inr (by simpa only [e,Function.update_self] using hy)
    · simpa only [e,Function.update_of_ne hk] using hc k
  have hdx : color x = color (c bb) := by
    simpa only [d,Function.update_self,Function.update_of_ne hne] using hmono d hd aa bb
  have hey : color y = color (c bb) := by
    simpa only [e,Function.update_self,Function.update_of_ne hne] using hmono e he aa bb
  have hxy := CircuitLedger.Budget.topAdj hAO (Finset.mem_sdiff.mp ha).1
    (show x ∈ side (n := n) C a 0 by rw [hx]; simp)
    (show y ∈ side (n := n) C a 1 by rw [hy]; simp)
  exact hbip x y hxy (hdx.trans hey.symm)

lemma low_residual_no_double_singleton
    {n : ℕ} (q N P : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (hfour : NoFourCycle G)
    (pi li : Fin N → Fin n) (hpi : Function.Injective pi) (hli : Function.Injective li)
    (hdis : ∀ p l, pi p ≠ li l)
    (hI : ∀ p l, I p l → G.Adj (pi p) (li l))
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hcounter : (tops G C \ centreless G C).card + P + 1 ≤ N + (Ustar G C).card)
    (hpaid : (Ustar G C).card ≤ P)
    (hsmall : (Ustar G C).card < 2 * q)
    {a : ℕ} (ha : a ∈ tops G C \ centreless G C) {x y : Fin n}
    (hx : side (n := n) C a 0 = {x}) (hy : side (n := n) C a 1 = {y}) : False := by
  classical
  obtain ⟨c,hc,_,_⟩ := exists_selected_centres G C hAO hfour
  have hr := low_residual_selected_centres_rigid q N P I hq hN hcol hunique
    G C pi li hpi hli hdis hI c hc hcounter hpaid hsmall
  have hcard : 2 ≤ (tops G C \ centreless G C).card := by
    have ht := hr.2.2.1
    have hq2 : 4 ≤ q ^ 2 := by nlinarith
    omega
  obtain ⟨hpc,hlc⟩ := plane_embeddings_monochromatic q N I hcol hunique G pi li hI color hbip
  apply no_double_singleton_of_monochromatic_choices G C hAO color hbip hcard c hc ?_ ha hx hy
  intro d hd b k
  have shape := (low_residual_selected_centres_rigid q N P I hq hN hcol hunique
    G C pi li hpi hli hdis hI d hd hcounter hpaid hsmall).2.2.2.2
  have hb : d b ∈ (tops G C \ centreless G C).attach.image d :=
    Finset.mem_image.mpr ⟨b,Finset.mem_attach _ _,rfl⟩
  have hk : d k ∈ (tops G C \ centreless G C).attach.image d :=
    Finset.mem_image.mpr ⟨k,Finset.mem_attach _ _,rfl⟩
  rcases shape with ⟨p,heq⟩ | ⟨l,heq⟩
  · rw [heq] at hb hk
    obtain ⟨u,_,hu⟩ := Finset.mem_image.mp hb
    obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hk
    rw [← hu,← hv]
    exact hpc u v
  · rw [heq] at hb hk
    obtain ⟨u,_,hu⟩ := Finset.mem_image.mp hb
    obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hk
    rw [← hu,← hv]
    exact hlc u v

end ActualTopCentres


namespace ActualTopCentres

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open CircuitLedger CircuitLedger.Budget

lemma selected_leaf_colour
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hno : ∀ a : {a // a ∈ tops G C \ centreless G C}, ¬ ((side (n := n) C a.val 0).card = 1 ∧
      (side (n := n) C a.val 1).card = 1))
    (a : {a // a ∈ tops G C \ centreless G C}) (b : Fin 2)
    (hunit : (side (n := n) C a.val (1-b)).card = 1)
    {v : Fin n} (hv : v ∈ side (n := n) C a.val b) : color v ≠ color (c a) := by
  have ha := (Finset.mem_sdiff.mp a.property).1
  fin_cases b
  · change (side (n := n) C a.val 1).card = 1 at hunit
    rcases hc a with h0 | h1
    · exact False.elim (hno a ⟨by simp [h0],hunit⟩)
    · have hcm : c a ∈ side (n := n) C a.val 1 := by rw [h1]; simp
      exact hbip _ _ (topAdj hAO ha hv hcm)
  · change (side (n := n) C a.val 0).card = 1 at hunit
    rcases hc a with h0 | h1
    · have hcm : c a ∈ side (n := n) C a.val 0 := by rw [h0]; simp
      exact hbip _ _ (topAdj hAO ha hcm hv).symm
    · exact False.elim (hno a ⟨hunit,by simp [h1]⟩)

lemma lambda_raw_colour
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hno : ∀ a : {a // a ∈ tops G C \ centreless G C}, ¬ ((side (n := n) C a.val 0).card = 1 ∧
      (side (n := n) C a.val 1).card = 1))
    (b : Bool) (hcolor : ∀ a, color (c a) = b) :
    ∀ h ∈ lam G C, ∀ v ∈ orIn n C (n+h), color v ≠ b := by
  classical
  intro h hh v hv
  obtain ⟨_,_,_,a,ha,k,hunit,hr⟩ := Finset.mem_filter.mp hh
  have hvside : v ∈ side (n := n) C a k :=
    reach_mem_orIn v ((orReaches_reach h _ hr).1.trans (mem_orIn_reach v hv))
  have hother : (side (n := n) C a (1-k)).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hsides : (side (n := n) C a 0).Nonempty ∧ (side (n := n) C a 1).Nonempty := by
    fin_cases k
    · exact ⟨⟨v,hvside⟩,hother⟩
    · exact ⟨hother,⟨v,hvside⟩⟩
  have hat : a ∈ tops G C \ centreless G C := by
    refine Finset.mem_sdiff.mpr ⟨ha,?_⟩
    intro hz
    rcases (Finset.mem_filter.mp hz).2 with h0 | h1
    · exact hsides.1.ne_empty h0
    · exact hsides.2.ne_empty h1
  let aa : {a // a ∈ tops G C \ centreless G C} := ⟨a,hat⟩
  have H := selected_leaf_colour G C hAO color hbip c hc hno aa k hunit hvside
  simpa only [hcolor aa] using H

end ActualTopCentres




namespace TwoPaidOr
open PureProvider

variable {V : Type*} [DecidableEq V]

def GoodQ (P : Finset V → Prop) (Q : Finset (Finset V)) : Prop := ∀ S ∈ Q, P S

def guard (b : Bool) (p : Prop) : Prop := b = true → p

def twoOrExpr (E A0 A1 B0 B1 : Finset (Finset V))
    (e0 e1 d0 d1 : Bool) (X : Set V) : Prop :=
  Hits E X ∧ guard d0 (Hits A0 X ∨ Hits A1 X) ∧
    guard d1 ((Hits B0 X ∧ guard e0 (Hits A0 X ∨ Hits A1 X)) ∨
      (Hits B1 X ∧ guard e1 (Hits A0 X ∨ Hits A1 X)))

def Ternary (P : Finset V → Prop) (F : Set V → Prop) : Prop :=
  ∃ Q0 Q1 Q2 : Finset (Finset V), GoodQ P Q0 ∧ GoodQ P Q1 ∧ GoodQ P Q2 ∧
    ∀ X, F X ↔ Hits Q0 X ∨ Hits Q1 X ∨ Hits Q2 X

def Grid (P : Finset V → Prop) (F : Set V → Prop) : Prop :=
  ∃ E A0 A1 B0 B1 : Finset (Finset V),
    GoodQ P E ∧ GoodQ P A0 ∧ GoodQ P A1 ∧ GoodQ P B0 ∧ GoodQ P B1 ∧
    ∀ X, F X ↔ Hits E X ∧ (Hits A0 X ∨ Hits A1 X) ∧ (Hits B0 X ∨ Hits B1 X)

lemma goodQ_union {P : Finset V → Prop} {Q R : Finset (Finset V)}
    (hQ : GoodQ P Q) (hR : GoodQ P R) : GoodQ P (Q ∪ R) := by
  intro S hS
  rcases Finset.mem_union.mp hS with h | h
  · exact hQ S h
  · exact hR S h

lemma hits_union (Q R : Finset (Finset V)) (X : Set V) :
    Hits (Q ∪ R) X ↔ Hits Q X ∧ Hits R X := by
  constructor
  · intro h
    exact ⟨fun S hS => h S (Finset.mem_union_left _ hS),
      fun S hS => h S (Finset.mem_union_right _ hS)⟩
  · rintro ⟨hQ,hR⟩ S hS
    rcases Finset.mem_union.mp hS with h | h
    · exact hQ S h
    · exact hR S h

lemma hits_false (X : Set V) : ¬ Hits ({∅} : Finset (Finset V)) X := by
  simp [Hits]

end TwoPaidOr

namespace TwoPaidOr
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PureProvider CircuitLedger.Budget

noncomputable def input {n : ℕ} (X : Set (Fin n)) : Fin n → Bool := by
  classical
  exact fun v => decide (v ∈ X)

lemma input_true {n : ℕ} (X : Set (Fin n)) (v : Fin n) :
    input X v = true ↔ v ∈ X := by
  classical
  simp [input]

def wireTrue {n : ℕ} (C : Circuit) (w : ℕ) (X : Set (Fin n)) : Prop :=
  val C (List.ofFn (input X)) w = true

def Flags {n : ℕ} (C : Circuit) (F : Finset ℕ) (X : Set (Fin n)) : Prop :=
  ∀ j ∈ F, wireTrue C (n+j) X

lemma flags_union {n : ℕ} (C : Circuit) (F J : Finset ℕ) (X : Set (Fin n)) :
    Flags C (F ∪ J) X ↔ Flags C F X ∧ Flags C J X := by
  constructor
  · intro h
    exact ⟨fun j hj => h j (Finset.mem_union_left _ hj),
      fun j hj => h j (Finset.mem_union_right _ hj)⟩
  · rintro ⟨hF,hJ⟩ j hj
    rcases Finset.mem_union.mp hj with h | h
    · exact hF j h
    · exact hJ j h

lemma wire_normal_form
    {n : ℕ} (C : Circuit) (P : Finset (Fin n) → Prop) (paid : Finset ℕ)
    (ao : IsAO2 n C) (hsmall : ∀ S, S.card ≤ 1 → P S)
    (hpure : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or → j ∉ paid →
      ∃ S, P S ∧ ∀ X : Set (Fin n), wireTrue C (n+j) X ↔ Hits {S} X) :
    ∀ w : ℕ, ∃ Q : Finset (Finset (Fin n)), ∃ F : Finset ℕ,
      GoodQ P Q ∧ F ⊆ paid ∧ (∀ j ∈ F, n+j ≤ w) ∧
      ∀ X : Set (Fin n), wireTrue C w X ↔ Hits Q X ∧ Flags C F X := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hw : w < n
    · let v : Fin n := ⟨w,hw⟩
      refine ⟨{{v}},∅,?_,by simp,by simp,?_⟩
      · intro S hS
        have hs : S = {v} := Finset.mem_singleton.mp hS
        subst S
        exact hsmall _ (by simp)
      · intro X
        unfold wireTrue
        rw [val_input (n := n) (by simp) hw]
        simp [List.getD_eq_getElem?_getD, hw, Hits, Flags, input, v]
    · by_cases hge : n + C.gates.length ≤ w
      · refine ⟨{∅},∅,?_,by simp,by simp,?_⟩
        · intro S hS
          have hs : S = ∅ := Finset.mem_singleton.mp hS
          subst S
          exact hsmall _ (by simp)
        · intro X
          unfold wireTrue
          rw [val_ge (n := n) (by simp) hge]
          simp [Hits,Flags]
      · obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
        have hj : j < C.gates.length := by omega
        rcases ao.1 _ (gateAt_mem hj) with hand | hor
        · have h0 := opndBound ao hj (0 : Fin 2)
          have h1 := opndBound ao hj (1 : Fin 2)
          obtain ⟨Q0,F0,hQ0,hF0,hB0,hV0⟩ := ih (opnd C j 0) h0
          obtain ⟨Q1,F1,hQ1,hF1,hB1,hV1⟩ := ih (opnd C j 1) h1
          refine ⟨Q0 ∪ Q1,F0 ∪ F1,goodQ_union hQ0 hQ1,
            Finset.union_subset hF0 hF1,?_,?_⟩
          · intro k hk
            rcases Finset.mem_union.mp hk with h | h
            · have := hB0 k h; omega
            · have := hB1 k h; omega
          · intro X
            have hv : wireTrue C (n+j) X ↔
                wireTrue C (opnd C j 0) X ∧ wireTrue C (opnd C j 1) X :=
              andValBoth ao hj hand (input X)
            rw [hv,hV0 X,hV1 X,hits_union,flags_union]
            tauto
        · by_cases hpaid : j ∈ paid
          · refine ⟨∅,{j},by simp [GoodQ],by simpa using hpaid,?_,?_⟩
            · intro k hk
              have : k = j := Finset.mem_singleton.mp hk
              omega
            · intro X
              simp [Hits,Flags]
          · obtain ⟨S,hS,hsem⟩ := hpure j hj hor hpaid
            refine ⟨{S},∅,?_,by simp,by simp,?_⟩
            · intro T hT
              simpa only [Finset.mem_singleton.mp hT] using hS
            · intro X
              simpa [Flags] using hsem X

end TwoPaidOr

namespace TwoPaidOr
open PureProvider

variable {V : Type*} [DecidableEq V]

/-- With two paid ORs, a conjunction of provider clauses has either at most
  three pure-CNF choices or the Cartesian product of two binary choices. -/
lemma two_or_algebra {P : Finset V → Prop}
    (hP : P ∅) (E A0 A1 B0 B1 : Finset (Finset V))
    (hE : GoodQ P E) (hA0 : GoodQ P A0) (hA1 : GoodQ P A1)
    (hB0 : GoodQ P B0) (hB1 : GoodQ P B1)
    (e0 e1 d0 d1 : Bool) :
    Ternary P (twoOrExpr E A0 A1 B0 B1 e0 e1 d0 d1) ∨
      Grid P (twoOrExpr E A0 A1 B0 B1 e0 e1 d0 d1) := by
  have hz : GoodQ P ({∅} : Finset (Finset V)) := by
    intro S hS
    have hS' : S = ∅ := Finset.mem_singleton.mp hS
    subst S
    exact hP
  cases d0 with
  | false =>
    cases d1 with
    | false =>
      left
      refine ⟨E, {∅}, {∅}, hE, hz, hz, ?_⟩
      intro X
      cases e0 <;> cases e1 <;> simp [twoOrExpr, guard, hits_false]
    | true =>
      cases e0 with
      | false =>
        cases e1 with
        | false =>
          left
          refine ⟨E ∪ B0, E ∪ B1, {∅}, goodQ_union hE hB0,
            goodQ_union hE hB1, hz, ?_⟩
          intro X
          simp [twoOrExpr, guard, hits_union, hits_false] <;> tauto
        | true =>
          left
          refine ⟨E ∪ B0, (E ∪ B1) ∪ A0, (E ∪ B1) ∪ A1,
            goodQ_union hE hB0, goodQ_union (goodQ_union hE hB1) hA0,
            goodQ_union (goodQ_union hE hB1) hA1, ?_⟩
          intro X
          simp [twoOrExpr, guard, hits_union] <;> tauto
      | true =>
        cases e1 with
        | false =>
          left
          refine ⟨E ∪ B1, (E ∪ B0) ∪ A0, (E ∪ B0) ∪ A1,
            goodQ_union hE hB1, goodQ_union (goodQ_union hE hB0) hA0,
            goodQ_union (goodQ_union hE hB0) hA1, ?_⟩
          intro X
          simp [twoOrExpr, guard, hits_union] <;> tauto
        | true =>
          right
          refine ⟨E, A0, A1, B0, B1, hE, hA0, hA1, hB0, hB1, ?_⟩
          intro X
          simp [twoOrExpr, guard] <;> tauto
  | true =>
    cases d1 with
    | false =>
      left
      refine ⟨E ∪ A0, E ∪ A1, {∅}, goodQ_union hE hA0,
        goodQ_union hE hA1, hz, ?_⟩
      intro X
      cases e0 <;> cases e1 <;>
        simp [twoOrExpr, guard, hits_union, hits_false] <;> tauto
    | true =>
      right
      refine ⟨E, A0, A1, B0, B1, hE, hA0, hA1, hB0, hB1, ?_⟩
      intro X
      cases e0 <;> cases e1 <;> simp [twoOrExpr, guard] <;> tauto

end TwoPaidOr

namespace TwoPaidOr
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover

/-- At most two effective paid OR gates occupy two ordered slots. Missing
  slots are placed outside the circuit and therefore require no gate hypothesis. -/
lemma paid_slots (C : Circuit) (B : Finset ℕ) (hcard : B.card ≤ 2)
    (hvalid : ∀ j ∈ B, j < C.gates.length ∧ (gateAt C j).op = .or) :
    ∃ a b : ℕ, a < b ∧ B ⊆ {a, b} ∧
      (a < C.gates.length → (gateAt C a).op = .or) ∧
      (b < C.gates.length → (gateAt C b).op = .or) := by
  by_cases hz : B.card = 0
  · have hB : B = ∅ := Finset.card_eq_zero.mp hz
    subst B
    refine ⟨C.gates.length, C.gates.length + 1, by omega, by simp, ?_, ?_⟩ <;>
      intro h <;> omega
  by_cases hs : B.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hs
    have ha := hvalid a (by simp)
    refine ⟨a, C.gates.length, ha.1, by simp, fun _ => ha.2, ?_⟩
    intro h
    omega
  have ht : B.card = 2 := by omega
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp ht
  have ha := hvalid a (by simp)
  have hb := hvalid b (by simp)
  rcases lt_or_gt_of_ne hab with hab | hba
  · exact ⟨a, b, hab, Finset.Subset.refl _, fun _ => ha.2, fun _ => hb.2⟩
  · refine ⟨b, a, hba, ?_, fun _ => hb.2, fun _ => ha.2⟩
    intro j hj
    simpa only [Finset.mem_insert, Finset.mem_singleton, or_comm] using hj

end TwoPaidOr

namespace TwoPaidOr
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PureProvider CircuitLedger.Budget

lemma good_false {n : ℕ} {P : Finset (Fin n) → Prop} (hP : P ∅) :
    GoodQ P ({∅} : Finset (Finset (Fin n))) := by
  intro S hS
  simpa only [Finset.mem_singleton.mp hS] using hP

lemma wire_or {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or) (X : Set (Fin n)) :
    wireTrue C (n+j) X ↔ wireTrue C (opnd C j 0) X ∨ wireTrue C (opnd C j 1) X := by
  change val C _ _ = true ↔ _
  rw [val_or (n := n) (by simp) hj hor]
  constructor
  · rintro ⟨w,hw,_,hv⟩
    obtain ⟨b,hb⟩ := inputsAsOpnd ao hj hw
    fin_cases b
    · exact Or.inl (by simpa [wireTrue,hb,opnd] using hv)
    · exact Or.inr (by simpa [wireTrue,hb,opnd] using hv)
  · rintro (h | h)
    · exact ⟨opnd C j 0,opndMem ao hj 0,opndBound ao hj 0,h⟩
    · exact ⟨opnd C j 1,opndMem ao hj 1,opndBound ao hj 1,h⟩

lemma flags_singleton {n : ℕ} (C : Circuit) {F : Finset ℕ} {a : ℕ}
    (hF : F ⊆ {a}) (X : Set (Fin n)) :
    Flags C F X ↔ guard (decide (a ∈ F)) (wireTrue C (n+a) X) := by
  simp only [guard,decide_eq_true_eq]
  constructor
  · intro h ha
    exact h a ha
  · intro h k hk
    have heq : k = a := Finset.mem_singleton.mp (hF hk)
    subst k
    exact h hk

lemma flags_two {n : ℕ} (C : Circuit) {F : Finset ℕ} {a b : ℕ}
    (hF : F ⊆ {a,b}) (X : Set (Fin n)) :
    Flags C F X ↔ guard (decide (a ∈ F)) (wireTrue C (n+a) X) ∧
      guard (decide (b ∈ F)) (wireTrue C (n+b) X) := by
  simp only [guard,decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨fun ha => h a ha,fun hb => h b hb⟩
  · rintro ⟨ha,hb⟩ k hk
    have hmem := hF hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · exact ha hk
    · exact hb hk

lemma first_slot_form
    {n : ℕ} (C : Circuit) (P : Finset (Fin n) → Prop) (a b : ℕ)
    (ao : IsAO2 n C) (hab : a < b) (hsmall : ∀ S, S.card ≤ 1 → P S)
    (haor : a < C.gates.length → (gateAt C a).op = GateOp.or)
    (hpure : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or → j ∉ ({a,b} : Finset ℕ) →
      ∃ S, P S ∧ ∀ X : Set (Fin n), wireTrue C (n+j) X ↔ Hits {S} X) :
    ∃ A0 A1 : Finset (Finset (Fin n)), GoodQ P A0 ∧ GoodQ P A1 ∧
      ∀ X, wireTrue C (n+a) X ↔ Hits A0 X ∨ Hits A1 X := by
  classical
  by_cases ha : a < C.gates.length
  · have operand (d : Fin 2) : ∃ Q : Finset (Finset (Fin n)), GoodQ P Q ∧
        ∀ X, wireTrue C (opnd C a d) X ↔ Hits Q X := by
      obtain ⟨Q,F,hQ,hF,hbd,hsem⟩ := wire_normal_form C P {a,b} ao hsmall hpure (opnd C a d)
      have hbound := opndBound ao ha d
      have hempty : F = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        have hmem := hF hk
        have hkb := hbd k hk
        simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
        rcases hmem with rfl | rfl <;> omega
      exact ⟨Q,hQ,fun X => by simpa [hempty,Flags] using hsem X⟩
    obtain ⟨A0,hA0,h0⟩ := operand 0
    obtain ⟨A1,hA1,h1⟩ := operand 1
    refine ⟨A0,A1,hA0,hA1,?_⟩
    intro X
    rw [wire_or ao ha (haor ha),h0 X,h1 X]
  · have hfalse := good_false (hsmall ∅ (by simp))
    refine ⟨{∅},{∅},hfalse,hfalse,?_⟩
    intro X
    unfold wireTrue
    rw [val_ge (n := n) (by simp) (by omega)]
    simp [Hits]

lemma second_slot_form
    {n : ℕ} (C : Circuit) (P : Finset (Fin n) → Prop) (a b : ℕ)
    (ao : IsAO2 n C) (hsmall : ∀ S, S.card ≤ 1 → P S)
    (hbor : b < C.gates.length → (gateAt C b).op = GateOp.or)
    (hpure : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or → j ∉ ({a,b} : Finset ℕ) →
      ∃ S, P S ∧ ∀ X : Set (Fin n), wireTrue C (n+j) X ↔ Hits {S} X) :
    ∃ B0 B1 : Finset (Finset (Fin n)), ∃ e0 e1 : Bool, GoodQ P B0 ∧ GoodQ P B1 ∧
      ∀ X, wireTrue C (n+b) X ↔
        (Hits B0 X ∧ guard e0 (wireTrue C (n+a) X)) ∨
        (Hits B1 X ∧ guard e1 (wireTrue C (n+a) X)) := by
  classical
  by_cases hb : b < C.gates.length
  · have operand (d : Fin 2) : ∃ Q : Finset (Finset (Fin n)), ∃ e : Bool, GoodQ P Q ∧
        ∀ X, wireTrue C (opnd C b d) X ↔ Hits Q X ∧ guard e (wireTrue C (n+a) X) := by
      obtain ⟨Q,F,hQ,hF,hbd,hsem⟩ := wire_normal_form C P {a,b} ao hsmall hpure (opnd C b d)
      have hbound := opndBound ao hb d
      have hsub : F ⊆ {a} := by
        intro k hk
        have hmem := hF hk
        have hkb := hbd k hk
        simp only [Finset.mem_insert,Finset.mem_singleton] at hmem
        rcases hmem with rfl | rfl
        · simp
        · omega
      refine ⟨Q,decide (a ∈ F),hQ,?_⟩
      intro X
      rw [hsem X,flags_singleton C hsub X]
    obtain ⟨B0,e0,hB0,h0⟩ := operand 0
    obtain ⟨B1,e1,hB1,h1⟩ := operand 1
    refine ⟨B0,B1,e0,e1,hB0,hB1,?_⟩
    intro X
    rw [wire_or ao hb (hbor hb),h0 X,h1 X]
  · have hfalse := good_false (hsmall ∅ (by simp))
    refine ⟨{∅},{∅},false,false,hfalse,hfalse,?_⟩
    intro X
    unfold wireTrue
    rw [val_ge (n := n) (by simp) (by omega)]
    simp [Hits,guard]

lemma two_slot_expression
    {n : ℕ} (C : Circuit) (P : Finset (Fin n) → Prop) (a b : ℕ)
    (ao : IsAO2 n C) (hab : a < b) (hsmall : ∀ S, S.card ≤ 1 → P S)
    (haor : a < C.gates.length → (gateAt C a).op = GateOp.or)
    (hbor : b < C.gates.length → (gateAt C b).op = GateOp.or)
    (hpure : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or → j ∉ ({a,b} : Finset ℕ) →
      ∃ S, P S ∧ ∀ X : Set (Fin n), wireTrue C (n+j) X ↔ Hits {S} X) :
    ∃ E A0 A1 B0 B1 : Finset (Finset (Fin n)), ∃ e0 e1 d0 d1 : Bool,
      GoodQ P E ∧ GoodQ P A0 ∧ GoodQ P A1 ∧ GoodQ P B0 ∧ GoodQ P B1 ∧
      ∀ X, wireTrue C C.output X ↔ twoOrExpr E A0 A1 B0 B1 e0 e1 d0 d1 X := by
  classical
  obtain ⟨A0,A1,hA0,hA1,hA⟩ := first_slot_form C P a b ao hab hsmall haor hpure
  obtain ⟨B0,B1,e0,e1,hB0,hB1,hB⟩ := second_slot_form C P a b ao hsmall hbor hpure
  obtain ⟨E,F,hE,hF,_,hV⟩ := wire_normal_form C P {a,b} ao hsmall hpure C.output
  refine ⟨E,A0,A1,B0,B1,e0,e1,decide (a ∈ F),decide (b ∈ F),hE,hA0,hA1,hB0,hB1,?_⟩
  intro X
  rw [hV X,flags_two C hF X,hB X,hA X]
  rfl

lemma two_slot_normal_form
    {n : ℕ} (C : Circuit) (P : Finset (Fin n) → Prop) (a b : ℕ)
    (ao : IsAO2 n C) (hab : a < b) (hsmall : ∀ S, S.card ≤ 1 → P S)
    (haor : a < C.gates.length → (gateAt C a).op = GateOp.or)
    (hbor : b < C.gates.length → (gateAt C b).op = GateOp.or)
    (hpure : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or → j ∉ ({a,b} : Finset ℕ) →
      ∃ S, P S ∧ ∀ X : Set (Fin n), wireTrue C (n+j) X ↔ Hits {S} X) :
    Ternary P (wireTrue C C.output) ∨ Grid P (wireTrue C C.output) := by
  obtain ⟨E,A0,A1,B0,B1,e0,e1,d0,d1,hE,hA0,hA1,hB0,hB1,hsem⟩ :=
    two_slot_expression C P a b ao hab hsmall haor hbor hpure
  rcases two_or_algebra (hsmall ∅ (by simp)) E A0 A1 B0 B1 hE hA0 hA1 hB0 hB1 e0 e1 d0 d1 with h | h
  · obtain ⟨Q0,Q1,Q2,h0,h1,h2,hQ⟩ := h
    exact Or.inl ⟨Q0,Q1,Q2,h0,h1,h2,fun X => (hsem X).trans (hQ X)⟩
  · obtain ⟨E',A0',A1',B0',B1',hE',hA0',hA1',hB0',hB1',hQ⟩ := h
    exact Or.inr ⟨E',A0',A1',B0',B1',hE',hA0',hA1',hB0',hB1',fun X => (hsem X).trans (hQ X)⟩

end TwoPaidOr

namespace TwoPaidOr
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PureProvider CircuitLedger.Budget

lemma at_most_two_normal_form
    {n : ℕ} (C : Circuit) (P : Finset (Fin n) → Prop) (paid : Finset ℕ)
    (ao : IsAO2 n C) (hcard : paid.card ≤ 2) (hsmall : ∀ S, S.card ≤ 1 → P S)
    (hpure : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or → j ∉ paid →
      ∃ S, P S ∧ ∀ X : Set (Fin n), wireTrue C (n+j) X ↔ Hits {S} X) :
    Ternary P (wireTrue C C.output) ∨ Grid P (wireTrue C C.output) := by
  classical
  let B := paid.filter fun j => j < C.gates.length ∧ (gateAt C j).op = GateOp.or
  have hBcard : B.card ≤ 2 := (Finset.card_filter_le _ _).trans hcard
  have hBvalid : ∀ j ∈ B, j < C.gates.length ∧ (gateAt C j).op = GateOp.or := by
    intro j hj
    exact (Finset.mem_filter.mp hj).2
  obtain ⟨a,b,hab,hBsub,haor,hbor⟩ := paid_slots C B hBcard hBvalid
  apply two_slot_normal_form C P a b ao hab hsmall haor hbor
  intro j hj hor hnot
  apply hpure j hj hor
  intro hjpaid
  exact hnot (hBsub (Finset.mem_filter.mpr ⟨hjpaid,hj,hor⟩))

/-- Every OR outside the paid set must have the displayed pure provider semantics.
  This premise is explicit; membership in lambda alone does not supply it. -/
lemma pure_provider_two_paid_normal_form
    {n : ℕ} (K : SimpleGraph (Fin n)) (U : Finset (Sym2 (Fin n)))
    (C : Circuit) (paid : Finset ℕ) (ao : IsAO2 n C) (hcard : paid.card ≤ 2)
    (hpure : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or → j ∉ paid →
      ∃ S : Finset (Fin n), Provider K U S ∧
        ∀ x : Fin n → Bool, gateVal n C j x = true ↔ ∃ v ∈ S, x v = true) :
    Ternary (Provider K U) (wireTrue C C.output) ∨
      Grid (Provider K U) (wireTrue C C.output) := by
  apply at_most_two_normal_form C (Provider K U) paid ao hcard
    (fun _ hS => Or.inl hS)
  intro j hj hor hn
  obtain ⟨S,hS,hsem⟩ := hpure j hj hor hn
  refine ⟨S,hS,?_⟩
  intro X
  simpa [wireTrue,gateVal,val,Hits,input] using hsem (input X)

lemma input_pair {n : ℕ} (p l : Fin n) : input ({p,l} : Set (Fin n)) = pairInput p l := by
  classical
  funext v
  simp [input,pairInput]

lemma wire_output {n : ℕ} (C : Circuit) (X : Set (Fin n)) :
    wireTrue C C.output X ↔ C.eval (List.ofFn (input X)) = true := Iff.rfl

end TwoPaidOr


namespace TwoPaidOr

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover PureProvider CircuitLedger.Budget

lemma two_paid_residual_card_le_three
    {n : ℕ} (K : SimpleGraph (Fin n)) [DecidableRel K.Adj]
    (U : Finset (Sym2 (Fin n))) (C : Circuit) (paid : Finset ℕ)
    (ao : IsAO2 n C) (hcard : paid.card ≤ 2)
    (color : Fin n → Bool) (hbip : ∀ u v, K.Adj u v → color u ≠ color v)
    (hfour : NoFourCycle K)
    (hpure : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or → j ∉ paid →
      ∃ S : Finset (Fin n), Provider K U S ∧
        ∀ x : Fin n → Bool, gateVal n C j x = true ↔ ∃ v ∈ S, x v = true)
    (hsafe : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true →
      ∃ u v, K.Adj u v ∧ x u = true ∧ x v = true)
    (haccept : ∀ p l, s(p,l) ∈ U → C.eval (List.ofFn (pairInput p l)) = true) :
    U.card ≤ 3 := by
  have hf : ∀ X : Set (Fin n), wireTrue C C.output X →
      ∃ u ∈ X, ∃ v ∈ X, K.Adj u v := by
    intro X hx
    obtain ⟨u,v,huv,hu,hv⟩ := hsafe (input X) ((wire_output C X).mp hx)
    exact ⟨u,(input_true X u).mp hu,v,(input_true X v).mp hv,huv⟩
  have hpair : ∀ p l, wireTrue C C.output ({p,l} : Set (Fin n)) → K.Adj p l := by
    intro p l h
    obtain ⟨u,hu,v,hv,huv⟩ := hf _ h
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact False.elim (K.irrefl huv)
    · exact huv
    · exact huv.symm
    · exact False.elim (K.irrefl huv)
  have hacc : ∀ p l, s(p,l) ∈ U → wireTrue C C.output ({p,l} : Set (Fin n)) := by
    intro p l he
    rw [wire_output,input_pair]
    exact haccept p l he
  have h4 : ∀ a b, a ≠ b → ∀ l m,
      K.Adj a l → K.Adj b l → K.Adj a m → K.Adj b m → l = m := by
    intro a b hab l m hal hbl ham hbm
    apply Finset.card_le_one.mp (hfour a b hab) l ?_ m ?_
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hal,hbl⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ham,hbm⟩
  rcases pure_provider_two_paid_normal_form K U C paid ao hcard hpure with hT | hG
  · obtain ⟨Q0,Q1,Q2,h0,h1,h2,hsem⟩ := hT
    let Q : Fin 3 → Finset (Finset (Fin n)) := ![Q0,Q1,Q2]
    have hgood : ∀ i, GoodQ (Provider K U) (Q i) := by
      intro i
      fin_cases i
      · exact h0
      · exact h1
      · exact h2
    have hout : ∀ i X, Hits (Q i) X → wireTrue C C.output X := by
      intro i X h
      apply (hsem X).mpr
      fin_cases i
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    apply cnf_family_residual_card_le K U Q color hbip h4 hgood
      (fun i p l h => hpair p l (hout i _ (hits_pair_iff.mpr h)))
    intro p l he
    rcases (hsem _).mp (hacc p l he) with h | h | h
    · exact ⟨0,hits_pair_iff.mp h⟩
    · exact ⟨1,hits_pair_iff.mp h⟩
    · exact ⟨2,hits_pair_iff.mp h⟩
  · obtain ⟨E,A0,A1,B0,B1,hE,hA0,hA1,hB0,hB1,hsem⟩ := hG
    let A : Fin 2 → Finset (Finset (Fin n)) := ![A0,A1]
    let B : Fin 2 → Finset (Finset (Fin n)) := ![B0,B1]
    have hA : ∀ i, GoodQ (Provider K U) (A i) := by
      intro i
      fin_cases i
      · exact hA0
      · exact hA1
    have hB : ∀ i, GoodQ (Provider K U) (B i) := by
      intro i
      fin_cases i
      · exact hB0
      · exact hB1
    apply grid_residual_card_le_three K U E A B color hbip h4
      (fun p l he => hpair p l (hacc p l he))
    · letI : DecidableEq (Fin n) := fun a b => Classical.propDecidable (a = b)
      intro i j
      exact goodQ_union (goodQ_union hE (hA i)) (hB j)
    · intro X h
      exact hf X ((hsem X).mpr h)
    · intro p l he
      have h := (hsem _).mp (hacc p l he)
      simpa only [A,B,Matrix.cons_val_zero,Matrix.cons_val_one,hits_pair_iff] using h

end TwoPaidOr


namespace MissingCentreMixing

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge
open CircuitLedger CircuitLedger.Budget FirstMixing

lemma singleton_operand_mixing
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ} (ha : a ∈ tops G C)
    (b : Fin 2) {c p l : Fin n} (hside : side (n := n) C a b = {c})
    (hcp : c ≠ p) (hcl : c ≠ l) (hv : gateVal n C a (pairInput p l) = true) :
    ∃ m ∈ mixing G C, (orIn n C (n+m)).Nonempty ∧
      (∀ u ∈ orIn n C (n+m), u = c) ∧
      Relation.ReflTransGen (OrStep n C) (opnd C a b) (n+m) := by
  obtain ⟨hlen,hop,_⟩ := topData ha
  have hb := (andValOperands hAO hlen hop (pairInput p l)).mp hv b
  have hex : ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j := by
    rcases operandSupport hAO hT hlen hop hb with ⟨u,hu,hup | hul⟩ | ⟨j,hj,hr,_⟩
    · have huc : u = c := Finset.mem_singleton.mp (hside ▸ hu)
      exact (hcp (huc.symm.trans hup)).elim
    · have huc : u = c := Finset.mem_singleton.mp (hside ▸ hu)
      exact (hcl (huc.symm.trans hul)).elim
    · exact ⟨j,hj,hr⟩
  obtain ⟨j,hj,hr⟩ := hex
  have hn : (side (n := n) C a b).Nonempty := by rw [hside]; simp
  obtain ⟨m,hm,hraw,hpath,_⟩ := first_mixing hAO hj _ hn (orReaches_reach j _ hr).1
  refine ⟨m,hm,hraw,?_,hpath⟩
  intro u hu
  have hua : u ∈ side (n := n) C a b :=
    reach_mem_orIn u (hpath.trans (mem_orIn_reach u hu))
  exact Finset.mem_singleton.mp (hside ▸ hua)

lemma pencil_of_point_mixing
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ} (ha : a ∈ tops G C)
    (b : Fin 2) {c p l : Fin n} (hside : side (n := n) C a b = {c})
    (hcp : c ≠ p) (hleaf : (side (n := n) C a (1-b)).Nonempty)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (hccol : color c = color p) (hlcol : color l ≠ color p)
    (hmcol : ∀ m ∈ mixing G C, ∀ u ∈ orIn n C (n+m), color u = color p)
    (hv : gateVal n C a (pairInput p l) = true) :
    ∃ m ∈ mixing G C, PencilAt G C m l := by
  have hleafcol : ∀ u ∈ side (n := n) C a (1-b), color u ≠ color p := by
    intro u hu he
    have hcu := (SimpleGraph.deleteEdges_adj.mp
      (cleanAdj hAO ha b (show c ∈ side (n := n) C a b by rw [hside]; simp) hu)).1
    exact hbip c u hcu (hccol.trans he.symm)
  obtain ⟨hlen,hop,_⟩ := topData ha
  have hvleaf := (andValOperands hAO hlen hop (pairInput p l)).mp hv (1-b)
  have hlraw : l ∈ side (n := n) C a (1-b) := by
    rcases operandSupport hAO hT hlen hop hvleaf with ⟨u,hu,hup | hul⟩ | ⟨j,hj,hr,_⟩
    · subst u
      exact (hleafcol p hu rfl).elim
    · simpa only [hul] using hu
    · obtain ⟨m,hm,hraw,hpath,_⟩ :=
        first_mixing hAO hj _ hleaf (orReaches_reach j _ hr).1
      obtain ⟨u,hu⟩ := hraw
      have hua : u ∈ side (n := n) C a (1-b) :=
        reach_mem_orIn u (hpath.trans (mem_orIn_reach u hu))
      exact (hleafcol u hua (hmcol m hm u hu)).elim
  have hcl : c ≠ l := by
    intro he
    exact hlcol (he ▸ hccol)
  obtain ⟨m,hm,hraw,_,hpath⟩ := singleton_operand_mixing hAO hT ha b hside hcp hcl hv
  exact ⟨m,hm,hraw,a,ha,b,hpath,hlraw⟩

lemma star_card_le_mixing_of_point_mixing
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (hz : centreless G C = ∅) (p : Fin n) (X : Finset (Fin n))
    (hX : ∀ l ∈ X, G.Adj p l) (hres : ∀ l ∈ X, s(p,l) ∈ Ustar G C)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (hXcol : ∀ l ∈ X, color l ≠ color p)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hccol : ∀ a, color (c a) = color p) (hcne : ∀ a, c a ≠ p)
    (hmcol : ∀ m ∈ mixing G C, ∀ u ∈ orIn n C (n+m), color u = color p) :
    X.card ≤ (mixing G C).card := by
  classical
  apply FirstMixing.pencil_count G C hL.1 hfour p X hres hX
  intro l hl
  obtain ⟨a,ha,_,_,_,hv,_,_⟩ := residualTrace hL hT (hres l hl)
  have hat : a ∈ tops G C \ centreless G C := Finset.mem_sdiff.mpr ⟨ha,by simp [hz]⟩
  let aa : {a // a ∈ tops G C \ centreless G C} := ⟨a,hat⟩
  rcases hc aa with hside | hside
  · exact pencil_of_point_mixing hL.1 hT ha 0 hside (hcne aa) (topSides hz ha (1-0))
      color hbip (hccol aa) (hXcol l hl) hmcol hv
  · exact pencil_of_point_mixing hL.1 hT ha 1 hside (hcne aa) (topSides hz ha (1-1))
      color hbip (hccol aa) (hXcol l hl) hmcol hv

lemma all_mixing_point_of_card_one
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hz : centreless G C = ∅)
    (p l : Fin n) (hres : s(p,l) ∈ Ustar G C)
    (color : Fin n → Bool) (hlcol : color l ≠ color p)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hccol : ∀ a, color (c a) = color p) (hcne : ∀ a, c a ≠ p)
    (hcard : (mixing G C).card = 1) :
    ∀ m ∈ mixing G C, ∀ u ∈ orIn n C (n+m), color u = color p := by
  classical
  obtain ⟨a,ha,_,_,_,hv,_,_⟩ := residualTrace hL hT hres
  have hat : a ∈ tops G C \ centreless G C := Finset.mem_sdiff.mpr ⟨ha,by simp [hz]⟩
  let aa : {a // a ∈ tops G C \ centreless G C} := ⟨a,hat⟩
  have hcl : c aa ≠ l := by
    intro he
    exact hlcol (he ▸ hccol aa)
  have get (b : Fin 2) (hside : side (n := n) C a b = {c aa}) :
      ∃ m ∈ mixing G C, ∀ u ∈ orIn n C (n+m), color u = color p := by
    obtain ⟨m,hm,_,hraw,_⟩ := singleton_operand_mixing hL.1 hT ha b hside (hcne aa) hcl hv
    exact ⟨m,hm,fun u hu => by rw [hraw u hu]; exact hccol aa⟩
  have hex : ∃ m ∈ mixing G C, ∀ u ∈ orIn n C (n+m), color u = color p := by
    rcases hc aa with hside | hside
    · exact get 0 hside
    · exact get 1 hside
  obtain ⟨m0,hm0,hpoint⟩ := hex
  intro m hm
  have heq : m = m0 := Finset.card_le_one.mp (by omega) m hm m0 hm0
  simpa only [heq] using hpoint

end MissingCentreMixing

namespace FirstMixing
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge CircuitLedger CircuitLedger.Budget

lemma pencil_count_surjective
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (hfour : NoFourCycle G)
    (p : Fin n) (L : Finset (Fin n))
    (hstar : ∀ l ∈ L, s(p,l) ∈ Ustar G C) (hL : ∀ l ∈ L, G.Adj p l)
    (hcover : ∀ l ∈ L, ∃ m ∈ mixing G C, PencilAt G C m l)
    (hcard : L.card = (mixing G C).card) :
    ∀ m ∈ mixing G C, ∃ l ∈ L, PencilAt G C m l := by
  classical
  let pick (l : Fin n) : ℕ := if h : l ∈ L then (hcover l h).choose else 0
  have hpick (l : Fin n) (hl : l ∈ L) :
      pick l ∈ mixing G C ∧ PencilAt G C (pick l) l := by
    simpa only [pick,dif_pos hl] using (hcover l hl).choose_spec
  have hinj : Set.InjOn pick L := by
    intro l hl k hk he
    obtain ⟨hn,a,ha,b,hp,hside⟩ := (hpick l hl).2
    obtain ⟨_,a',ha',b',hp',hside'⟩ := (hpick k hk).2
    rw [← he] at hp'
    exact raw_pencil_leaf_unique ao hfour p (hstar l hl) hn ha ha' hp hp'
      hside hside' (hL l hl) (hL k hk)
  intro m hm
  by_contra hno
  have hbound : L.card ≤ ((mixing G C).erase m).card := by
    apply Finset.card_le_card_of_injOn pick ?_ hinj
    intro l hl
    refine Finset.mem_erase.mpr ⟨?_,(hpick l hl).1⟩
    intro he
    exact hno ⟨l,hl,he ▸ (hpick l hl).2⟩
  have hlt := Finset.card_erase_lt_of_mem hm
  omega

lemma pencil_raw_colour
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    {p l : Fin n} (hpl : G.Adj p l) {m : ℕ} (hpen : PencilAt G C m l)
    {v : Fin n} (hv : v ∈ orIn n C (n+m)) : color v = color p := by
  obtain ⟨_,a,ha,b,hpath,hl⟩ := hpen
  have hva : v ∈ side C a b := reach_mem_orIn v (hpath.trans (mem_orIn_reach v hv))
  have hvl : G.Adj v l := (SimpleGraph.deleteEdges_adj.mp (cleanAdj ao ha b hva hl)).1
  exact PureProvider.bool_eq_of_ne_common _ _ _ (hbip v l hvl) (hbip p l hpl)

lemma tight_some_true_unserved_eq_mixing
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hz : centreless G C = ∅) (hfour : NoFourCycle G)
    (p : Fin n) (X : Finset (Fin n))
    (hX : ∀ l ∈ X, G.Adj p l) (hstar : ∀ l ∈ X, s(p,l) ∈ Ustar G C)
    (htight : (junk G C).card + (orN G C \ lam G C).card = X.card + 1)
    (htrue : ∃ j ∈ junk G C, gateVal n C j (pairInput p p) = true) :
    (X \ falseServed G C p X).card = (mixing G C).card := by
  classical
  let J := (junk G C).filter fun j => gateVal n C j (pairInput p p) = false
  have hJsub : J ⊆ junk G C := Finset.filter_subset _ _
  have hJne : J ≠ junk G C := by
    intro heq
    obtain ⟨j,hj,hjtrue⟩ := htrue
    have hjfalse := (Finset.mem_filter.mp (show j ∈ J by rw [heq]; exact hj)).2
    exact Bool.noConfusion (hjfalse.symm.trans hjtrue)
  have hJlt : J.card < (junk G C).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hJsub,hJne⟩)
  have hfalse := false_served_budget G C hL.1 hT hfour p X hX hstar
  have hrest := unserved_mixing_count G C hL hT hz hfour p X hX hstar
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (show falseServed G C p X ⊆ X from Finset.filter_subset _ _)
  have hmixsplit := Finset.card_sdiff_add_card_eq_card (mixing_subset_extra G C)
  change (falseServed G C p X).card ≤
    ((orN G C \ lam G C) \ mixing G C).card + J.card at hfalse
  omega

lemma tight_some_true_mixing_colour
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C)
    (hz : centreless G C = ∅) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (p : Fin n) (X : Finset (Fin n))
    (hX : ∀ l ∈ X, G.Adj p l) (hstar : ∀ l ∈ X, s(p,l) ∈ Ustar G C)
    (htight : (junk G C).card + (orN G C \ lam G C).card = X.card + 1)
    (htrue : ∃ j ∈ junk G C, gateVal n C j (pairInput p p) = true) :
    ∀ m ∈ mixing G C, ∀ v ∈ orIn n C (n+m), color v = color p := by
  classical
  have hcard := tight_some_true_unserved_eq_mixing G C hL hT hz hfour p X hX hstar htight htrue
  have hcover : ∀ l ∈ X \ falseServed G C p X, ∃ m ∈ mixing G C, PencilAt G C m l := by
    intro l hl
    obtain ⟨hlX,hlf⟩ := Finset.mem_sdiff.mp hl
    apply true_leaf_mixing hL hT hz (hstar l hlX)
    intro j hj hjp
    apply Bool.eq_false_of_not_eq_true
    intro hjl
    exact hlf (Finset.mem_filter.mpr ⟨hlX,j,hj,hjp,hjl⟩)
  have honto := pencil_count_surjective G C hL.1 hfour p _
    (fun l hl => hstar l (Finset.mem_sdiff.mp hl).1)
    (fun l hl => hX l (Finset.mem_sdiff.mp hl).1) hcover hcard
  intro m hm v hv
  obtain ⟨l,hl,hpen⟩ := honto m hm
  exact pencil_raw_colour G C hL.1 color hbip (hX l (Finset.mem_sdiff.mp hl).1) hpen hv

end FirstMixing

namespace MissingCentreMixing

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge CircuitLedger CircuitLedger.Budget FirstMixing

lemma tight_all_false_mixing_card_one
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (hz : centreless G C = ∅) (p : Fin n) (X : Finset (Fin n)) (hXne : X.Nonempty)
    (hX : ∀ l ∈ X, G.Adj p l) (hres : ∀ l ∈ X, s(p,l) ∈ Ustar G C)
    (htight : (junk G C).card + (orN G C \ lam G C).card = X.card + 1)
    (hfalse : ∀ j ∈ junk G C, gateVal n C j (pairInput p p) = false) :
    (mixing G C).card = 1 := by
  classical
  have hall : falseServed G C p X = X := by
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro l hl
    obtain ⟨a,ha,b,j,hj,_,_,hjl⟩ := residualTrace hL hT (hres l hl)
    exact Finset.mem_filter.mpr ⟨hl,j,hj,hfalse j hj,hjl⟩
  have hJ : ((junk G C).filter fun j => gateVal n C j (pairInput p p) = false) = junk G C :=
    Finset.filter_eq_self.mpr hfalse
  have hbudget := false_served_budget G C hL.1 hT hfour p X hX hres
  rw [hall,hJ] at hbudget
  have hsplit := Finset.card_sdiff_add_card_eq_card (mixing_subset_extra G C)
  obtain ⟨l,hl⟩ := hXne
  obtain ⟨a,ha,b,j,hj,_,hr,_⟩ := residualTrace hL hT (hres l hl)
  obtain ⟨m,hm,_⟩ := first_mixing hL.1 hj _ (topSides hz ha b) (orReaches_reach j _ hr).1
  have hpos : 0 < (mixing G C).card := Finset.card_pos.mpr ⟨m,hm⟩
  omega

lemma tight_missing_centre_counts
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (hz : centreless G C = ∅) (p : Fin n) (X : Finset (Fin n)) (hXcard : 2 ≤ X.card)
    (hX : ∀ l ∈ X, G.Adj p l) (hres : ∀ l ∈ X, s(p,l) ∈ Ustar G C)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (hXcol : ∀ l ∈ X, color l ≠ color p)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hccol : ∀ a, color (c a) = color p) (hcne : ∀ a, c a ≠ p)
    (htight : (junk G C).card + (orN G C \ lam G C).card = X.card + 1) :
    (junk G C).card = 1 ∧ (orN G C \ lam G C).card = X.card ∧
      (mixing G C).card = X.card ∧
      ∃ j ∈ junk G C, gateVal n C j (pairInput p p) = true := by
  classical
  by_cases htrue : ∃ j ∈ junk G C, gateVal n C j (pairInput p p) = true
  · have hmixcol := FirstMixing.tight_some_true_mixing_colour G C hL hT hz hfour
      color hbip p X hX hres htight htrue
    have hbound := star_card_le_mixing_of_point_mixing G C hL hT hfour hz p X hX hres
      color hbip hXcol c hc hccol hcne hmixcol
    have hmixle := Finset.card_le_card (mixing_subset_extra G C)
    have hjpos : 0 < (junk G C).card := by
      obtain ⟨j,hj,_⟩ := htrue
      exact Finset.card_pos.mpr ⟨j,hj⟩
    exact ⟨by omega,by omega,by omega,htrue⟩
  · have hfalse : ∀ j ∈ junk G C, gateVal n C j (pairInput p p) = false := by
      intro j hj
      apply Bool.eq_false_of_not_eq_true
      intro hv
      exact htrue ⟨j,hj,hv⟩
    have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
    have hmixcard := tight_all_false_mixing_card_one G C hL hT hfour hz p X hXne hX hres htight hfalse
    obtain ⟨l,hl⟩ := hXne
    have hmixcol := all_mixing_point_of_card_one G C hL hT hz p l (hres l hl)
      color (hXcol l hl) c hc hccol hcne hmixcard
    have hbound := star_card_le_mixing_of_point_mixing G C hL hT hfour hz p X hX hres
      color hbip hXcol c hc hccol hcne hmixcol
    omega

end MissingCentreMixing

namespace FirstMixing
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge CircuitLedger CircuitLedger.Budget

lemma all_false_residual_pencil_budget
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (p : Fin n) (X : Finset (Fin n))
    (hX : ∀ l ∈ X, G.Adj p l) (hstar : ∀ l ∈ X, s(p,l) ∈ Ustar G C)
    (hall : ∀ j ∈ junk G C, gateVal n C j (pairInput p p) = false) :
    X.card + (mixing G C).card ≤ (orN G C \ lam G C).card + (junk G C).card := by
  classical
  have hserved : falseServed G C p X = X := by
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro l hl
    obtain ⟨a,ha,b,j,hj,_,_,hjl⟩ := residualTrace hL hT (hstar l hl)
    exact Finset.mem_filter.mpr ⟨hl,j,hj,hall j hj,hjl⟩
  have hJ : ((junk G C).filter fun j => gateVal n C j (pairInput p p) = false) = junk G C :=
    Finset.filter_eq_self.mpr hall
  have hfalse := false_served_budget G C hL.1 hT hfour p X hX hstar
  rw [hserved,hJ] at hfalse
  have hmixsplit := Finset.card_sdiff_add_card_eq_card (mixing_subset_extra G C)
  omega

/-- Equality in the strengthened residual-pencil penalty forces every top to have raw inputs on both sides. -/
lemma tight_centreless_empty
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (p : Fin n) (X : Finset (Fin n))
    (hX : ∀ l ∈ X, G.Adj p l) (hstar : ∀ l ∈ X, s(p,l) ∈ Ustar G C)
    (htight : 2 * (centreless G C).card + (junk G C).card +
      (orN G C \ lam G C).card = X.card + 1) : centreless G C = ∅ := by
  classical
  have hshape := tight_residual_pencil_shape G C hL hT hfour p X hX hstar htight
  by_contra hz
  have hzpos : 0 < (centreless G C).card :=
    Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hz)
  have hall : ∀ j ∈ junk G C, gateVal n C j (pairInput p p) = false := by
    intro j hj
    apply Bool.eq_false_of_not_eq_true
    intro hjtrue
    have hpos : 0 < ((junk G C).filter fun j => gateVal n C j (pairInput p p) = true).card :=
      Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨hj,hjtrue⟩⟩
    omega
  have hb := all_false_residual_pencil_budget G C hL hT hfour p X hX hstar hall
  omega

end FirstMixing

namespace IdentityErase

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open CircuitLedger.Budget

/-- One evaluation step: append the value of gate `g` to the wire list `w`. -/
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma fold_prefix : ∀ (gs : List Gate) (w : List Bool),
    ∃ t, gs.foldl step w = w ++ t ∧ t.length = gs.length
  | [], w => ⟨[], by simp⟩
  | g :: gs, w => by
    obtain ⟨t, ht, hl⟩ := fold_prefix gs (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]
    simp [step]

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht, List.length_append, hl]

lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨t, ht, -⟩ := fold_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false :=
  List.getD_eq_default _ _ hi

/-! Erasing one gate -/

/-- Where wire `i` of the erased circuit sits in the old one (`k = n + m`). -/
def up (k i : ℕ) : ℕ := if i < k then i else i + 1

/-- The renamed copy of a gate after the erased one. -/
def ren (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩

lemma up_redir (n m p r : ℕ) (hr : r ≠ n + m) : up (n + m) (eraseRedirect n m p r) = r := by
  unfold up eraseRedirect
  split_ifs <;> omega

lemma sim (n m p : ℕ) : ∀ (rest : List Gate) (U V : List Bool),
    (∀ i, U.getD i false = V.getD (up (n + m) i) false) → n + m ≤ U.length →
    V.length = U.length + 1 →
    ((U.getD p false = V.getD (n + m) false ∧ (p < n + m ∨ U.length + rest.length < p)) ∨
      ∀ g ∈ rest, n + m ∉ g.inputs) →
    ∀ i, ((rest.map (ren n m p)).foldl step U).getD i false =
      (rest.foldl step V).getD (up (n + m) i) false
  | [], U, V, hrel, _, _, _ => by simpa using hrel
  | g :: rest, U, V, hrel, hk, hlen, hS => by
    have hread : ∀ r ∈ g.inputs, U.getD (eraseRedirect n m p r) false = V.getD r false := by
      intro r hr
      by_cases hrk : r = n + m
      · subst hrk
        rcases hS with ⟨hS, -⟩ | hS
        · simpa [eraseRedirect] using hS
        · exact absurd hr (hS g (List.mem_cons_self ..))
      · rw [hrel, up_redir n m p r hrk]
    set a := g.op.eval (g.inputs.map fun i => V.getD i false) with ha
    have hU : step U (ren n m p g) = U ++ [a] := by
      simp only [step, ren, List.map_map]
      congr 3
      exact List.map_congr_left fun r hr => hread r hr
    have hV : step V g = V ++ [a] := rfl
    simp only [List.map_cons, List.foldl_cons, hU, hV]
    apply sim n m p rest
    · intro i
      rcases lt_trichotomy i U.length with hi | rfl | hi
      · have hup : up (n + m) i < V.length := by unfold up; split_ifs <;> omega
        rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hup, hrel]
      · have hup : up (n + m) U.length = V.length := by unfold up; split_ifs <;> omega
        rw [hup, List.getD_append_right _ _ _ _ le_rfl, List.getD_append_right _ _ _ _ le_rfl]
        simp
      · rw [getD_ge _ _ (by simp; omega), getD_ge _ _ (by simp; unfold up; split_ifs <;> omega)]
    · simp; omega
    · simp; omega
    · rcases hS with ⟨hS, hp⟩ | hS
      · left
        refine ⟨?_, ?_⟩
        · rw [List.getD_append _ _ _ _ (by omega : n + m < V.length)]
          rcases hp with hp | hp
          · rw [List.getD_append _ _ _ _ (by omega)]; exact hS
          · rw [getD_ge _ _ (by simp at hp ⊢; omega)]
            rw [getD_ge _ _ (by simp at hp ⊢; omega)] at hS
            exact hS
        · rcases hp with hp | hp
          · exact Or.inl hp
          · right; simp at hp ⊢; omega
      · exact Or.inr fun g' hg' => hS g' (List.mem_cons_of_mem _ hg')

lemma erase_gates (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates = C.gates.take m ++ (C.gates.drop (m + 1)).map (ren n m p) ∧
    (eraseGate n C m p).output = eraseRedirect n m p C.output := by
  unfold eraseGate
  rw [if_pos hm]
  exact ⟨rfl, rfl⟩

lemma erase_eval (n : ℕ) (C : Circuit) (m p : ℕ) (y : List Bool) (hy : y.length = n)
    (hm : m < C.gates.length) (hp : p < n + m ∨ n + C.gates.length ≤ p)
    (hc : (C.wires y).getD (n + m) false = (C.wires y).getD p false ∨
      (C.output ≠ n + m ∧ ∀ g ∈ C.gates.drop (m + 1), n + m ∉ g.inputs)) :
    (eraseGate n C m p).eval y = C.eval y := by
  obtain ⟨hg, ho⟩ := erase_gates n C m p hm
  have hsplit : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hm, List.take_append_drop]
  set A := (C.gates.take m).foldl step y with hA
  have hAl : A.length = n + m := by
    rw [hA, fold_length, hy, List.length_take]; omega
  set rest := C.gates.drop (m + 1) with hrest
  have hrl : rest.length = C.gates.length - (m + 1) := List.length_drop
  have hW : C.wires y = rest.foldl step (step A C.gates[m]) := by
    rw [wires_eq]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hW' : (eraseGate n C m p).wires y = (rest.map (ren n m p)).foldl step A := by
    rw [wires_eq, hg, List.foldl_append]
  have hVl : (step A C.gates[m]).length = A.length + 1 := by simp [step]
  have hWl : (C.wires y).length = n + C.gates.length := by
    rw [wires_eq, fold_length, hy]
  have hstable : ∀ i, i < n + m + 1 → (step A C.gates[m]).getD i false = (C.wires y).getD i false := by
    intro i hi
    rw [hW, fold_getD_lt _ _ _ (by omega)]
  have hsim := sim n m p rest A (step A C.gates[m]) (by
      intro i
      by_cases hi : i < n + m
      · simp only [up, if_pos hi, step]
        rw [List.getD_append _ _ _ _ (by omega)]
      · simp only [up, if_neg hi]
        rw [getD_ge _ _ (by omega), getD_ge _ _ (by omega)])
    (by omega) hVl (by
      rcases hc with hc | ⟨-, hc⟩
      · left
        refine ⟨?_, ?_⟩
        · rw [hstable _ (by omega)]
          rcases hp with hp | hp
          · rw [hc, ← hstable _ (by omega), step, List.getD_append _ _ _ _ (by omega)]
          · rw [getD_ge _ _ (by omega), hc, getD_ge _ _ (by omega)]
        · rcases hp with hp | hp
          · exact Or.inl hp
          · right; omega
      · exact Or.inr hc)
  unfold Circuit.eval
  rw [ho, hW', hsim, ← hW]
  by_cases hout : C.output = n + m
  · rcases hc with hc | ⟨hc, -⟩
    · have hr : eraseRedirect n m p C.output = p := by
        unfold eraseRedirect; rw [if_pos hout]
      rw [hr, hout]
      rcases hp with hp | hp
      · have hu : up (n + m) p = p := by unfold up; rw [if_pos hp]
        rw [hu]; exact hc.symm
      · have hu : up (n + m) p = p + 1 := by unfold up; rw [if_neg (by omega)]
        rw [hu, hc, getD_ge _ _ (by omega), getD_ge _ _ (by omega)]
    · exact absurd hout hc
  · rw [up_redir n m p _ hout]

lemma erase_size (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).size + 1 = C.size := by
  unfold Circuit.size
  rw [(erase_gates n C m p hm).1]
  simp
  omega

lemma getD_erase (l : List Gate) (f : Gate → Gate) (d : Gate) (m j : ℕ) (hm : m < l.length)
    (hj : j + 1 < l.length) :
    (l.take m ++ (l.drop (m + 1)).map f).getD j d
      = if j < m then l.getD j d else f (l.getD (j + 1) d) := by
  have hlt : (l.take m).length = m := by
    rw [List.length_take]
    omega
  by_cases h : j < m
  · rw [if_pos h, List.getD_append _ _ _ _ (by omega)]
    rw [List.getD_eq_getElem (l.take m) d (by omega), List.getD_eq_getElem l d (by omega),
      List.getElem_take]
  · rw [if_neg h, List.getD_append_right _ _ _ _ (by omega), hlt]
    have e : m + 1 + (j - m) = j + 1 := by omega
    rw [List.getD_eq_getElem (List.map f (l.drop (m + 1))) d
        (by rw [List.length_map, List.length_drop]; omega),
      List.getD_eq_getElem l d hj, List.getElem_map, List.getElem_drop]
    simp only [e]

lemma erase_AO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {m p : ℕ} (hm : m < C.gates.length) (hp : p < n + m) :
    IsAO2 n (eraseGate n C m p) := by
  have hg := (erase_gates n C m p hm).1
  have hlen : (eraseGate n C m p).gates.length + 1 = C.gates.length :=
    erase_size n C m p hm
  refine ⟨?_, ?_, ?_⟩
  · intro g hmem
    rw [hg, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact hAO.1 g (List.mem_of_mem_take hmem)
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hmem
      exact hAO.1 g' (List.mem_of_mem_drop hg')
  · intro j hj i hi
    have hga : gateAt (eraseGate n C m p) j =
        if j < m then gateAt C j else ren n m p (gateAt C (j + 1)) := by
      change ((eraseGate n C m p).gates).getD j _ = _
      rw [hg]
      exact getD_erase C.gates (ren n m p) _ m j hm (by omega)
    rw [hga] at hi
    by_cases hjm : j < m
    · rw [if_pos hjm] at hi
      exact hAO.2.1 j (by omega) i hi
    · rw [if_neg hjm] at hi
      obtain ⟨i0, hi0, rfl⟩ := List.mem_map.mp hi
      have hbound := hAO.2.1 (j + 1) (by omega) i0 hi0
      unfold eraseRedirect
      split_ifs <;> omega
  · intro g hmem
    rw [hg, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact hAO.2.2 g (List.mem_of_mem_take hmem)
    · obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hmem
      simpa [ren] using hAO.2.2 g' (List.mem_of_mem_drop hg')

lemma least_no_identity {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hmin : IsLeastAO G C) {j p : ℕ}
    (hj : j < C.gates.length) (hp : p < n + j)
    (heq : ∀ x : Fin n → Bool,
      gateVal n C j x = (C.wires (List.ofFn x)).getD p false) : False := by
  let D := eraseGate n C j p
  have hAO : IsAO2 n D := erase_AO2 hmin.1 hj hp
  have hfun : PEqualNP.MetaComplexity.circuitFun n D =
      PEqualNP.MetaComplexity.circuitFun n C := by
    funext x
    exact erase_eval n C j p (List.ofFn x) (by simp) hj (Or.inl hp)
      (Or.inl (heq x))
  have hle := hmin.2.2 D hAO (hfun.trans hmin.2.1)
  have hsize := erase_size n C j p hj
  change C.size ≤ (eraseGate n C j p).size at hle
  omega

lemma least_no_duplicate_and {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hmin : IsLeastAO G C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (p : Fin n) (hdup : ∀ b : Fin 2, opnd C j b = p.val) : False := by
  apply least_no_identity hmin hj (p := p.val) (by omega)
  intro x
  apply Bool.eq_iff_iff.mpr
  simpa only [hdup, and_self, val] using andValBoth hmin.1 hj hop x

end IdentityErase


namespace OneJunkCone

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CleanedNonEdge CircuitLedger CircuitLedger.Budget

lemma raw_or_and_source
    {n : ℕ} {C : Circuit} (ao : IsAO2 n C) :
    ∀ w, w < n + C.gates.length → (orIn n C w).Nonempty ∨
      ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧
        Relation.ReflTransGen (OrStep n C) w (n+j) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · left
      refine ⟨⟨w,hin⟩,?_⟩
      exact reach_mem_orIn ⟨w,hin⟩ Relation.ReflTransGen.refl
    · let k := w - n
      have heq : w = n+k := by dsimp [k]; omega
      have hk : k < C.gates.length := by omega
      rcases ao.1 _ (gateAt_mem hk) with hop | hop
      · exact Or.inr ⟨k,hk,hop,heq ▸ Relation.ReflTransGen.refl⟩
      · have hv := opndBound ao hk 0
        have hs : OrStep n C w (opnd C k 0) := ⟨k,hk,heq,hop,opndMem ao hk 0,hv⟩
        rcases ih (opnd C k 0) (by omega) (by omega) with hraw | ⟨j,hj,hopj,hpath⟩
        · left
          obtain ⟨u,hu⟩ := hraw
          exact ⟨u,reach_mem_orIn u (Relation.ReflTransGen.head hs (mem_orIn_reach u hu))⟩
        · exact Or.inr ⟨j,hj,hopj,Relation.ReflTransGen.head hs hpath⟩

lemma no_earlier_junk_raw_nonempty
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) (hT : TopForm G C) {j : ℕ} (hj : j ∈ junk G C)
    (huniq : ∀ k ∈ junk G C, k = j) (b : Fin 2) {w : ℕ}
    (hw : w < n + C.gates.length)
    (hpath : Relation.ReflTransGen (OrStep n C) (opnd C j b) w) :
    (orIn n C w).Nonempty := by
  rcases raw_or_and_source ao w hw with hraw | ⟨k,hk,hopk,hkpath⟩
  · exact hraw
  · obtain ⟨hjlen,hopj,_⟩ := junkData hj
    have hr := reach_orReaches (hpath.trans hkpath) k rfl hk
    have hkj := huniq k (operandOrAndJunk ao hT hjlen hopj hr hopk)
    have hlt := operand_reachable_lt ao hjlen hr
    omega

lemma only_junk_operand_is_input
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (ao : IsAO2 n C) (hT : TopForm G C) {j : ℕ} (hj : j ∈ junk G C)
    (huniq : ∀ k ∈ junk G C, k = j)
    (hextra : orN G C \ lam G C ⊆ mixing G C) (p : Fin n)
    (hfree : ∀ k ∈ lam G C, p ∉ orIn n C (n+k))
    (htrue : gateVal n C j (pairInput p p) = true) (b : Fin 2) :
    opnd C j b = p.val := by
  classical
  obtain ⟨hjlen,hopj,_⟩ := junkData hj
  have hv := (andValOperands ao hjlen hopj (pairInput p p)).mp htrue b
  have hpraw : p ∈ orIn n C (opnd C j b) := by
    rcases operandSupport ao hT hjlen hopj hv with ⟨u,hu,hup | hup⟩ | ⟨k,hk,hr,_⟩
    · simpa only [side,hup] using hu
    · simpa only [side,hup] using hu
    · have hkj := huniq k hk
      have hlt := operand_reachable_lt ao hjlen hr
      omega
  rcases Relation.ReflTransGen.cases_head (mem_orIn_reach p hpraw) with he | ⟨w,hs,_⟩
  · exact he
  · obtain ⟨k,hk,heq,hopk,_,_⟩ := hs
    have hpk : p ∈ orIn n C (n+k) := by simpa only [heq] using hpraw
    have hn : ¬ BelowF G C k := by
      intro hbelow
      have hvp : gateVal n C k (pairInput p p) = true :=
        reach_var_val (pairInput p p) (n+k) p (mem_orIn_reach p hpk) (pairInput_left p p)
      exact G.irrefl ((graphFun_pair G p p).mp (hbelow _ hvp))
    have hkn : k ∈ orN G C := by
      simpa only [orN,gatesWhere,Finset.mem_filter,Finset.mem_range] using ⟨hk,hopk,hn⟩
    have hkmix := hextra (Finset.mem_sdiff.mpr ⟨hkn,fun hklam => hfree k hklam hpk⟩)
    have hraw (d : Fin 2) : (orIn n C (opnd C k d)).Nonempty := by
      have hvk := opndBound ao hk d
      have hs' : OrStep n C (opnd C j b) (opnd C k d) :=
        ⟨k,hk,heq,hopk,opndMem ao hk d,hvk⟩
      apply no_earlier_junk_raw_nonempty ao hT hj huniq b (by omega)
      exact Relation.ReflTransGen.single hs'
    have h0 := Finset.nonempty_iff_ne_empty.mp (hraw 0)
    have h1 := Finset.nonempty_iff_ne_empty.mp (hraw 1)
    have hx := (Finset.mem_filter.mp hkmix).2
    exact (hx (propext (iff_of_false h0 h1))).elim

end OneJunkCone

namespace MissingCentreMixing

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover CircuitLedger CircuitLedger.Budget FirstMixing

lemma strong_missing_centre_penalty
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (p : Fin n) (X : Finset (Fin n)) (hXcard : 2 ≤ X.card)
    (hX : ∀ l ∈ X, G.Adj p l) (hres : ∀ l ∈ X, s(p,l) ∈ Ustar G C)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hccol : ∀ a, color (c a) = color p) (hcne : ∀ a, c a ≠ p)
    (hfree : ∀ k ∈ lam G C, p ∉ orIn n C (n+k)) :
    X.card + 2 ≤ 2 * (centreless G C).card + (junk G C).card +
      (orN G C \ lam G C).card := by
  classical
  have hXne : X.Nonempty := Finset.card_pos.mp (by omega)
  have hbase := FirstMixing.residual_pencil_penalty G C hL hT hfour p X hXne hX hres
  by_contra hweak
  have htight : 2 * (centreless G C).card + (junk G C).card +
      (orN G C \ lam G C).card = X.card + 1 := by omega
  have hz := FirstMixing.tight_centreless_empty G C hL hT hfour p X hX hres htight
  have htight0 : (junk G C).card + (orN G C \ lam G C).card = X.card + 1 := by
    simpa only [hz,Finset.card_empty,Nat.mul_zero,Nat.zero_add] using htight
  have hXcol : ∀ l ∈ X, color l ≠ color p := fun l hl => (hbip p l (hX l hl)).symm
  obtain ⟨hjcard,hrcard,hmcard,j,hj,htrue⟩ := tight_missing_centre_counts G C hL hT hfour hz
    p X hXcard hX hres color hbip hXcol c hc hccol hcne htight0
  have huniq : ∀ k ∈ junk G C, k = j := by
    intro k hk
    exact Finset.card_le_one.mp (by omega) k hk j hj
  have heq : mixing G C = orN G C \ lam G C := by
    apply Finset.eq_of_subset_of_card_le (mixing_subset_extra G C)
    omega
  have hextra : orN G C \ lam G C ⊆ mixing G C := by rw [heq]
  obtain ⟨hjlen,hopj,_⟩ := junkData hj
  apply IdentityErase.least_no_duplicate_and hL hjlen hopj p
  intro b
  exact OneJunkCone.only_junk_operand_is_input hL.1 hT hj huniq hextra p hfree htrue b

end MissingCentreMixing


namespace FirstMixing
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge CircuitLedger CircuitLedger.Budget

/-- Mixing gates with a raw input whose colour differs from the pencil centre. -/
noncomputable def badMixing
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (color : Fin n → Bool) (p : Fin n) : Finset ℕ := by
  classical
  exact (mixing G C).filter fun m => ∃ v ∈ orIn n C (n+m), color v ≠ color p

lemma badMixing_subset
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (color : Fin n → Bool) (p : Fin n) : badMixing G C color p ⊆ mixing G C :=
  Finset.filter_subset _ _

lemma pencil_count_good_mixing
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : IsAO2 n C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (p : Fin n) (L : Finset (Fin n))
    (hstar : ∀ l ∈ L, s(p,l) ∈ Ustar G C) (hL : ∀ l ∈ L, G.Adj p l)
    (hcover : ∀ l ∈ L, ∃ m ∈ mixing G C, PencilAt G C m l) :
    L.card ≤ (mixing G C \ badMixing G C color p).card := by
  classical
  let pick (l : Fin n) : ℕ := if h : l ∈ L then (hcover l h).choose else 0
  have hpick (l : Fin n) (hl : l ∈ L) :
      pick l ∈ mixing G C ∧ PencilAt G C (pick l) l := by
    simpa only [pick,dite_eq_left hl] using (hcover l hl).choose_spec
  apply Finset.card_le_card_of_injOn pick ?_ ?_
  · intro l hl
    refine Finset.mem_sdiff.mpr ⟨(hpick l hl).1,?_⟩
    intro hbad
    obtain ⟨_,v,hv,hcol⟩ := Finset.mem_filter.mp hbad
    exact hcol (pencil_raw_colour G C ao color hbip (hL l hl) (hpick l hl).2 hv)
  · intro l hl k hk he
    obtain ⟨hn,a,ha,b,hp,hside⟩ := (hpick l hl).2
    obtain ⟨_,a',ha',b',hp',hside'⟩ := (hpick k hk).2
    rw [← he] at hp'
    exact raw_pencil_leaf_unique ao hfour p (hstar l hl) hn ha ha' hp hp'
      hside hside' (hL l hl) (hL k hk)

lemma other_served_good_mixing_count
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (p : Fin n) (X : Finset (Fin n))
    (hX : ∀ l ∈ X, G.Adj p l) (hstar : ∀ l ∈ X, s(p,l) ∈ Ustar G C) :
    (X \ (falseServed G C p X ∪ centrelessServed G C p X)).card ≤
      (mixing G C \ badMixing G C color p).card := by
  classical
  apply pencil_count_good_mixing G C hL.1 hfour color hbip p _
    (fun l hl => hstar l (Finset.mem_sdiff.mp hl).1)
    (fun l hl => hX l (Finset.mem_sdiff.mp hl).1)
  intro l hl
  obtain ⟨hlX,hlf⟩ := Finset.mem_sdiff.mp hl
  apply true_leaf_mixing_of_no_centreless hL hT (hstar l hlX)
  · intro a ha
    apply Bool.eq_false_of_not_eq_true
    intro hav
    exact hlf (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hlX,a,ha,hav⟩))
  · intro j hj hjp
    apply Bool.eq_false_of_not_eq_true
    intro hjl
    exact hlf (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hlX,j,hj,hjp,hjl⟩))

lemma residual_pencil_bad_mixing_budget
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (p : Fin n) (X : Finset (Fin n))
    (hX : ∀ l ∈ X, G.Adj p l) (hstar : ∀ l ∈ X, s(p,l) ∈ Ustar G C) :
    X.card + (badMixing G C color p).card ≤ (orN G C \ lam G C).card +
      ((junk G C).filter fun j => gateVal n C j (pairInput p p) = false).card +
        (centreless G C).card := by
  classical
  have hraw := false_or_centreless_served_budget G C hL.1 hT hfour p X hX hstar
  have hrest := other_served_good_mixing_count G C hL hT hfour color hbip p X hX hstar
  have hsubset : falseServed G C p X ∪ centrelessServed G C p X ⊆ X :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsplit := Finset.card_sdiff_add_card_eq_card hsubset
  have hmixsplit := Finset.card_sdiff_add_card_eq_card (mixing_subset_extra G C)
  have hbadsplit := Finset.card_sdiff_add_card_eq_card (badMixing_subset G C color p)
  omega

lemma residual_pencil_bad_mixing_penalty
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (p : Fin n) (X : Finset (Fin n))
    (hX : ∀ l ∈ X, G.Adj p l) (hstar : ∀ l ∈ X, s(p,l) ∈ Ustar G C) :
    X.card + (badMixing G C color p).card + (centreless G C).card +
      ((junk G C).filter fun j => gateVal n C j (pairInput p p) = true).card ≤
        2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card := by
  classical
  have hb := residual_pencil_bad_mixing_budget G C hL hT hfour color hbip p X hX hstar
  let J := (junk G C).filter fun j => gateVal n C j (pairInput p p) = false
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (show J ⊆ junk G C from Finset.filter_subset _ _)
  have heq : junk G C \ J =
      (junk G C).filter (fun j => gateVal n C j (pairInput p p) = true) := by
    ext j
    simp only [J,Finset.mem_sdiff,Finset.mem_filter]
    cases gateVal n C j (pairInput p p) <;> simp
  rw [heq] at hsplit
  change X.card + (badMixing G C color p).card ≤
    (orN G C \ lam G C).card + J.card + (centreless G C).card at hb
  omega

end FirstMixing




namespace MissingCentreMixing

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover CircuitLedger CircuitLedger.Budget

lemma missing_centre_not_in_top_side
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (p : Fin n)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hccol : ∀ a, color (c a) = color p) (hcne : ∀ a, c a ≠ p)
    {a : ℕ} (ha : a ∈ tops G C \ centreless G C) (b : Fin 2) :
    p ∉ side (n := n) C a b := by
  classical
  let aa : {a // a ∈ tops G C \ centreless G C} := ⟨a,ha⟩
  have get (d : Fin 2) (hs : side (n := n) C a d = {c aa}) :
      p ∉ side (n := n) C a b := by
    intro hp
    rcases opposite d b with he | he
    · rw [he,hs] at hp
      exact hcne aa (Finset.mem_singleton.mp hp).symm
    · rw [he] at hp
      have hadj := (SimpleGraph.deleteEdges_adj.mp
        (cleanAdj hAO (Finset.mem_sdiff.mp ha).1 d
          (show c aa ∈ side (n := n) C a d by rw [hs]; simp) hp)).1
      exact hbip _ _ hadj (hccol aa)
  rcases hc aa with hs | hs
  · exact get 0 hs
  · exact get 1 hs

lemma missing_centre_not_in_lambda
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hAO : IsAO2 n C) (p : Fin n)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hccol : ∀ a, color (c a) = color p) (hcne : ∀ a, c a ≠ p) :
    ∀ k ∈ lam G C, p ∉ orIn n C (n+k) := by
  classical
  intro k hk hp
  obtain ⟨_,_,_,a,ha,b,hcard,hr⟩ := Finset.mem_filter.mp hk
  have hpraw : p ∈ side (n := n) C a b :=
    reach_mem_orIn p ((orReaches_reach k _ hr).1.trans (mem_orIn_reach p hp))
  have hnb : side (n := n) C a b ≠ ∅ := Finset.nonempty_iff_ne_empty.mp ⟨p,hpraw⟩
  have hnopp : side (n := n) C a (1-b) ≠ ∅ := by
    apply Finset.nonempty_iff_ne_empty.mp
    exact Finset.card_pos.mp (by omega)
  have hat : a ∈ tops G C \ centreless G C := by
    refine Finset.mem_sdiff.mpr ⟨ha,?_⟩
    intro hz
    have hz' := (Finset.mem_filter.mp hz).2
    fin_cases b <;> simp_all
  exact missing_centre_not_in_top_side G C hAO p color hbip c hc hccol hcne hat b hpraw

lemma strong_missing_centre_penalty_of_centres
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (p : Fin n) (X : Finset (Fin n)) (hXcard : 2 ≤ X.card)
    (hX : ∀ l ∈ X, G.Adj p l) (hres : ∀ l ∈ X, s(p,l) ∈ Ustar G C)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hccol : ∀ a, color (c a) = color p) (hcne : ∀ a, c a ≠ p) :
    X.card + 2 ≤ 2 * (centreless G C).card + (junk G C).card +
      (orN G C \ lam G C).card :=
  strong_missing_centre_penalty G C hL hT hfour p X hXcard hX hres color hbip c hc hccol hcne
    (missing_centre_not_in_lambda G C hL.1 p color hbip c hc hccol hcne)

end MissingCentreMixing


namespace ActualTopCentres

open PEqualNP.TopForm

lemma encoded_incidence_properties
    {n N : ℕ} (I : Fin N → Fin N → Prop)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pi li : Fin N → Fin n) (hpi : Function.Injective pi) (hli : Function.Injective li)
    (hdis : ∀ p l, pi p ≠ li l)
    (hgraph : ∀ a b, G.Adj a b ↔ ∃ p l, I p l ∧
      ((a = pi p ∧ b = li l) ∨ (a = li l ∧ b = pi p))) :
    (∀ p l, I p l → G.Adj (pi p) (li l)) ∧ NoFourCycle G ∧
      ∃ color : Fin n → Bool, ∀ a b, G.Adj a b → color a ≠ color b := by
  classical
  have hpAdj (p : Fin N) (w : Fin n) :
      G.Adj (pi p) w ↔ ∃ l, I p l ∧ w = li l := by
    constructor
    · intro h
      obtain ⟨r,l,hr,he | he⟩ := (hgraph _ _).mp h
      · have hp := hpi he.1
        subst r
        exact ⟨l,hr,he.2⟩
      · exact (hdis p l he.1).elim
    · rintro ⟨l,hl,rfl⟩
      exact (hgraph _ _).mpr ⟨p,l,hl,Or.inl ⟨rfl,rfl⟩⟩
  have hlAdj (l : Fin N) (w : Fin n) :
      G.Adj (li l) w ↔ ∃ p, I p l ∧ w = pi p := by
    constructor
    · intro h
      obtain ⟨p,k,hp,he | he⟩ := (hgraph _ _).mp h
      · exact (hdis p l he.1.symm).elim
      · have hl := hli he.1
        subst k
        exact ⟨p,hp,he.2⟩
    · rintro ⟨p,hp,rfl⟩
      exact (hgraph _ _).mpr ⟨p,l,hp,Or.inr ⟨rfl,rfl⟩⟩
  refine ⟨fun p l h => (hpAdj p (li l)).mpr ⟨l,h,rfl⟩,?_,?_⟩
  · intro a b hab
    apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨hau,hbu⟩ := (Finset.mem_filter.mp hu).2
    obtain ⟨hav,hbv⟩ := (Finset.mem_filter.mp hv).2
    obtain ⟨p,l,hpl,he | he⟩ := (hgraph a u).mp hau
    · obtain ⟨rfl,rfl⟩ := he
      obtain ⟨r,hrl,rfl⟩ := (hlAdj l b).mp hbu.symm
      obtain ⟨k,hpk,rfl⟩ := (hpAdj p v).mp hav
      obtain ⟨k',hrk,hekk⟩ := (hpAdj r (li k)).mp hbv
      have hkk := hli hekk
      subst k'
      have hpr : p ≠ r := fun he => hab (congrArg pi he)
      obtain ⟨t,_,ht⟩ := hunique p r hpr
      exact congrArg li ((ht l ⟨hpl,hrl⟩).trans (ht k ⟨hpk,hrk⟩).symm)
    · obtain ⟨rfl,rfl⟩ := he
      obtain ⟨k,hpk,rfl⟩ := (hpAdj p b).mp hbu.symm
      obtain ⟨r,hrl,rfl⟩ := (hlAdj l v).mp hav
      obtain ⟨r',hrk,herr⟩ := (hlAdj k (pi r)).mp hbv
      have hrr := hpi herr
      subst r'
      by_cases hpr : p = r
      · exact congrArg pi hpr
      · obtain ⟨t,_,ht⟩ := hunique p r hpr
        exact (hab (congrArg li ((ht l ⟨hpl,hrl⟩).trans (ht k ⟨hpk,hrk⟩).symm))).elim
  · let color : Fin n → Bool := fun v => decide (∃ p, pi p = v)
    have hcpi (p : Fin N) : color (pi p) = true := by
      simp only [color, decide_eq_true_eq]
      exact ⟨p,rfl⟩
    have hcli (l : Fin N) : color (li l) = false := by
      simp only [color, decide_eq_false_iff_not]
      rintro ⟨p,hp⟩
      exact hdis p l hp
    refine ⟨color,?_⟩
    intro a b hab
    obtain ⟨p,l,_,he | he⟩ := (hgraph a b).mp hab
    · obtain ⟨rfl,rfl⟩ := he
      rw [hcpi,hcli]
      decide
    · obtain ⟨rfl,rfl⟩ := he
      rw [hcli,hcpi]
      decide

end ActualTopCentres



namespace ActualTopCentres

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
open CircuitLedger CircuitLedger.Budget

lemma low_residual_plane_penalty
    {n : ℕ} (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (pi li : Fin N → Fin n) (hpi : Function.Injective pi) (hli : Function.Injective li)
    (hdis : ∀ p l, pi p ≠ li l)
    (hI : ∀ p l, I p l → G.Adj (pi p) (li l))
    (color : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → color a ≠ color b)
    (hcounter : (tops G C \ centreless G C).card +
      (2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) + 1 ≤
        N + (Ustar G C).card)
    (hpaid : (Ustar G C).card ≤
      2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card)
    (hsmall : (Ustar G C).card < 2 * q) : q + 3 ≤ (Ustar G C).card := by
  classical
  let P := 2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card
  obtain ⟨c,hc,_,hcover⟩ := exists_selected_centres G C hL.1 hfour
  have hr := low_residual_selected_centres_rigid q N P I hq hN hcol hunique
    G C pi li hpi hli hdis hI c hc hcounter hpaid hsmall
  have hPu : P = (Ustar G C).card := hr.2.2.2.1
  have hno : ∀ a : {a // a ∈ tops G C \ centreless G C},
      ¬ ((side (n := n) C a.val 0).card = 1 ∧ (side (n := n) C a.val 1).card = 1) := by
    intro a ha
    obtain ⟨x,hx⟩ := Finset.card_eq_one.mp ha.1
    obtain ⟨y,hy⟩ := Finset.card_eq_one.mp ha.2
    exact low_residual_no_double_singleton q N P I hq hN hcol hunique
      G C hL.1 hfour pi li hpi hli hdis hI color hbip hcounter hpaid hsmall a.property hx hy
  have hmiss {v w : Fin n} (hvw : G.Adj v w)
      (hv : v ∉ (tops G C \ centreless G C).attach.image c)
      (hw : w ∉ (tops G C \ centreless G C).attach.image c) :
      s(v,w) ∈ Ustar G C := by
    by_contra hn
    have ha : (G.deleteEdges (Ustar G C : Set (Sym2 (Fin n)))).Adj v w := by
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨hvw,hn⟩
    exact (hcover ha).elim hv hw
  have hfinish (p : Fin n) (X : Finset (Fin n)) (hXcard : X.card = q + 1)
      (hX : ∀ l ∈ X, G.Adj p l) (hres : ∀ l ∈ X, s(p,l) ∈ Ustar G C)
      (hccol : ∀ a, color (c a) = color p) (hcne : ∀ a, c a ≠ p) :
      q + 3 ≤ (Ustar G C).card := by
    have hfree : ∀ k ∈ lam G C, p ∉ orIn n C (n+k) := by
      intro k hk hp
      exact lambda_raw_colour G C hL.1 color hbip c hc hno (color p) hccol
        k hk p hp rfl
    have hh := MissingCentreMixing.strong_missing_centre_penalty G C hL hT hfour
      p X (by omega) hX hres color hbip c hc hccol hcne hfree
    change X.card + 2 ≤ P at hh
    omega
  obtain ⟨hpc,hlc⟩ := plane_embeddings_monochromatic q N I hcol hunique G pi li hI color hbip
  rcases hr.2.2.2.2 with ⟨p,hshape⟩ | ⟨l,hshape⟩
  · have hpnot : pi p ∉ (tops G C \ centreless G C).attach.image c := by
      rw [hshape]
      intro hp
      obtain ⟨r,hr,heq⟩ := Finset.mem_image.mp hp
      exact (Finset.mem_erase.mp hr).1 (hpi heq)
    have hlinot (l : Fin N) : li l ∉ (tops G C \ centreless G C).attach.image c := by
      rw [hshape]
      intro hl
      obtain ⟨r,_,heq⟩ := Finset.mem_image.mp hl
      exact hdis r l heq
    let X := (Finset.univ.filter (I p)).image li
    have hXcard : X.card = q + 1 := by
      rw [Finset.card_image_of_injective _ hli]
      exact plane_point_degree q N I (by omega) hN hcol hunique p
    apply hfinish (pi p) X hXcard
    · intro v hv
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv
      exact hI p l (Finset.mem_filter.mp hl).2
    · intro v hv
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hv
      exact hmiss (hI p l (Finset.mem_filter.mp hl).2) hpnot (hlinot l)
    · intro a
      have ha : c a ∈ (Finset.univ.erase p).image pi := by
        rw [← hshape]
        exact Finset.mem_image.mpr ⟨a,Finset.mem_attach _ _,rfl⟩
      obtain ⟨r,_,hr⟩ := Finset.mem_image.mp ha
      rw [← hr]
      exact hpc r p
    · intro a heq
      exact hpnot (heq ▸ Finset.mem_image.mpr ⟨a,Finset.mem_attach _ _,rfl⟩)
  · have hlnot : li l ∉ (tops G C \ centreless G C).attach.image c := by
      rw [hshape]
      intro hl
      obtain ⟨k,hk,heq⟩ := Finset.mem_image.mp hl
      exact (Finset.mem_erase.mp hk).1 (hli heq)
    have hpinot (p : Fin N) : pi p ∉ (tops G C \ centreless G C).attach.image c := by
      rw [hshape]
      intro hp
      obtain ⟨k,_,heq⟩ := Finset.mem_image.mp hp
      exact hdis p k heq.symm
    let X := (Finset.univ.filter (fun p => I p l)).image pi
    have hXcard : X.card = q + 1 := by
      rw [Finset.card_image_of_injective _ hpi]
      exact hcol l
    apply hfinish (li l) X hXcard
    · intro v hv
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
      exact (hI p l (Finset.mem_filter.mp hp).2).symm
    · intro v hv
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
      exact hmiss (hI p l (Finset.mem_filter.mp hp).2).symm hlnot (hpinot p)
    · intro a
      have ha : c a ∈ (Finset.univ.erase l).image li := by
        rw [← hshape]
        exact Finset.mem_image.mpr ⟨a,Finset.mem_attach _ _,rfl⟩
      obtain ⟨k,_,hk⟩ := Finset.mem_image.mp ha
      rw [← hk]
      exact hlc k l
    · intro a heq
      exact hlnot (heq ▸ Finset.mem_image.mpr ⟨a,Finset.mem_attach _ _,rfl⟩)

end ActualTopCentres



namespace ActualTopCentres

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

lemma low_residual_encoded_plane_penalty
    {n : ℕ} (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (pi li : Fin N → Fin n) (hpi : Function.Injective pi) (hli : Function.Injective li)
    (hdis : ∀ p l, pi p ≠ li l)
    (hgraph : ∀ a b, G.Adj a b ↔ ∃ p l, I p l ∧
      ((a = pi p ∧ b = li l) ∨ (a = li l ∧ b = pi p)))
    (hcounter : (tops G C \ centreless G C).card +
      (2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) + 1 ≤
        N + (Ustar G C).card)
    (hpaid : (Ustar G C).card ≤
      2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card)
    (hsmall : (Ustar G C).card < 2 * q) : q + 3 ≤ (Ustar G C).card := by
  obtain ⟨hI,hfour,color,hbip⟩ := encoded_incidence_properties I hunique
    G pi li hpi hli hdis hgraph
  exact low_residual_plane_penalty q N I hq hN hcol hunique G C hL hT hfour
    pi li hpi hli hdis hI color hbip hcounter hpaid hsmall

lemma encoded_plane_residual_at_least
    {n : ℕ} (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hcol : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hunique : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (pi li : Fin N → Fin n) (hpi : Function.Injective pi) (hli : Function.Injective li)
    (hdis : ∀ p l, pi p ≠ li l)
    (hgraph : ∀ a b, G.Adj a b ↔ ∃ p l, I p l ∧
      ((a = pi p ∧ b = li l) ∨ (a = li l ∧ b = pi p)))
    (hcounter : (tops G C \ centreless G C).card +
      (2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) + 1 ≤
        N + (Ustar G C).card)
    (hpaid : (Ustar G C).card ≤
      2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card) :
    min (q + 3) (2 * q) ≤ (Ustar G C).card := by
  by_cases hsmall : (Ustar G C).card < 2 * q
  · exact (min_le_left _ _).trans (low_residual_encoded_plane_penalty q N I hq hN hcol
      hunique G C hL hT pi li hpi hli hdis hgraph hcounter hpaid hsmall)
  · exact (min_le_right _ _).trans (by omega)

end ActualTopCentres





namespace MissingCentreMixing
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge CircuitLedger CircuitLedger.Budget FirstMixing

lemma selected_centre_operand_false
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hAO : IsAO2 n C) (hT : TopForm G C) (hfour : NoFourCycle G)
    {a : ℕ} (ha : a ∈ tops G C) (b : Fin 2) {c p : Fin n}
    (hside : side (n := n) C a b = {c}) (hcp : c ≠ p)
    (hmany : 2 ≤ (side (n := n) C a (1-b)).card) :
    val C (List.ofFn (pairInput p p)) (opnd C a b) = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hv
  obtain ⟨hlen,hop,_⟩ := topData ha
  have hex : ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
      gateVal n C j (pairInput p p) = true := by
    rcases operandSupport hAO hT hlen hop hv with ⟨u,hu,hup | hup⟩ | ⟨j,hj,hr,hjv⟩
    · have huc : u = c := Finset.mem_singleton.mp (hside ▸ hu)
      exact (hcp (huc.symm.trans hup)).elim
    · have huc : u = c := Finset.mem_singleton.mp (hside ▸ hu)
      exact (hcp (huc.symm.trans hup)).elim
    · exact ⟨j,hj,hr,hjv⟩
  obtain ⟨j,_,hr,hjv⟩ := hex
  have hpadj : ∀ v ∈ side (n := n) C a (1-b), G.Adj p v := by
    intro v hv
    exact (graphFun_pair G p v).mp (firingTop hAO ha (orReaches_reach j _ hr).1 hv
      (pairInput p v) (GlobalMixing.singleton_to_pair hAO p v j hjv) (pairInput_right p v))
  have hcadj : ∀ v ∈ side (n := n) C a (1-b), G.Adj c v := by
    intro v hv
    exact (SimpleGraph.deleteEdges_adj.mp (cleanAdj hAO ha b
      (show c ∈ side (n := n) C a b by rw [hside]; simp) hv)).1
  obtain ⟨v,w,hv,hw,hvw⟩ := Finset.one_lt_card_iff.mp (show 1 < (side (n := n) C a (1-b)).card by omega)
  exact hvw (common_neighbors_unique_of_card_le_one G hfour c p hcp v w
    (hcadj v hv) (hpadj v hv) (hcadj w hw) (hpadj w hw))

lemma false_singleton_operand_junk
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ} (ha : a ∈ tops G C)
    (b : Fin 2) {c p l : Fin n} (hside : side (n := n) C a b = {c})
    (hcp : c ≠ p) (hcl : c ≠ l)
    (hf : val C (List.ofFn (pairInput p p)) (opnd C a b) = false)
    (hv : gateVal n C a (pairInput p l) = true) :
    ∃ j ∈ junk G C, gateVal n C j (pairInput p p) = false ∧
      gateVal n C j (pairInput p l) = true := by
  obtain ⟨hlen,hop,_⟩ := topData ha
  have hb := (andValOperands hAO hlen hop (pairInput p l)).mp hv b
  rcases operandSupport hAO hT hlen hop hb with ⟨u,hu,hup | hul⟩ | ⟨j,hj,hr,hjv⟩
  · have huc : u = c := Finset.mem_singleton.mp (hside ▸ hu)
    exact (hcp (huc.symm.trans hup)).elim
  · have huc : u = c := Finset.mem_singleton.mp (hside ▸ hu)
    exact (hcl (huc.symm.trans hul)).elim
  · refine ⟨j,hj,?_,hjv⟩
    apply Bool.eq_false_of_not_eq_true
    intro hjp
    have ht : val C (List.ofFn (pairInput p p)) (opnd C a b) = true :=
      orStep_up (n := n) (by simp) (orReaches_reach j _ hr).1 hjp
    exact Bool.noConfusion (hf.symm.trans ht)

lemma missing_centre_false_served_all
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (hz : centreless G C = ∅) (p : Fin n) (X : Finset (Fin n))
    (hres : ∀ l ∈ X, s(p,l) ∈ Ustar G C)
    (color : Fin n → Bool) (hXcol : ∀ l ∈ X, color l ≠ color p)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hccol : ∀ a, color (c a) = color p) (hcne : ∀ a, c a ≠ p)
    (hno : ∀ a : {a // a ∈ tops G C \ centreless G C},
      ¬ ((side (n := n) C a.val 0).card = 1 ∧ (side (n := n) C a.val 1).card = 1)) :
    falseServed G C p X = X := by
  classical
  apply Finset.Subset.antisymm (Finset.filter_subset _ _)
  intro l hl
  obtain ⟨a,ha,_,_,_,hv,_,_⟩ := residualTrace hL hT (hres l hl)
  have hat : a ∈ tops G C \ centreless G C := Finset.mem_sdiff.mpr ⟨ha,by simp [hz]⟩
  let aa : {a // a ∈ tops G C \ centreless G C} := ⟨a,hat⟩
  have hcl : c aa ≠ l := by
    intro heq
    exact hXcol l hl (heq ▸ hccol aa)
  have get (b : Fin 2) (hside : side (n := n) C a b = {c aa}) :
      ∃ j ∈ junk G C, gateVal n C j (pairInput p p) = false ∧
        gateVal n C j (pairInput p l) = true := by
    have hpos := Finset.card_pos.mpr (topSides hz ha (1-b))
    have hunit : (side (n := n) C a b).card = 1 := by rw [hside]; simp
    have hone : (side (n := n) C a (1-b)).card ≠ 1 := by
      intro hone
      apply hno aa
      fin_cases b
      · exact ⟨hunit,hone⟩
      · exact ⟨hone,hunit⟩
    have hf := selected_centre_operand_false hL.1 hT hfour ha b hside (hcne aa) (by omega)
    exact false_singleton_operand_junk hL.1 hT ha b hside (hcne aa) hcl hf hv
  have hex : ∃ j ∈ junk G C, gateVal n C j (pairInput p p) = false ∧
      gateVal n C j (pairInput p l) = true := by
    rcases hc aa with hside | hside
    · exact get 0 hside
    · exact get 1 hside
  obtain ⟨j,hj,hjp,hjl⟩ := hex
  exact Finset.mem_filter.mpr ⟨hl,j,hj,hjp,hjl⟩

/-- Under a missing monochromatic centre selection without double-singleton tops,
  every mixing gate and every singleton-true junk gate consumes residual-pencil slack. -/
lemma missing_centre_all_mixing_budget
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (hz : centreless G C = ∅) (p : Fin n) (X : Finset (Fin n))
    (hX : ∀ l ∈ X, G.Adj p l) (hres : ∀ l ∈ X, s(p,l) ∈ Ustar G C)
    (color : Fin n → Bool) (hXcol : ∀ l ∈ X, color l ≠ color p)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hccol : ∀ a, color (c a) = color p) (hcne : ∀ a, c a ≠ p)
    (hno : ∀ a : {a // a ∈ tops G C \ centreless G C},
      ¬ ((side (n := n) C a.val 0).card = 1 ∧ (side (n := n) C a.val 1).card = 1)) :
    X.card + (mixing G C).card +
      ((junk G C).filter fun j => gateVal n C j (pairInput p p) = true).card ≤
        (orN G C \ lam G C).card + (junk G C).card := by
  classical
  have hserved := missing_centre_false_served_all G C hL hT hfour hz p X hres
    color hXcol c hc hccol hcne hno
  have hfalse := false_served_budget G C hL.1 hT hfour p X hX hres
  rw [hserved] at hfalse
  have hmixsplit := Finset.card_sdiff_add_card_eq_card (mixing_subset_extra G C)
  let J := (junk G C).filter fun j => gateVal n C j (pairInput p p) = false
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (show J ⊆ junk G C from Finset.filter_subset _ _)
  have heq : junk G C \ J =
      (junk G C).filter (fun j => gateVal n C j (pairInput p p) = true) := by
    ext j
    simp only [J,Finset.mem_sdiff,Finset.mem_filter]
    cases gateVal n C j (pairInput p p) <;> simp
  rw [heq] at hsplit
  change X.card ≤ ((orN G C \ lam G C) \ mixing G C).card + J.card at hfalse
  omega

end MissingCentreMixing


namespace MissingCentreMixing
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.CleanedNonEdge CircuitLedger CircuitLedger.Budget FirstMixing

lemma missing_centre_false_or_centreless_served_all
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (p : Fin n) (X : Finset (Fin n)) (hres : ∀ l ∈ X, s(p,l) ∈ Ustar G C)
    (color : Fin n → Bool) (hXcol : ∀ l ∈ X, color l ≠ color p)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hccol : ∀ a, color (c a) = color p) (hcne : ∀ a, c a ≠ p)
    (hno : ∀ a : {a // a ∈ tops G C \ centreless G C},
      ¬ ((side (n := n) C a.val 0).card = 1 ∧ (side (n := n) C a.val 1).card = 1)) :
    falseServed G C p X ∪ centrelessServed G C p X = X := by
  classical
  apply Finset.Subset.antisymm (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  intro l hl
  obtain ⟨a,ha,_,_,_,hv,_,_⟩ := residualTrace hL hT (hres l hl)
  by_cases haz : a ∈ centreless G C
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hl,a,haz,hv⟩)
  have hat : a ∈ tops G C \ centreless G C := Finset.mem_sdiff.mpr ⟨ha,haz⟩
  let aa : {a // a ∈ tops G C \ centreless G C} := ⟨a,hat⟩
  have hnon (k : Fin 2) : (side (n := n) C a k).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    apply haz
    apply Finset.mem_filter.mpr
    refine ⟨ha,?_⟩
    fin_cases k
    · exact Or.inl he
    · exact Or.inr he
  have hcl : c aa ≠ l := by
    intro heq
    exact hXcol l hl (heq ▸ hccol aa)
  have get (b : Fin 2) (hside : side (n := n) C a b = {c aa}) :
      ∃ j ∈ junk G C, gateVal n C j (pairInput p p) = false ∧
        gateVal n C j (pairInput p l) = true := by
    have hpos := Finset.card_pos.mpr (hnon (1-b))
    have hunit : (side (n := n) C a b).card = 1 := by rw [hside]; simp
    have hone : (side (n := n) C a (1-b)).card ≠ 1 := by
      intro hone
      apply hno aa
      fin_cases b
      · exact ⟨hunit,hone⟩
      · exact ⟨hone,hunit⟩
    have hf := selected_centre_operand_false hL.1 hT hfour ha b hside (hcne aa) (by omega)
    exact false_singleton_operand_junk hL.1 hT ha b hside (hcne aa) hcl hf hv
  have hex : ∃ j ∈ junk G C, gateVal n C j (pairInput p p) = false ∧
      gateVal n C j (pairInput p l) = true := by
    rcases hc aa with hside | hside
    · exact get 0 hside
    · exact get 1 hside
  obtain ⟨j,hj,hjp,hjl⟩ := hex
  exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hl,j,hj,hjp,hjl⟩)

/-- The all-mixing slack budget also permits centreless tops, charged once on the left. -/
lemma missing_centre_all_mixing_penalty
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (p : Fin n) (X : Finset (Fin n))
    (hX : ∀ l ∈ X, G.Adj p l) (hres : ∀ l ∈ X, s(p,l) ∈ Ustar G C)
    (color : Fin n → Bool) (hXcol : ∀ l ∈ X, color l ≠ color p)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hccol : ∀ a, color (c a) = color p) (hcne : ∀ a, c a ≠ p)
    (hno : ∀ a : {a // a ∈ tops G C \ centreless G C},
      ¬ ((side (n := n) C a.val 0).card = 1 ∧ (side (n := n) C a.val 1).card = 1)) :
    X.card + (mixing G C).card +
      ((junk G C).filter fun j => gateVal n C j (pairInput p p) = true).card +
        (centreless G C).card ≤
      2 * (centreless G C).card + (junk G C).card + (orN G C \ lam G C).card := by
  classical
  have hserved := missing_centre_false_or_centreless_served_all G C hL hT hfour p X hres
    color hXcol c hc hccol hcne hno
  have hfalse := false_or_centreless_served_budget G C hL.1 hT hfour p X hX hres
  rw [hserved] at hfalse
  have hmixsplit := Finset.card_sdiff_add_card_eq_card (mixing_subset_extra G C)
  let J := (junk G C).filter fun j => gateVal n C j (pairInput p p) = false
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (show J ⊆ junk G C from Finset.filter_subset _ _)
  have heq : junk G C \ J =
      (junk G C).filter (fun j => gateVal n C j (pairInput p p) = true) := by
    ext j
    simp only [J,Finset.mem_sdiff,Finset.mem_filter]
    cases gateVal n C j (pairInput p p) <;> simp
  rw [heq] at hsplit
  change X.card ≤ ((orN G C \ lam G C) \ mixing G C).card + J.card + (centreless G C).card at hfalse
  omega

end MissingCentreMixing


namespace MissingCentreMixing

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
open CircuitLedger CircuitLedger.Budget FirstMixing

lemma accepting_centres_eq_of_two_mixing
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hAO : IsAO2 n C) (hT : TopForm G C) (p : Fin n)
    (color : Fin n → Bool)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hccol : ∀ a, color (c a) = color p) (hcne : ∀ a, c a ≠ p)
    (hmix : (mixing G C).card ≤ 2)
    (hbad : ∃ m ∈ mixing G C, ∃ u ∈ orIn n C (n+m), color u ≠ color p)
    (a a' : {a // a ∈ tops G C \ centreless G C}) (l l' : Fin n)
    (hl : color l ≠ color p) (hl' : color l' ≠ color p)
    (hv : gateVal n C a.val (pairInput p l) = true)
    (hv' : gateVal n C a'.val (pairInput p l') = true) :
    c a = c a' := by
  classical
  obtain ⟨bad,hbadmem,u,hu,hucol⟩ := hbad
  have hsmall : ((mixing G C).erase bad).card ≤ 1 := by
    have := Finset.card_erase_add_one hbadmem
    omega
  have get (a : {a // a ∈ tops G C \ centreless G C}) (l : Fin n)
      (hl : color l ≠ color p) (hv : gateVal n C a.val (pairInput p l) = true) :
      ∃ m ∈ (mixing G C).erase bad, (orIn n C (n+m)).Nonempty ∧
        ∀ v ∈ orIn n C (n+m), v = c a := by
    have hcl : c a ≠ l := by
      intro he
      exact hl (he ▸ hccol a)
    have hex : ∃ m ∈ mixing G C, (orIn n C (n+m)).Nonempty ∧
        ∀ v ∈ orIn n C (n+m), v = c a := by
      rcases hc a with hs | hs
      · obtain ⟨m,hm,hn,hraw,_⟩ := singleton_operand_mixing hAO hT
          (Finset.mem_sdiff.mp a.property).1 0 hs (hcne a) hcl hv
        exact ⟨m,hm,hn,hraw⟩
      · obtain ⟨m,hm,hn,hraw,_⟩ := singleton_operand_mixing hAO hT
          (Finset.mem_sdiff.mp a.property).1 1 hs (hcne a) hcl hv
        exact ⟨m,hm,hn,hraw⟩
    obtain ⟨m,hm,hn,hraw⟩ := hex
    have hmne : m ≠ bad := by
      intro he
      subst m
      exact hucol ((congrArg color (hraw u hu)).trans (hccol a))
    exact ⟨m,Finset.mem_erase.mpr ⟨hmne,hm⟩,hn,hraw⟩
  obtain ⟨m,hm,hn,hraw⟩ := get a l hl hv
  obtain ⟨m',hm',_,hraw'⟩ := get a' l' hl' hv'
  have he : m = m' := Finset.card_le_one.mp hsmall m hm m' hm'
  subst m'
  obtain ⟨v,hv⟩ := hn
  exact (hraw v hv).symm.trans (hraw' v hv)

lemma residual_pencil_bad_mixing_of_card_le_two
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (hz : centreless G C = ∅) (p : Fin n) (X : Finset (Fin n)) (hXcard : 3 ≤ X.card)
    (hX : ∀ l ∈ X, G.Adj p l) (hres : ∀ l ∈ X, s(p,l) ∈ Ustar G C)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (hXcol : ∀ l ∈ X, color l ≠ color p)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hccol : ∀ a, color (c a) = color p) (hcne : ∀ a, c a ≠ p)
    (hmix : (mixing G C).card ≤ 2) :
    ∃ m ∈ mixing G C, ∃ u ∈ orIn n C (n+m), color u ≠ color p := by
  classical
  by_contra h
  have hmcol : ∀ m ∈ mixing G C, ∀ u ∈ orIn n C (n+m), color u = color p := by
    intro m hm u hu
    by_contra hne
    exact h ⟨m,hm,u,hu,hne⟩
  have hbound := star_card_le_mixing_of_point_mixing G C hL hT hfour hz p X hX hres
    color hbip hXcol c hc hccol hcne hmcol
  omega

/-- With at most two mixing gates, distinct selected centres cannot jointly serve
  a residual pencil of at least three leaves. -/
lemma two_mixing_one_accepting_top
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hL : IsLeastAO G C) (hT : TopForm G C) (hfour : NoFourCycle G)
    (hz : centreless G C = ∅) (p : Fin n) (X : Finset (Fin n)) (hXcard : 3 ≤ X.card)
    (hX : ∀ l ∈ X, G.Adj p l) (hres : ∀ l ∈ X, s(p,l) ∈ Ustar G C)
    (color : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → color u ≠ color v)
    (hXcol : ∀ l ∈ X, color l ≠ color p)
    (c : {a // a ∈ tops G C \ centreless G C} → Fin n)
    (hc : ∀ a, side (n := n) C a.val 0 = {c a} ∨ side (n := n) C a.val 1 = {c a})
    (hccol : ∀ a, color (c a) = color p) (hcne : ∀ a, c a ≠ p)
    (hcinj : Function.Injective c) (hmix : (mixing G C).card ≤ 2) :
    ∃ a ∈ tops G C, ∀ l ∈ X, gateVal n C a (pairInput p l) = true := by
  classical
  have hbad := residual_pencil_bad_mixing_of_card_le_two G C hL hT hfour hz p X hXcard
    hX hres color hbip hXcol c hc hccol hcne hmix
  obtain ⟨l0,hl0⟩ := Finset.card_pos.mp (show 0 < X.card by omega)
  obtain ⟨a,ha,hav⟩ := acceptedTop hL (hX l0 hl0)
  let aa : {a // a ∈ tops G C \ centreless G C} :=
    ⟨a,Finset.mem_sdiff.mpr ⟨ha,by simp [hz]⟩⟩
  refine ⟨a,ha,?_⟩
  intro l hl
  obtain ⟨a',ha',hav'⟩ := acceptedTop hL (hX l hl)
  let aa' : {a // a ∈ tops G C \ centreless G C} :=
    ⟨a',Finset.mem_sdiff.mpr ⟨ha',by simp [hz]⟩⟩
  have hec : c aa = c aa' := accepting_centres_eq_of_two_mixing hL.1 hT p color c hc
    hccol hcne hmix hbad aa aa' l0 l (hXcol l0 hl0) (hXcol l hl) hav hav'
  have he : a = a' := congrArg Subtype.val (hcinj hec)
  simpa only [he] using hav'

end MissingCentreMixing


end PEqualNP.Outside.L_meta_2583
