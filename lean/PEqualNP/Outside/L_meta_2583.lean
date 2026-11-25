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

end PEqualNP.Outside.L_meta_2583
