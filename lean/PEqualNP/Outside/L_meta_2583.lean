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


end PEqualNP.Outside.L_meta_2583
