import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.LiftMeasure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.TopForm PEqualNP.Outside.L_meta_4675.Pruning
  PEqualNP.Outside.L_meta_4675.ConeAPI PEqualNP.Outside.L_meta_4675.ConeTrace

lemma and_index_append_or (gs : List Gate) (g : Gate) (hgo : g.op = GateOp.or)
    (k : ℕ) (hk : k < (gs ++ [g]).length) (hand : (gateAt ⟨gs ++ [g], 0⟩ k).op = GateOp.and) :
    k < gs.length := by
  by_contra h
  have he : k = gs.length := by simp only [List.length_append, List.length_singleton] at hk; omega
  rw [he, gateAt_snoc_last, hgo] at hand
  cases hand

lemma andPairs_append_or (n : ℕ) (gs : List Gate) (g : Gate) (hgo : g.op = GateOp.or) :
    andPairs n ⟨gs ++ [g], 0⟩ = andPairs n ⟨gs, 0⟩ := by
  unfold andPairs
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨ha, hb⟩, hoa, hob, hc⟩
    have hao := and_index_append_or gs g hgo p.1 ha hoa
    have hbo := and_index_append_or gs g hgo p.2 hb hob
    rw [gateAt_snoc_old gs g p.1 hao] at hoa
    rw [gateAt_snoc_old gs g p.2 hbo] at hob
    refine ⟨⟨hao, hbo⟩, hoa, hob, ?_⟩
    unfold InCone at hc ⊢
    rwa [cones_append_prefix n gs [g] p.2 hbo] at hc
  · rintro ⟨⟨ha, hb⟩, hoa, hob, hc⟩
    refine ⟨⟨by simp; omega, by simp; omega⟩, ?_, ?_, ?_⟩
    · rwa [gateAt_snoc_old gs g p.1 ha]
    · rwa [gateAt_snoc_old gs g p.2 hb]
    · unfold InCone at hc ⊢
      rwa [cones_append_prefix n gs [g] p.2 hb]

lemma andPairs_output_eq (n : ℕ) (gs : List Gate) (u v : ℕ) :
    andPairs n ⟨gs, u⟩ = andPairs n ⟨gs, v⟩ := by
  unfold andPairs
  congr 1

lemma trace_cone (n q : ℕ) (C : Circuit) (o : ℕ → ℕ)
    (ht : GateTrace n C C.gates.length (compiled n q C.gates) o)
    (a b : ℕ) (ha : a < (pruned n q C).gates.length) (hb : b < (pruned n q C).gates.length)
    (hc : InCone n (pruned n q C) a b) : InCone n C (o a) (o b) := by
  have hab : a < b := PEqualNP.Outside.L_meta_4675.OneJunk.inCone_lt n (pruned n q C) b a hc
  have horig := ht.2.1 a b hab hb
  have hnew : WireCone n ⟨(compiled n q C.gates).1, 0⟩ (n + b) a :=
    Or.inr ⟨by omega, by simpa only [Nat.add_sub_cancel_left, InCone, cones, pruned] using hc⟩
  have hold := ht.2.2.2.2 (n + o b) (n + b) (ht.2.2.2.1 b hb) a ha hnew
  rcases hold with he | ⟨_, hold⟩
  · omega
  · simpa using hold

lemma trace_avoids (n q : ℕ) (C : Circuit) (o : ℕ → ℕ)
    (ht : GateTrace n C C.gates.length (compiled n q C.gates) o) (hq : q < C.gates.length)
    (k : ℕ) (hk : k < (pruned n q C).gates.length) : o k ≠ q := by
  intro he
  have hlookup := ht.2.2.2.1 k hk
  rw [he, killed_alias n q C.gates hq] at hlookup
  cases hlookup

lemma trace_injective (n q : ℕ) (C : Circuit) (o : ℕ → ℕ)
    (ht : GateTrace n C C.gates.length (compiled n q C.gates) o)
    (a b : ℕ) (ha : a < (pruned n q C).gates.length) (hb : b < (pruned n q C).gates.length)
    (he : o a = o b) : a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · have := ht.2.1 a b h hb; omega
  · exact h
  · have := ht.2.1 b a h ha; omega

def restoredBase (n q : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨(pruned n q C).gates ++ [⟨GateOp.and, [a, b]⟩], 0⟩

lemma restored_base_embedding (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hq : q < C.gates.length) (hqand : (gateAt C q).op = GateOp.and)
    (a b : ℕ) (hinputs : (gateAt C q).inputs = [a, b]) :
    ∃ f : ℕ → ℕ,
      (∀ k < (restoredBase n q C a b).gates.length, f k < C.gates.length) ∧
      (∀ k l, k < (restoredBase n q C a b).gates.length →
        l < (restoredBase n q C a b).gates.length → f k = f l → k = l) ∧
      (∀ k < (restoredBase n q C a b).gates.length,
        (gateAt (restoredBase n q C a b) k).op = (gateAt C (f k)).op) ∧
      (∀ k l, k < (restoredBase n q C a b).gates.length →
        l < (restoredBase n q C a b).gates.length → InCone n (restoredBase n q C a b) k l →
        InCone n C (f k) (f l) ∧ f k ≠ q) := by
  obtain ⟨o, ht⟩ := compiled_trace n q C hAO
  let K := (pruned n q C).gates.length
  let f := extendOrigin o K q
  have hsplit : ∀ k < (restoredBase n q C a b).gates.length, k < K ∨ k = K := by
    intro k hk
    have hk' : k < K + 1 := by simpa only [restoredBase, List.length_append, List.length_singleton] using hk
    omega
  have havoid : ∀ k < K, o k ≠ q := trace_avoids n q C o ht hq
  have hfo : ∀ k < K, f k = o k := by intro k hk; simp [f, extendOrigin, hk]
  have hfl : f K = q := by simp [f, extendOrigin]
  have hvld := (compiled_valid_related n q C hAO (List.replicate n false) (by simp)).1
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rcases hsplit k hk with hk | rfl
    · rw [hfo k hk]
      exact ht.1 k hk
    · rw [hfl]
      exact hq
  · intro k l hk hl he
    rcases hsplit k hk with hk | rfl <;> rcases hsplit l hl with hl | rfl
    · rw [hfo k hk, hfo l hl] at he
      exact trace_injective n q C o ht k l hk hl he
    · rw [hfo k hk, hfl] at he
      exact False.elim (havoid k hk he)
    · rw [hfl, hfo l hl] at he
      exact False.elim (havoid l hl he.symm)
    · rfl
  · intro k hk
    rcases hsplit k hk with hk | rfl
    · rw [hfo k hk]
      change (gateAt ⟨(pruned n q C).gates ++ [⟨GateOp.and, [a, b]⟩], 0⟩ k).op = _
      rw [gateAt_snoc_old _ _ k hk]
      exact ht.2.2.1 k hk
    · rw [hfl]
      change (gateAt ⟨(pruned n q C).gates ++ [⟨GateOp.and, [a, b]⟩], 0⟩ K).op = _
      rw [gateAt_snoc_last]
      exact hqand.symm
  · intro k l hk hl hcone
    have hkl := PEqualNP.Outside.L_meta_4675.OneJunk.inCone_lt n (restoredBase n q C a b) l k hcone
    have hko : k < K := by rcases hsplit l hl with h | h <;> omega
    rw [hfo k hko]
    refine ⟨?_, havoid k hko⟩
    rcases hsplit l hl with hlo | rfl
    · rw [hfo l hlo]
      apply trace_cone n q C o ht k l hko hlo
      unfold InCone at hcone ⊢
      change k ∈ (cones n ⟨(pruned n q C).gates ++ [⟨GateOp.and, [a, b]⟩], 0⟩).getD l [] at hcone
      rw [cones_append_prefix n (pruned n q C).gates [_] l hlo] at hcone
      exact hcone
    · rw [hfl]
      have hwire : WireCone n (restoredBase n q C a b) (n + K) k :=
        Or.inr ⟨by omega, by simpa only [Nat.add_sub_cancel_left] using hcone⟩
      have hK : K < (restoredBase n q C a b).gates.length := by simp [restoredBase, K]
      obtain he | ⟨w, hw, hwb, hwc⟩ := (wireCone_gate_iff n (restoredBase n q C a b) K hK k).mp hwire
      · omega
      · have hwin : w ∈ (gateAt C q).inputs := by
          change w ∈ (gateAt ⟨(pruned n q C).gates ++ [⟨GateOp.and, [a, b]⟩], 0⟩ K).inputs at hw
          rw [gateAt_snoc_last] at hw
          simpa [hinputs] using hw
        have hbefore : w < n + q := hAO.2.1 q hq w hwin
        have hmap := PEqualNP.Outside.L_meta_4675.PruningPrefix.alias_before n q C hAO (by omega) w hbefore
        have hwpruned := bounded_getD n (compiled n q C.gates) hvld.2 w w hmap
        have hwcp : WireCone n ⟨(compiled n q C.gates).1, 0⟩ w k :=
          (wireCone_append_prefix n (compiled n q C.gates).1 [⟨GateOp.and, [a, b]⟩] w hwpruned k).mp hwc
        have hwco := ht.2.2.2.2 w w hmap k hko hwcp
        have hparent := wireCone_of_input n C q hq w hwin hbefore (o k) hwco
        rcases hparent with he | ⟨_, hc⟩
        · have hneq := havoid k hko
          omega
        · simpa only [Nat.add_sub_cancel_left] using hc

lemma restored_base_andPairs_lt (n q r : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hq : q < C.gates.length) (hqand : (gateAt C q).op = GateOp.and)
    (hr : r < C.gates.length) (hrand : (gateAt C r).op = GateOp.and)
    (hcone : InCone n C q r) (a b : ℕ) (hinputs : (gateAt C q).inputs = [a, b]) :
    andPairs n (restoredBase n q C a b) < andPairs n C := by
  let _ : DecidableEq GateOp := gateOpDecEq
  obtain ⟨f, hf, hi, ho, hc⟩ := restored_base_embedding n q C hAO hq hqand a b hinputs
  let D := restoredBase n q C a b
  let S := ((Finset.range D.gates.length ×ˢ Finset.range D.gates.length).filter fun p =>
    (gateAt D p.1).op = GateOp.and ∧ (gateAt D p.2).op = GateOp.and ∧ InCone n D p.1 p.2)
  let T := ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter fun p =>
    (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)
  have hm : (q, r) ∈ T := by simp [T, hq, hr, hqand, hrand, hcone]
  have hle : S.card ≤ (T.erase (q, r)).card := by
    apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => (f p.1, f p.2))
    · intro p hp
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      have hpcone := hc p.1 p.2 hp.1.1 hp.1.2 hp.2.2.2
      apply Finset.mem_erase.mpr
      refine ⟨?_, ?_⟩
      · intro he
        exact hpcone.2 (congrArg Prod.fst he)
      · simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        exact ⟨⟨hf p.1 hp.1.1, hf p.2 hp.1.2⟩,
          (ho p.1 hp.1.1).symm.trans hp.2.1,
          (ho p.2 hp.1.2).symm.trans hp.2.2.1, hpcone.1⟩
    · intro p hp z hz he
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp hz
      exact Prod.ext (hi p.1 z.1 hp.1.1 hz.1.1 (congrArg Prod.fst he))
        (hi p.2 z.2 hp.1.2 hz.1.2 (congrArg Prod.snd he))
  exact lt_of_le_of_lt hle (Finset.card_erase_lt_of_mem hm)

lemma restoreStar_pairs (n : ℕ) (P : Circuit) (a b : ℕ) :
    andPairs n (PEqualNP.Outside.L_meta_4675.StarAppendOptional.restoreStar n P a b) =
      andPairs n ⟨P.gates ++ [⟨GateOp.and, [a, b]⟩], 0⟩ := by
  unfold PEqualNP.Outside.L_meta_4675.StarAppendOptional.restoreStar
  split_ifs
  · have h := andPairs_append_or n (P.gates ++ [⟨GateOp.and, [a, b]⟩])
      ⟨GateOp.or, [P.output, n + P.gates.length]⟩ rfl
    unfold PEqualNP.Outside.L_meta_4675.StarAppend.appendStar
    rw [andPairs_output_eq n _ (n + P.gates.length + 1) 0]
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using h
  · rfl

lemma restored_andPairs_lt (n q r : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hq : q < C.gates.length) (hqand : (gateAt C q).op = GateOp.and)
    (hr : r < C.gates.length) (hrand : (gateAt C r).op = GateOp.and)
    (hcone : InCone n C q r) (a b : ℕ) (hinputs : (gateAt C q).inputs = [a, b]) :
    andPairs n (PEqualNP.Outside.L_meta_4675.StarAppendOptional.restoreStar n (pruned n q C) a b) <
      andPairs n C := by
  rw [restoreStar_pairs]
  exact restored_base_andPairs_lt n q r C hAO hq hqand hr hrand hcone a b hinputs

end PEqualNP.Outside.L_meta_4675.LiftMeasure
