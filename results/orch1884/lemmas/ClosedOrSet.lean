import PEqualNP.MetaComplexity.Helpers.LiftFixMain
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

namespace PEqualNP.Outside.L_meta_1884.ClosedOrSet

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.LiftFix

lemma or_read (n : Nat) (D : Circuit) (hR : ReadsBack n D)
    (k : Nat) (g : Gate) (hg : D.gates[k]? = some g) (hop : g.op = GateOp.or)
    (i : Nat) (hi : i ∈ g.inputs) (x : Fin n → Bool)
    (hv : (D.wires (List.ofFn x)).getD i false = true) :
    (D.wires (List.ofFn x)).getD (n + k) false = true := by
  have hk := (List.getElem?_eq_some_iff.mp hg).1
  have hkg := (List.getElem?_eq_some_iff.mp hg).2
  have hir := readsBack_get n D hR k g hg i hi
  have he := LowMergeProof.wires_gate D (List.ofFn x) k hk
  simp only [List.length_ofFn, hkg, hop, GateOp.eval] at he
  rw [he]
  simp only [List.any_eq_true, List.mem_map]
  exact ⟨true, ⟨i, hi, by simpa only [LowMergeProof.rd, if_pos hir] using hv⟩, rfl⟩

lemma closed_true (n : Nat) (D : Circuit) (T : Finset Nat)
    (hR : ReadsBack n D) (hA : PA D T) (hB : PB n D T)
    (j : Nat) (hj : j ∈ T) (x : Fin n → Bool)
    (hv : (D.wires (List.ofFn x)).getD (n + j) false = true) :
    circuitFun n D x = true := by
  have aux : ∀ m j, D.gates.length ≤ j + m → j ∈ T →
      (D.wires (List.ofFn x)).getD (n + j) false = true →
      circuitFun n D x = true := by
    intro m
    induction m with
    | zero =>
      intro j hbound hj _
      obtain ⟨g, hg, _⟩ := hA j hj
      have := (List.getElem?_eq_some_iff.mp hg).1
      omega
    | succ m ih =>
      intro j hbound hj hv
      rcases hB j hj with hout | ⟨k, hk, g, hg, hin⟩
      · simpa [circuitFun, Circuit.eval, hout] using hv
      · obtain ⟨g', hg', hop⟩ := hA k hk
        have heq : g' = g := Option.some.inj (hg'.symm.trans hg)
        subst g'
        have hlt := readsBack_get n D hR k g hg (n + j) hin
        exact ih k (by omega) hk (or_read n D hR k g hg hop (n + j) hin x hv)
  exact aux D.gates.length j (by omega) hj hv

theorem excludes_safe_or (n : Nat) (D : Circuit) (T : Finset Nat)
    (hR : ReadsBack n D) (hA : PA D T) (hB : PB n D T) (hC : PC n D T)
    (k : Nat) (g : Gate) (hg : D.gates[k]? = some g) (hop : g.op = GateOp.or)
    (a t : Nat) (ha : a ∈ g.inputs) (ht : t ∈ g.inputs)
    (hsat : ∃ x : Fin n → Bool, (D.wires (List.ofFn x)).getD a false = true)
    (hsafe : ∀ x : Fin n → Bool,
      (D.wires (List.ofFn x)).getD a false = true → circuitFun n D x = true)
    (x : Fin n → Bool) (hxt : (D.wires (List.ofFn x)).getD t false = true)
    (hxout : circuitFun n D x = false) : False := by
  have hk := hC k g hg hop a ha hsat hsafe
  have htrue := closed_true n D T hR hA hB k hk x (or_read n D hR k g hg hop t ht x hxt)
  rw [hxout] at htrue
  cases htrue

theorem normalize (n : Nat) (D : Circuit) (hM : Monotone2 D) (hR : ReadsBack n D) :
    ∃ D' : Circuit, Monotone2 D' ∧ ReadsBack n D' ∧ D'.size ≤ D.size ∧
      circuitFun n D' = circuitFun n D ∧
      ∃ T : Finset Nat, PA D' T ∧ PB n D' T ∧ PC n D' T := by
  exact main n (2 * D.gates.length) D ∅ (by simp) hM hR
    (by intro j hj; simp at hj) (by intro j hj; simp at hj)

theorem no_copy (n : Nat) (D : Circuit) (hM : Monotone2 D) (hR : ReadsBack n D)
    (hmin : ∀ E : Circuit, Monotone2 E → circuitFun n E = circuitFun n D → D.size ≤ E.size)
    (k a : Nat) (hk : k < D.gates.length) (ha : a < n + k)
    (hcopy : ∀ x : Fin n → Bool,
      (D.wires (List.ofFn x)).getD (n + k) false = (D.wires (List.ofFn x)).getD a false) :
    False := by
  have hfun := del_fun n k a D hk ha (readsBack_take n D hR k) hcopy
  have hsize := hmin (del n k a D) (del_mono n k a D hM) hfun
  have hlen := del_length n k a D hk
  simp only [Circuit.size] at hsize
  omega

end PEqualNP.Outside.L_meta_1884.ClosedOrSet
