import Forced13Compile

namespace PEqualNP.Outside.L_meta_1884.ForcedTrueCompile

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers ElimManyCount

def identityMap (n : Nat) : List Stat := List.ofFn fun i : Fin n => Stat.wire i.val

lemma identity_invariant (n : Nat) (w : List Bool) (hw : w.length = n) :
    Inv n w w (identityMap n,[]) := by
  refine ⟨by simp [identityMap,hw],?_⟩
  intro i
  by_cases hi : i < n
  · simp [identityMap,hi,Stat.Valid,Stat.val,wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [identityMap];omega),
      List.getD_eq_default _ _ (by omega)]
    exact ⟨trivial,rfl⟩

theorem compile {α : Type} (n : Nat) (pre post : List Gate) (o : Nat)
    (input : α → List Bool) (hlen : ∀ x, (input x).length = n)
    (hp : ∀ g ∈ pre, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hs : ∀ g ∈ post, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hnonconstant : ∃ x y : α,
      Circuit.eval ⟨pre ++ ⟨.and,[]⟩ :: post,o⟩ (input x) ≠
        Circuit.eval ⟨pre ++ ⟨.and,[]⟩ :: post,o⟩ (input y)) :
    ∃ D : Circuit, Monotone2 D ∧
      D.size + 1 ≤ (pre ++ ⟨GateOp.and,[]⟩ :: post).length ∧
      ∀ x : α, D.eval (input x) =
        Circuit.eval ⟨pre ++ ⟨.and,[]⟩ :: post,o⟩ (input x) := by
  let gs := pre ++ ⟨GateOp.and,[]⟩ :: post
  have hmono : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hp g hg
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨Or.inl rfl,by decide⟩
      · exact hs g hg
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨hop,hlen⟩ := hmono g hg
    refine ⟨⟨?_,hlen⟩,?_⟩
    · rcases hop with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · intro hnot
      rcases hop with h | h <;> rw [h] at hnot <;> cases hnot
  let result := elim n gs (identityMap n,[])
  have hcost := forced_true_count n ∅ pre post (identityMap n,[])
    (fun g hg => hnok g (List.mem_append.mpr (Or.inl hg)))
    (fun g hg => hnok g (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hg))))
    (by simp [constant])
  have hsize : result.2.length + 1 ≤ gs.length := by
    change result.2.length + _ + _ + 1 ≤ _ at hcost
    simp only [List.length_nil,zero_add] at hcost
    dsimp only [gs]
    omega
  have hinv : ∀ x : α, Inv n (input x) (wiresFrom gs (input x)) result := by
    intro x
    exact inv_elim n _ (hlen x) gs _ _ (fun g hg => (hnok g hg).1)
      (identity_invariant n _ (hlen x))
  have hvalue : ∀ x : α,
      (result.1.getD o (Stat.const false)).val (wiresFrom result.2 (input x)) =
        Circuit.eval ⟨gs,o⟩ (input x) := by
    intro x
    exact ((hinv x).2 o).2
  cases hout : result.1.getD o (Stat.const false) with
  | const b =>
    obtain ⟨x,y,hne⟩ := hnonconstant
    have hx := hvalue x
    have hy := hvalue y
    rw [hout] at hx hy
    exact False.elim (hne (hx.symm.trans hy))
  | wire j =>
    refine ⟨⟨result.2,j⟩,?_,hsize,?_⟩
    · intro g hg
      have hop := Forced13Compile.elim_monotone n gs (identityMap n,[])
        (fun g hg => (hmono g hg).1) (by simp) g hg
      have hok := elim_ok n gs (identityMap n,[]) (by simp) g hg
      refine ⟨?_,hok.2⟩
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hop
    · intro x
      have h := hvalue x
      rw [hout] at h
      exact h

end PEqualNP.Outside.L_meta_1884.ForcedTrueCompile
