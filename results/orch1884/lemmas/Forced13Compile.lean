import ElimManyCount

namespace PEqualNP.Outside.L_meta_1884.Forced13Compile

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers ElimManyCount

def inputMap : List Stat :=
  [Stat.const false, Stat.wire 0, Stat.wire 1, Stat.wire 2, Stat.wire 3,
    Stat.wire 4, Stat.wire 5, Stat.wire 6, Stat.wire 7, Stat.wire 8, Stat.const true]

def seed (y : Fin 9 → Bool) : List Bool :=
  [false,y 0,y 1,y 2,y 3,y 4,y 5,y 6,y 7,y 8,true]

def rails : Finset Nat := {0,10}

lemma input_constants : constant rails inputMap := by
  intro k hk
  simp only [rails, Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl
  · exact ⟨by decide, false, rfl⟩
  · exact ⟨by decide, true, rfl⟩

lemma input_invariant (y : Fin 9 → Bool) :
    Inv 9 (List.ofFn y) (seed y) (inputMap, []) := by
  refine ⟨rfl, ?_⟩
  intro i
  by_cases hi : i < 11
  · interval_cases i <;> simp [inputMap, seed, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [inputMap]; omega),
      List.getD_eq_default _ _ (by simp [seed]; omega)]
    exact ⟨trivial, rfl⟩

lemma simplify_monotone (op : GateOp) (hop : op = .and ∨ op = .or)
    (m : Nat) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1.toList, g.op = .and ∨ g.op = .or := by
  intro g hg
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;> simp [simplify, simpAnd] at hg
    subst g
    exact Or.inl rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
      (try cases a) <;> (try cases b) <;> simp [simplify, simpOr] at hg
    subst g
    exact Or.inr rfl

lemma elim_monotone (n : Nat) (gs : List Gate) (acc : List Stat × List Gate)
    (hg : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (ha : ∀ g ∈ acc.2, g.op = .and ∨ g.op = .or) :
    ∀ g ∈ (elim n gs acc).2, g.op = .and ∨ g.op = .or := by
  induction gs generalizing acc with
  | nil => exact ha
  | cons g gs ih =>
    apply ih (elimStep n acc g) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    intro g' hg'
    rcases List.mem_append.mp hg' with hold | hnew
    · exact ha g' hold
    · exact simplify_monotone g.op (hg g List.mem_cons_self) _ _ g' hnew

theorem compile (pre post : List Gate) (o : Nat)
    (hp : ∀ g ∈ pre, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hs : ∀ g ∈ post, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hsize : pre.length + post.length + 1 ≤ 18)
    (hcharge : 4 ≤ pre.countP (reads rails) +
      post.countP (reads (insert (11 + pre.length) rails)))
    (hnonconstant : ∃ x y : Fin 9 → Bool,
      Circuit.eval ⟨pre ++ ⟨.and, []⟩ :: post, o⟩ (seed x) ≠
        Circuit.eval ⟨pre ++ ⟨.and, []⟩ :: post, o⟩ (seed y)) :
    ∃ D : Circuit, Monotone2 D ∧ D.size ≤ 13 ∧
      ∀ y : Fin 9 → Bool, D.eval (List.ofFn y) =
        Circuit.eval ⟨pre ++ ⟨.and, []⟩ :: post, o⟩ (seed y) := by
  let gs := pre ++ ⟨GateOp.and, []⟩ :: post
  have hmono : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hp g hg
    · rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨Or.inl rfl, by decide⟩
      · exact hs g hg
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨hop, hlen⟩ := hmono g hg
    refine ⟨⟨?_, hlen⟩, ?_⟩
    · rcases hop with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · intro hnot
      rcases hop with h | h <;> rw [h] at hnot <;> cases hnot
  let result := elim 9 gs (inputMap, [])
  have hcost := forced_true_count 9 rails pre post (inputMap, [])
    (fun g hg => hnok g (List.mem_append.mpr (Or.inl hg)))
    (fun g hg => hnok g (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hg))))
    input_constants
  have hresult_size : result.2.length ≤ 13 := by
    change result.2.length + _ + _ + 1 ≤ _ at hcost
    simp only [inputMap, List.length_cons, List.length_nil, List.length_append] at hcost
    norm_num only at hcost
    omega
  have hinv : ∀ y : Fin 9 → Bool,
      Inv 9 (List.ofFn y) (wiresFrom gs (seed y)) result := by
    intro y
    exact inv_elim 9 _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (input_invariant y)
  have hvalue : ∀ y : Fin 9 → Bool,
      (result.1.getD o (Stat.const false)).val (wiresFrom result.2 (List.ofFn y)) =
        Circuit.eval ⟨gs,o⟩ (seed y) := by
    intro y
    exact ((hinv y).2 o).2
  cases hout : result.1.getD o (Stat.const false) with
  | const b =>
    obtain ⟨x, y, hne⟩ := hnonconstant
    have hx := hvalue x
    have hy := hvalue y
    rw [hout] at hx hy
    exact False.elim (hne (hx.symm.trans hy))
  | wire j =>
    refine ⟨⟨result.2,j⟩, ?_, hresult_size, ?_⟩
    · intro g hg
      have hop := elim_monotone 9 gs (inputMap, []) (fun g hg => (hmono g hg).1)
        (by simp) g hg
      have hok := elim_ok 9 gs (inputMap, []) (by simp) g hg
      refine ⟨?_, hok.2⟩
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop
    · intro y
      have h := hvalue y
      rw [hout] at h
      exact h

end PEqualNP.Outside.L_meta_1884.Forced13Compile
