import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502

open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace FullCompile
abbrev W (ι : Type) := ι → Bool
def input {n : Nat} (i : Fin n) : W (Fin n → Bool) := fun x => x i
noncomputable def inputSet (n : Nat) : Finset (W (Fin n → Bool)) := Finset.univ.image input
def function (n : Nat) (C : Circuit) : W (Fin n → Bool) := fun x => C.eval (List.ofFn x)
def agrees {ι : Type} (goal : W ι) (F : (W ι → Bool) → Bool) : Prop :=
  ∀ x, F (fun f => f x) = goal x
def DirectedCut {n : Nat} (goal : W (Fin n → Bool)) (i : Fin n) : Prop :=
  ∃ x y, goal x = true ∧ goal y = false ∧
    ∀ j, x j = true → y j = false → j = i
lemma input_injective (n : Nat) : Function.Injective (@input n) := by
  intro i j hij
  by_contra hn
  have h := congrFun hij (fun k => decide (k=i))
  simp [input, Ne.symm hn] at h
end FullCompile

namespace Structural
variable {α : Type} [DecidableEq α]
def on (a c : α) : α → Bool := fun i => decide (i = a) || decide (i = c)
def Dep (F : (α → Bool) → Bool) (N : Finset α) : Prop :=
  ∀ x y : α → Bool, (∀ i ∈ N, x i = y i) → F x = F y
end Structural

namespace SemanticBridge
open FullCompile Structural

lemma agrees_on {n : Nat} {goal : (Fin n → Bool) → Bool}
    {F : (((Fin n → Bool) → Bool) → Bool) → Bool}
    (hd : Dep F (inputSet n)) (ha : agrees goal F) (i j : Fin n) :
    F (on (input i) (input j)) = goal (on i j) := by
  calc
    F (on (input i) (input j)) = F (fun f => f (on i j)) := by
      apply hd
      intro f hf
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hf
      change (decide (input k = input i) || decide (input k = input j)) =
        (decide (k = i) || decide (k = j))
      simp only [(input_injective n).eq_iff]
    _ = goal (on i j) := ha _

def leftWire (a : Fin 33) : Fin 66 := ⟨a.val, by omega⟩
def rightWire (b : Fin 33) : Fin 66 := ⟨33+b.val, by omega⟩

lemma oneEach_on (a b : Fin 33) :
    oneEach a b = List.ofFn (on (leftWire a) (rightWire b)) := by
  apply List.ext_getElem
  · simp [oneEach]
  · intro i hi hj
    simp only [oneEach, List.length_append, List.length_ofFn] at hi hj ⊢
    by_cases h : i < 33
    · rw [List.getElem_append_left (by simpa using h)]
      simp only [List.getElem_ofFn, on, Fin.ext_iff, leftWire, rightWire]
      have hn : ¬ i = 33 + b.val := by omega
      simp [hn]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn, on, Fin.ext_iff, leftWire, rightWire]
      have hn : ¬ i = a.val := by omega
      simp only [hn, decide_false, Bool.false_or, decide_eq_decide]
      omega

lemma agrees_represents {A : Fin 33 → Fin 33 → Bool} {C : Circuit}
    {F : (((Fin 66 → Bool) → Bool) → Bool) → Bool}
    (hd : Dep F (inputSet 66)) (ha : agrees (function 66 C) F) (hr : Represents A C) :
    ∀ a b : Fin 33, F (on (input (leftWire a)) (input (rightWire b))) = A a b := by
  intro a b
  rw [agrees_on hd ha]
  change C.eval (List.ofFn (on (leftWire a) (rightWire b))) = A a b
  rw [← oneEach_on]
  exact hr a b

lemma agrees_singletons {C : Circuit}
    {F : (((Fin 66 → Bool) → Bool) → Bool) → Bool}
    (hd : Dep F (inputSet 66)) (ha : agrees (function 66 C) F)
    (hs : ∀ i : Fin 66, C.eval (List.ofFn (fun j : Fin 66 => decide (j=i))) = false) :
    ∀ i : Fin 66, F (on (input i) (input i)) = false := by
  intro i
  rw [agrees_on hd ha]
  simpa [function, on] using hs i

def graph (a b : Fin 33) : Bool :=
  decide (∃ i : Fin 11,
    ((a.val = i.val ∨ a.val = 11+i.val) ∧ (b.val = (i.val+1)%11 ∨ b.val = 22+i.val)) ∨
    ((b.val = i.val ∨ b.val = 11+i.val) ∧ (a.val = (i.val+1)%11 ∨ a.val = 22+i.val)))

def neighbor (a : Fin 33) : Fin 33 :=
  if h : a.val < 22 then ⟨22+a.val%11, by omega⟩ else ⟨a.val-22, by omega⟩

lemma graph_neighbor : ∀ a : Fin 33, graph a (neighbor a) = true ∧ graph (neighbor a) a = true := by
  decide +kernel

lemma graph_diagonal : ∀ a : Fin 33, graph a a = false := by
  decide +kernel

lemma directed_left {C : Circuit} (hr : Represents graph C) (a : Fin 33) :
    DirectedCut (function 66 C) (leftWire a) := by
  let b := neighbor a
  refine ⟨on (leftWire a) (rightWire b), on (leftWire b) (rightWire b), ?_, ?_, ?_⟩
  · change C.eval (List.ofFn _) = true
    rw [← oneEach_on, hr]
    exact (graph_neighbor a).1
  · change C.eval (List.ofFn _) = false
    rw [← oneEach_on, hr]
    exact graph_diagonal b
  · intro j hx hy
    simp only [on, Bool.or_eq_true, decide_eq_true_eq] at hx
    rcases hx with h | h
    · exact h
    · subst j
      simp [on] at hy

lemma directed_right {C : Circuit} (hr : Represents graph C) (b : Fin 33) :
    DirectedCut (function 66 C) (rightWire b) := by
  let a := neighbor b
  refine ⟨on (leftWire a) (rightWire b), on (leftWire a) (rightWire a), ?_, ?_, ?_⟩
  · change C.eval (List.ofFn _) = true
    rw [← oneEach_on, hr]
    exact (graph_neighbor b).2
  · change C.eval (List.ofFn _) = false
    rw [← oneEach_on, hr]
    exact graph_diagonal a
  · intro j hx hy
    simp only [on, Bool.or_eq_true, decide_eq_true_eq] at hx
    rcases hx with h | h
    · subst j
      simp [on] at hy
    · exact h

lemma all_directed {C : Circuit} (hr : Represents graph C) :
    ∀ i : Fin 66, DirectedCut (function 66 C) i := by
  intro i
  by_cases h : i.val < 33
  · have hi : i = leftWire ⟨i.val,h⟩ := by apply Fin.ext; rfl
    rw [hi]
    exact directed_left hr _
  · have hh : i.val-33 < 33 := by omega
    have hi : i = rightWire ⟨i.val-33,hh⟩ := by apply Fin.ext; simp [rightWire]; omega
    rw [hi]
    exact directed_right hr _

end SemanticBridge
end PEqualNP.Outside.L_meta_9502
