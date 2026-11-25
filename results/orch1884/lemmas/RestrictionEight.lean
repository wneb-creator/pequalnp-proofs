import EightExtension
import Forced13Compile
import StrongRelaxRows

namespace PEqualNP.Outside.L_meta_1884.RestrictionEight

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.Helpers ElimManyCount

def inputMap : List Stat :=
  [Stat.wire 0,Stat.wire 1,Stat.const false,Stat.wire 2,Stat.wire 3,
    Stat.wire 4,Stat.wire 5,Stat.wire 6,Stat.wire 7]

def seed (y : Fin 8 → Bool) : List Bool :=
  [y 0,y 1,false,y 2,y 3,y 4,y 5,y 6,y 7]

def embed (y : Fin 8 → Bool) : Fin 9 → Bool :=
  ![y 0,y 1,false,y 2,y 3,y 4,y 5,y 6,y 7]

def deleted : Finset Nat := {2}

lemma input_constants : constant deleted inputMap := by
  intro k hk
  have hk' : k = 2 := by simpa [deleted] using hk
  subst k
  exact ⟨by decide,false,rfl⟩

lemma input_invariant (y : Fin 8 → Bool) :
    Inv 8 (List.ofFn y) (seed y) (inputMap,[]) := by
  refine ⟨rfl,?_⟩
  intro i
  by_cases hi : i < 9
  · interval_cases i <;> simp [inputMap,seed,Stat.Valid,Stat.val,wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [inputMap];omega),
      List.getD_eq_default _ _ (by simp [seed];omega)]
    exact ⟨trivial,rfl⟩

lemma seed_eq (y : Fin 8 → Bool) : seed y = List.ofFn (embed y) := by
  simp [seed,embed]

lemma target_eq : ∀ y : Fin 8 → Bool,
    StrongRelaxRows.target (embed y) = EightExtension.eight y := by decide +kernel

lemma nonconstant : ∃ x y : Fin 8 → Bool,
    EightExtension.eight x ≠ EightExtension.eight y := by
  exact ⟨fun _=>false,fun _=>true,by decide⟩

lemma mono_nok (D : Circuit) (hm : Monotone2 D) : ∀ g ∈ D.gates,NOk g := by
  intro g hg
  have hop : g.op = .and ∨ g.op = .or := by simpa using (hm g hg).1
  refine ⟨⟨?_,(hm g hg).2⟩,?_⟩
  · rcases hop with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · intro hnot
    rcases hop with h | h <;> rw [h] at hnot <;> cases hnot

theorem compile (D : Circuit) (hm : Monotone2 D)
    (hcorrect : ∀ y : Fin 8 → Bool,D.eval (seed y) = EightExtension.eight y) :
    ∃ C : Circuit,Monotone2 C ∧ C.size = (elim 8 D.gates (inputMap,[])).2.length ∧
      C.size+D.gates.countP (reads deleted) ≤ D.size ∧
      ∀ y : Fin 8 → Bool,C.eval (List.ofFn y) = EightExtension.eight y := by
  let result := elim 8 D.gates (inputMap,[])
  have hnok := mono_nok D hm
  have hsize := count_readers 8 deleted D.gates (inputMap,[]) hnok input_constants
  have hinv : ∀ y : Fin 8 → Bool,
      Inv 8 (List.ofFn y) (wiresFrom D.gates (seed y)) result := by
    intro y
    exact inv_elim 8 _ (by simp) D.gates _ _ (fun g hg=>(hnok g hg).1) (input_invariant y)
  have hvalue : ∀ y : Fin 8 → Bool,
      (result.1.getD D.output (Stat.const false)).val (wiresFrom result.2 (List.ofFn y)) =
        EightExtension.eight y := by
    intro y
    exact ((hinv y).2 D.output).2.trans (hcorrect y)
  cases hout : result.1.getD D.output (Stat.const false) with
  | const b =>
    obtain ⟨x,y,hne⟩ := nonconstant
    have hx := hvalue x
    have hy := hvalue y
    rw [hout] at hx hy
    exact False.elim (hne (hx.symm.trans hy))
  | wire j =>
    refine ⟨⟨result.2,j⟩,?_,rfl,?_,?_⟩
    · intro g hg
      have hop := Forced13Compile.elim_monotone 8 D.gates (inputMap,[])
        (fun g hg=>by simpa using (hm g hg).1) (by simp) g hg
      have hok := elim_ok 8 D.gates (inputMap,[]) (by simp) g hg
      refine ⟨?_,hok.2⟩
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hop
    · simpa [Circuit.size,result] using hsize
    · intro y
      have h := hvalue y
      rw [hout] at h
      exact h

lemma mono_fan (D : Circuit) (hm : Monotone2 D) : FanInTwo D := by
  intro g hg
  obtain ⟨hop,hlen⟩ := hm g hg
  refine ⟨?_,hlen⟩
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop ⊢
  rcases hop with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem compiled_floor (D : Circuit) (hm : Monotone2 D)
    (hcorrect : ∀ y : Fin 8 → Bool,D.eval (seed y) = EightExtension.eight y) :
    12 ≤ (elim 8 D.gates (inputMap,[])).2.length := by
  obtain ⟨C,hmono,heq,_,hfun⟩ := compile D hm hcorrect
  have h := EightExtension.eight_floor C (mono_fan C hmono) hfun
  omega

theorem twelve_plus_readers (D : Circuit) (hm : Monotone2 D)
    (hcorrect : ∀ y : Fin 8 → Bool,D.eval (seed y) = EightExtension.eight y) :
    12+D.gates.countP (reads deleted) ≤ D.size := by
  obtain ⟨C,hmono,_,hsize,hfun⟩ := compile D hm hcorrect
  have h := EightExtension.eight_floor C (mono_fan C hmono) hfun
  omega

theorem cofactor_reader_floor (D : Circuit) (hm : Monotone2 D)
    (hcorrect : ∀ x : Fin 9 → Bool,x 2 = false →
      D.eval (List.ofFn x) = StrongRelaxRows.target x) :
    12+D.gates.countP (reads deleted) ≤ D.size := by
  apply twelve_plus_readers D hm
  intro y
  rw [seed_eq,hcorrect (embed y) (by simp [embed]),target_eq]

end PEqualNP.Outside.L_meta_1884.RestrictionEight
