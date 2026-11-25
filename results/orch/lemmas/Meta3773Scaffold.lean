import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3773_aux

open PEqualNP.CircuitLowerBounds

def incidenceSet : Finset (Fin 13) := {0,1,3,9}

def positiveInput (a b : Fin 13) : List Bool :=
  List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd 13 a) (Fin.natAdd 13 b))

def negativeLeft (S : Finset (Fin 13)) : List Bool :=
  List.ofFn fun i : Fin (13+13) =>
    Fin.addCases (fun a : Fin 13 => decide (a ∈ S))
      (fun b : Fin 13 => decide (∀ a ∈ S, a+b ∉ incidenceSet)) i

def negativeRight (S : Finset (Fin 13)) : List Bool :=
  List.ofFn fun i : Fin (13+13) =>
    Fin.addCases (fun a : Fin 13 => decide (∀ b ∈ S, a+b ∉ incidenceSet))
      (fun b : Fin 13 => decide (b ∈ S)) i

def smallSets : Finset (Finset (Fin 13)) :=
  Finset.powersetCard 0 Finset.univ ∪ Finset.powersetCard 1 Finset.univ ∪
    Finset.powersetCard 2 Finset.univ ∪ Finset.powersetCard 3 Finset.univ

lemma mem_smallSets (S : Finset (Fin 13)) : S ∈ smallSets ↔ S.card ≤ 3 := by
  simp only [smallSets,Finset.mem_union,Finset.mem_powersetCard,
    Finset.subset_univ,true_and]
  omega

def gateCheck (g : Gate) : Bool :=
  match g.op with
  | .and => decide (g.inputs.length ≤ 2)
  | .or => decide (g.inputs.length ≤ 2)
  | _ => false

def monotoneCheck (C : Circuit) : Bool := C.gates.all gateCheck

lemma monotoneCheck_sound (C : Circuit) (h : monotoneCheck C = true) :
    PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  have hh : gateCheck g = true := List.all_eq_true.mp h g hg
  cases hop : g.op <;> simp [gateCheck,hop] at hh ⊢
  all_goals exact hh

def sizeCheck (C : Circuit) : Bool := decide (C.size ≤ 63)

def headCheck (C : Circuit) : Bool :=
  match C.gates.head? with
  | none => false
  | some g =>
    match g.op with
    | .and => decide (g.inputs = [0,13])
    | .or => decide (g.inputs ∈ [[0,1],[0,13],[2,13]])
    | _ => false

lemma headCheck_sound (C : Circuit) (h : headCheck C = true) :
    ∃ g : Gate, C.gates.head? = some g ∧
      (g.op = GateOp.and ∧ g.inputs = [0,13] ∨
        g.op = GateOp.or ∧ g.inputs ∈ [[0,1],[0,13],[2,13]]) := by
  cases he : C.gates.head? with
  | none => simp [headCheck,he] at h
  | some g =>
    refine ⟨g,rfl,?_⟩
    cases hop : g.op <;> simp [headCheck,he,hop] at h ⊢
    all_goals exact h

def positiveSamples : Finset (Fin 13 × Fin 13) :=
  Finset.univ.filter (fun p => p.1+p.2 ∈ incidenceSet)

def positiveFamilyCheck (C : Circuit) (family : Finset (Fin 13 × Fin 13)) : Bool :=
  decide (∀ p ∈ family, C.eval (positiveInput p.1 p.2) = true)

def positiveCheck (C : Circuit) : Bool := positiveFamilyCheck C positiveSamples

lemma positiveFamilyCheck_sound (C : Circuit) (family : Finset (Fin 13 × Fin 13))
    (h : positiveFamilyCheck C family = true) :
    ∀ p ∈ family, C.eval (positiveInput p.1 p.2) = true :=
  of_decide_eq_true h

def familyCheck (C : Circuit) (family : Finset (Finset (Fin 13))) : Bool :=
  decide (∀ S ∈ family,
    C.eval (negativeLeft S) = false ∧ C.eval (negativeRight S) = false)

def negativeCheck (C : Circuit) : Bool := familyCheck C smallSets

lemma familyCheck_sound (C : Circuit) (family : Finset (Finset (Fin 13)))
    (h : familyCheck C family = true) :
    ∀ S ∈ family,
      C.eval (negativeLeft S) = false ∧ C.eval (negativeRight S) = false :=
  of_decide_eq_true h

lemma positiveCheck_sound (C : Circuit) (h : positiveCheck C = true) :
    ∀ a b : Fin 13, a+b ∈ incidenceSet → C.eval (positiveInput a b) = true := by
  intro a b hab
  apply positiveFamilyCheck_sound C positiveSamples h (a,b)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hab⟩

lemma negativeCheck_sound (C : Circuit) (h : negativeCheck C = true) :
    ∀ S : Finset (Fin 13), S.card ≤ 3 →
      C.eval (negativeLeft S) = false ∧ C.eval (negativeRight S) = false := by
  intro S hS
  exact familyCheck_sound C smallSets h S ((mem_smallSets S).mpr hS)

end PEqualNP.Outside.L_meta_3773_aux
