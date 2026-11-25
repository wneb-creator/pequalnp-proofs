import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Set.Image
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Intervals
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_670
namespace C2444
abbrev Sig := BitVec 512
def zero : Sig := 0
abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def Reach {R : Type} (roots : List (Wire R)) (k : Nat) (ws : List (Wire R)) : Prop :=
  ∀ P : Nat → List (Wire R) → Prop,
    (P 0 roots) →
    (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R}, P p bank → (ha : Available bank a) → P (p+1) (inv a :: bank)) →
    (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R}, (op : Bool) → P p bank → (ha : Available bank a) → (hb : Available bank b) → P (p+1) (combine op a b :: bank)) →
    P k ws
def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
end C2444
namespace C4338
abbrev Sig:=BitVec 512
def zero : Sig:=0
abbrev Wire (R : Type):=R → Bool
def inv {R} (a : Wire R) : Wire R:=fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r||b r else fun r => a r&&b r
def Constant {R} (a : Wire R) : Prop:=∃ b : Bool,a=fun _ => b
def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop:=v ∈ pool∨Constant v
def Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop:=fun p bank =>
  ∀ (M : (Nat → List (Wire R) → Prop)),(M 0 roots) →
  (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R},M p bank → Available bank a → M (p+1) (inv a :: bank)) →
  (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool),M p bank → Available bank a → Available bank b → M (p+1) (combine op a b :: bank)) →
  M p bank
def bit (i : Fin 512) (a : Sig) : Bool:=a.getLsbD i.val
abbrev Row:=Fin 512
def observe (a : Sig) : Wire Row:=fun r => bit r a
def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank,Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p
def inputs : List Sig:=[0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat):=(selected m).map Prod.snd
def vertex (m j : Nat):=if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x:=vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
end C4338
namespace C1676
abbrev Sig := BitVec 512
def zero : Sig := 0
abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def Reach {R : Type} (roots : List (Wire R)) (k : Nat) (ws : List (Wire R)) : Prop :=
  ∀ P : Nat → List (Wire R) → Prop,
    (P 0 roots) →
    (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R}, P p bank → (ha : Available bank a) → P (p+1) (inv a :: bank)) →
    (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R}, (op : Bool) → P p bank → (ha : Available bank a) → (hb : Available bank b) → P (p+1) (combine op a b :: bank)) →
    P k ws
def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
end C1676
namespace C1678
abbrev Sig := BitVec 512
def zero : Sig := 0
abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def Reach {R : Type} (roots : List (Wire R)) (k : Nat) (ws : List (Wire R)) : Prop :=
  ∀ P : Nat → List (Wire R) → Prop,
    (P 0 roots) →
    (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R}, P p bank → (ha : Available bank a) → P (p+1) (inv a :: bank)) →
    (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R}, (op : Bool) → P p bank → (ha : Available bank a) → (hb : Available bank b) → P (p+1) (combine op a b :: bank)) →
    P k ws
def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
end C1678
namespace C1674
abbrev Sig := BitVec 512
def zero : Sig := 0
abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
end C1674
namespace C5120
abbrev Sig := BitVec 512
def zero : Sig := 0
abbrev Wire (R : Type) := R → Bool
def inv {R} (a : Wire R) : Wire R := fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b
def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)
def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
end C5120
namespace C1677
abbrev Sig := BitVec 512
def zero : Sig := 0
abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
end C1677
end PEqualNP.Outside.L_meta_670

namespace PEqualNP.Outside.L_meta_670.Equalities
theorem Lower_C4338 : PEqualNP.Outside.L_meta_670.C4338.Lower = PEqualNP.Outside.L_meta_670.C2444.Lower := rfl
theorem vars_C4338 : PEqualNP.Outside.L_meta_670.C4338.vars = PEqualNP.Outside.L_meta_670.C2444.vars := rfl
theorem graphGoal_C4338 : PEqualNP.Outside.L_meta_670.C4338.graphGoal = PEqualNP.Outside.L_meta_670.C2444.graphGoal := rfl
theorem bound_C4338 (m L : Nat) : PEqualNP.Outside.L_meta_670.C4338.Lower (PEqualNP.Outside.L_meta_670.C4338.vars m) (PEqualNP.Outside.L_meta_670.C4338.graphGoal m) L = PEqualNP.Outside.L_meta_670.C2444.Lower (PEqualNP.Outside.L_meta_670.C2444.vars m) (PEqualNP.Outside.L_meta_670.C2444.graphGoal m) L := rfl
theorem Lower_C1676 : PEqualNP.Outside.L_meta_670.C1676.Lower = PEqualNP.Outside.L_meta_670.C2444.Lower := rfl
theorem vars_C1676 : PEqualNP.Outside.L_meta_670.C1676.vars = PEqualNP.Outside.L_meta_670.C2444.vars := rfl
theorem graphGoal_C1676 : PEqualNP.Outside.L_meta_670.C1676.graphGoal = PEqualNP.Outside.L_meta_670.C2444.graphGoal := rfl
theorem bound_C1676 (m L : Nat) : PEqualNP.Outside.L_meta_670.C1676.Lower (PEqualNP.Outside.L_meta_670.C1676.vars m) (PEqualNP.Outside.L_meta_670.C1676.graphGoal m) L = PEqualNP.Outside.L_meta_670.C2444.Lower (PEqualNP.Outside.L_meta_670.C2444.vars m) (PEqualNP.Outside.L_meta_670.C2444.graphGoal m) L := rfl
theorem Lower_C1678 : PEqualNP.Outside.L_meta_670.C1678.Lower = PEqualNP.Outside.L_meta_670.C2444.Lower := rfl
theorem vars_C1678 : PEqualNP.Outside.L_meta_670.C1678.vars = PEqualNP.Outside.L_meta_670.C2444.vars := rfl
theorem graphGoal_C1678 : PEqualNP.Outside.L_meta_670.C1678.graphGoal = PEqualNP.Outside.L_meta_670.C2444.graphGoal := rfl
theorem bound_C1678 (m L : Nat) : PEqualNP.Outside.L_meta_670.C1678.Lower (PEqualNP.Outside.L_meta_670.C1678.vars m) (PEqualNP.Outside.L_meta_670.C1678.graphGoal m) L = PEqualNP.Outside.L_meta_670.C2444.Lower (PEqualNP.Outside.L_meta_670.C2444.vars m) (PEqualNP.Outside.L_meta_670.C2444.graphGoal m) L := rfl
theorem reach_C5120 {R : Type} (u : Bool) (roots : List (R → Bool)) (p : Nat) (bank : List (R → Bool)) : PEqualNP.Outside.L_meta_670.C5120.Reach u roots p bank = PEqualNP.Outside.L_meta_670.C1674.Reach u roots p bank := by
  induction p generalizing bank with
  | zero => rfl
  | succ p ih => simp only [PEqualNP.Outside.L_meta_670.C5120.Reach, PEqualNP.Outside.L_meta_670.C1674.Reach, ih] <;> rfl
theorem Lower_C5120 : PEqualNP.Outside.L_meta_670.C5120.Lower = PEqualNP.Outside.L_meta_670.C1674.Lower := by
  funext u roots T L
  simp only [PEqualNP.Outside.L_meta_670.C5120.Lower, PEqualNP.Outside.L_meta_670.C1674.Lower, reach_C5120] <;> rfl
theorem vars_C5120 : PEqualNP.Outside.L_meta_670.C5120.vars = PEqualNP.Outside.L_meta_670.C1674.vars := rfl
theorem graphGoal_C5120 : PEqualNP.Outside.L_meta_670.C5120.graphGoal = PEqualNP.Outside.L_meta_670.C1674.graphGoal := rfl
theorem bound_C5120 (m L : Nat) : PEqualNP.Outside.L_meta_670.C5120.Lower true (PEqualNP.Outside.L_meta_670.C5120.vars m) (PEqualNP.Outside.L_meta_670.C5120.graphGoal m) L = PEqualNP.Outside.L_meta_670.C1674.Lower true (PEqualNP.Outside.L_meta_670.C1674.vars m) (PEqualNP.Outside.L_meta_670.C1674.graphGoal m) L := by rw [Lower_C5120, vars_C5120, graphGoal_C5120]
theorem reach_C1677 {R : Type} (u : Bool) (roots : List (R → Bool)) (p : Nat) (bank : List (R → Bool)) : PEqualNP.Outside.L_meta_670.C1677.Reach u roots p bank = PEqualNP.Outside.L_meta_670.C1674.Reach u roots p bank := by
  induction p generalizing bank with
  | zero => rfl
  | succ p ih => simp only [PEqualNP.Outside.L_meta_670.C1677.Reach, PEqualNP.Outside.L_meta_670.C1674.Reach, ih] <;> rfl
theorem Lower_C1677 : PEqualNP.Outside.L_meta_670.C1677.Lower = PEqualNP.Outside.L_meta_670.C1674.Lower := by
  funext u roots T L
  simp only [PEqualNP.Outside.L_meta_670.C1677.Lower, PEqualNP.Outside.L_meta_670.C1674.Lower, reach_C1677] <;> rfl
theorem vars_C1677 : PEqualNP.Outside.L_meta_670.C1677.vars = PEqualNP.Outside.L_meta_670.C1674.vars := rfl
theorem graphGoal_C1677 : PEqualNP.Outside.L_meta_670.C1677.graphGoal = PEqualNP.Outside.L_meta_670.C1674.graphGoal := rfl
theorem bound_C1677 (m L : Nat) : PEqualNP.Outside.L_meta_670.C1677.Lower true (PEqualNP.Outside.L_meta_670.C1677.vars m) (PEqualNP.Outside.L_meta_670.C1677.graphGoal m) L = PEqualNP.Outside.L_meta_670.C1674.Lower true (PEqualNP.Outside.L_meta_670.C1674.vars m) (PEqualNP.Outside.L_meta_670.C1674.graphGoal m) L := by rw [Lower_C1677, vars_C1677, graphGoal_C1677]
end PEqualNP.Outside.L_meta_670.Equalities
