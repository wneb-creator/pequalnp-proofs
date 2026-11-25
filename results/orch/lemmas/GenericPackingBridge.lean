import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502_aux

def cycle33 (a b : Fin 33) : Bool :=
  decide (∃ i : Fin 11,
    ((a.val = i.val ∨ a.val = 11 + i.val) ∧
      (b.val = (i.val + 1) % 11 ∨ b.val = 22 + i.val)) ∨
    ((b.val = i.val ∨ b.val = 11 + i.val) ∧
      (a.val = (i.val + 1) % 11 ∨ a.val = 22 + i.val)))

def packedP4A (i : Fin 14) : Fin 33 :=
  ⟨([1, 2, 4, 6, 7, 9, 10, 11, 24, 14, 16, 29, 19, 32] : List Nat)[i.val]! % 33,
    Nat.mod_lt _ (by decide)⟩

def packedP4B (i : Fin 14) : Fin 33 :=
  ⟨([22, 13, 25, 27, 18, 30, 21, 23, 12, 26, 28, 17, 31, 20] : List Nat)[i.val]! % 33,
    Nat.mod_lt _ (by decide)⟩

def packedP4C (i : Fin 14) : Fin 33 :=
  ⟨([11, 24, 14, 16, 29, 19, 32, 1, 2, 4, 6, 7, 9, 10] : List Nat)[i.val]! % 33,
    Nat.mod_lt _ (by decide)⟩

def packedP4D (i : Fin 14) : Fin 33 :=
  ⟨([23, 12, 26, 28, 17, 31, 20, 22, 13, 25, 27, 18, 30, 21] : List Nat)[i.val]! % 33,
    Nat.mod_lt _ (by decide)⟩

def packedP4Wire (i : Fin 14) (j : Fin 4) : Fin 66 :=
  if j.val = 0 then ⟨(packedP4A i).val, by omega⟩
  else if j.val = 1 then ⟨(packedP4B i).val, by omega⟩
  else if j.val = 2 then ⟨33 + (packedP4C i).val, by omega⟩
  else ⟨33 + (packedP4D i).val, by omega⟩

lemma packedP4_edges : ∀ i,
    cycle33 (packedP4A i) (packedP4C i) = true ∧
    cycle33 (packedP4A i) (packedP4D i) = true ∧
    cycle33 (packedP4B i) (packedP4C i) = true ∧
    cycle33 (packedP4B i) (packedP4D i) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma packedP4_disjoint : Function.Injective
    (fun p : Fin 14 × Fin 4 => packedP4Wire p.1 p.2) := by
  decide +kernel

lemma packedP4_hitting_size (S : Finset (Fin 66))
    (h : ∀ i : Fin 14, ∃ j : Fin 4, packedP4Wire i j ∈ S) : 14 ≤ S.card := by
  classical
  choose j hj using h
  let f : Fin 14 → {v // v ∈ S} := fun i => ⟨packedP4Wire i (j i), hj i⟩
  have hf : Function.Injective f := by
    intro i k heq
    have hw : packedP4Wire i (j i) = packedP4Wire k (j k) := congrArg Subtype.val heq
    exact congrArg Prod.fst (@packedP4_disjoint (i, j i) (k, j k) hw)
  have hc := Fintype.card_le_of_injective f hf
  simpa using hc


end PEqualNP.Outside.L_meta_9502_aux

namespace PEqualNP.Outside.L_meta_9502.Generic

universe u
variable {α : Type u} [DecidableEq α]

def on (a c : α) : α → Bool := fun i => decide (i = a) || decide (i = c)

theorem on_iff (a c i : α) : on a c i = true ↔ i = a ∨ i = c := by simp [on]

/-- `F` depends only on `N`. -/
def Dep (F : (α → Bool) → Bool) (N : Finset α) : Prop :=
  ∀ x y : α → Bool, (∀ i ∈ N, x i = y i) → F x = F y

/-- `F` is off at no wire, and accepted pairs of wires not accepted alone have no path. -/
def Free (F : (α → Bool) → Bool) : Prop :=
  F (fun _ => false) = false ∧ ∀ a b c d, F (on a a) = false → F (on b b) = false →
    F (on c c) = false → F (on d d) = false → F (on a c) = true → F (on a d) = true →
    F (on b c) = true → F (on b d) = true

theorem bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all


def zeroWires (S : Finset α) (x : α → Bool) : α → Bool :=
  fun i => if i ∈ S then false else x i

lemma zeroWires_on (S : Finset α) {p q : α} (hp : p ∉ S) (hq : q ∉ S) :
    zeroWires S (on p q) = on p q := by
  funext i
  by_cases hi : i ∈ S
  · have hip : i ≠ p := fun h => hp (h ▸ hi)
    have hiq : i ≠ q := fun h => hq (h ▸ hi)
    simp [zeroWires, hi, on, hip, hiq]
  · simp [zeroWires, hi]

open PEqualNP.Outside.L_meta_9502_aux

def leftWire (a : Fin 33) : Fin 66 := ⟨a.val, by omega⟩
def rightWire (b : Fin 33) : Fin 66 := ⟨33 + b.val, by omega⟩

omit [DecidableEq α] in
lemma packedP4_hitting_size_generic (wire : Fin 66 → α) (hinj : Function.Injective wire)
    (S : Finset α)
    (h : ∀ i : Fin 14, ∃ j : Fin 4, wire (packedP4Wire i j) ∈ S) : 14 ≤ S.card := by
  classical
  choose j hj using h
  let f : Fin 14 → {v // v ∈ S} := fun i => ⟨wire (packedP4Wire i (j i)), hj i⟩
  have hf : Function.Injective f := by
    intro i k heq
    have hw : packedP4Wire i (j i) = packedP4Wire k (j k) :=
      hinj (congrArg Subtype.val heq)
    exact congrArg Prod.fst (@packedP4_disjoint (i, j i) (k, j k) hw)
  have hc := Fintype.card_le_of_injective f hf
  simpa using hc

theorem cycle33_free_deletion_lower_generic
    (wire : Fin 66 → α) (hinj : Function.Injective wire)
    (F : (α → Bool) → Bool)
    (hrep : ∀ a b : Fin 33, F (on (wire (leftWire a)) (wire (rightWire b))) = cycle33 a b)
    (hsingle : ∀ w : Fin 66, F (on (wire w) (wire w)) = false)
    (S : Finset α)
    (hfree : Free (fun x => F (zeroWires S x))) : 14 ≤ S.card := by
  apply packedP4_hitting_size_generic wire hinj S
  intro i
  by_contra h
  have hn : ∀ j : Fin 4, wire (packedP4Wire i j) ∉ S := by simpa using h
  have hbad := hfree.2 (wire (packedP4Wire i 0)) (wire (packedP4Wire i 1))
    (wire (packedP4Wire i 2)) (wire (packedP4Wire i 3))
  simp only [zeroWires_on S (hn 0) (hn 0), zeroWires_on S (hn 1) (hn 1),
    zeroWires_on S (hn 2) (hn 2), zeroWires_on S (hn 3) (hn 3),
    zeroWires_on S (hn 0) (hn 2), zeroWires_on S (hn 0) (hn 3),
    zeroWires_on S (hn 1) (hn 2), zeroWires_on S (hn 1) (hn 3)] at hbad
  obtain ⟨heac, head, hebc, hebd⟩ := packedP4_edges i
  have he1 : F (on (wire (packedP4Wire i 0)) (wire (packedP4Wire i 2))) = true := by
    simpa [packedP4Wire, leftWire, rightWire, heac] using hrep (packedP4A i) (packedP4C i)
  have he2 : F (on (wire (packedP4Wire i 0)) (wire (packedP4Wire i 3))) = true := by
    simpa [packedP4Wire, leftWire, rightWire, head] using hrep (packedP4A i) (packedP4D i)
  have he3 : F (on (wire (packedP4Wire i 1)) (wire (packedP4Wire i 2))) = true := by
    simpa [packedP4Wire, leftWire, rightWire, hebc] using hrep (packedP4B i) (packedP4C i)
  have he4 : F (on (wire (packedP4Wire i 1)) (wire (packedP4Wire i 3))) = false := by
    simpa [packedP4Wire, leftWire, rightWire, hebd] using hrep (packedP4B i) (packedP4D i)
  have hf := hbad (hsingle _) (hsingle _) (hsingle _) (hsingle _) he1 he2 he3
  rw [he4] at hf
  exact Bool.noConfusion hf

end PEqualNP.Outside.L_meta_9502.Generic
