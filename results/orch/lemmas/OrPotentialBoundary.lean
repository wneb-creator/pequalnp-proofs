import Mathlib

namespace PEqualNP.Outside.L_meta_1031.OrPotentialBoundary

abbrev Sig := BitVec 37

def e1 : Sig := 512
def e2 : Sig := 4194304
def e3 : Sig := 2147483648
def e4 : Sig := 68719476736
def poison : Sig := 524288
def poison1 : Sig := 16384
def poison2 : Sig := 8388608
def target : Sig := e1 ||| e2 ||| e3 ||| e4

def inputSigs : List Sig := [65026, 4129284, 130089992, 2017593360,
  15175258144, 53972836416, 90765803648, 112812130560]

def base : List Sig := [0, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65026,
  65536, 131072, 262144, 524288, 1048576, 2097152, 4129284, 4194304, 8388608,
  16777216, 33554432, 67108864, 130089992, 134217728, 268435456, 536870912,
  1073741824, 2017593360, 2147483648, 4294967296, 8589934592, 15175258144,
  17179869184, 34359738368, 53972836416, 68719476736, 90765803648,
  112812130560, 137438953471]

def aSig : Sig := (e1 ||| poison) ||| e3
def bSig : Sig := (e2 ||| poison) ||| e4
def d1Sig : Sig := (e1 ||| poison1) ||| e2
def d2Sig : Sig := (e3 ||| poison2) ||| e4
def uSig : Sig := aSig ||| bSig

def operations : List (Sig × Sig) :=
  [(e1, poison), (e1 ||| poison, e3), (e2, poison), (e2 ||| poison, e4),
   (e1, poison1), (e1 ||| poison1, e2), (e3, poison2), (e3 ||| poison2, e4)]

def add (xs : List Sig) (v : Sig) : List Sig :=
  (xs ++ xs.map (fun x => x &&& v)).dedup

def run (xs : List Sig) (ops : List (Sig × Sig)) : List Sig :=
  ops.foldl (fun ys op => add ys (op.1 ||| op.2)) xs

def oldState : List Sig := run base operations
def newState : List Sig := add oldState uSig

lemma base_valid : 0 ∈ base ∧ (~~~(0 : Sig)) ∈ base ∧
    (∀ s ∈ inputSigs, s ∈ base) ∧
    ∀ s ∈ base, ∀ t ∈ base, (s &&& t) ∈ base := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · have h : inputSigs.all (fun s => base.contains s) = true := by decide +kernel
    simpa [List.contains_iff_mem] using h
  · have h : base.all (fun s => base.all (fun t => base.contains (s &&& t))) = true := by
      decide +kernel
    simpa [List.contains_iff_mem] using h

lemma operations_valid : ∀ i : Fin operations.length,
    let prev := run base (operations.take i.val)
    (operations.get i).1 ∈ prev ∧ (operations.get i).2 ∈ prev := by
  decide +kernel

lemma base_generated : ∀ s ∈ base,
    s = 0 ∨ s = ~~~(0 : Sig) ∨
      (∃ i : Fin 8, s = inputSigs.getD i.val 0) ∨
      ∃ i j : Fin 8, s = inputSigs.getD i.val 0 &&& inputSigs.getD j.val 0 := by
  have h : base.all (fun s => decide
      (s = 0 ∨ s = ~~~(0 : Sig) ∨
        (∃ i : Fin 8, s = inputSigs.getD i.val 0) ∨
        ∃ i j : Fin 8, s = inputSigs.getD i.val 0 &&& inputSigs.getD j.val 0)) = true := by
    decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp h s hs)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma old_closed : ∀ s ∈ oldState, ∀ t ∈ oldState, (s &&& t) ∈ oldState := by
  have h : oldState.all (fun s => oldState.all (fun t =>
      oldState.contains (s &&& t))) = true := by decide +kernel
  simpa [List.contains_iff_mem] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma old_proper : ∀ s ∈ oldState, s &&& ~~~target = 0 → s ∈ [0, e1, e2, e3, e4] := by
  have h : oldState.all (fun s => decide
      (s &&& ~~~target = 0 → s ∈ [0, e1, e2, e3, e4])) = true := by decide +kernel
  intro s hs
  exact of_decide_eq_true (List.all_eq_true.mp h s hs)

lemma new_step_valid : aSig ∈ oldState ∧ bSig ∈ oldState ∧
    uSig = aSig ||| bSig := by
  decide +kernel

lemma new_witnesses :
    (e1 ||| e2) ∈ newState ∧ (e3 ||| e4) ∈ newState ∧
    uSig &&& d1Sig = e1 ||| e2 ∧ uSig &&& d2Sig = e3 ||| e4 ∧
    e1 ≠ e2 ∧ e1 ≠ e3 ∧ e1 ≠ e4 ∧ e2 ≠ e3 ∧ e2 ≠ e4 ∧ e3 ≠ e4 := by
  decide +kernel

def sampleMasks : List (BitVec 8) := [0, 1, 2, 4, 8, 16, 32, 64, 128,
  3, 5, 9, 17, 33, 65, 129, 6, 10, 18, 34, 66, 130, 12, 20, 36, 68, 132,
  24, 40, 72, 136, 48, 80, 144, 96, 160, 192]

def sample (j : Fin 37) (i : Fin 8) : Bool :=
  (sampleMasks.getD j.val 0).getLsbD i.val

lemma input_certificates : ∀ i : Fin 8, ∀ j : Fin 37,
    (inputSigs.getD i.val 0).getLsbD j.val = sample j i := by
  decide +kernel

def E1 (x : Fin 8 → Bool) : Bool := x 0 && x 1
def E2 (x : Fin 8 → Bool) : Bool := x 2 && x 3
def E3 (x : Fin 8 → Bool) : Bool := x 4 && x 5
def E4 (x : Fin 8 → Bool) : Bool := x 6 && x 7
def P (x : Fin 8 → Bool) : Bool := x 1 && x 5
def P1 (x : Fin 8 → Bool) : Bool := x 0 && x 6
def P2 (x : Fin 8 → Bool) : Bool := x 2 && x 4
def A (x : Fin 8 → Bool) : Bool := (E1 x || P x) || E3 x
def B (x : Fin 8 → Bool) : Bool := (E2 x || P x) || E4 x
def D1 (x : Fin 8 → Bool) : Bool := (E1 x || P1 x) || E2 x
def D2 (x : Fin 8 → Bool) : Bool := (E3 x || P2 x) || E4 x
def U (x : Fin 8 → Bool) : Bool := A x || B x
def F (x : Fin 8 → Bool) : Bool := E1 x || E2 x || E3 x || E4 x

lemma signal_certificates : ∀ j : Fin 37,
    e1.getLsbD j.val = E1 (sample j) ∧ e2.getLsbD j.val = E2 (sample j) ∧
    e3.getLsbD j.val = E3 (sample j) ∧ e4.getLsbD j.val = E4 (sample j) ∧
    poison.getLsbD j.val = P (sample j) ∧ poison1.getLsbD j.val = P1 (sample j) ∧
    poison2.getLsbD j.val = P2 (sample j) ∧
    aSig.getLsbD j.val = A (sample j) ∧ bSig.getLsbD j.val = B (sample j) ∧
    d1Sig.getLsbD j.val = D1 (sample j) ∧ d2Sig.getLsbD j.val = D2 (sample j) := by
  decide +kernel

lemma sound_witnesses : ∀ x : Fin 8 → Bool,
    ((U x && D1 x) = true → F x = true) ∧
    ((U x && D2 x) = true → F x = true) ∧
    ((U x && D1 x) || (U x && D2 x)) = F x := by
  decide +kernel

abbrev Adj (u v : Fin 8) : Prop := u.val / 2 = v.val / 2 ∧ u ≠ v

lemma matching_girth : (∀ u : Fin 8, ¬ Adj u u) ∧
    (∀ u v : Fin 8, Adj u v → Adj v u) ∧
    (∀ a b c : Fin 8, Adj a b → Adj b c → ¬ Adj c a) ∧
    (∀ a b c d : Fin 8, Adj a b → Adj b c → Adj c d → Adj d a → a = c ∨ b = d) := by
  refine ⟨by intro u; simp [Adj], ?_, ?_, ?_⟩
  · intro u v h
    exact ⟨h.1.symm, h.2.symm⟩
  · intro a b c hab hbc hca
    simp only [Adj, Fin.ext_iff] at hab hbc hca
    omega
  · intro a b c d hab hbc _ _
    apply Or.inl
    apply Fin.ext
    simp only [Adj, Fin.ext_iff] at hab hbc
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma matching_function : ∀ x : Fin 8 → Bool,
    F x = decide (∃ u v : Fin 8, Adj u v ∧ x u = true ∧ x v = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_1031.OrPotentialBoundary
