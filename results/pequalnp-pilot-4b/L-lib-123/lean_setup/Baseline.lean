import Mathlib
import PEqualNP.Library.Evasion.MBudget
import PEqualNP.Library.Evasion.MTrans

namespace Baseline

open PEqualNP.Library PEqualNP.Library.Evasion PEqualNP.Library.Machines

def swapLeft : Bool ⊕ Bool → Option (Bool ⊕ Bool)
  | .inl _ => none
  | .inr b => some (.inl b)

def swapRight : Bool ⊕ Bool → Option (Bool ⊕ Bool)
  | .inl b => some (.inr b)
  | .inr _ => none

lemma swap_time : ComputableInTime encodePair encodePair
    (fun p : List Bool × List Bool => (p.2, p.1)) (fun n => 4 * n + 4) := by
  apply tp_time _ _ _ swapLeft swapRight (.inl true)
  intro p
  simp [encodePair, List.filterMap_append, List.filterMap_map, Function.comp_def,
    swapLeft, swapRight]

def sealStep : Bool → Bool ⊕ Bool → Bool × Option (Bool ⊕ Bool) × Option (Bool ⊕ Bool)
  | seen, .inl _ => (seen, some (.inl true), none)
  | false, .inr b => (true, some (.inl false), some (.inl b))
  | true, .inr b => (true, some (.inl b), none)

def sealFinish : Bool → Option (Bool ⊕ Bool)
  | false => some (.inl false)
  | true => none

lemma seal_right (x : List Bool) :
    fstRun2 sealStep sealFinish true (x.map Sum.inr) = x.map Sum.inl := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [fstRun2, sealStep, ih]

lemma seal_start_right (x : List Bool) :
    fstRun2 sealStep sealFinish false (x.map Sum.inr) = .inl false :: x.map Sum.inl := by
  cases x with
  | nil => rfl
  | cons b x => simp [fstRun2, sealStep, seal_right]

lemma seal_run (u x : List Bool) :
    fstRun2 sealStep sealFinish false (encodePair (u, x)) =
      (List.replicate u.length true ++ false :: x).map Sum.inl := by
  induction u with
  | nil => simpa [encodePair] using seal_start_right x
  | cons b u ih => simpa [encodePair, fstRun2, sealStep, List.replicate_succ] using ih

lemma seal_time : ComputableInTime encodePair encodePair
    (fun p : List Bool × List Bool => (List.replicate p.1.length true ++ false :: p.2, []))
    (fun n => 3 * n + 3) := by
  have h := fst2_time encodePair encodePair
    (fun p : List Bool × List Bool => (List.replicate p.1.length true ++ false :: p.2, []))
    sealStep sealFinish false (.inl true) (by
      intro p
      simpa [encodePair] using (seal_run p.1 p.2).symm)
  exact time_mono h (by intro n; omega)

def pack (p : List Bool × List Bool) : List Bool × List Bool :=
  (List.replicate p.2.length true ++ false :: p.1, [])

lemma pack_time : ∃ C : ℕ, ComputableInTime encodePair encodePair pack
    (fun n => C * n + C) := by
  obtain ⟨C, hC⟩ := lin_comp (D := 1) swap_time seal_time (by
    intro p
    simp [encodePair]
    omega)
  exact ⟨C, hC⟩

def project : Bool ⊕ Bool → Option Bool
  | .inl b => some b
  | .inr _ => none

lemma project_time : ComputableInTime encodePair (fun x : List Bool => x)
    (fun p : List Bool × List Bool => p.1) (fun n => 4 * n + 4) := by
  apply tp_time _ _ _ project (fun _ => none) true
  intro p
  simp [encodePair, List.filterMap_append, List.filterMap_map, Function.comp_def, project]

lemma pair_decider (L : Language Bool) (t : ℕ → ℕ) (ht : Monotone t)
    (hL : L ∈ DTIME t) :
    DecidableInTime encodePair {p : List Bool × List Bool | p.1 ∈ L}
      (fun n => 6 * n + 6 + t n) := by
  obtain ⟨f, hf, hcomp⟩ := hL
  refine ⟨fun p => f p.1, fun p => hf p.1, ?_⟩
  have h := comp_time encodePair (fun x : List Bool => x) Computability.encodeBool
    (fun p : List Bool × List Bool => p.1) f _ t (fun n => n) project_time hcomp ht
    (by intro p; simp [encodePair])
  exact time_mono h (by intro n; omega)

lemma clocked_relation (L : Language Bool) (t : ℕ → ℕ) (ht : Monotone t)
    (hL : L ∈ DTIME t) :
    ∃ (R : Set (List Bool × List Bool)) (C : ℕ),
      DecidableInTime encodePair R (fun n => C * n + C) ∧
      (∀ x w, (x, w) ∈ R → x ∈ L) ∧
      (∀ x w, 6 * x.length + 6 + t x.length ≤ w.length → x ∈ L → (x, w) ∈ R) := by
  obtain ⟨B, CB, hB, hs, hc⟩ := budget _ _ (pair_decider L t ht hL)
  obtain ⟨fB, hfB, hcompB⟩ := hB
  obtain ⟨CP, hP⟩ := pack_time
  obtain ⟨C, hC⟩ := lin_comp (D := 1) hP hcompB (by
    intro p
    simp [pack, encodePair]
    omega)
  refine ⟨pack ⁻¹' B, C, ⟨fun p => fB (pack p), fun p => hfB (pack p), hC⟩, ?_, ?_⟩
  · intro x w h
    exact hs w.length x [] h
  · intro x w h hx
    apply hc w.length x []
    · simpa using h
    · exact hx

lemma alt_three (s : ℕ) (P : List Bool → Prop) :
    Alt 3 s P ↔ ∃ y, y.length = s ∧ ∀ z, z.length = s →
      ∃ w, w.length = s ∧ P (y ++ z ++ w) := by
  classical
  simp [Alt, List.append_assoc]

lemma alt_three_uniform (s : ℕ) (P : List Bool → Prop) (A : Prop)
    (h : ∀ w, w.length = 3 * s → (P w ↔ A)) : Alt 3 s P ↔ A := by
  rw [alt_three]
  constructor
  · rintro ⟨y, hy, hz⟩
    obtain ⟨w, hw, hp⟩ := hz (List.replicate s false) (by simp)
    exact (h _ (by simp [List.length_append, hy, hw]; omega)).mp hp
  · intro hA
    refine ⟨List.replicate s false, by simp, ?_⟩
    intro z hz
    refine ⟨List.replicate s false, by simp, ?_⟩
    exact (h _ (by simp [List.length_append, hz]; omega)).mpr hA

lemma matching_exponent (p : ℕ) (hp : 1 ≤ p) : FP3 p p := by
  intro L hL
  obtain ⟨A, hA⟩ := hL
  let t : ℕ → ℕ := fun n => A * 2 ^ (p * n) + A
  have ht : Monotone t := by
    intro a b hab
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hab))) _
  obtain ⟨R, C, hR, hs, hc⟩ := clocked_relation L t ht hA
  refine ⟨A + 6, by omega, R, C, hR, ?_⟩
  intro x
  apply Iff.symm
  apply alt_three_uniform
  intro w hw
  constructor
  · exact hs x w
  · intro hx
    apply hc x w _ hx
    have hn : x.length ≤ 2 ^ (p * x.length) := by
      calc
        x.length ≤ 2 ^ x.length := (Nat.lt_two_pow_self).le
        _ ≤ 2 ^ (p * x.length) := Nat.pow_le_pow_right (by omega) (by nlinarith)
    dsimp [t]
    nlinarith

end Baseline
