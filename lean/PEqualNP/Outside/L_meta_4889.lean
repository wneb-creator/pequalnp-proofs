import Mathlib.Data.Finset.Card
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_4889.PlaneUnblocked

abbrev Adj (a b : Fin 13) : Prop :=
  (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)

lemma adj_comm (a b : Fin 13) : Adj a b ↔ Adj b a := by
  simp only [Adj, Nat.add_comm]

def neighbors (u : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter (Adj u)

lemma mem_neighbors (u v : Fin 13) : v ∈ neighbors u ↔ Adj u v := by
  simp [neighbors]

set_option maxRecDepth 10000 in
lemma neighbors_card : ∀ u : Fin 13, (neighbors u).card = 4 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma unique_common :
    ∀ u s v w : Fin 13, u ≠ s → Adj u v → Adj s v → Adj u w → Adj s w → v = w := by
  decide +kernel

lemma exists_unblocked (S : Finset (Fin 13)) (hS : S.card ≤ 3)
    (u : Fin 13) (hu : u ∉ S) :
    ∃ v : Fin 13, Adj u v ∧ ∀ s ∈ S, ¬ Adj s v := by
  classical
  by_contra h
  have cover (v : Fin 13) (hv : v ∈ neighbors u) : ∃ s ∈ S, Adj s v := by
    by_contra h'
    exact h ⟨v, (mem_neighbors u v).mp hv, fun s hs hadj => h' ⟨s, hs, hadj⟩⟩
  let f (v : Fin 13) : Fin 13 :=
    if hv : v ∈ neighbors u then Classical.choose (cover v hv) else 0
  have hf (v : Fin 13) (hv : v ∈ neighbors u) : f v ∈ S ∧ Adj (f v) v := by
    simpa only [f, dite_eq_left hv] using Classical.choose_spec (cover v hv)
  have hm : (neighbors u).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn f
    · intro v hv
      exact (hf v hv).1
    · intro v hv w hw heq
      have hv' := hf v hv
      have hw' := hf w hw
      exact unique_common u (f v) v w (fun he => hu (he ▸ hv'.1))
        ((mem_neighbors u v).mp hv) hv'.2 ((mem_neighbors u w).mp hw) (heq.symm ▸ hw'.2)
  rw [neighbors_card] at hm
  omega

end PEqualNP.Outside.L_meta_4889.PlaneUnblocked


namespace PEqualNP.Outside.L_meta_4889.PlaneBitAssignments

def bits (p l : Finset (Fin 13)) (i : Fin 26) : Bool :=
  if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ p) else decide (Fin.ofNat 13 i.val ∈ l)

lemma bits_castAdd (p l : Finset (Fin 13)) (u : Fin 13) :
    bits p l (Fin.castAdd 13 u) = decide (u ∈ p) := by
  have h : Fin.ofNat 13 u.val = u := by
    apply Fin.ext
    change u.val % 13 = u.val
    exact Nat.mod_eq_of_lt u.isLt
  change (if u.val < 13 then decide (Fin.ofNat 13 u.val ∈ p)
    else decide (Fin.ofNat 13 u.val ∈ l)) = decide (u ∈ p)
  rw [ite_eq_left u.isLt, h]

lemma bits_natAdd (p l : Finset (Fin 13)) (v : Fin 13) :
    bits p l (Fin.natAdd 13 v) = decide (v ∈ l) := by
  have h : Fin.ofNat 13 (13 + v.val) = v := by
    apply Fin.ext
    change (13 + v.val) % 13 = v.val
    omega
  have hv : ¬ 13 + v.val < 13 := by omega
  change (if 13 + v.val < 13 then decide (Fin.ofNat 13 (13 + v.val) ∈ p)
    else decide (Fin.ofNat 13 (13 + v.val) ∈ l)) = decide (v ∈ l)
  rw [ite_eq_right hv, h]

end PEqualNP.Outside.L_meta_4889.PlaneBitAssignments

namespace PEqualNP.Outside.L_meta_4889

open PlaneUnblocked PlaneBitAssignments

def accepts (x : Fin 26 → Bool) : Prop :=
  ∃ u v : Fin 13, Adj u v ∧ x (Fin.castAdd 13 u) = true ∧ x (Fin.natAdd 13 v) = true

def opposite (S : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun v => ∀ u ∈ S, ¬ Adj u v

lemma mem_opposite (S : Finset (Fin 13)) (v : Fin 13) :
    v ∈ opposite S ↔ ∀ u ∈ S, ¬ Adj u v := by
  simp [opposite]

lemma le_of_true_imp {a b : Bool} (h : a = true → b = true) : a ≤ b := by
  cases a <;> cases b <;> simp_all

lemma true_of_le {a b : Bool} (h : a ≤ b) (ha : a = true) : b = true := by
  subst a
  cases b with
  | false => exact False.elim ((by decide : ¬ (true ≤ false)) h)
  | true => rfl

lemma single_edge_minimal (u v : Fin 13) (huv : Adj u v) :
    Minimal accepts (bits {u} {v}) := by
  refine ⟨⟨u, v, huv, by simp [bits_castAdd], by rw [bits_natAdd]; simp⟩, ?_⟩
  intro x hx hle
  obtain ⟨u', v', _, hxu, hxv⟩ := hx
  have huu : u' = u := by
    have h := true_of_le (hle (Fin.castAdd 13 u')) hxu
    simpa only [bits_castAdd, decide_eq_true_eq, Finset.mem_singleton] using h
  have hvv : v' = v := by
    have h := true_of_le (hle (Fin.natAdd 13 v')) hxv
    simpa only [bits_natAdd, decide_eq_true_eq, Finset.mem_singleton] using h
  subst u'
  subst v'
  intro i
  refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
  · intro a
    apply le_of_true_imp
    intro ha
    have h : a = u := by simpa only [bits_castAdd, decide_eq_true_eq, Finset.mem_singleton] using ha
    simpa only [h] using hxu
  · intro b
    apply le_of_true_imp
    intro hb
    have h : b = v := by simpa only [bits_natAdd, decide_eq_true_eq, Finset.mem_singleton] using hb
    simpa only [h] using hxv

lemma maximal_of (P L : Finset (Fin 13))
    (hind : ∀ u ∈ P, ∀ v ∈ L, ¬ Adj u v)
    (hP : ∀ u ∉ P, ∃ v ∈ L, Adj u v)
    (hL : ∀ v ∉ L, ∃ u ∈ P, Adj u v) :
    Maximal (fun x => ¬ accepts x) (bits P L) := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    have hu' : u ∈ P := by simpa only [bits_castAdd, decide_eq_true_eq] using hu
    have hv' : v ∈ L := by simpa only [bits_natAdd, decide_eq_true_eq] using hv
    exact hind u hu' v hv' huv
  · intro x hx hle i
    refine Fin.addCases (m := 13) (n := 13) ?_ ?_ i
    · intro u
      apply le_of_true_imp
      intro hu
      rw [bits_castAdd, decide_eq_true_eq]
      by_contra hout
      obtain ⟨v, hv, huv⟩ := hP u hout
      have hbit : bits P L (Fin.natAdd 13 v) = true := by rw [bits_natAdd, decide_eq_true_eq]; exact hv
      exact hx ⟨u, v, huv, hu, true_of_le (hle (Fin.natAdd 13 v)) hbit⟩
    · intro v
      apply le_of_true_imp
      intro hv
      rw [bits_natAdd, decide_eq_true_eq]
      by_contra hout
      obtain ⟨u, hu, huv⟩ := hL v hout
      have hbit : bits P L (Fin.castAdd 13 u) = true := by simp [bits_castAdd, hu]
      exact hx ⟨u, v, huv, true_of_le (hle (Fin.castAdd 13 u)) hbit, hv⟩

lemma small_side_maximal (S : Finset (Fin 13)) (hS : S.card ≤ 3) :
    Maximal (fun x => ¬ accepts x) (bits S (opposite S)) ∧
      Maximal (fun x => ¬ accepts x) (bits (opposite S) S) := by
  have hind (u : Fin 13) (hu : u ∈ S) (v : Fin 13) (hv : v ∈ opposite S) : ¬ Adj u v :=
    (mem_opposite S v).mp hv u hu
  have hP (u : Fin 13) (hu : u ∉ S) : ∃ v ∈ opposite S, Adj u v := by
    obtain ⟨v, huv, hv⟩ := exists_unblocked S hS u hu
    exact ⟨v, (mem_opposite S v).mpr hv, huv⟩
  have hL (v : Fin 13) (hv : v ∉ opposite S) : ∃ u ∈ S, Adj u v := by
    by_contra h
    exact hv ((mem_opposite S v).mpr (fun u hu hadj => h ⟨u, hu, hadj⟩))
  refine ⟨maximal_of S (opposite S) hind hP hL, maximal_of (opposite S) S ?_ ?_ ?_⟩
  · intro u hu v hv huv
    exact hind v hv u hu ((adj_comm u v).mp huv)
  · intro u hu
    obtain ⟨v, hv, hvu⟩ := hL u hu
    exact ⟨v, hv, (adj_comm v u).mp hvu⟩
  · intro v hv
    obtain ⟨u, hu, hvu⟩ := hP v hv
    exact ⟨u, hu, (adj_comm v u).mp hvu⟩

end PEqualNP.Outside.L_meta_4889


open PEqualNP.Outside.L_meta_4889 PEqualNP.Outside.L_meta_4889.PlaneUnblocked
open PEqualNP.Outside.L_meta_4889.PlaneBitAssignments

theorem PEqualNP.Outside.L_meta_4889 :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; have x2 : (Fin (26 : ℕ) → Bool) → Prop := fun (x2 : Fin (26 : ℕ) → Bool) => ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) => if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4); have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x1 x6 x5}; (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → Minimal x2 (x3 {x5} {x6})) ∧ ∀ (x5 : Finset (Fin (13 : ℕ))), x5.card ≤ (3 : ℕ) → Maximal (fun (x7 : Fin (26 : ℕ) → Bool) => ¬x2 x7) (x3 x5 (x4 x5)) ∧ Maximal (fun (x7 : Fin (26 : ℕ) → Bool) => ¬x2 x7) (x3 (x4 x5) x5) := by
  change (∀ u v : Fin 13, Adj u v → Minimal accepts (bits {u} {v})) ∧
    ∀ S : Finset (Fin 13), S.card ≤ 3 →
      Maximal (fun x => ¬ accepts x) (bits S (opposite S)) ∧
      Maximal (fun x => ¬ accepts x) (bits (opposite S) S)
  exact ⟨single_edge_minimal, small_side_maximal⟩
