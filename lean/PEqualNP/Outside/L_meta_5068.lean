import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_5068 : ∀ (x1 x2 x3 : ℕ) (x4 : Fin x2 → Fin x2 → Prop) [x5 : DecidableRel x4],   (∀ (x6 : Fin x2), Fintype.card { x7 : Fin x2 // x4 x7 x6 } = x1 + (1 : ℕ)) →     ∀ x7 ⊆ {x8 : Fin x2 × Fin x2 | x4 x8.1 x8.2},       x7.ncard ≤ (4 : ℕ) * x3 →         (100 : ℕ) * x3 < x2 * x1 →           have x11 : Set (Fin x2 × Fin x2) := {x11 : Fin x2 × Fin x2 | x4 x11.1 x11.2} \ x7;           (96 : ℕ) * x3 + x2 < x11.ncard ∧ (24 : ℕ) * (x2 * x1) + (25 : ℕ) * x2 < (25 : ℕ) * x11.ncard := by
  classical
  intro q n s I _ hline X hX hXs hbig
  have hfinI : ({e : Fin n × Fin n | I e.1 e.2} : Set (Fin n × Fin n)).Finite := Set.toFinite _
  have hI : ({e : Fin n × Fin n | I e.1 e.2} : Set (Fin n × Fin n)).ncard = n * (q + 1) := by
    rw [Set.ncard_eq_toFinset_card' ]
    have h1 : ({e : Fin n × Fin n | I e.1 e.2} : Set (Fin n × Fin n)).toFinset =
        Finset.univ.filter (fun e : Fin n × Fin n => I e.1 e.2) := by
      ext e; simp
    rw [h1]
    have h2 : (Finset.univ.filter (fun e : Fin n × Fin n => I e.1 e.2)).card =
        ∑ l : Fin n, ((Finset.univ.filter (fun e : Fin n × Fin n => I e.1 e.2)).filter
          (fun e => e.2 = l)).card :=
      Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    rw [h2]
    have h3 : ∀ l : Fin n, ((Finset.univ.filter (fun e : Fin n × Fin n => I e.1 e.2)).filter
        (fun e => e.2 = l)).card = q + 1 := by
      intro l
      rw [← hline l, Fintype.card_subtype]
      apply Finset.card_bij (fun e _ => e.1)
      · intro e he
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        rw [← he.2]; exact he.1
      · intro e1 he1 e2 he2 h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he1 he2
        exact Prod.ext h (he1.2.trans he2.2.symm)
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact ⟨(p, l), by simp [hp], rfl⟩
    simp [h3]
  have hdiff : (({e : Fin n × Fin n | I e.1 e.2} : Set (Fin n × Fin n)) \ X).ncard =
      n * (q + 1) - X.ncard := by
    rw [Set.ncard_diff hX (Set.toFinite X), hI]
  show 96 * s + n < (({e : Fin n × Fin n | I e.1 e.2} : Set (Fin n × Fin n)) \ X).ncard ∧
    24 * (n * q) + 25 * n < 25 * (({e : Fin n × Fin n | I e.1 e.2} : Set (Fin n × Fin n)) \ X).ncard
  rw [hdiff]
  have hmul : n * (q + 1) = n * q + n := by ring
  rw [hmul]
  constructor <;> omega
