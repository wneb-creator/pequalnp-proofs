import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2870_aux

private lemma sharing_point_ne_line {n : ℕ} (p l : Fin n) :
    Fin.castAdd n p ≠ Fin.natAdd n l := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  have hp := p.isLt
  omega

private lemma sharing_line_ne_point {n : ℕ} (l p : Fin n) :
    Fin.natAdd n l ≠ Fin.castAdd n p := (sharing_point_ne_line p l).symm

private lemma sharing_sound_pair (q n : ℕ) (I : Fin n → Fin n → Prop)
    (F : Finset (Finset (Fin (n+n)))) (hq : 1 ≤ q)
    (sound : ∀ t ∈ F, Fintype.card {l : Fin n // Fin.natAdd n l ∈ t} ≤ q →
      ∃ p l, I p l ∧ Fin.castAdd n p ∈ t ∧ Fin.natAdd n l ∈ t)
    (p l : Fin n) (mem : ({Fin.castAdd n p, Fin.natAdd n l} :
      Finset (Fin (n+n))) ∈ F) : I p l := by
  have small : Fintype.card {r : Fin n // Fin.natAdd n r ∈
      ({Fin.castAdd n p, Fin.natAdd n l} : Finset (Fin (n+n)))} ≤ q := by
    simp only [Finset.mem_insert, Finset.mem_singleton, sharing_line_ne_point,
      false_or, Fin.natAdd_inj]
    simpa using hq
  obtain ⟨a, b, inc, ha, hb⟩ := sound _ mem small
  simp only [Finset.mem_insert, Finset.mem_singleton, sharing_point_ne_line,
    or_false, Fin.castAdd_inj] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton, sharing_line_ne_point,
    false_or, Fin.natAdd_inj] at hb
  subst a b
  exact inc

lemma two_points_force_unique_line_context (q n : ℕ) (I : Fin n → Fin n → Prop)
    (A B F : Finset (Finset (Fin (n+n)))) (hq : 1 ≤ q)
    (join : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (product : ∀ a ∈ A, ∀ b ∈ B, a ∪ b ∈ F)
    (sound : ∀ t ∈ F, Fintype.card {l : Fin n // Fin.natAdd n l ∈ t} ≤ q →
      ∃ p l, I p l ∧ Fin.castAdd n p ∈ t ∧ Fin.natAdd n l ∈ t)
    (p r : Fin n) (different : p ≠ r)
    (hp : ({Fin.castAdd n p} : Finset (Fin (n+n))) ∈ A)
    (hr : ({Fin.castAdd n r} : Finset (Fin (n+n))) ∈ A)
    (l m : Fin n)
    (hl : ({Fin.natAdd n l} : Finset (Fin (n+n))) ∈ B)
    (hm : ({Fin.natAdd n m} : Finset (Fin (n+n))) ∈ B) : l = m := by
  have incident (a : Fin n) (ha : ({Fin.castAdd n a} : Finset (Fin (n+n))) ∈ A)
      (b : Fin n) (hb : ({Fin.natAdd n b} : Finset (Fin (n+n))) ∈ B) : I a b := by
    apply sharing_sound_pair q n I F hq sound a b
    simpa only [Finset.singleton_union] using product _ ha _ hb
  exact (join p r different).unique ⟨incident p hp l hl, incident r hr l hl⟩
    ⟨incident p hp m hm, incident r hr m hm⟩

end PEqualNP.Outside.L_meta_2870_aux
