import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2732_aux.SupportCounterexample

open Function

def columns : List ℕ := [7, 56, 11, 52, 19, 44, 35, 28, 13, 50, 21, 42]

def support (i : Fin 6) (u : Fin 12) : Prop :=
  (columns.getD u.val 0).testBit i.val = true

def accepted (u v : Fin 12) : Prop := ∀ i : Fin 6, support i u ∨ support i v

def matching (u v : Fin 12) : Prop := u.val / 2 = v.val / 2 ∧ u ≠ v

lemma pair_iff : ∀ u v : Fin 12, accepted u v ↔ matching u v := by
  unfold accepted support matching
  decide +kernel

lemma matching_symm (u v : Fin 12) (h : matching u v) : matching v u :=
  ⟨h.1.symm, Ne.symm h.2⟩

lemma matching_irrefl (u : Fin 12) : ¬ matching u u := fun h => h.2 rfl

lemma unique_neighbor (u v w : Fin 12) (hv : matching u v) (hw : matching u w) : v = w := by
  have huv : u.val ≠ v.val := fun h => hv.2 (Fin.ext h)
  have huw : u.val ≠ w.val := fun h => hw.2 (Fin.ext h)
  have hqv := hv.1
  have hqw := hw.1
  apply Fin.ext
  omega

lemma triangle_free (u v w : Fin 12)
    (huv : matching u v) (hvw : matching v w) : ¬ matching u w := by
  intro huw
  have h := unique_neighbor u v w huv huw
  exact hvw.2 h

lemma square_free (a a' b b' : Fin 12) (_ha : a ≠ a') (hb : b ≠ b') :
    ¬ (matching a b ∧ matching a b' ∧ matching a' b ∧ matching a' b') := by
  intro h
  exact hb (unique_neighbor a b b' h.1 h.2.1)

lemma no_five_cover : ¬ ∃ c : Fin 5 → Fin 12,
    ∀ u v, accepted u v → ∃ i : Fin 5, c i = u ∨ c i = v := by
  rintro ⟨c, hc⟩
  let f : Fin 5 → Fin 6 := fun i => ⟨(c i).val / 2, by have h := (c i).isLt; omega⟩
  have hsurj : Surjective f := by
    intro j
    let u : Fin 12 := ⟨2 * j.val, by have h := j.isLt; omega⟩
    let v : Fin 12 := ⟨2 * j.val + 1, by have h := j.isLt; omega⟩
    have huv : accepted u v := by
      apply (pair_iff u v).mpr
      refine ⟨?_, ?_⟩
      · dsimp [u, v]
        omega
      · intro h
        have he := congrArg Fin.val h
        dsimp [u, v] at he
        omega
    obtain ⟨i, hi | hi⟩ := hc u v huv
    · refine ⟨i, ?_⟩
      apply Fin.ext
      change (c i).val / 2 = j.val
      rw [hi]
      dsimp [u]
      omega
    · refine ⟨i, ?_⟩
      apply Fin.ext
      change (c i).val / 2 = j.val
      rw [hi]
      dsimp [v]
      omega
  have hcard := Fintype.card_le_of_surjective f hsurj
  simp only [Fintype.card_fin] at hcard
  omega

lemma independent_triple_accepted :
    (∀ i : Fin 6, support i 0 ∨ support i 2 ∨ support i 9) ∧
      ¬ matching 0 2 ∧ ¬ matching 0 9 ∧ ¬ matching 2 9 := by
  unfold support matching
  decide +kernel

end PEqualNP.Outside.L_meta_2732_aux.SupportCounterexample
