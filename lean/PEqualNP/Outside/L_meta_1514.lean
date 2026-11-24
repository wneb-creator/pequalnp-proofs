import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1514 : ∀ (n : ℕ) (V : Fin 3 → Fin n) (M Y : Fin 3 → Finset (Fin n)) (P Q : Finset (Fin n)),
    Function.Injective V →
    (∀ x y z : Fin 3, x ≠ y → y ≠ z → x ≠ z → M x ∩ M y = {V z}) →
    (∀ x : Fin 3, ∀ p ∈ Y x, p ∈ M x ∧ ∀ y : Fin 3, p ≠ V y) →
    (∀ x : Fin 3, ¬ ((∃ v ∈ P, v ∉ M x) ∧ (∃ v ∈ Q, v ∉ M x))) →
    ∀ x y : Fin 3,
      (∃ p ∈ Y x, (∃ v ∈ P, v = p ∨ v = V x) ∧ (∃ v ∈ Q, v = p ∨ v = V x)) →
      (∃ p ∈ Y y, (∃ v ∈ P, v = p ∨ v = V y) ∧ (∃ v ∈ Q, v = p ∨ v = V y)) →
      x = y := by
  classical
  intro n V M Y P Q hV hM hY hPQ x y hx hy
  by_contra hxy
  obtain ⟨z, hzx, hzy⟩ : ∃ z : Fin 3, z ≠ x ∧ z ≠ y := by
    have : ∀ x y : Fin 3, x ≠ y → ∃ z : Fin 3, z ≠ x ∧ z ≠ y := by decide
    exact this x y hxy
  -- the vertex opposite a side is off that side
  have hoff : ∀ s t u : Fin 3, s ≠ t → t ≠ u → s ≠ u → V s ∉ M s := by
    intro s t u hst htu hsu hin
    have h1 : V s ∈ M t ∩ M u := by rw [hM t u s htu (Ne.symm hsu) (Ne.symm hst)]; simp
    have h2 : V s ∈ M s ∩ M t := Finset.mem_inter.2 ⟨hin, (Finset.mem_inter.1 h1).1⟩
    rw [hM s t u hst htu hsu, Finset.mem_singleton] at h2
    exact hsu (hV h2)
  -- an inner point of a side is on no other side
  have hin : ∀ s t u : Fin 3, s ≠ t → t ≠ u → s ≠ u → ∀ p ∈ Y s, p ∉ M t := by
    intro s t u hst htu hsu p hp hpt
    have h2 : p ∈ M s ∩ M t := Finset.mem_inter.2 ⟨(hY s p hp).1, hpt⟩
    rw [hM s t u hst htu hsu, Finset.mem_singleton] at h2
    exact (hY s p hp).2 u h2
  have hsplit : ∀ s : Fin 3, (∀ v ∈ P, v ∈ M s) ∨ (∀ v ∈ Q, v ∈ M s) := by
    intro s
    by_contra hcon
    push_neg at hcon
    exact hPQ s ⟨hcon.1, hcon.2⟩
  obtain ⟨p, hp, ⟨a, haP, ha⟩, ⟨b, hbQ, hb⟩⟩ := hx
  obtain ⟨p', hp', ⟨a', haP', ha'⟩, ⟨b', hbQ', hb'⟩⟩ := hy
  have hpV : p ≠ V x := (hY x p hp).2 x
  have hpV' : p' ≠ V y := (hY y p' hp').2 y
  have n1 : V x ∉ M x := hoff x y z hxy (Ne.symm hzy) (Ne.symm hzx)
  have n2 : p ∉ M y := hin x y z hxy (Ne.symm hzy) (Ne.symm hzx) p hp
  have n3 : p ∉ M z := hin x z y (Ne.symm hzx) hzy hxy p hp
  have n4 : V y ∉ M y := hoff y x z (Ne.symm hxy) (Ne.symm hzx) (Ne.symm hzy)
  have n5 : p' ∉ M x := hin y x z (Ne.symm hxy) (Ne.symm hzx) (Ne.symm hzy) p' hp'
  have n6 : p' ∉ M z := hin y z x (Ne.symm hzy) hzx (Ne.symm hxy) p' hp'
  rcases hsplit x with sx | sx <;> rcases hsplit y with sy | sy <;> rcases hsplit z with sz | sz
  all_goals
    first
    | (have h1 := sx a haP; have h2 := sy a haP
       rcases ha with rfl | rfl
       · exact n2 h2
       · exact n1 h1)
    | (have h1 := sx b hbQ; have h2 := sy b hbQ
       rcases hb with rfl | rfl
       · exact n2 h2
       · exact n1 h1)
    | (have h1 := sx a haP; have h2 := sz a haP
       rcases ha with rfl | rfl
       · exact n3 h2
       · exact n1 h1)
    | (have h1 := sx b hbQ; have h2 := sz b hbQ
       rcases hb with rfl | rfl
       · exact n3 h2
       · exact n1 h1)
    | (have h1 := sy a' haP'; have h2 := sz a' haP'
       rcases ha' with rfl | rfl
       · exact n6 h2
       · exact n4 h1)
    | (have h1 := sy b' hbQ'; have h2 := sz b' hbQ'
       rcases hb' with rfl | rfl
       · exact n6 h2
       · exact n4 h1)
    | (have h1 := sx a' haP'; have h2 := sy a' haP'
       rcases ha' with rfl | rfl
       · exact n5 h1
       · exact n4 h2)
    | (have h1 := sx b' hbQ'; have h2 := sy b' hbQ'
       rcases hb' with rfl | rfl
       · exact n5 h1
       · exact n4 h2)
