import Mathlib
import PEqualNP.Defs

-- Cut by the first function added to the seed set. The seed set holds the constants, NOT x0 and
-- the nine inputs; a chain that reaches a pool containing the edge function either never adds a
-- new function, which the proof below rules out directly, or adds a first new one, an AND, an OR or
-- a NOT of seed functions. Each child is the same search started one step later, with that first
-- function known and known to be new.
theorem PEqualNP.Outside.R_meta_5320_1
    (andFirst : let x1 : Finset ((Fin (9 : ℕ) → Bool) → Bool) := (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => Bool.false) (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => Bool.true) (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => !x2 (0 : Fin (9 : ℕ))) (Finset.image (fun (x2 : Fin (9 : ℕ)) (x3 : Fin (9 : ℕ) → Bool) => x3 x2) Finset.univ))));
      ∀ x2 ∈ x1, ∀ x3 ∈ x1, (fun (x6 : Fin (9 : ℕ) → Bool) => x2 x6 && x3 x6) ∉ x1 →
      ∀ (x4 : Finset ((Fin (9 : ℕ) → Bool) → Bool)), Relation.ReflTransGen (fun (x2 x3 : Finset ((Fin (9 : ℕ) → Bool) → Bool)) => ∃ x4 ∈ x2, ∃ x5 ∈ x2, x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 && x5 x6) x2 ∨ x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 || x5 x6) x2 ∨ x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => !x4 x6) x2) (Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x2 x6 && x3 x6) x1) x4 → x4.card ≤ (26 : ℕ) → (22 : ℕ) ≤ (Finset.image (fun (x4 : (Fin (9 : ℕ) → Bool) → Bool) (x5 : Fin (8 : ℕ) → Bool) => x4 (Fin.cons Bool.false x5)) x4).card → (fun (x5 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x6 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 x6.1 && x5 x6.2) ∉ x4)
    (orFirst : let x1 : Finset ((Fin (9 : ℕ) → Bool) → Bool) := (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => Bool.false) (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => Bool.true) (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => !x2 (0 : Fin (9 : ℕ))) (Finset.image (fun (x2 : Fin (9 : ℕ)) (x3 : Fin (9 : ℕ) → Bool) => x3 x2) Finset.univ))));
      ∀ x2 ∈ x1, ∀ x3 ∈ x1, (fun (x6 : Fin (9 : ℕ) → Bool) => x2 x6 || x3 x6) ∉ x1 →
      ∀ (x4 : Finset ((Fin (9 : ℕ) → Bool) → Bool)), Relation.ReflTransGen (fun (x2 x3 : Finset ((Fin (9 : ℕ) → Bool) → Bool)) => ∃ x4 ∈ x2, ∃ x5 ∈ x2, x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 && x5 x6) x2 ∨ x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 || x5 x6) x2 ∨ x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => !x4 x6) x2) (Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x2 x6 || x3 x6) x1) x4 → x4.card ≤ (26 : ℕ) → (22 : ℕ) ≤ (Finset.image (fun (x4 : (Fin (9 : ℕ) → Bool) → Bool) (x5 : Fin (8 : ℕ) → Bool) => x4 (Fin.cons Bool.false x5)) x4).card → (fun (x5 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x6 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 x6.1 && x5 x6.2) ∉ x4)
    (notFirst : let x1 : Finset ((Fin (9 : ℕ) → Bool) → Bool) := (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => Bool.false) (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => Bool.true) (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => !x2 (0 : Fin (9 : ℕ))) (Finset.image (fun (x2 : Fin (9 : ℕ)) (x3 : Fin (9 : ℕ) → Bool) => x3 x2) Finset.univ))));
      ∀ x2 ∈ x1, (fun (x6 : Fin (9 : ℕ) → Bool) => !x2 x6) ∉ x1 →
      ∀ (x4 : Finset ((Fin (9 : ℕ) → Bool) → Bool)), Relation.ReflTransGen (fun (x2 x3 : Finset ((Fin (9 : ℕ) → Bool) → Bool)) => ∃ x4 ∈ x2, ∃ x5 ∈ x2, x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 && x5 x6) x2 ∨ x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 || x5 x6) x2 ∨ x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => !x4 x6) x2) (Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => !x2 x6) x1) x4 → x4.card ≤ (26 : ℕ) → (22 : ℕ) ≤ (Finset.image (fun (x4 : (Fin (9 : ℕ) → Bool) → Bool) (x5 : Fin (8 : ℕ) → Bool) => x4 (Fin.cons Bool.false x5)) x4).card → (fun (x5 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x6 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 x6.1 && x5 x6.2) ∉ x4) :
    ∀ (x1 : Finset ((Fin (9 : ℕ) → Bool) → Bool)), Relation.ReflTransGen (fun (x2 x3 : Finset ((Fin (9 : ℕ) → Bool) → Bool)) => ∃ x4 ∈ x2, ∃ x5 ∈ x2, x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 && x5 x6) x2 ∨ x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 || x5 x6) x2 ∨ x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => !x4 x6) x2) (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => Bool.false) (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => Bool.true) (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => !x2 (0 : Fin (9 : ℕ))) (Finset.image (fun (x2 : Fin (9 : ℕ)) (x3 : Fin (9 : ℕ) → Bool) => x3 x2) Finset.univ)))) x1 → x1.card ≤ (26 : ℕ) → (22 : ℕ) ≤ (Finset.image (fun (x4 : (Fin (9 : ℕ) → Bool) → Bool) (x5 : Fin (8 : ℕ) → Bool) => x4 (Fin.cons Bool.false x5)) x1).card → (fun (x5 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x6 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x5 x6.1 && x5 x6.2) ∉ x1 := by
  intro s hs hcard hslice hedge
  set R := (fun (x2 x3 : Finset ((Fin (9 : ℕ) → Bool) → Bool)) => ∃ x4 ∈ x2, ∃ x5 ∈ x2, x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 && x5 x6) x2 ∨ x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => x4 x6 || x5 x6) x2 ∨ x3 = Insert.insert (fun (x6 : Fin (9 : ℕ) → Bool) => !x4 x6) x2) with hR
  set init := (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => Bool.false) (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => Bool.true) (Insert.insert (fun (x2 : Fin (9 : ℕ) → Bool) => !x2 (0 : Fin (9 : ℕ))) (Finset.image (fun (x2 : Fin (9 : ℕ)) (x3 : Fin (9 : ℕ) → Bool) => x3 x2) Finset.univ)))) with hinit
  -- Peel the chain: either nothing new was ever added, or some first new function g, built from
  -- two seed functions, was inserted and the rest of the chain runs from the seed set plus g.
  have key : ∀ t, Relation.ReflTransGen R init t → t = init ∨
      ∃ g, g ∉ init ∧ (∃ a ∈ init, ∃ b ∈ init, g = (fun x => a x && b x) ∨
        g = (fun x => a x || b x) ∨ g = (fun x => !a x)) ∧
      Relation.ReflTransGen R (insert g init) t := by
    intro t ht
    induction ht with
    | refl => exact Or.inl rfl
    | tail _ step ih =>
      rcases ih with rfl | ⟨g, hg, hop, hreach⟩
      · have step' := step
        rw [hR] at step'
        obtain ⟨a, ha, b, hb, hu⟩ := step'
        rcases hu with rfl | rfl | rfl
        · by_cases hg : (fun x => a x && b x) ∈ init
          · exact Or.inl (Finset.insert_eq_of_mem hg)
          · exact Or.inr ⟨_, hg, ⟨a, ha, b, hb, Or.inl rfl⟩, Relation.ReflTransGen.refl⟩
        · by_cases hg : (fun x => a x || b x) ∈ init
          · exact Or.inl (Finset.insert_eq_of_mem hg)
          · exact Or.inr ⟨_, hg, ⟨a, ha, b, hb, Or.inr (Or.inl rfl)⟩, Relation.ReflTransGen.refl⟩
        · by_cases hg : (fun x => !a x) ∈ init
          · exact Or.inl (Finset.insert_eq_of_mem hg)
          · exact Or.inr ⟨_, hg, ⟨a, ha, b, hb, Or.inr (Or.inr rfl)⟩, Relation.ReflTransGen.refl⟩
      · exact Or.inr ⟨g, hg, hop, hreach.tail step⟩
  rcases key s hs with rfl | ⟨g, hg, ⟨a, ha, b, hb, hop⟩, hreach⟩
  · -- The edge function is not one of the twelve seed functions.
    rw [hinit] at hedge
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and] at hedge
    rcases hedge with h | h | h | ⟨i, h⟩
    · exact absurd (congrFun h (fun _ => true)) (by decide)
    · exact absurd (congrFun h (fun _ => false)) (by decide)
    · exact absurd (congrFun h (fun _ => false)) (by decide)
    · have h' := congrFun h (fun j => decide (j = i))
      fin_cases i <;> exact absurd h' (by decide)
  · rcases hop with rfl | rfl | rfl
    · exact andFirst a ha b hb hg s hreach hcard hslice hedge
    · exact orFirst a ha b hb hg s hreach hcard hslice hedge
    · exact notFirst a ha hg s hreach hcard hslice hedge
