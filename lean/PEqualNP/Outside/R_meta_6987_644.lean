import Mathlib
import PEqualNP.Defs

set_option maxRecDepth 16000 in
set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_6987_644
 (middle : ∀ (x1 : List (Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ)))),   (18 : ℕ) ≤ x1.length → x1.length ≤ (34 : ℕ) →     ∃ (x3 : Fin (16 : ℕ)) (x4 : Fin (13 : ℕ)) (x5 : Fin (3 : ℕ)),       have x6 : Fin (13 : ℕ) × Fin (4 : ℕ) → Fin (26 : ℕ) → Bool := fun (x6 : Fin (13 : ℕ) × Fin (4 : ℕ)) (x7 : Fin (26 : ℕ)) => Decidable.decide (x7 = Fin.castAdd (13 : ℕ) (x6.1 + [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x6.2 (0 : Fin (13 : ℕ))) ∨ x7 = Fin.natAdd (13 : ℕ) x6.1);       let x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x7 x8 : Fin (13 : ℕ)) => x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ));       have x8 : Finset (Fin (13 : ℕ)) := {x8 : Fin (13 : ℕ) | ([(4544 : ℕ), (2464 : ℕ), (6464 : ℕ), (5440 : ℕ), (4416 : ℕ), (3332 : ℕ), (5264 : ℕ), (3204 : ℕ), (3076 : ℕ), (2336 : ℕ), (6400 : ℕ), (5376 : ℕ), (5136 : ℕ), (6164 : ℕ), (6148 : ℕ), (6160 : ℕ)].getD ↑x3 (0 : ℕ)).testBit ↑((x8 - x4) * [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x5 (0 : Fin (13 : ℕ))) = Bool.true};       have x9 : Fin (26 : ℕ) → Bool := fun (x9 : Fin (26 : ℕ)) => Decidable.decide ((∃ x10 ∈ x8, x9 = Fin.castAdd (13 : ℕ) x10) ∨ ∃ (x10 : Fin (13 : ℕ)), x9 = Fin.natAdd (13 : ℕ) x10 ∧ ∀ x11 ∈ x8, ¬x7 x11 x10);       ¬List.foldl (fun (x10 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) → Prop) (x11 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) (x12 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x10 x12 ∨ x12 ⊆ x11.1 ∪ x11.2 ∧ x10 x11.1 ∧ x10 x11.2) (fun (x10 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x10 = ∅ ∨ ∃ (x11 : Fin (26 : ℕ)), x9 x11 = Bool.false ∧ ∀ x12 ∈ x10, x6 x12 x11 = Bool.true) x1 Finset.univ)
 (upper : ∀ (x1 : List (Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ)))),   (35 : ℕ) ≤ x1.length → x1.length ≤ (50 : ℕ) →     ∃ (x3 : Fin (16 : ℕ)) (x4 : Fin (13 : ℕ)) (x5 : Fin (3 : ℕ)),       have x6 : Fin (13 : ℕ) × Fin (4 : ℕ) → Fin (26 : ℕ) → Bool := fun (x6 : Fin (13 : ℕ) × Fin (4 : ℕ)) (x7 : Fin (26 : ℕ)) => Decidable.decide (x7 = Fin.castAdd (13 : ℕ) (x6.1 + [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x6.2 (0 : Fin (13 : ℕ))) ∨ x7 = Fin.natAdd (13 : ℕ) x6.1);       let x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x7 x8 : Fin (13 : ℕ)) => x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ));       have x8 : Finset (Fin (13 : ℕ)) := {x8 : Fin (13 : ℕ) | ([(4544 : ℕ), (2464 : ℕ), (6464 : ℕ), (5440 : ℕ), (4416 : ℕ), (3332 : ℕ), (5264 : ℕ), (3204 : ℕ), (3076 : ℕ), (2336 : ℕ), (6400 : ℕ), (5376 : ℕ), (5136 : ℕ), (6164 : ℕ), (6148 : ℕ), (6160 : ℕ)].getD ↑x3 (0 : ℕ)).testBit ↑((x8 - x4) * [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x5 (0 : Fin (13 : ℕ))) = Bool.true};       have x9 : Fin (26 : ℕ) → Bool := fun (x9 : Fin (26 : ℕ)) => Decidable.decide ((∃ x10 ∈ x8, x9 = Fin.castAdd (13 : ℕ) x10) ∨ ∃ (x10 : Fin (13 : ℕ)), x9 = Fin.natAdd (13 : ℕ) x10 ∧ ∀ x11 ∈ x8, ¬x7 x11 x10);       ¬List.foldl (fun (x10 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) → Prop) (x11 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) (x12 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x10 x12 ∨ x12 ⊆ x11.1 ∪ x11.2 ∧ x10 x11.1 ∧ x10 x11.2) (fun (x10 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x10 = ∅ ∨ ∃ (x11 : Fin (26 : ℕ)), x9 x11 = Bool.false ∧ ∀ x12 ∈ x10, x6 x12 x11 = Bool.true) x1 Finset.univ) :
∀ (x1 : List (Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ)))),   x1.length ≤ (50 : ℕ) →     ∃ (x3 : Fin (16 : ℕ)) (x4 : Fin (13 : ℕ)) (x5 : Fin (3 : ℕ)),       have x6 : Fin (13 : ℕ) × Fin (4 : ℕ) → Fin (26 : ℕ) → Bool := fun (x6 : Fin (13 : ℕ) × Fin (4 : ℕ)) (x7 : Fin (26 : ℕ)) => Decidable.decide (x7 = Fin.castAdd (13 : ℕ) (x6.1 + [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x6.2 (0 : Fin (13 : ℕ))) ∨ x7 = Fin.natAdd (13 : ℕ) x6.1);       let x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x7 x8 : Fin (13 : ℕ)) => x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ));       have x8 : Finset (Fin (13 : ℕ)) := {x8 : Fin (13 : ℕ) | ([(4544 : ℕ), (2464 : ℕ), (6464 : ℕ), (5440 : ℕ), (4416 : ℕ), (3332 : ℕ), (5264 : ℕ), (3204 : ℕ), (3076 : ℕ), (2336 : ℕ), (6400 : ℕ), (5376 : ℕ), (5136 : ℕ), (6164 : ℕ), (6148 : ℕ), (6160 : ℕ)].getD ↑x3 (0 : ℕ)).testBit ↑((x8 - x4) * [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x5 (0 : Fin (13 : ℕ))) = Bool.true};       have x9 : Fin (26 : ℕ) → Bool := fun (x9 : Fin (26 : ℕ)) => Decidable.decide ((∃ x10 ∈ x8, x9 = Fin.castAdd (13 : ℕ) x10) ∨ ∃ (x10 : Fin (13 : ℕ)), x9 = Fin.natAdd (13 : ℕ) x10 ∧ ∀ x11 ∈ x8, ¬x7 x11 x10);       ¬List.foldl (fun (x10 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) → Prop) (x11 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) (x12 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x10 x12 ∨ x12 ⊆ x11.1 ∪ x11.2 ∧ x10 x11.1 ∧ x10 x11.2) (fun (x10 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x10 = ∅ ∨ ∃ (x11 : Fin (26 : ℕ)), x9 x11 = Bool.false ∧ ∀ x12 ∈ x10, x6 x12 x11 = Bool.true) x1 Finset.univ := by

  classical
  intro L hL
  by_cases hlo : 18 ≤ L.length
  · by_cases hmid : L.length ≤ 34
    · exact middle L hlo hmid
    · exact upper L (by omega) hL
  refine ⟨0, 0, 0, ?_⟩
  let E := Fin 13 × Fin 4
  let X : E → Fin 26 → Bool := fun e v => decide
    (v = Fin.castAdd 13 (e.1 + ([0,1,3,9] : List (Fin 13)).getD e.2.val 0) ∨
     v = Fin.natAdd 13 e.1)
  let P : Finset (Fin 13) := {p | (4544 : ℕ).testBit p.val = true}
  let neg : Fin 26 → Bool := fun v => decide
    ((∃ p ∈ P, v = Fin.castAdd 13 p) ∨ ∃ l : Fin 13,
      v = Fin.natAdd 13 l ∧ ∀ p ∈ P, ¬(p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9))
  let W : Finset E := {(0,0),(0,1),(1,1),(0,2),(1,2),(2,2),(0,3),(1,3),(2,3),
    (3,2),(4,2),(5,1),(6,0),(7,0),(8,0),(9,2),(10,3),(11,1),(12,0)}
  let Q : Finset E → Prop := fun S => S = ∅ ∨ ∃ v : Fin 26,
    neg v = false ∧ ∀ e ∈ S, X e v = true
  let st : (Finset E → Prop) → Finset E × Finset E → Finset E → Prop :=
    fun D p S => D S ∨ S ⊆ p.1 ∪ p.2 ∧ D p.1 ∧ D p.2
  simp only [Fin.val_zero, List.getD_cons_zero, sub_zero, mul_one]
  change ¬L.foldl st Q Finset.univ
  have wc : W.card = 19 := by decide +kernel
  have star : ∀ v : Fin 26, neg v = false →
      (W.filter fun e => X e v = true).card ≤ 1 := by
    intro v
    fin_cases v <;> decide +kernel
  have base : ∀ S, Q S → (S ∩ W).card ≤ 1 := by
    intro S hS
    rcases hS with rfl | ⟨v, hv, hs⟩
    · simp
    · apply le_trans (Finset.card_le_card ?_) (star v hv)
      intro e he
      exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp he).2, hs e (Finset.mem_inter.mp he).1⟩
  have count : ∀ G : List (Finset E × Finset E), ∀ T : Finset (Finset E),
      (∀ S ∈ T, G.foldl st Q S) → (T.biUnion (fun S => S ∩ W)).card ≤ G.length + T.card := by
    intro G
    induction G using List.reverseRecOn with
    | nil =>
      intro T hT
      calc
        (T.biUnion (fun S => S ∩ W)).card ≤ ∑ S ∈ T, (S ∩ W).card := Finset.card_biUnion_le
        _ ≤ ∑ S ∈ T, 1 := Finset.sum_le_sum (fun S hS => base S (hT S hS))
        _ = 0 + T.card := by simp
    | append_singleton G p ih =>
      intro T hT
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at hT
      by_cases hall : ∀ S ∈ T, G.foldl st Q S
      · have hc := ih T hall
        simpa only [List.length_append, List.length_singleton] using
          (show (T.biUnion (fun S => S ∩ W)).card ≤ G.length + 1 + T.card by omega)
      · push Not at hall
        obtain ⟨S0, hs0, hbad⟩ := hall
        let A := T.filter (fun S => G.foldl st Q S)
        let T' := A ∪ {p.1, p.2}
        have hp : G.foldl st Q p.1 ∧ G.foldl st Q p.2 := by
          exact ((hT S0 hs0).resolve_left hbad).2
        have hT' : ∀ S ∈ T', G.foldl st Q S := by
          intro S hS
          rcases Finset.mem_union.mp hS with h | h
          · exact (Finset.mem_filter.mp h).2
          · simp only [Finset.mem_insert, Finset.mem_singleton] at h
            rcases h with rfl | rfl
            · exact hp.1
            · exact hp.2
        have sub : T.biUnion (fun S => S ∩ W) ⊆ T'.biUnion (fun S => S ∩ W) := by
          intro e he
          obtain ⟨S, hS, heS⟩ := Finset.mem_biUnion.mp he
          by_cases ho : G.foldl st Q S
          · exact Finset.mem_biUnion.mpr ⟨S, Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS,ho⟩), heS⟩
          · have hm := ((hT S hS).resolve_left ho).1 (Finset.mem_inter.mp heS).1
            rcases Finset.mem_union.mp hm with h | h
            · exact Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_union_right _ (by simp), Finset.mem_inter.mpr ⟨h,(Finset.mem_inter.mp heS).2⟩⟩
            · exact Finset.mem_biUnion.mpr ⟨p.2, Finset.mem_union_right _ (by simp), Finset.mem_inter.mpr ⟨h,(Finset.mem_inter.mp heS).2⟩⟩
        have asub : A ⊆ T.erase S0 := by
          intro S hS
          obtain ⟨h1,h2⟩ := Finset.mem_filter.mp hS
          exact Finset.mem_erase.mpr ⟨fun eq => hbad (eq ▸ h2),h1⟩
        have ac := Finset.card_le_card asub
        have ec := Finset.card_erase_of_mem hs0
        have uc := Finset.card_union_le A ({p.1,p.2} : Finset (Finset E))
        have pc : ({p.1,p.2} : Finset (Finset E)).card ≤ 2 := by
          have h := Finset.card_insert_le p.1 ({p.2} : Finset (Finset E))
          simpa using h
        have tp : 0 < T.card := Finset.card_pos.mpr ⟨S0, hs0⟩
        have tc : T'.card ≤ T.card + 1 := by dsimp [T']; omega
        have hc := ih T' hT'
        have sc := Finset.card_le_card sub
        simp only [List.length_append, List.length_singleton]
        omega
  intro h
  have hc := count L {Finset.univ} (by intro S hS; have e : S = Finset.univ := Finset.mem_singleton.mp hS; subst S; exact h)
  simp only [Finset.singleton_biUnion, Finset.univ_inter, Finset.card_singleton] at hc
  omega
