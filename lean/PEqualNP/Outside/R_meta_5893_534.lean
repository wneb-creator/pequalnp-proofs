import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_5893_534
    (base : ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ), PEqualNP.MetaComplexity.Monotone2 x1 ∧ x1.size ≤ (45 : ℕ) ∧ x1.output < (25 : ℕ) + x1.size ∧ x2 < (25 : ℕ) + x1.size ∧ ∀ (x3 : Fin (25 : ℕ) → Bool), (x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (25 : ℕ)) (x5 : Fin (25 : ℕ)), ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ ↑x4 ∉ [(0 : ℕ), (2 : ℕ), (8 : ℕ)] ∧ x3 x4 = Bool.true ∧ x3 x5 = Bool.true) ∧ (x1.eval (List.ofFn x3) = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))))
    (extend : ∀ (n s : ℕ) (C : Circuit) (q : ℕ)
      (p : Fin 3 → Fin n) (l : Fin 3 → Fin 4 → Fin n) (t : Fin n),
      Monotone2 C → C.size ≤ s → C.output < n+C.size → q < n+C.size →
      ∃ (D : Circuit) (r : ℕ), Monotone2 D ∧ D.size = s+16 ∧
        D.output < n+D.size ∧ r < n+D.size ∧ ∀ x : Fin n → Bool,
        D.eval (List.ofFn x) = (C.eval (List.ofFn x) ||
          (x (p 0) && (x (l 0 0) || x (l 0 1) || x (l 0 2) || x (l 0 3))) ||
          (x (p 1) && (x (l 1 0) || x (l 1 1) || x (l 1 2) || x (l 1 3))) ||
          (x (p 2) && (x (l 2 0) || x (l 2 1) || x (l 2 2) || x (l 2 3)))) ∧
        (D.wires (List.ofFn x)).getD r false = ((C.wires (List.ofFn x)).getD q false || x t)) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ),   PEqualNP.MetaComplexity.Monotone2 x1 ∧     x1.size = (61 : ℕ) ∧       x1.output < (25 : ℕ) + x1.size ∧         x2 < (25 : ℕ) + x1.size ∧           ∀ (x3 : Fin (25 : ℕ) → Bool),             have x4 : Fin (25 : ℕ) → Fin (25 : ℕ) → Prop := fun (x4 x5 : Fin (25 : ℕ)) => ↑x4 < (12 : ℕ) ∧ (12 : ℕ) ≤ ↑x5 ∧ (↑x4 + ↑x5 + (2 : ℕ)) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];             have x5 : Bool := x1.eval (List.ofFn x3);             (x5 = Bool.true ↔ ∃ (x6 : Fin (25 : ℕ)) (x7 : Fin (25 : ℕ)), x4 x6 x7 ∧ x3 x6 = Bool.true ∧ x3 x7 = Bool.true) ∧ (x5 = Bool.false → (x1.wires (List.ofFn x3)).getD x2 Bool.false = (x3 (12 : Fin (25 : ℕ)) || x3 (13 : Fin (25 : ℕ)) || x3 (15 : Fin (25 : ℕ)) || x3 (21 : Fin (25 : ℕ)))) := by
  classical
  obtain ⟨C,q,hm,hsize,hout,hq,hC⟩ := base
  let p : Fin 3 → Fin 25 := ![0,2,8]
  let l : Fin 3 → Fin 4 → Fin 25 := ![![12,14,20,24],![12,18,22,23],![12,16,17,19]]
  obtain ⟨D,r,hD,hDs,hDo,hr,hDval⟩ := extend 25 45 C q p l 12 hm hsize hout hq
  refine ⟨D,r,hD,by omega,hDo,hr,?_⟩
  intro x
  dsimp only
  let old : Prop := ∃ a b : Fin 25, a.val < 12 ∧ 12 ≤ b.val ∧
    (a.val+b.val+2)%13 ∈ ([0,1,3,9] : List ℕ) ∧ a.val ∉ ([0,2,8] : List ℕ) ∧
    x a = true ∧ x b = true
  let full : Prop := ∃ a b : Fin 25, a.val < 12 ∧ 12 ≤ b.val ∧
    (a.val+b.val+2)%13 ∈ ([0,1,3,9] : List ℕ) ∧ x a = true ∧ x b = true
  let extra : Bool := (x 0 && (x 12 || x 14 || x 20 || x 24)) ||
    (x 2 && (x 12 || x 18 || x 22 || x 23)) ||
    (x 8 && (x 12 || x 16 || x 17 || x 19))
  have hsplit : full ↔ old ∨ extra = true := by
    dsimp [full,old,extra]
    simp only [Bool.or_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨a,b,ha,hb,hi,hxa,hxb⟩
      have hclass : a.val ∉ ([0,2,8] : List ℕ) ∨ a = 0 ∨ a = 2 ∨ a = 8 := by
        fin_cases a <;> simp_all
      rcases hclass with hne | rfl | rfl | rfl
      · exact Or.inl ⟨a,b,ha,hb,hi,hne,hxa,hxb⟩
      all_goals
        fin_cases b <;> simp_all <;> aesop
    · rintro (⟨a,b,ha,hb,hi,hne,hxa,hxb⟩ | h)
      · exact ⟨a,b,ha,hb,hi,hxa,hxb⟩
      · rcases h with (h | h) | h <;> rcases h with ⟨hp,hl⟩
        all_goals
          rcases hl with ((h | h) | h) | h <;>
          first | exact ⟨0,12,by decide,by decide,by decide,hp,h⟩
                | exact ⟨0,14,by decide,by decide,by decide,hp,h⟩
                | exact ⟨0,20,by decide,by decide,by decide,hp,h⟩
                | exact ⟨0,24,by decide,by decide,by decide,hp,h⟩
                | exact ⟨2,12,by decide,by decide,by decide,hp,h⟩
                | exact ⟨2,18,by decide,by decide,by decide,hp,h⟩
                | exact ⟨2,22,by decide,by decide,by decide,hp,h⟩
                | exact ⟨2,23,by decide,by decide,by decide,hp,h⟩
                | exact ⟨8,12,by decide,by decide,by decide,hp,h⟩
                | exact ⟨8,16,by decide,by decide,by decide,hp,h⟩
                | exact ⟨8,17,by decide,by decide,by decide,hp,h⟩
                | exact ⟨8,19,by decide,by decide,by decide,hp,h⟩
  have hc := hC x
  have hd := hDval x
  have hdval : D.eval (List.ofFn x) = (C.eval (List.ofFn x) || extra) := by
    simpa [p,l,extra, Bool.or_assoc] using hd.1
  constructor
  · simp only [and_assoc]
    change D.eval (List.ofFn x) = true ↔ full
    rw [hdval, Bool.or_eq_true, hc.1, hsplit]
  · intro hf
    have hcfalse : C.eval (List.ofFn x) = false := by
      rw [hdval] at hf
      simp only [Bool.or_eq_false_iff] at hf
      exact hf.1
    rw [hd.2, hc.2 hcfalse]
    simp [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
