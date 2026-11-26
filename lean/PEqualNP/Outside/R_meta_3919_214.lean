import Mathlib
import PEqualNP.Defs

open PEqualNP.MetaComplexity

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_3919_214
    (blind :
      let target (x : Fin 9 → Bool) : Bool :=
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (D : BinaryCircuit) (s : Bool),
        (∀ g ∈ D.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) →
        (∀ j : Fin D.size, (D.gates.get j).left < (D.gates.get j).right ∧
          (D.gates.get j).right < 10 + j.val) →
        D.output = 10 + D.size - 1 →
        (∀ g ∈ D.gates, g.left ≠ 9 ∧ g.right ≠ 9) →
        (∀ x : Fin 9 → Bool, (D.eval (List.ofFn x ++ [false]) != s) = target x) →
        14 ≤ D.size)
    (reads :
      let target (x : Fin 9 → Bool) : Bool :=
        ([1, 12, 23, 34, 40, 5, 16, 27, 38, 57, 68, 85] : List ℕ).any
          (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
      ∀ (D : BinaryCircuit) (s : Bool) (h : 0 < D.size),
        (∀ g ∈ D.gates, ∃ a b : Bool, g.op = fun x y => (x == a) && (y == b)) →
        (∀ j : Fin D.size, (D.gates.get j).left < (D.gates.get j).right ∧
          (D.gates.get j).right < 10 + j.val) →
        D.output = 10 + D.size - 1 →
        (D.gates.get ⟨0, h⟩).right < 9 →
        (∃ g ∈ D.gates, g.left = 9 ∨ g.right = 9) →
        (∀ x : Fin 9 → Bool, (D.eval (List.ofFn x ++ [x 0 || x 1]) != s) = target x) →
        14 ≤ D.size) :
    have x1 : PEqualNP.MetaComplexity.BinaryCircuit → Prop := fun (x1 : PEqualNP.MetaComplexity.BinaryCircuit) => ∀ x2 ∈ x1.gates, ∃ (x4 : Bool) (x5 : Bool), x2.op = fun (x6 x7 : Bool) => x6 == x4 && x7 == x5; have x2 : ℕ → PEqualNP.MetaComplexity.BinaryCircuit → Prop := fun (x2 : ℕ) (x3 : PEqualNP.MetaComplexity.BinaryCircuit) => ∀ (x4 : Fin x3.size), (x3.gates.get x4).left < (x3.gates.get x4).right ∧ (x3.gates.get x4).right < x2 + ↑x4; have x3 : (Fin (9 : ℕ) → Bool) → Bool := fun (x3 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x4 : ℕ) => x3 (Fin.ofNat (9 : ℕ) (x4 / (10 : ℕ))) && x3 (Fin.ofNat (9 : ℕ) (x4 % (10 : ℕ))); ∀ (x4 : PEqualNP.MetaComplexity.BinaryCircuit) (x5 : Bool) (x6 : (0 : ℕ) < x4.size), x1 x4 → x2 (10 : ℕ) x4 → x4.output = (10 : ℕ) + x4.size - (1 : ℕ) → (x4.gates.get (⟨(0 : ℕ), x6⟩ : Fin x4.gates.length)).right < (9 : ℕ) → (∀ (x11 : Fin (9 : ℕ) → Bool), (x4.eval (List.ofFn x11 ++ [x11 (0 : Fin (9 : ℕ)) || x11 (1 : Fin (9 : ℕ))]) != x5) = x3 x11) → (14 : ℕ) ≤ x4.size := by
  intro _ _ _ C s hpos hsig hord hout hfirst hev
  by_cases hr : ∃ g ∈ C.gates, g.left = 9 ∨ g.right = 9
  · exact reads C s hpos hsig hord hout hfirst hr hev
  · push_neg at hr
    refine blind C s hsig hord hout hr ?_
    intro x
    -- wire 9 is never read, so its value does not matter
    have key : ∀ (gs : List BinaryGate) (u v : List Bool), (∀ g ∈ gs, g.left ≠ 9 ∧ g.right ≠ 9) →
        u.length = v.length → (∀ i, i ≠ 9 → u.getD i false = v.getD i false) →
        ∀ i, i ≠ 9 →
          (gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) u).getD i false =
          (gs.foldl (fun w g => w ++ [g.op (w.getD g.left false) (w.getD g.right false)]) v).getD i false := by
      intro gs
      induction gs with
      | nil => intro u v _ _ h; exact h
      | cons g t ih =>
        intro u v hg hl h
        simp only [List.foldl_cons]
        apply ih _ _ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
        · simp [hl]
        · intro i hi
          have hgl := hg g List.mem_cons_self
          rw [h g.left hgl.1, h g.right hgl.2]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append] at h ⊢
          rcases Nat.lt_or_ge i u.length with hu | hu
          · have hv : i < v.length := hl ▸ hu
            simp only [hu, hv, if_true]
            exact h i hi
          · have hv : ¬ i < v.length := by omega
            have hu' : ¬ i < u.length := by omega
            simp only [hv, if_false, hl]
    have e := key C.gates (List.ofFn x ++ [x 0 || x 1]) (List.ofFn x ++ [false]) hr (by simp)
      (by
        intro i hi
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
        split_ifs with h1
        · rfl
        · simp at h1
          have : i - 9 ≠ 0 := by omega
          simp [this])
      C.output (by omega)
    have e' : C.eval (List.ofFn x ++ [false]) = C.eval (List.ofFn x ++ [x 0 || x 1]) := e.symm
    rw [e']
    exact hev x
