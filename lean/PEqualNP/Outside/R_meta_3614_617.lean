import Mathlib.Tactic.ByContra
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_3614_617
  (ordinary :
    let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    ¬ HasCircuitSize 9 F 14)
  (separation :
    let F := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
      (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
    let X := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
    ∀ (v : Fin 9) (C : Circuit) (k : ℕ) (b : Bool),
    let err := fun x => C.eval (X x) ≠ F x
    let w := fun x => (C.wires (X x)).getD k false
    v ≠ 0 → v ≠ 6 → FanInTwo C → C.size ≤ 13 → 10 ≤ k → k < 10+C.size →
    (∀ g ∈ C.gates.take (k+1-10), v.val ∉ g.inputs) →
    (∃ x, err x) → (∀ x, err x → x v ≠ b ∧ w x = b) →
    ∃ x, x v = false ∧ F x = false ∧ F (Function.update x v true) = true ∧ w x = b) :
  have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (6 : Fin (9 : ℕ))]; ∀ (x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) (x5 : ℕ) (x6 : Bool),   x3 ≠ (0 : Fin (9 : ℕ)) →     x3 ≠ (6 : Fin (9 : ℕ)) →       PEqualNP.MetaComplexity.FanInTwo x4 →         x4.size ≤ (13 : ℕ) →           (10 : ℕ) ≤ x5 →             x5 < (10 : ℕ) + x4.size →               (∀ x13 ∈ List.take (x5 + (1 : ℕ) - (10 : ℕ)) x4.gates, ↑x3 ∉ x13.inputs) →                 (∀ (x14 x15 : Fin (9 : ℕ) → Bool), (∀ (x16 : Fin (9 : ℕ)), x16 ≠ x3 → x14 x16 = x15 x16) → x1 x14 ≠ x1 x15 → (x4.wires (x2 x14)).getD x5 Bool.false = !x6) →                   ∃ (x15 : Fin (9 : ℕ) → Bool),                     have x16 : Bool := (x4.wires (x2 x15)).getD x5 Bool.false;                     x4.eval ((x2 x15).set (↑x3) (if x6 = Bool.true then x15 x3 || x16 else x15 x3 && x16)) ≠ x1 x15 := by
  classical
  dsimp only at ordinary separation ⊢
  intro v C k b hv0 hv6 fan size lo hi blind sensitive
  let target := fun x : Fin 9 → Bool => ([1,12,23,34,40,5,16,27,38,57,68,85] : List ℕ).any
    (fun e => x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10)))
  let aug := fun x : Fin 9 → Bool => List.ofFn x ++ [x 0 || x 6]
  have miss : ∃ x, C.eval (aug x) ≠ target x := by
    by_contra! fits
    let gate : Gate := ⟨.or, [0, 6]⟩
    let D : Circuit := ⟨gate :: C.gates, C.output⟩
    apply ordinary
    refine ⟨D, ?_, ?_, ?_⟩
    · intro g mem
      change g ∈ gate :: C.gates at mem
      rcases List.mem_cons.mp mem with rfl | mem
      · simp [gate]
      · exact fan g mem
    · change C.gates.length + 1 ≤ 14
      change C.gates.length ≤ 13 at size
      omega
    · intro x
      change D.eval (List.ofFn x) = target x
      rw [← fits x]
      change (C.wires _).getD C.output false = (C.wires _).getD C.output false
      congr 2
      change List.ofFn x ++ [x 0 || (x 6 || false)] = aug x
      simp only [Bool.or_false, aug]
  by_contra! correct
  obtain ⟨x, _, low, high, active⟩ := separation v C k b hv0 hv6 fan size lo hi blind
    miss (by
      intro x err
      let X := List.ofFn x ++ [x 0 || x 6]
      let w := (C.wires X).getD k false
      have sameBit : X.set v.val (x v) = X := by
        change (List.ofFn x ++ [x 0 || x 6]).set v.val (x v) = List.ofFn x ++ [x 0 || x 6]
        rw [List.set_append_left _ _ (by simpa using v.isLt)]
        congr 1
        have hlt : v.val < (List.ofFn x).length := by simpa only [List.length_ofFn] using v.isLt
        have elem : (List.ofFn x)[v.val] = x v := List.getElem_ofFn hlt
        rw [← elem]
        exact List.set_getElem_self hlt
      have fixed : (if b = true then x v || w else x v && w) ≠ x v := by
        intro eq
        have h := correct x
        change C.eval (X.set v.val (if b = true then x v || w else x v && w)) = _ at h
        rw [eq, sameBit] at h
        exact err h
      change x v ≠ b ∧ w = b
      have logic : ∀ a c s : Bool, (if s = true then a || c else a && c) ≠ a → a ≠ s ∧ c = s := by decide
      exact logic (x v) w b fixed)
  have neutral := sensitive x (Function.update x v true)
    (fun i hi => (Function.update_of_ne hi true x).symm) (by rw [low, high]; decide)
  rw [active] at neutral
  cases b <;> contradiction
