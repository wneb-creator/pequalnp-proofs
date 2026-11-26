import PEqualNP.Defs

open PEqualNP PEqualNP.CircuitLowerBounds

set_option maxRecDepth 50000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.R_meta_7692_481
    (finite : ∃ (C : Circuit) (u v : ℕ),
      C.size ≤ 24 ∧ TopForm.IsAO2 14 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      u < 14 + C.size ∧ v < 14 + C.size ∧ u ≠ 2 ∧ u ≠ v ∧
      let w := fun (m r : ℕ) => BlindGate.wireValue C 14 (fun i => m.testBit i.val) r
      (∀ m ∈ ([129,130,136,258,260,272,516,520,544,1032,1040,1088,2064,2080,2049,4128,4160,4098,8256,8193,8196] : List ℕ),
        (w m u || w m 2 && w m v) = true) ∧
      (∀ m ∈ ([127,244,361,480,595,720,833,1063,1188,1313,1539,2126,2244,2376,2626,3008,3078,4125,4244,4361,4625,5125,5889,6156,7300,8250,8368,8488,8722,9250,9632,10250,11778,12312,12944,14600,16256] : List ℕ),
        (w m u || w m 2 && w m v) = false) ∧
      w 1 v = false ∧ w 128 v = false)
    (mono : ∀ (C : Circuit), TopForm.IsAO2 14 C → ∀ (x y : Fin 14 → Bool) (r : ℕ),
      (∀ i, x i = true → y i = true) →
      BlindGate.wireValue C 14 x r = true → BlindGate.wireValue C 14 y r = true) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : ℕ) (x3 : ℕ),   x1.size ≤ (24 : ℕ) ∧     PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 ∧       (∀ x4 ∈ x1.gates, x4.inputs.Nodup) ∧         x2 < (14 : ℕ) + x1.size ∧           x3 < (14 : ℕ) + x1.size ∧             x2 ≠ (2 : ℕ) ∧               x2 ≠ x3 ∧                 ∀ (x4 : Fin (14 : ℕ) → Bool),                   have x5 : ℕ → Bool := PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x4;                   (x5 x2 || x5 (2 : ℕ) && x5 x3) = Decidable.decide (∃ (x6 : Fin (7 : ℕ)) (x7 : Fin (7 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (7 : ℕ)) ∨ x6 = x7 + (3 : Fin (7 : ℕ))) ∧ x4 (Fin.castAdd (7 : ℕ) x6) = Bool.true ∧ x4 (Fin.natAdd (7 : ℕ) x7) = Bool.true) ∧ ∀ x6 ∈ [(0 : Fin (14 : ℕ)), (7 : Fin (14 : ℕ))], (x4 = fun (x8 : Fin (14 : ℕ)) => Decidable.decide (x8 = x6)) → x5 (2 : ℕ) = Bool.false ∧ x5 x3 = Bool.false := by
  let E := fun p l : Fin 7 => p = l ∨ p = l + 1 ∨ p = l + 3
  let P : List ℕ := [129,130,136,258,260,272,516,520,544,1032,1040,1088,2064,2080,2049,4128,4160,4098,8256,8193,8196]
  let Z : List ℕ := [127,244,361,480,595,720,833,1063,1188,1313,1539,2126,2244,2376,2626,3008,3078,4125,4244,4361,4625,5125,5889,6156,7300,8250,8368,8488,8722,9250,9632,10250,11778,12312,12944,14600,16256]
  let row (m : ℕ) (i : Fin 14) := m.testBit i.val
  have pos : ∀ p l : Fin 7, E p l → ∃ m ∈ P,
      ∀ i : Fin 14, row m i = true → i = Fin.castAdd 7 p ∨ i = Fin.natAdd 7 l := by
    decide +kernel
  have neg : ∀ a : Fin 7 → Bool, ∃ m ∈ Z,
      (∀ i : Fin 7, a i = true → row m (Fin.castAdd 7 i) = true) ∧
      (∀ j : Fin 7, (∀ i : Fin 7, E i j → a i = false) → row m (Fin.natAdd 7 j) = true) := by
    decide +kernel
  obtain ⟨C, u, v, hs, hC, hnd, hu, hv, hne, huv, hp, hn, hv1, hv128⟩ := finite
  let w := BlindGate.wireValue C 14
  let f := fun x : Fin 14 → Bool => w x u || w x 2 && w x v
  have keep (gs : List Gate) (z : List Bool) (hz : 2 < z.length) :
      ((Circuit.mk gs 0).wires z).getD 2 false = z.getD 2 false := by
    induction gs generalizing z with
    | nil => rfl
    | cons g gs ih =>
      let zs := z ++ [g.op.eval (g.inputs.map fun i => z.getD i false)]
      change ((Circuit.mk gs 0).wires zs).getD 2 false = z.getD 2 false
      rw [ih zs (by simp [zs]; omega)]
      exact List.getD_append _ _ _ _ hz
  have inputTwo (y : Fin 14 → Bool) : w y 2 = y 2 := by
    change ((Circuit.mk C.gates 0).wires (List.ofFn y)).getD 2 false = y 2
    rw [keep _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD]
  have fm (a b : Fin 14 → Bool) (hab : ∀ i, a i = true → b i = true) :
      f a = true → f b = true := by
    simp only [f, Bool.or_eq_true, Bool.and_eq_true]
    rintro (h | ⟨h₁,h₂⟩)
    · exact Or.inl (mono C hC a b u hab h)
    · exact Or.inr ⟨mono C hC a b 2 hab h₁, mono C hC a b v hab h₂⟩
  refine ⟨C,u,v,hs,hC,hnd,hu,hv,hne,huv,?_⟩
  intro x
  change f x = decide (∃ p l : Fin 7, E p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true) ∧ _
  constructor
  · by_cases he : ∃ p l : Fin 7, E p l ∧ x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true
    · rw [decide_eq_true he]
      obtain ⟨p,l,he,hxp,hxl⟩ := he
      obtain ⟨m,hm,hm'⟩ := pos p l he
      apply fm (row m) x _ (hp m hm)
      intro i hi
      rcases hm' i hi with rfl | rfl
      · exact hxp
      · exact hxl
    · rw [decide_eq_false he]
      obtain ⟨m,hm,hmp,hml⟩ := neg (fun i => x (Fin.castAdd 7 i))
      have sub : ∀ i, x i = true → row m i = true := by
        intro i hi
        by_cases hl : i.val < 7
        · let p : Fin 7 := ⟨i.val,hl⟩
          have eq : Fin.castAdd 7 p = i := Fin.ext rfl
          rw [← eq] at hi ⊢
          exact hmp p hi
        · let l : Fin 7 := ⟨i.val - 7, by omega⟩
          have eq : Fin.natAdd 7 l = i := Fin.ext (by simp [l]; omega)
          rw [← eq] at hi ⊢
          apply hml l
          intro p hepl
          cases hx : x (Fin.castAdd 7 p)
          · rfl
          · exact False.elim (he ⟨p,l,hepl,hx,hi⟩)
      cases hfx : f x
      · rfl
      · have hh := fm x (row m) sub hfx
        exact Bool.noConfusion ((hn m hm).symm.trans hh)
  · intro i hi hx
    have cases_i : i = 0 ∨ i = 7 := by simpa using hi
    have r₀ : (fun k : Fin 14 => decide (k = (0 : Fin 14))) = row 1 := by decide +kernel
    have r₇ : (fun k : Fin 14 => decide (k = (7 : Fin 14))) = row 128 := by decide +kernel
    rcases cases_i with rfl | rfl
    · rw [r₀] at hx
      change w x 2 = false ∧ w x v = false
      rw [hx, inputTwo]
      exact ⟨by decide +kernel, hv1⟩
    · rw [r₇] at hx
      change w x 2 = false ∧ w x v = false
      rw [hx, inputTwo]
      exact ⟨by decide +kernel, hv128⟩
