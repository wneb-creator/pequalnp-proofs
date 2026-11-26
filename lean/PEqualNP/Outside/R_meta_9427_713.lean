import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_9427_713
    (seeds : ∀ (D X : Finset (Finset ℕ)),
      (∀ w ∈ D \ X, ∃ a ∈ D, ∃ b ∈ D, a ⊂ w ∧ b ⊂ w ∧ w = a ∪ b) →
      ∀ w ∈ D, ((D ∩ X).filter (fun a => a ⊆ w)).biUnion id = w)
    (lower : let R := Finset.range 40
      let I := ([2147418115,663661903884,34144976944,728266375360,21653750532,
        103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146] :
        List ℕ).toFinset.image (fun v => R.filter (fun i => v.testBit i = true))
      let T := insert 40 (Finset.range 16)
      ∀ (d e : Finset ℕ) (D B : Finset (Finset ℕ)),
        let X := insert (insert 40 d) (insert (insert 41 e) I)
        let P := D.filter (fun w => w ⊆ R)
        let A := Finset.image₂ (· ∩ ·) P P
        let F := Finset.image₂ (fun a b : Finset ℕ =>
          (a ∩ b ∩ R) ∪ (if {40,41} ⊆ a ∪ b then {40} else ∅)) D D
        d ∈ A → e ∈ A → ¬ d ⊆ Finset.range 16 → ¬ e ⊆ Finset.range 16 →
        (∀ w ∈ D \ X, ∃ a ∈ D, ∃ b ∈ D, a ⊂ w ∧ b ⊂ w ∧ w = a ∪ b) →
        (∀ w ∈ D, ((D ∩ X).filter (fun a => a ⊆ w)).biUnion id = w) →
        1 ≤ (D \ X).card → (D \ X).card ≤ 18 → B.card ≤ 9 →
        B.biUnion id = T →
        (∀ b ∈ B, b ∈ F ∧ b ⊆ T ∧ ∀ c ∈ F, c ⊆ T → b ⊆ c → c = b) →
        (∀ b ∈ B, ∃ r ∈ b, ∀ c ∈ B, r ∈ c → c = b) →
        21 ≤ (D \ X).card + 2 * B.card)
    : have x1 : Finset ℕ := Finset.range (40 : ℕ); have x2 : List ℕ := [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)]; have x3 : Finset (Finset ℕ) := Finset.image (fun (x3 : ℕ) => {x4 ∈ x1 | x3.testBit x4 = Bool.true}) x2.toFinset; have x4 : Finset ℕ := Insert.insert (40 : ℕ) (Finset.range (16 : ℕ)); ∀ (x5 x6 : Finset ℕ) (x7 x8 : Finset (Finset ℕ)),   have x9 : Finset (Finset ℕ) := Insert.insert (Insert.insert (40 : ℕ) x5) (Insert.insert (Insert.insert (41 : ℕ) x6) x3);   have x10 : Finset (Finset ℕ) := {x10 ∈ x7 | x10 ⊆ x1};   have x11 : Finset (Finset ℕ) := Finset.image₂ (fun (x11 x12 : Finset ℕ) => x11 ∩ x12) x10 x10;   have x12 : Finset ℕ → Finset ℕ → Finset ℕ := fun (x12 x13 : Finset ℕ) => x12 ∩ x13 ∩ x1 ∪ if {(40 : ℕ), (41 : ℕ)} ⊆ x12 ∪ x13 then {(40 : ℕ)} else ∅;   have x13 : Finset (Finset ℕ) := Finset.image₂ x12 x7 x7;   x5 ∈ x11 → x6 ∈ x11 → ¬x5 ⊆ Finset.range (16 : ℕ) → ¬x6 ⊆ Finset.range (16 : ℕ) → (∀ x18 ∈ x7 \ x9, ∃ x20 ∈ x7, ∃ x21 ∈ x7, x20 ⊂ x18 ∧ x21 ⊂ x18 ∧ x18 = x20 ∪ x21) → x7 ⊆ (Finset.range (42 : ℕ)).powerset → (1 : ℕ) ≤ (x7 \ x9).card → (x7 \ x9).card ≤ (18 : ℕ) → x8.card ≤ (9 : ℕ) → x8.biUnion id = x4 → (∀ x24 ∈ x8, x24 ∈ x13 ∧ x24 ⊆ x4 ∧ ∀ x26 ∈ x13, x26 ⊆ x4 → x24 ⊆ x26 → x26 = x24) → (∀ x25 ∈ x8, ∃ x27 ∈ x25, ∀ x28 ∈ x8, x27 ∈ x28 → x28 = x25) → (21 : ℕ) ≤ (x7 \ x9).card + (2 : ℕ) * x8.card := by
  dsimp only at lower ⊢
  intro d e D B hd he hdn hen build _ positive bounded count covers maximal privateRows
  exact lower d e D B hd he hdn hen build (seeds D _ build)
    positive bounded count covers maximal privateRows
