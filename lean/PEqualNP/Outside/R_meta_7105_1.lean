theorem PEqualNP.Outside.R_meta_7105_1
    (meet : let E : List (Fin 10 × Fin 10) := ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).map (fun n => (Fin.ofNat 10 (n / 10), Fin.ofNat 10 n))
      let base : List ((Fin 10 → Bool) → Bool) := ((fun _ => false) :: (fun _ => true) :: List.ofFn (fun (i : Fin 10) (x : Fin 10 → Bool) => x i)) ++ [fun x => x 0 || x 2]
      ∀ a ∈ base, ∀ b ∈ base, let h := fun x => a x && b x
        h ∉ base →
        ∀ ws : List ((Fin 10 → Bool) → Bool), ws.length ≤ 17 →
        (∀ i : Fin ws.length,
          let avail := base ++ (h :: ws.take i.val)
          ws.get i ∉ avail ∧ ∃ u ∈ avail, ∃ v ∈ avail,
            ws.get i = (fun x => u x && v x) ∨ ws.get i = (fun x => u x || v x)) →
        (∀ w ∈ h :: ws, ∀ i j : Fin 10, i ≠ j →
          let adj := (E.any fun e => decide ((i,j) = e ∨ (j,i) = e)) = true
          (¬adj → w ≠ fun x => x i && x j) ∧ (adj → w ≠ fun x => x i || x j)) →
        (fun x => E.any fun e => x e.1 && x e.2) ∉ ws)
    (join : let E : List (Fin 10 × Fin 10) := ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).map (fun n => (Fin.ofNat 10 (n / 10), Fin.ofNat 10 n))
      let base : List ((Fin 10 → Bool) → Bool) := ((fun _ => false) :: (fun _ => true) :: List.ofFn (fun (i : Fin 10) (x : Fin 10 → Bool) => x i)) ++ [fun x => x 0 || x 2]
      ∀ a ∈ base, ∀ b ∈ base, let h := fun x => a x || b x
        h ∉ base →
        ∀ ws : List ((Fin 10 → Bool) → Bool), ws.length ≤ 17 →
        (∀ i : Fin ws.length,
          let avail := base ++ (h :: ws.take i.val)
          ws.get i ∉ avail ∧ ∃ u ∈ avail, ∃ v ∈ avail,
            ws.get i = (fun x => u x && v x) ∨ ws.get i = (fun x => u x || v x)) →
        (∀ w ∈ h :: ws, ∀ i j : Fin 10, i ≠ j →
          let adj := (E.any fun e => decide ((i,j) = e ∨ (j,i) = e)) = true
          (¬adj → w ≠ fun x => x i && x j) ∧ (adj → w ≠ fun x => x i || x j)) →
        (fun x => E.any fun e => x e.1 && x e.2) ∉ ws)
    : (have x1 : List (Fin (10 : Nat) × Fin (10 : Nat)) := [((0 : Fin (10 : Nat)), (1 : Fin (10 : Nat))), ((1 : Fin (10 : Nat)), (2 : Fin (10 : Nat))), ((2 : Fin (10 : Nat)), (3 : Fin (10 : Nat))), ((3 : Fin (10 : Nat)), (4 : Fin (10 : Nat))), ((4 : Fin (10 : Nat)), (0 : Fin (10 : Nat))), ((0 : Fin (10 : Nat)), (5 : Fin (10 : Nat))), ((1 : Fin (10 : Nat)), (6 : Fin (10 : Nat))), ((2 : Fin (10 : Nat)), (7 : Fin (10 : Nat))), ((3 : Fin (10 : Nat)), (8 : Fin (10 : Nat))), ((4 : Fin (10 : Nat)), (9 : Fin (10 : Nat))), ((5 : Fin (10 : Nat)), (7 : Fin (10 : Nat))), ((7 : Fin (10 : Nat)), (9 : Fin (10 : Nat))), ((9 : Fin (10 : Nat)), (6 : Fin (10 : Nat))), ((6 : Fin (10 : Nat)), (8 : Fin (10 : Nat))), ((8 : Fin (10 : Nat)), (5 : Fin (10 : Nat)))]; ∀ (x2 : List ((Fin (10 : Nat) → Bool) → Bool)),   x2.length ≤ (18 : Nat) →     (∀ (x4 : Fin x2.length),         have x5 : List ((Fin (10 : Nat) → Bool) → Bool) := ((fun (x5 : Fin (10 : Nat) → Bool) => Bool.false) :: (fun (x5 : Fin (10 : Nat) → Bool) => Bool.true) :: List.ofFn fun (x5 : Fin (10 : Nat)) (x6 : Fin (10 : Nat) → Bool) => x6 x5) ++ [fun (x5 : Fin (10 : Nat) → Bool) => x5 (0 : Fin (10 : Nat)) || x5 (2 : Fin (10 : Nat))] ++ List.take (↑x4) x2;         x2.get x4 ∉ x5 ∧ ∃ x6 ∈ x5, ∃ x7 ∈ x5, (x2.get x4 = fun (x8 : Fin (10 : Nat) → Bool) => x6 x8 && x7 x8) ∨ x2.get x4 = fun (x8 : Fin (10 : Nat) → Bool) => x6 x8 || x7 x8) →       (∀ x5 ∈ x2,           ∀ (x7 x8 : Fin (10 : Nat)),             x7 ≠ x8 →               have x10 : Prop := (x1.any fun (x10 : Fin (10 : Nat) × Fin (10 : Nat)) => Decidable.decide ((x7, x8) = x10 ∨ (x8, x7) = x10)) = Bool.true;               (¬x10 → x5 ≠ fun (x12 : Fin (10 : Nat) → Bool) => x12 x7 && x12 x8) ∧ (x10 → x5 ≠ fun (x12 : Fin (10 : Nat) → Bool) => x12 x7 || x12 x8)) →         (fun (x6 : Fin (10 : Nat) → Bool) => x1.any fun (x7 : Fin (10 : Nat) × Fin (10 : Nat)) => x6 x7.1 && x6 x7.2) ∉ x2) := by
  let E : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
  let base : List ((Fin 10 → Bool) → Bool) := ((fun _ => false) :: (fun _ => true) :: List.ofFn (fun (i : Fin 10) (x : Fin 10 → Bool) => x i)) ++ [fun x => x 0 || x 2]
  let F := fun x : Fin 10 → Bool => E.any fun e => x e.1 && x e.2
  have headFails : ∀ a ∈ base, ∀ b ∈ base,
      F ≠ (fun x => a x && b x) ∧ F ≠ (fun x => a x || b x) := by
    let edge : Fin 10 → Fin 10 → Fin 10 → Bool := fun i j k => decide (k = i ∨ k = j)
    have samples : ∀ a ∈ base, ∀ b ∈ base,
        (∃ i j, F (edge i j) ≠ (a (edge i j) && b (edge i j))) ∧
        (∃ i j, F (edge i j) ≠ (a (edge i j) || b (edge i j))) := by decide +kernel
    intro a ha b hb
    obtain ⟨⟨i,j,h⟩,⟨k,l,h'⟩⟩ := samples a ha b hb
    exact ⟨fun eq => h (congrFun eq _), fun eq => h' (congrFun eq _)⟩
  dsimp only
  intro gs sz legal forbid
  cases gs with
  | nil => simp
  | cons h ws =>
    have first := legal ⟨0, by simp⟩
    change h ∉ base ++ [] ∧ _ at first
    simp only [List.append_nil] at first
    obtain ⟨fresh, a, ha, b, hb, op⟩ := first
    have rest (i : Fin ws.length) := legal ⟨i.val+1, by simpa using i.isLt⟩
    have small : ws.length ≤ 17 := by simpa using sz
    intro occurs
    change F ∈ h :: ws at occurs
    rcases List.mem_cons.mp occurs with eq | hm
    · rcases op with h1 | h2
      · exact (headFails a ha b hb).1 (eq.trans h1)
      · exact (headFails a ha b hb).2 (eq.trans h2)
    · rcases op with rfl | rfl
      · exact meet a ha b hb fresh ws small (fun i => by simpa [base] using rest i) forbid hm
      · exact join a ha b hb fresh ws small (fun i => by simpa [base] using rest i) forbid hm
