def padI {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin (N + 1)) : Prop :=
  ∃ a b : Fin N, p = a.castSucc ∧ l = b.castSucc ∧ I a b

def padLift {N : ℕ} : Fin (N + N) → Option (Fin ((N + 1) + (N + 1))) :=
  Fin.addCases (fun p => some (Fin.castAdd (N + 1) p.castSucc))
    (fun l => some (Fin.natAdd (N + 1) l.castSucc))

def padDrop {N : ℕ} : Fin ((N + 1) + (N + 1)) → Option (Fin (N + N)) :=
  Fin.addCases (Fin.lastCases none (fun p => some (Fin.castAdd N p)))
    (Fin.lastCases none (fun l => some (Fin.natAdd N l)))

lemma padI_cast {N : ℕ} (I : Fin N → Fin N → Prop) (p l : Fin N) :
    padI I p.castSucc l.castSucc ↔ I p l := by
  simp [padI]

lemma padI_point_last {N : ℕ} (I : Fin N → Fin N → Prop) (l : Fin (N + 1)) :
    ¬ padI I (Fin.last N) l := by
  rintro ⟨a, b, h, _, _⟩
  have := congrArg Fin.val h
  simp at this
  omega

lemma padI_line_last {N : ℕ} (I : Fin N → Fin N → Prop) (p : Fin (N + 1)) :
    ¬ padI I p (Fin.last N) := by
  rintro ⟨a, b, _, h, _⟩
  have := congrArg Fin.val h
  simp at this
  omega

lemma padI_noRect {N : ℕ} (I : Fin N → Fin N → Prop)
    (h : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) :
    ∀ p p' l l' : Fin (N + 1), p ≠ p' → l ≠ l' →
      ¬ (padI I p l ∧ padI I p l' ∧ padI I p' l ∧ padI I p' l') := by
  rintro p p' l l' hpp hll ⟨⟨a, b, rfl, rfl, hab⟩, h1, h2, h3⟩
  obtain ⟨a', d, ha', rfl, had⟩ := h1
  have haa : a = a' := Fin.castSucc_injective N ha'
  subst a'
  obtain ⟨c, b', rfl, hb', hcb⟩ := h2
  have hbb : b = b' := Fin.castSucc_injective N hb'
  subst b'
  have hcd := (padI_cast I c d).mp h3
  exact h a c b d (fun e => hpp (congrArg Fin.castSucc e))
    (fun e => hll (congrArg Fin.castSucc e)) ⟨hab, had, hcb, hcd⟩

lemma padLift_input_point {N : ℕ} (z : Fin ((N + 1) + (N + 1)) → Bool) (p : Fin N) :
    zResInput padLift z (Fin.castAdd N p) = z (Fin.castAdd (N + 1) p.castSucc) := by
  simp only [zResInput, padLift, Fin.addCases_left, Fin.addCases_right, Option.elim_some]

lemma padLift_input_line {N : ℕ} (z : Fin ((N + 1) + (N + 1)) → Bool) (l : Fin N) :
    zResInput padLift z (Fin.natAdd N l) = z (Fin.natAdd (N + 1) l.castSucc) := by
  simp only [zResInput, padLift, Fin.addCases_left, Fin.addCases_right, Option.elim_some]

lemma padDrop_input_point {N : ℕ} (z : Fin (N + N) → Bool) (p : Fin N) :
    zResInput padDrop z (Fin.castAdd (N + 1) p.castSucc) = z (Fin.castAdd N p) := by
  simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_castSucc, Option.elim_some]

lemma padDrop_input_line {N : ℕ} (z : Fin (N + N) → Bool) (l : Fin N) :
    zResInput padDrop z (Fin.natAdd (N + 1) l.castSucc) = z (Fin.natAdd N l) := by
  simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_castSucc, Option.elim_some]

lemma padLift_computes {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit)
    (hC : Monotone2 C)
    (hf : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∀ z : Fin ((N + 1) + (N + 1)) → Bool,
      circuitFun ((N + 1) + (N + 1)) (zResCircuit (padLift (N := N)) C) z = true ↔
      ∃ p l : Fin (N + 1), padI I p l ∧
        z (Fin.castAdd (N + 1) p) = true ∧ z (Fin.natAdd (N + 1) l) = true := by
  intro z
  rw [zRes_eval _ _ hC, hf]
  constructor
  · rintro ⟨p, l, hpl, hp, hl⟩
    exact ⟨p.castSucc, l.castSucc, (padI_cast I p l).mpr hpl,
      by simpa only [padLift_input_point] using hp, by simpa only [padLift_input_line] using hl⟩
  · rintro ⟨p, l, ⟨a, b, rfl, rfl, hab⟩, hp, hl⟩
    exact ⟨a, b, hab, by simpa only [padLift_input_point] using hp,
      by simpa only [padLift_input_line] using hl⟩

lemma padDrop_computes {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit)
    (hC : Monotone2 C)
    (hf : ∀ z : Fin ((N + 1) + (N + 1)) → Bool,
      circuitFun ((N + 1) + (N + 1)) C z = true ↔
      ∃ p l : Fin (N + 1), padI I p l ∧
        z (Fin.castAdd (N + 1) p) = true ∧ z (Fin.natAdd (N + 1) l) = true) :
    ∀ z : Fin (N + N) → Bool, circuitFun (N + N) (zResCircuit (padDrop (N := N)) C) z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  intro z
  rw [zRes_eval _ _ hC, hf]
  constructor
  · rintro ⟨p, l, ⟨a, b, rfl, rfl, hab⟩, hp, hl⟩
    exact ⟨a, b, hab, by simpa only [padDrop_input_point] using hp,
      by simpa only [padDrop_input_line] using hl⟩
  · rintro ⟨a, b, hab, hp, hl⟩
    exact ⟨a.castSucc, b.castSucc, (padI_cast I a b).mpr hab,
      by simpa only [padDrop_input_point] using hp, by simpa only [padDrop_input_line] using hl⟩

lemma padDrop_pair {N : ℕ} (p l : Fin N) :
    zResInput padDrop (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) =
      (fun k : Fin ((N + 1) + (N + 1)) =>
        decide (k = Fin.castAdd (N + 1) p.castSucc ∨ k = Fin.natAdd (N + 1) l.castSucc)) := by
  funext k
  refine Fin.addCases (fun q => ?_) (fun q => ?_) k
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)

lemma padDrop_point {N : ℕ} (p : Fin N) :
    zResInput padDrop (fun k : Fin (N + N) => decide (k = Fin.castAdd N p)) =
      (fun k : Fin ((N + 1) + (N + 1)) => decide (k = Fin.castAdd (N + 1) p.castSucc)) := by
  funext k
  refine Fin.addCases (fun q => ?_) (fun q => ?_) k
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)

lemma padDrop_line {N : ℕ} (l : Fin N) :
    zResInput padDrop (fun k : Fin (N + N) => decide (k = Fin.natAdd N l)) =
      (fun k : Fin ((N + 1) + (N + 1)) => decide (k = Fin.natAdd (N + 1) l.castSucc)) := by
  funext k
  refine Fin.addCases (fun q => ?_) (fun q => ?_) k
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)
  · refine Fin.lastCases ?_ (fun q => ?_) q <;>
      simp only [zResInput, padDrop, Fin.addCases_left, Fin.addCases_right, Fin.lastCases_last, Fin.lastCases_castSucc, Option.elim_none, Option.elim_some]
    all_goals simp [Fin.ext_iff]
    all_goals first | omega | (congr 1 <;> simp_all <;> omega)
