namespace PEqualNP.Outside.L_meta_3451_aux.Support

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

noncomputable def pick {N : ℕ} (e : Fin 2 ↪ Fin N) (p : Fin N) : Option (Fin 2) :=
  if h : ∃ i, e i = p then some h.choose else none

lemma pick_embed {N : ℕ} (e : Fin 2 ↪ Fin N) (i : Fin 2) : pick e (e i) = some i := by
  unfold pick
  have h : ∃ j, e j = e i := ⟨i, rfl⟩
  rw [dite_eq_left h]
  exact congrArg some (e.injective h.choose_spec)

lemma pick_some {N : ℕ} (e : Fin 2 ↪ Fin N) (p : Fin N) (i : Fin 2)
    (h : pick e p = some i) : e i = p := by
  unfold pick at h
  split_ifs at h with hex
  have he := Option.some.inj h
  rw [← he]
  exact hex.choose_spec

def embed {N : ℕ} (ep el : Fin 2 ↪ Fin N) : Fin 4 → Fin (N + N) :=
  Fin.addCases (m := 2) (n := 2) (motive := fun _ => Fin (N + N))
    (fun p => Fin.castAdd N (ep p)) (fun l => Fin.natAdd N (el l))

noncomputable def project {N : ℕ} (ep el : Fin 2 ↪ Fin N) :
    Fin (N + N) → Option (Fin 4) :=
  Fin.addCases (fun p => (pick ep p).map (Fin.castAdd 2))
    (fun l => (pick el l).map (Fin.natAdd 2))

lemma project_embed {N : ℕ} (ep el : Fin 2 ↪ Fin N) (i : Fin 4) :
    project ep el (embed ep el i) = some i := by
  refine Fin.addCases (m := 2) (n := 2) (fun p => ?_) (fun l => ?_) i
  · rw [embed, Fin.addCases_left, project, Fin.addCases_left, pick_embed]
    rfl
  · rw [embed, Fin.addCases_right, project, Fin.addCases_right, pick_embed]
    rfl

lemma input_point {N : ℕ} (ep el : Fin 2 ↪ Fin N) (z : Fin 4 → Bool) (p : Fin 2) :
    Restriction.input (project ep el) z (Fin.castAdd N (ep p)) = z (Fin.castAdd 2 p) := by
  simp only [Restriction.input, project, Fin.addCases_left, pick_embed,
    Option.map_some, Option.getD_some]

lemma input_line {N : ℕ} (ep el : Fin 2 ↪ Fin N) (z : Fin 4 → Bool) (l : Fin 2) :
    Restriction.input (project ep el) z (Fin.natAdd N (el l)) = z (Fin.natAdd 2 l) := by
  simp only [Restriction.input, project, Fin.addCases_right, pick_embed,
    Option.map_some, Option.getD_some]

lemma rename_point {N : ℕ} (ep el : Fin 2 ↪ Fin N) (z : Fin (N + N) → Bool) (p : Fin 2) :
    Restriction.input (fun i => some (embed ep el i)) z (Fin.castAdd 2 p) =
      z (Fin.castAdd N (ep p)) := by
  simp only [Restriction.input, embed, Fin.addCases_left, Option.map_some, Option.getD_some]

lemma rename_line {N : ℕ} (ep el : Fin 2 ↪ Fin N) (z : Fin (N + N) → Bool) (l : Fin 2) :
    Restriction.input (fun i => some (embed ep el i)) z (Fin.natAdd 2 l) =
      z (Fin.natAdd N (el l)) := by
  simp only [Restriction.input, embed, Fin.addCases_right, Option.map_some, Option.getD_some]

lemma computes_project {N : ℕ} (ep el : Fin 2 ↪ Fin N) (I : Fin N → Fin N → Prop)
    (support : ∀ p l, I p l → ∃ a b : Fin 2, p = ep a ∧ l = el b)
    (C : Circuit) (hm : Monotone2 C)
    (sem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∀ z : Fin 4 → Bool, circuitFun 4 (Restriction.circuit (project ep el) C) z = true ↔
      ∃ p l : Fin 2, I (ep p) (el l) ∧
        z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true := by
  intro z
  rw [Restriction.eval _ C hm, sem]
  constructor
  · rintro ⟨p, l, hi, hp, hl⟩
    obtain ⟨a, b, rfl, rfl⟩ := support p l hi
    exact ⟨a, b, hi, by simpa only [input_point] using hp,
      by simpa only [input_line] using hl⟩
  · rintro ⟨p, l, hi, hp, hl⟩
    exact ⟨ep p, el l, hi, by simpa only [input_point] using hp,
      by simpa only [input_line] using hl⟩

lemma computes_rename {N : ℕ} (ep el : Fin 2 ↪ Fin N) (I : Fin N → Fin N → Prop)
    (support : ∀ p l, I p l → ∃ a b : Fin 2, p = ep a ∧ l = el b)
    (C : Circuit) (hm : Monotone2 C)
    (sem : ∀ z : Fin 4 → Bool, circuitFun 4 C z = true ↔
      ∃ p l : Fin 2, I (ep p) (el l) ∧ z (Fin.castAdd 2 p) = true ∧ z (Fin.natAdd 2 l) = true) :
    ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) (Restriction.circuit (fun i => some (embed ep el i)) C) z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  intro z
  rw [Restriction.eval _ C hm, sem]
  constructor
  · rintro ⟨p, l, hi, hp, hl⟩
    exact ⟨ep p, el l, hi, by simpa only [rename_point] using hp,
      by simpa only [rename_line] using hl⟩
  · rintro ⟨p, l, hi, hp, hl⟩
    obtain ⟨a, b, rfl, rfl⟩ := support p l hi
    exact ⟨a, b, hi, by simpa only [rename_point] using hp,
      by simpa only [rename_line] using hl⟩

end PEqualNP.Outside.L_meta_3451_aux.Support
