import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9033_aux

namespace Normalization

def RowRel (target old new : Bool) : Prop :=
  (old = true → new = true) ∧ (target = false → old = new)

def StateRel (target : Fin 40 → Bool)
    (old new : Nat → Fin 40 → Bool) : Prop :=
  ∀ i r, RowRel (target r) (old i r) (new i r)

def gate (g : Bool × Nat × Nat) (s : Nat → Fin 40 → Bool) : Fin 40 → Bool :=
  fun r => if g.1 then s g.2.1 r && s g.2.2 r else s g.2.1 r || s g.2.2 r

def run : List (Bool × Nat × Nat) → Nat →
    (Nat → Fin 40 → Bool) → Nat → Fin 40 → Bool
  | [], _, s => s
  | g :: gs, k, s => run gs (k + 1) (Function.update s k (gate g s))

lemma and_rel (t a b c d : Bool) (ha : RowRel t a c) (hb : RowRel t b d) :
    RowRel t (a && b) (c && d) := by
  cases t <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [RowRel]

lemma or_rel (t a b c d : Bool) (ha : RowRel t a c) (hb : RowRel t b d) :
    RowRel t (a || b) (c || d) := by
  cases t <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [RowRel]

lemma gate_rel (target : Fin 40 → Bool) (old new : Nat → Fin 40 → Bool)
    (h : StateRel target old new) (g : Bool × Nat × Nat) (r : Fin 40) :
    RowRel (target r) (gate g old r) (gate g new r) := by
  unfold gate
  split
  · exact and_rel _ _ _ _ _ (h _ _) (h _ _)
  · exact or_rel _ _ _ _ _ (h _ _) (h _ _)

lemma update_rel (target : Fin 40 → Bool) (old new : Nat → Fin 40 → Bool)
    (h : StateRel target old new) (k : Nat) (a b : Fin 40 → Bool)
    (hab : ∀ r, RowRel (target r) (a r) (b r)) :
    StateRel target (Function.update old k a) (Function.update new k b) := by
  intro i r
  by_cases hik : i = k
  · subst i
    simpa using hab r
  · simpa [Function.update_of_ne hik] using h i r

lemma run_rel (target : Fin 40 → Bool) (gs : List (Bool × Nat × Nat))
    (k : Nat) (old new : Nat → Fin 40 → Bool) (h : StateRel target old new) :
    StateRel target (run gs k old) (run gs k new) := by
  induction gs generalizing k old new with
  | nil => exact h
  | cons g gs ih =>
    exact ih (k + 1) _ _ (update_rel target old new h k _ _ (gate_rel target old new h g))

lemma clean_and_to_identity (t a b : Bool) (hc : t = false → a = false) :
    RowRel t (a && b) (a || a) := by
  cases t <;> cases a <;> cases b <;> simp_all [RowRel]

lemma replace_clean_and (target : Fin 40 → Bool) (s : Nat → Fin 40 → Bool)
    (k a b : Nat) (tail : List (Bool × Nat × Nat))
    (hc : ∀ r, target r = false → s a r = false) :
    StateRel target
      (run tail (k + 1) (Function.update s k (gate (true, a, b) s)))
      (run tail (k + 1) (Function.update s k (gate (false, a, a) s))) := by
  apply run_rel
  apply update_rel
  · intro i r
    exact ⟨id, fun _ => rfl⟩
  · intro r
    simpa [gate] using clean_and_to_identity (target r) (s a r) (s b r) (hc r)

lemma exact_target (target old new : Fin 40 → Bool)
    (hrel : ∀ r, RowRel (target r) (old r) (new r)) (h : old = target) :
    new = target := by
  subst old
  funext r
  have hr := hrel r
  cases ht : target r <;> simp_all [RowRel]

def Clean (target signal : Fin 40 → Bool) : Prop :=
  ∀ r, target r = false → signal r = false

noncomputable def normalizeGate (target : Fin 40 → Bool)
    (s : Nat → Fin 40 → Bool) (g : Bool × Nat × Nat) : Bool × Nat × Nat := by
  classical
  exact if g.1 = true ∧ Clean target (s g.2.1) then (false, g.2.1, g.2.1)
    else if g.1 = true ∧ Clean target (s g.2.2) then (false, g.2.2, g.2.2)
    else g

noncomputable def normalize (target : Fin 40 → Bool) :
    List (Bool × Nat × Nat) → Nat → (Nat → Fin 40 → Bool) → List (Bool × Nat × Nat)
  | [], _, _ => []
  | g :: gs, k, s =>
    let g' := normalizeGate target s g
    g' :: normalize target gs (k + 1) (Function.update s k (gate g' s))

lemma rowRel_trans (t a b c : Bool) (hab : RowRel t a b) (hbc : RowRel t b c) :
    RowRel t a c :=
  ⟨fun h => hbc.1 (hab.1 h), fun h => (hab.2 h).trans (hbc.2 h)⟩

lemma normalizeGate_rel (target : Fin 40 → Bool) (s : Nat → Fin 40 → Bool)
    (g : Bool × Nat × Nat) (r : Fin 40) :
    RowRel (target r) (gate g s r) (gate (normalizeGate target s g) s r) := by
  classical
  unfold normalizeGate
  split_ifs with ha hb
  · simpa [gate, ha.1] using clean_and_to_identity (target r) (s g.2.1 r) (s g.2.2 r) (ha.2 r)
  · simpa [gate, hb.1, Bool.and_comm] using
      clean_and_to_identity (target r) (s g.2.2 r) (s g.2.1 r) (hb.2 r)
  · exact ⟨id, fun _ => rfl⟩

lemma normalizeGate_preserves_dirty (target : Fin 40 → Bool)
    (s : Nat → Fin 40 → Bool) (g : Bool × Nat × Nat)
    (hop : g.1 = true) (r : Fin 40) (ht : target r = false)
    (hv : gate g s r = true) : normalizeGate target s g = g := by
  classical
  unfold normalizeGate
  split_ifs with ha hb
  · have hz := ha.2 r ht
    simp [gate, hop, hz] at hv
  · have hz := hb.2 r ht
    simp [gate, hop, hz] at hv
  · rfl

lemma normalizeGate_and_inputs_dirty (target : Fin 40 → Bool)
    (s : Nat → Fin 40 → Bool) (g : Bool × Nat × Nat)
    (h : (normalizeGate target s g).1 = true) :
    ¬ Clean target (s (normalizeGate target s g).2.1) ∧
      ¬ Clean target (s (normalizeGate target s g).2.2) := by
  classical
  unfold normalizeGate at h ⊢
  by_cases ha : g.1 = true ∧ Clean target (s g.2.1)
  · rw [ite_eq_left ha] at h
    cases h
  · by_cases hb : g.1 = true ∧ Clean target (s g.2.2)
    · rw [ite_eq_right ha, ite_eq_left hb] at h
      cases h
    · simp only [ite_eq_right ha, ite_eq_right hb] at h ⊢
      exact ⟨fun hc => ha ⟨h, hc⟩, fun hc => hb ⟨h, hc⟩⟩

lemma normalize_run_rel (target : Fin 40 → Bool) (gs : List (Bool × Nat × Nat))
    (k : Nat) (old new : Nat → Fin 40 → Bool) (h : StateRel target old new) :
    StateRel target (run gs k old) (run (normalize target gs k new) k new) := by
  induction gs generalizing k old new with
  | nil => exact h
  | cons g gs ih =>
    exact ih (k + 1) (Function.update old k (gate g old))
      (Function.update new k (gate (normalizeGate target new g) new))
      (update_rel target old new h k _ _ (fun r =>
        rowRel_trans _ _ _ _ (gate_rel target old new h g r) (normalizeGate_rel target new g r)))

lemma normalize_length (target : Fin 40 → Bool) (gs : List (Bool × Nat × Nat))
    (k : Nat) (s : Nat → Fin 40 → Bool) :
    (normalize target gs k s).length = gs.length := by
  induction gs generalizing k s with
  | nil => rfl
  | cons g gs ih => simp only [normalize, List.length_cons, ih]

lemma normalized_exact_target (target : Fin 40 → Bool) (gs : List (Bool × Nat × Nat))
    (k output : Nat) (s : Nat → Fin 40 → Bool) (h : run gs k s output = target) :
    run (normalize target gs k s) k s output = target := by
  apply exact_target target (run gs k s output) _ _ h
  intro r
  exact normalize_run_rel target gs k s s (fun _ _ => ⟨id, fun _ => rfl⟩) output r

def Dirty (target : Fin 40 → Bool) (s : Nat → Fin 40 → Bool)
    (g : Bool × Nat × Nat) : Prop :=
  g.1 = true ∧ ∃ r, target r = false ∧ gate g s r = true

lemma dirty_state_iff (target : Fin 40 → Bool)
    (old new : Nat → Fin 40 → Bool) (h : StateRel target old new)
    (g : Bool × Nat × Nat) : Dirty target old g ↔ Dirty target new g := by
  constructor
  · rintro ⟨hop, r, ht, hv⟩
    exact ⟨hop, r, ht, ((gate_rel target old new h g r).2 ht).symm.trans hv⟩
  · rintro ⟨hop, r, ht, hv⟩
    exact ⟨hop, r, ht, ((gate_rel target old new h g r).2 ht).trans hv⟩

lemma dirty_normalizeGate_iff (target : Fin 40 → Bool)
    (s : Nat → Fin 40 → Bool) (g : Bool × Nat × Nat) :
    Dirty target s (normalizeGate target s g) ↔ Dirty target s g := by
  constructor
  · intro h
    unfold normalizeGate at h
    split_ifs at h with ha hb
    · exact Bool.false_ne_true h.1 |>.elim
    · exact Bool.false_ne_true h.1 |>.elim
    · exact h
  · intro h
    obtain ⟨hop, r, ht, hv⟩ := h
    rw [normalizeGate_preserves_dirty target s g hop r ht hv]
    exact ⟨hop, r, ht, hv⟩

noncomputable def dirtyFlags (target : Fin 40 → Bool) :
    List (Bool × Nat × Nat) → Nat → (Nat → Fin 40 → Bool) → List Bool
  | [], _, _ => []
  | g :: gs, k, s => by
    classical
    exact decide (Dirty target s g) ::
      dirtyFlags target gs (k + 1) (Function.update s k (gate g s))

lemma normalize_dirtyFlags (target : Fin 40 → Bool)
    (gs : List (Bool × Nat × Nat)) (k : Nat)
    (old new : Nat → Fin 40 → Bool) (h : StateRel target old new) :
    dirtyFlags target (normalize target gs k new) k new =
      dirtyFlags target gs k old := by
  classical
  induction gs generalizing k old new with
  | nil => rfl
  | cons g gs ih =>
    simp only [normalize, dirtyFlags]
    congr 1
    · exact congrArg (fun p : Prop => decide p) (propext ((dirty_normalizeGate_iff target new g).trans
        (dirty_state_iff target old new h g).symm))
    · apply ih
      apply update_rel target old new h
      intro r
      exact rowRel_trans _ _ _ _ (gate_rel target old new h g r)
        (normalizeGate_rel target new g r)

lemma comparable_and_to_identity (t a b : Bool)
    (h : t = false → a = true → b = true) :
    RowRel t (a && b) (a || a) := by
  cases t <;> cases a <;> cases b <;> simp_all [RowRel]

lemma replace_comparable_and (target : Fin 40 → Bool)
    (s : Nat → Fin 40 → Bool) (k a b : Nat)
    (tail : List (Bool × Nat × Nat))
    (h : ∀ r, target r = false → s a r = true → s b r = true) :
    StateRel target
      (run tail (k + 1) (Function.update s k (gate (true, a, b) s)))
      (run tail (k + 1) (Function.update s k (gate (false, a, a) s))) := by
  apply run_rel
  apply update_rel
  · intro i r
    exact ⟨id, fun _ => rfl⟩
  · intro r
    simpa [gate] using comparable_and_to_identity (target r) (s a r) (s b r) (h r)

lemma replace_comparable_and_exact_target (target : Fin 40 → Bool)
    (s : Nat → Fin 40 → Bool) (k a b output : Nat)
    (tail : List (Bool × Nat × Nat))
    (h : ∀ r, target r = false → s a r = true → s b r = true)
    (hexact : run ((true, a, b) :: tail) k s output = target) :
    run ((false, a, a) :: tail) k s output = target := by
  apply exact_target target (run ((true, a, b) :: tail) k s output) _ _ hexact
  exact replace_comparable_and target s k a b tail h output

def DownRowRel (target old new : Bool) : Prop :=
  (new = true → old = true) ∧ (target = true → old = new)

def DownStateRel (target : Fin 40 → Bool)
    (old new : Nat → Fin 40 → Bool) : Prop :=
  ∀ i r, DownRowRel (target r) (old i r) (new i r)

lemma and_down_rel (t a b c d : Bool)
    (ha : DownRowRel t a c) (hb : DownRowRel t b d) :
    DownRowRel t (a && b) (c && d) := by
  cases t <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [DownRowRel]

lemma or_down_rel (t a b c d : Bool)
    (ha : DownRowRel t a c) (hb : DownRowRel t b d) :
    DownRowRel t (a || b) (c || d) := by
  cases t <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [DownRowRel]

lemma gate_down_rel (target : Fin 40 → Bool)
    (old new : Nat → Fin 40 → Bool) (h : DownStateRel target old new)
    (g : Bool × Nat × Nat) (r : Fin 40) :
    DownRowRel (target r) (gate g old r) (gate g new r) := by
  unfold gate
  split
  · exact and_down_rel _ _ _ _ _ (h _ _) (h _ _)
  · exact or_down_rel _ _ _ _ _ (h _ _) (h _ _)

lemma update_down_rel (target : Fin 40 → Bool)
    (old new : Nat → Fin 40 → Bool) (h : DownStateRel target old new)
    (k : Nat) (a b : Fin 40 → Bool)
    (hab : ∀ r, DownRowRel (target r) (a r) (b r)) :
    DownStateRel target (Function.update old k a) (Function.update new k b) := by
  intro i r
  by_cases hik : i = k
  · subst i
    simpa using hab r
  · simpa [Function.update_of_ne hik] using h i r

lemma run_down_rel (target : Fin 40 → Bool) (gs : List (Bool × Nat × Nat))
    (k : Nat) (old new : Nat → Fin 40 → Bool) (h : DownStateRel target old new) :
    DownStateRel target (run gs k old) (run gs k new) := by
  induction gs generalizing k old new with
  | nil => exact h
  | cons g gs ih =>
    exact ih (k + 1) _ _
      (update_down_rel target old new h k _ _ (gate_down_rel target old new h g))

lemma comparable_or_to_identity (t a b : Bool)
    (h : t = true → a = true → b = true) :
    DownRowRel t (a || b) (b && b) := by
  cases t <;> cases a <;> cases b <;> simp_all [DownRowRel]

lemma replace_comparable_or (target : Fin 40 → Bool)
    (s : Nat → Fin 40 → Bool) (k a b : Nat)
    (tail : List (Bool × Nat × Nat))
    (h : ∀ r, target r = true → s a r = true → s b r = true) :
    DownStateRel target
      (run tail (k + 1) (Function.update s k (gate (false, a, b) s)))
      (run tail (k + 1) (Function.update s k (gate (true, b, b) s))) := by
  apply run_down_rel
  apply update_down_rel
  · intro i r
    exact ⟨id, fun _ => rfl⟩
  · intro r
    simpa [gate] using comparable_or_to_identity (target r) (s a r) (s b r) (h r)

lemma exact_target_down (target old new : Fin 40 → Bool)
    (hrel : ∀ r, DownRowRel (target r) (old r) (new r)) (h : old = target) :
    new = target := by
  subst old
  funext r
  have hr := hrel r
  cases ht : target r <;> simp_all [DownRowRel]

lemma replace_comparable_or_exact_target (target : Fin 40 → Bool)
    (s : Nat → Fin 40 → Bool) (k a b output : Nat)
    (tail : List (Bool × Nat × Nat))
    (h : ∀ r, target r = true → s a r = true → s b r = true)
    (hexact : run ((false, a, b) :: tail) k s output = target) :
    run ((true, b, b) :: tail) k s output = target := by
  apply exact_target_down target (run ((false, a, b) :: tail) k s output) _ _ hexact
  exact replace_comparable_or target s k a b tail h output

lemma replace_comparable_and_count (a b : Nat) (tail : List (Bool × Nat × Nat)) :
    (((true, a, b) :: tail).countP fun g => g.1) =
      (((false, a, a) :: tail).countP fun g => g.1) + 1 := by
  simp

lemma replace_comparable_or_count (a b : Nat) (tail : List (Bool × Nat × Nat)) :
    (((false, a, b) :: tail).countP fun g => !g.1) =
      (((true, b, b) :: tail).countP fun g => !g.1) + 1 := by
  simp

def DirtyOn (target : Fin 40 → Bool) (P : Fin 40 → Prop)
    (s : Nat → Fin 40 → Bool) (g : Bool × Nat × Nat) : Prop :=
  g.1 = true ∧ ∃ r, P r ∧ target r = false ∧ gate g s r = true

lemma dirtyOn_state_iff (target : Fin 40 → Bool) (P : Fin 40 → Prop)
    (old new : Nat → Fin 40 → Bool) (h : StateRel target old new)
    (g : Bool × Nat × Nat) : DirtyOn target P old g ↔ DirtyOn target P new g := by
  constructor
  · rintro ⟨hop, r, hr, ht, hv⟩
    exact ⟨hop, r, hr, ht, ((gate_rel target old new h g r).2 ht).symm.trans hv⟩
  · rintro ⟨hop, r, hr, ht, hv⟩
    exact ⟨hop, r, hr, ht, ((gate_rel target old new h g r).2 ht).trans hv⟩

lemma dirtyOn_normalizeGate_iff (target : Fin 40 → Bool) (P : Fin 40 → Prop)
    (s : Nat → Fin 40 → Bool) (g : Bool × Nat × Nat) :
    DirtyOn target P s (normalizeGate target s g) ↔ DirtyOn target P s g := by
  constructor
  · intro h
    unfold normalizeGate at h
    split_ifs at h with ha hb
    · exact Bool.false_ne_true h.1 |>.elim
    · exact Bool.false_ne_true h.1 |>.elim
    · exact h
  · rintro ⟨hop, r, hr, ht, hv⟩
    rw [normalizeGate_preserves_dirty target s g hop r ht hv]
    exact ⟨hop, r, hr, ht, hv⟩

noncomputable def dirtyFlagsOn (target : Fin 40 → Bool) (P : Fin 40 → Prop) :
    List (Bool × Nat × Nat) → Nat → (Nat → Fin 40 → Bool) → List Bool
  | [], _, _ => []
  | g :: gs, k, s => by
    classical
    exact decide (DirtyOn target P s g) ::
      dirtyFlagsOn target P gs (k + 1) (Function.update s k (gate g s))

lemma normalize_dirtyFlagsOn (target : Fin 40 → Bool) (P : Fin 40 → Prop)
    (gs : List (Bool × Nat × Nat)) (k : Nat)
    (old new : Nat → Fin 40 → Bool) (h : StateRel target old new) :
    dirtyFlagsOn target P (normalize target gs k new) k new =
      dirtyFlagsOn target P gs k old := by
  classical
  induction gs generalizing k old new with
  | nil => rfl
  | cons g gs ih =>
    simp only [normalize, dirtyFlagsOn]
    congr 1
    · exact congrArg (fun p : Prop => decide p)
        (propext ((dirtyOn_normalizeGate_iff target P new g).trans
          (dirtyOn_state_iff target P old new h g).symm))
    · apply ih
      apply update_rel target old new h
      intro r
      exact rowRel_trans _ _ _ _ (gate_rel target old new h g r)
        (normalizeGate_rel target new g r)

lemma normalize_highDirtyFlags (target : Fin 40 → Bool)
    (gs : List (Bool × Nat × Nat)) (k : Nat)
    (old new : Nat → Fin 40 → Bool) (h : StateRel target old new) :
    dirtyFlagsOn target (fun r => 16 ≤ r.val) (normalize target gs k new) k new =
      dirtyFlagsOn target (fun r => 16 ≤ r.val) gs k old :=
  normalize_dirtyFlagsOn target (fun r => 16 ≤ r.val) gs k old new h

lemma normalize_highDirtyFlags_self (target : Fin 40 → Bool)
    (gs : List (Bool × Nat × Nat)) (k : Nat) (s : Nat → Fin 40 → Bool) :
    dirtyFlagsOn target (fun r => 16 ≤ r.val) (normalize target gs k s) k s =
      dirtyFlagsOn target (fun r => 16 ≤ r.val) gs k s :=
  normalize_highDirtyFlags target gs k s s (fun _ _ => ⟨id, fun _ => rfl⟩)

end Normalization

namespace CofactorSimplification

abbrev Gate := Bool × Nat × Nat

def evalGate (g : Gate) (s : Nat → Bool) : Bool :=
  if g.1 then s g.2.1 && s g.2.2 else s g.2.1 || s g.2.2

def run : List Gate → Nat → (Nat → Bool) → Nat → Bool
  | [], _, s => s
  | g :: gs, k, s => run gs (k + 1) (Function.update s k (evalGate g s))

def Keep (a b : Nat) : Bool := decide (a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b)


def replacement (op : Bool) (a b : Nat) : Nat :=
  if op then (if a = 0 ∨ b = 0 then 0 else a)
  else (if a = 0 then b else a)

def mapped (rho : Nat → Nat) (g : Gate) : Gate :=
  (g.1, rho g.2.1, rho g.2.2)

def compile : List Gate → Nat → Nat → (Nat → Nat) → List Gate × (Nat → Nat)
  | [], _, _, rho => ([], rho)
  | g :: gs, k, m, rho =>
    if Keep (rho g.2.1) (rho g.2.2) then
      let rest := compile gs (k + 1) (m + 1) (Function.update rho k m)
      (mapped rho g :: rest.1, rest.2)
    else
      compile gs (k + 1) m
        (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2)))

def survivors : List Gate → Nat → Nat → (Nat → Nat) → Nat
  | [], _, _, _ => 0
  | g :: gs, k, m, rho =>
    if Keep (rho g.2.1) (rho g.2.2) then
      1 + survivors gs (k + 1) (m + 1) (Function.update rho k m)
    else
      survivors gs (k + 1) m
        (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2)))

lemma replacement_sound (op : Bool) (a b : Nat) (t : Nat → Bool)
    (h0 : t 0 = false) (h : ¬ Keep a b) :
    t (replacement op a b) = (if op then t a && t b else t a || t b) := by
  cases op <;> by_cases ha : a = 0 <;> by_cases hb : b = 0 <;>
    by_cases hab : a = b <;> simp_all [Keep, replacement]

lemma replacement_lt (op : Bool) (a b m : Nat) (hm : 0 < m)
    (ha : a < m) (hb : b < m) : replacement op a b < m := by
  cases op <;> simp only [replacement, Bool.false_eq_true, ite_false, ite_true]
  · split_ifs <;> assumption
  · split_ifs <;> assumption

lemma mapped_sound (rho : Nat → Nat) (g : Gate) (s t : Nat → Bool)
    (h : ∀ i, s i = t (rho i)) : evalGate g s = evalGate (mapped rho g) t := by
  simp only [evalGate, mapped]
  rw [h g.2.1, h g.2.2]
  rfl

lemma update_same (rho : Nat → Nat) (s t : Nat → Bool) (k r : Nat) (v : Bool)
    (h : ∀ i, s i = t (rho i)) (hv : v = t r) :
    ∀ i, Function.update s k v i = t (Function.update rho k r i) := by
  intro i
  by_cases hi : i = k
  · subst i; simpa using hv
  · simpa [Function.update_of_ne hi] using h i

lemma update_fresh (rho : Nat → Nat) (s t : Nat → Bool) (k m : Nat) (v : Bool)
    (h : ∀ i, s i = t (rho i)) (hb : ∀ i, rho i < m) :
    ∀ i, Function.update s k v i =
      Function.update t m v (Function.update rho k m i) := by
  intro i
  by_cases hi : i = k
  · subst i; simp
  · have hr : rho i ≠ m := Nat.ne_of_lt (hb i)
    simpa [Function.update_of_ne hi, Function.update_of_ne hr] using h i

lemma compile_length (gs : List Gate) (k m : Nat) (rho : Nat → Nat) :
    (compile gs k m rho).1.length = survivors gs k m rho := by
  induction gs generalizing k m rho with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : Keep (rho g.2.1) (rho g.2.2)
    · simp [compile, survivors, h, ih, Nat.add_comm]
    · simp [compile, survivors, h, ih]

lemma compile_correct (gs : List Gate) (k m : Nat) (rho : Nat → Nat)
    (s t : Nat → Bool) (hm : 0 < m) (h0 : t 0 = false)
    (hb : ∀ i, rho i < m) (hr : ∀ i, s i = t (rho i)) :
    (∀ i, (compile gs k m rho).2 i < m + (compile gs k m rho).1.length) ∧
    (∀ i, run gs k s i = run (compile gs k m rho).1 m t ((compile gs k m rho).2 i)) := by
  induction gs generalizing k m rho s t with
  | nil => simpa [compile, run] using And.intro hb hr
  | cons g gs ih =>
    have he := mapped_sound rho g s t hr
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · have hb' : ∀ i, Function.update rho k m i < m + 1 := by
        intro i
        by_cases hi : i = k
        · subst i; simp
        · simpa [Function.update_of_ne hi] using Nat.lt_succ_of_lt (hb i)
      have hz : Function.update t m (evalGate g s) 0 = false := by
        simpa [Function.update_of_ne (Nat.ne_of_lt hm)] using h0
      have ih' := ih (k + 1) (m + 1) (Function.update rho k m)
        (Function.update s k (evalGate g s)) (Function.update t m (evalGate g s))
        (by omega) hz hb' (update_fresh rho s t k m (evalGate g s) hr hb)
      simp only [compile, hk, ite_true, List.length_cons, run]
      constructor
      · intro i
        have h := ih'.1 i
        omega
      · simpa only [he] using ih'.2
    · let r := replacement g.1 (rho g.2.1) (rho g.2.2)
      have hv : evalGate g s = t r := by
        rw [he]
        exact (replacement_sound g.1 (rho g.2.1) (rho g.2.2) t h0 hk).symm
      have hbr : r < m := replacement_lt _ _ _ _ hm (hb _) (hb _)
      have hb' : ∀ i, Function.update rho k r i < m := by
        intro i
        by_cases hi : i = k
        · subst i; simpa using hbr
        · simpa [Function.update_of_ne hi] using hb i
      have ih' := ih (k + 1) m (Function.update rho k r)
        (Function.update s k (evalGate g s)) t hm h0 hb'
        (update_same rho s t k r (evalGate g s) hr hv)
      simpa only [compile, hk, Bool.false_eq_true, ite_false, run] using ih'

def WellFormed : List Gate → Nat → Prop
  | [], _ => True
  | g :: gs, m => g.2.1 < m ∧ g.2.2 < m ∧ WellFormed gs (m + 1)

lemma compile_wellFormed (gs : List Gate) (k m : Nat) (rho : Nat → Nat)
    (hm : 0 < m) (hb : ∀ i, rho i < m) :
    WellFormed (compile gs k m rho).1 m := by
  induction gs generalizing k m rho with
  | nil => trivial
  | cons g gs ih =>
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · have hb' : ∀ i, Function.update rho k m i < m + 1 := by
        intro i
        by_cases hi : i = k
        · subst i; simp
        · simpa [Function.update_of_ne hi] using Nat.lt_succ_of_lt (hb i)
      have hh := ih (k + 1) (m + 1) (Function.update rho k m) (by omega) hb'
      simpa only [compile, hk, ite_true, WellFormed, mapped] using
        And.intro (hb g.2.1) (And.intro (hb g.2.2) hh)
    · let r := replacement g.1 (rho g.2.1) (rho g.2.2)
      have hbr : r < m := replacement_lt _ _ _ _ hm (hb _) (hb _)
      have hb' : ∀ i, Function.update rho k r i < m := by
        intro i
        by_cases hi : i = k
        · subst i; simpa using hbr
        · simpa [Function.update_of_ne hi] using hb i
      simpa only [compile, hk, Bool.false_eq_true, ite_false] using ih (k + 1) m (Function.update rho k r) hm hb'

lemma survivors_le_length (gs : List Gate) (k m : Nat) (rho : Nat → Nat) :
    survivors gs k m rho ≤ gs.length := by
  induction gs generalizing k m rho with
  | nil => simp [survivors]
  | cons g gs ih =>
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · simp only [survivors, hk, ite_true, List.length_cons]
      have h := ih (k + 1) (m + 1) (Function.update rho k m)
      omega
    · simp only [survivors, hk, Bool.false_eq_true, ite_false, List.length_cons]
      have h := ih (k + 1) m
        (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2)))
      omega

def initialMap (n v : Nat) : Nat → Nat :=
  fun i => if i < n then (if i = v then 0 else i + 1) else 0

def pinnedState (n v : Nat) (x : Nat → Bool) : Nat → Bool :=
  fun i => if i < n then (if i = v then false else x i) else false

def zeroState (n : Nat) (x : Nat → Bool) : Nat → Bool :=
  fun i => if 0 < i ∧ i ≤ n then x (i - 1) else false

lemma initialMap_bound (n v i : Nat) : initialMap n v i < n + 1 := by
  unfold initialMap
  split_ifs <;> omega

lemma initialMap_sound (n v : Nat) (x : Nat → Bool) :
    ∀ i, pinnedState n v x i = zeroState n x (initialMap n v i) := by
  intro i
  unfold pinnedState initialMap zeroState
  by_cases hi : i < n
  · by_cases hv : i = v
    · simp [hi, hv]
    · have hle : i + 1 ≤ n := by omega
      simp [hi, hv, hle]
  · simp [hi]

def cofactor (n v : Nat) (gs : List Gate) : List Gate × (Nat → Nat) :=
  compile gs n (n + 1) (initialMap n v)

lemma cofactor_correct (n v : Nat) (gs : List Gate) :
    WellFormed (cofactor n v gs).1 (n + 1) ∧
    (cofactor n v gs).1.length = survivors gs n (n + 1) (initialMap n v) ∧
    ∀ (x : Nat → Bool) (i : Nat),
      run gs n (pinnedState n v x) i =
        run (cofactor n v gs).1 (n + 1) (zeroState n x) ((cofactor n v gs).2 i) := by
  refine ⟨compile_wellFormed _ _ _ _ (by omega) (initialMap_bound n v),
    compile_length _ _ _ _, ?_⟩
  intro x
  exact (compile_correct gs n (n + 1) (initialMap n v)
    (pinnedState n v x) (zeroState n x) (by omega) (by simp [zeroState])
    (initialMap_bound n v) (initialMap_sound n v x)).2

end CofactorSimplification

namespace CofactorCountBridge

open CofactorSimplification

def SameAliases (rho sigma : Nat → Nat) : Prop :=
  (∀ i, rho i = 0 ↔ sigma i = 0) ∧
  ∀ i j, rho i = rho j ↔ sigma i = sigma j

def ValueAliases (rho sigma : Nat → Nat) (r s : Nat) : Prop :=
  (r = 0 ↔ s = 0) ∧ ∀ i, r = rho i ↔ s = sigma i

lemma value_zero (rho sigma : Nat → Nat) (h : SameAliases rho sigma) :
    ValueAliases rho sigma 0 0 := by
  refine ⟨Iff.rfl, ?_⟩
  intro i
  simpa only [eq_comm] using h.1 i

lemma value_input (rho sigma : Nat → Nat) (h : SameAliases rho sigma) (i : Nat) :
    ValueAliases rho sigma (rho i) (sigma i) :=
  ⟨h.1 i, h.2 i⟩

lemma keep_eq (rho sigma : Nat → Nat) (h : SameAliases rho sigma) (a b : Nat) :
    Keep (rho a) (rho b) = Keep (sigma a) (sigma b) := by
  simp only [Keep, ne_eq, h.1 a, h.1 b, h.2 a b]

lemma replacement_aliases (rho sigma : Nat → Nat) (h : SameAliases rho sigma)
    (op : Bool) (a b : Nat) :
    ValueAliases rho sigma (replacement op (rho a) (rho b))
      (replacement op (sigma a) (sigma b)) := by
  cases op <;> by_cases ha : rho a = 0 <;> by_cases hb : rho b = 0
  all_goals
    have ha' : (sigma a = 0) = (rho a = 0) := propext (h.1 a).symm
    have hb' : (sigma b = 0) = (rho b = 0) := propext (h.1 b).symm
    simp only [replacement, Bool.false_eq_true, ite_false, ite_true, ha', hb', ha, hb,
      or_true, true_or, false_or, ite_true, ite_false]
    first | exact value_zero rho sigma h |
      simpa only [ha, hb] using value_input rho sigma h a |
      simpa only [ha, hb] using value_input rho sigma h b

lemma update_aliases (rho sigma : Nat → Nat) (h : SameAliases rho sigma)
    (k r s : Nat) (hv : ValueAliases rho sigma r s) :
    SameAliases (Function.update rho k r) (Function.update sigma k s) := by
  constructor
  · intro i
    by_cases hi : i = k
    · subst i; simpa using hv.1
    · simpa [Function.update_of_ne hi] using h.1 i
  · intro i j
    by_cases hi : i = k <;> by_cases hj : j = k
    · subst i; subst j; simp
    · subst i; simpa [Function.update_of_ne hj] using hv.2 j
    · subst j
      simpa [Function.update_of_ne hi, eq_comm] using hv.2 i
    · simpa [Function.update_of_ne hi, Function.update_of_ne hj] using h.2 i j

lemma fresh_aliases (rho sigma : Nat → Nat) (m n : Nat)
    (hm : 0 < m) (hn : 0 < n) (hb : ∀ i, rho i < m) (hc : ∀ i, sigma i < n) :
    ValueAliases rho sigma m n := by
  constructor
  · simp [Nat.ne_of_gt hm, Nat.ne_of_gt hn]
  · intro i
    simp [Nat.ne_of_gt (hb i), Nat.ne_of_gt (hc i)]

lemma update_bound (rho : Nat → Nat) (k r m : Nat)
    (hr : r < m) (hb : ∀ i, rho i < m) : ∀ i, Function.update rho k r i < m := by
  intro i
  by_cases hi : i = k
  · subst i; simpa using hr
  · simpa [Function.update_of_ne hi] using hb i

def sparseSurvivors : List Gate → Nat → Nat → (Nat → Nat) → Nat
  | [], _, _, _ => 0
  | g :: gs, k, n, sigma =>
    if Keep (sigma g.2.1) (sigma g.2.2) then
      1 + sparseSurvivors gs (k + 1) (n + 1) (Function.update sigma k n)
    else
      sparseSurvivors gs (k + 1) (n + 1)
        (Function.update sigma k (replacement g.1 (sigma g.2.1) (sigma g.2.2)))

lemma survivors_eq_sparse (gs : List Gate) (k m n : Nat) (rho sigma : Nat → Nat)
    (hm : 0 < m) (hn : 0 < n) (hb : ∀ i, rho i < m) (hc : ∀ i, sigma i < n)
    (h : SameAliases rho sigma) :
    survivors gs k m rho = sparseSurvivors gs k n sigma := by
  induction gs generalizing k m n rho sigma with
  | nil => rfl
  | cons g gs ih =>
    have he := keep_eq rho sigma h g.2.1 g.2.2
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · have hk' : Keep (sigma g.2.1) (sigma g.2.2) := by simpa only [he] using hk
      simp only [survivors, sparseSurvivors, hk, hk', ite_true]
      congr 1
      apply ih (k + 1) (m + 1) (n + 1)
        (Function.update rho k m) (Function.update sigma k n) (by omega) (by omega)
      · exact update_bound rho k m (m + 1) (by omega) (fun i => by have := hb i; omega)
      · exact update_bound sigma k n (n + 1) (by omega) (fun i => by have := hc i; omega)
      · exact update_aliases rho sigma h k m n (fresh_aliases rho sigma m n hm hn hb hc)
    · have hk' : ¬ Keep (sigma g.2.1) (sigma g.2.2) := by simpa only [he] using hk
      simp only [survivors, sparseSurvivors, hk, hk', Bool.false_eq_true, ite_false]
      apply ih (k + 1) m (n + 1)
        (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2)))
        (Function.update sigma k (replacement g.1 (sigma g.2.1) (sigma g.2.2))) hm (by omega)
      · exact update_bound rho k _ m (replacement_lt _ _ _ _ hm (hb _) (hb _)) hb
      · exact update_bound sigma k _ (n + 1)
          (Nat.lt_succ_of_lt (replacement_lt _ _ _ _ hn (hc _) (hc _)))
          (fun i => Nat.lt_succ_of_lt (hc i))
      · exact update_aliases rho sigma h k _ _ (replacement_aliases rho sigma h _ _ _)

lemma cofactor_length_sparse (n v : Nat) (gs : List Gate) :
    (cofactor n v gs).1.length = sparseSurvivors gs n (n + 1) (initialMap n v) := by
  rw [cofactor, compile_length]
  exact survivors_eq_sparse gs n (n + 1) (n + 1) (initialMap n v) (initialMap n v)
    (by omega) (by omega) (initialMap_bound n v) (initialMap_bound n v)
    ⟨fun _ => Iff.rfl, fun _ _ => Iff.rfl⟩

end CofactorCountBridge

namespace CofactorWeightedCount

open CofactorSimplification CofactorCountBridge

def weightedCount (w : Bool → Nat) : List Gate → Nat
  | [] => 0
  | g :: gs => w g.1 + weightedCount w gs

def denseWeighted (w : Bool → Nat) : List Gate → Nat → Nat → (Nat → Nat) → Nat
  | [], _, _, _ => 0
  | g :: gs, k, m, rho =>
    if Keep (rho g.2.1) (rho g.2.2) then
      w g.1 + denseWeighted w gs (k + 1) (m + 1) (Function.update rho k m)
    else
      denseWeighted w gs (k + 1) m
        (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2)))

def sparseWeighted (w : Bool → Nat) : List Gate → Nat → Nat → (Nat → Nat) → Nat
  | [], _, _, _ => 0
  | g :: gs, k, n, sigma =>
    if Keep (sigma g.2.1) (sigma g.2.2) then
      w g.1 + sparseWeighted w gs (k + 1) (n + 1) (Function.update sigma k n)
    else
      sparseWeighted w gs (k + 1) (n + 1)
        (Function.update sigma k (replacement g.1 (sigma g.2.1) (sigma g.2.2)))

lemma compile_weighted (w : Bool → Nat) (gs : List Gate) (k m : Nat) (rho : Nat → Nat) :
    weightedCount w (compile gs k m rho).1 = denseWeighted w gs k m rho := by
  induction gs generalizing k m rho with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : Keep (rho g.2.1) (rho g.2.2)
    · simp [compile, weightedCount, denseWeighted, mapped, h, ih]
    · simp [compile, weightedCount, denseWeighted, h, ih]

lemma weighted_eq_sparse (w : Bool → Nat) (gs : List Gate) (k m n : Nat) (rho sigma : Nat → Nat)
    (hm : 0 < m) (hn : 0 < n) (hb : ∀ i, rho i < m) (hc : ∀ i, sigma i < n)
    (h : SameAliases rho sigma) :
    denseWeighted w gs k m rho = sparseWeighted w gs k n sigma := by
  induction gs generalizing k m n rho sigma with
  | nil => rfl
  | cons g gs ih =>
    have he := keep_eq rho sigma h g.2.1 g.2.2
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · have hk' : Keep (sigma g.2.1) (sigma g.2.2) := by simpa only [he] using hk
      simp only [denseWeighted, sparseWeighted, hk, hk', ite_true]
      congr 1
      apply ih (k + 1) (m + 1) (n + 1)
        (Function.update rho k m) (Function.update sigma k n) (by omega) (by omega)
      · exact update_bound rho k m (m + 1) (by omega) (fun i => by have := hb i; omega)
      · exact update_bound sigma k n (n + 1) (by omega) (fun i => by have := hc i; omega)
      · exact update_aliases rho sigma h k m n (fresh_aliases rho sigma m n hm hn hb hc)
    · have hk' : ¬ Keep (sigma g.2.1) (sigma g.2.2) := by simpa only [he] using hk
      simp only [denseWeighted, sparseWeighted, hk, hk', Bool.false_eq_true, ite_false]
      apply ih (k + 1) m (n + 1)
        (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2)))
        (Function.update sigma k (replacement g.1 (sigma g.2.1) (sigma g.2.2))) hm (by omega)
      · exact update_bound rho k _ m (replacement_lt _ _ _ _ hm (hb _) (hb _)) hb
      · exact update_bound sigma k _ (n + 1)
          (Nat.lt_succ_of_lt (replacement_lt _ _ _ _ hn (hc _) (hc _)))
          (fun i => Nat.lt_succ_of_lt (hc i))
      · exact update_aliases rho sigma h k _ _ (replacement_aliases rho sigma h _ _ _)

lemma cofactor_weight_sparse (w : Bool → Nat) (n v : Nat) (gs : List Gate) :
    weightedCount w (cofactor n v gs).1 =
      sparseWeighted w gs n (n + 1) (initialMap n v) := by
  rw [cofactor, compile_weighted]
  exact weighted_eq_sparse w gs n (n + 1) (n + 1) (initialMap n v) (initialMap n v)
    (by omega) (by omega) (initialMap_bound n v) (initialMap_bound n v)
    ⟨fun _ => Iff.rfl, fun _ _ => Iff.rfl⟩

lemma weightedCount_eq_filter (wanted : Bool) (gs : List Gate) :
    weightedCount (fun op => if op = wanted then 1 else 0) gs =
      (gs.filter (fun g => g.1 == wanted)).length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : g.1 = wanted
    · simp [weightedCount, h, ih, Nat.add_comm]
    · simp [weightedCount, h, ih]

end CofactorWeightedCount

namespace CofactorProjectBridge

open CofactorSimplification

abbrev PGate := PEqualNP.CircuitLowerBounds.Gate
abbrev PCircuit := PEqualNP.CircuitLowerBounds.Circuit

def Positive (gs : List Gate) : Prop :=
  ∀ g ∈ gs, 0 < g.2.1 ∧ 0 < g.2.2

lemma compile_positive (gs : List Gate) (k m : Nat) (rho : Nat → Nat) :
    Positive (compile gs k m rho).1 := by
  induction gs generalizing k m rho with
  | nil => simp [compile, Positive]
  | cons g gs ih =>
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · have hne : rho g.2.1 ≠ 0 ∧ rho g.2.2 ≠ 0 ∧ rho g.2.1 ≠ rho g.2.2 := by
        simpa [Keep] using hk
      have hh := ih (k + 1) (m + 1) (Function.update rho k m)
      simp only [compile, hk, ite_true]
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨Nat.pos_of_ne_zero hne.1, Nat.pos_of_ne_zero hne.2.1⟩
      · exact hh z hz
    · simpa only [compile, hk, Bool.false_eq_true, ite_false] using
        ih (k + 1) m (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2)))

def wireView (w : List Bool) : Nat → Bool :=
  fun i => if i = 0 then false else w.getD (i - 1) false

lemma getD_snoc_ne (w : List Bool) (b : Bool) (i : Nat) (h : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hi : i < w.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma wireView_snoc (w : List Bool) (b : Bool) :
    wireView (w ++ [b]) = Function.update (wireView w) (w.length + 1) b := by
  funext i
  by_cases hz : i = 0
  · subst i
    simp [wireView]
  · by_cases hi : i = w.length + 1
    · subst i
      simp [wireView]
    · have hs : i - 1 ≠ w.length := by omega
      simp only [wireView, hz, ite_false, Function.update_of_ne hi]
      exact getD_snoc_ne w b (i - 1) hs

def projectGate (g : Gate) : PGate :=
  ⟨if g.1 then .and else .or, [g.2.1 - 1, g.2.2 - 1]⟩

lemma projectGate_eval (g : Gate) (w : List Bool)
    (ha : 0 < g.2.1) (hb : 0 < g.2.2) :
    (projectGate g).op.eval ((projectGate g).inputs.map fun i => w.getD i false) =
      evalGate g (wireView w) := by
  cases hg : g.1 <;>
    simp [projectGate, hg, evalGate, wireView, Nat.ne_of_gt ha, Nat.ne_of_gt hb,
      PEqualNP.CircuitLowerBounds.GateOp.eval]

def projectRun : List Gate → List Bool → List Bool
  | [], w => w
  | g :: gs, w => projectRun gs
      (w ++ [(projectGate g).op.eval ((projectGate g).inputs.map fun i => w.getD i false)])

lemma projectRun_length (gs : List Gate) (w : List Bool) :
    (projectRun gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [projectRun]
  | cons g gs ih => simp [projectRun, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma projectRun_fold (gs : List Gate) (w : List Bool) :
    projectRun gs w = (gs.map projectGate).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simpa only [projectRun, List.map_cons, List.foldl_cons] using ih _

lemma wireView_projectRun (gs : List Gate) (w : List Bool) (hp : Positive gs) :
    wireView (projectRun gs w) = run gs (w.length + 1) (wireView w) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hg := hp g List.mem_cons_self
    have ht : Positive gs := fun z hz => hp z (List.mem_cons_of_mem g hz)
    change wireView (projectRun gs
      (w ++ [(projectGate g).op.eval ((projectGate g).inputs.map fun i => w.getD i false)])) = _
    rw [ih _ ht, wireView_snoc, projectGate_eval g w hg.1 hg.2]
    simp only [List.length_append, List.length_singleton, run]

def projectCircuit (n : Nat) (gs : List Gate) (rep : Nat) : PCircuit :=
  ⟨gs.map projectGate, if rep = 0 then n + gs.length else rep - 1⟩

lemma projectCircuit_size (n : Nat) (gs : List Gate) (rep : Nat) :
    (projectCircuit n gs rep).size = gs.length := by
  simp [projectCircuit, PEqualNP.CircuitLowerBounds.Circuit.size]

lemma projectCircuit_mono (n : Nat) (gs : List Gate) (rep : Nat) :
    PEqualNP.MetaComplexity.Monotone2 (projectCircuit n gs rep) := by
  intro g hg
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hg
  cases hz : z.1 <;> simp [projectGate, hz]

lemma projectCircuit_eval (gs : List Gate) (w : List Bool) (rep : Nat)
    (hp : Positive gs) :
    (projectCircuit w.length gs rep).eval w =
      run gs (w.length + 1) (wireView w) rep := by
  rw [← wireView_projectRun gs w hp]
  unfold projectCircuit PEqualNP.CircuitLowerBounds.Circuit.eval
    PEqualNP.CircuitLowerBounds.Circuit.wires
  rw [← projectRun_fold]
  by_cases hr : rep = 0
  · subst rep
    simp only [ite_true, wireView]
    exact List.getD_eq_default _ _ (by rw [projectRun_length])
  · simp only [hr, ite_false, wireView]

def cofactorCircuit (n v : Nat) (gs : List Gate) (output : Nat) : PCircuit :=
  projectCircuit n (cofactor n v gs).1 ((cofactor n v gs).2 output)

lemma zeroState_eq_wireView (w : List Bool) :
    zeroState w.length (fun i => w.getD i false) = wireView w := by
  funext i
  by_cases hz : i = 0
  · subst i; simp [zeroState, wireView]
  · have hi : 0 < i := Nat.pos_of_ne_zero hz
    by_cases hl : i ≤ w.length
    · simp [zeroState, wireView, hz, hi, hl]
    · have hn : w.length ≤ i - 1 := by omega
      simp only [zeroState, wireView, hz, ite_false, hi, hl, true_and]
      exact (List.getD_eq_default _ _ hn).symm

lemma cofactorCircuit_correct (v : Nat) (gs : List Gate) (output : Nat) (w : List Bool) :
    PEqualNP.MetaComplexity.Monotone2 (cofactorCircuit w.length v gs output) ∧
    (cofactorCircuit w.length v gs output).size =
      survivors gs w.length (w.length + 1) (initialMap w.length v) ∧
    (cofactorCircuit w.length v gs output).eval w =
      run gs w.length (pinnedState w.length v (fun i => w.getD i false)) output := by
  refine ⟨projectCircuit_mono _ _ _, ?_, ?_⟩
  · exact (projectCircuit_size _ _ _).trans (compile_length _ _ _ _)
  · unfold cofactorCircuit
    have hp : Positive (cofactor w.length v gs).1 :=
      compile_positive gs w.length (w.length + 1) (initialMap w.length v)
    rw [projectCircuit_eval (cofactor w.length v gs).1 w
      ((cofactor w.length v gs).2 output) hp]
    have h := (cofactor_correct w.length v gs).2.2 (fun i => w.getD i false) output
    rw [zeroState_eq_wireView] at h
    exact h.symm

def promote (g : Gate) : Gate := (g.1, g.2.1 + 1, g.2.2 + 1)

lemma promote_gate (g : Gate) (s t : Nat → Bool)
    (h : ∀ i, s i = t (i + 1)) : evalGate g s = evalGate (promote g) t := by
  simp only [evalGate, promote]
  rw [h g.2.1, h g.2.2]
  rfl

lemma promote_run (gs : List Gate) (k : Nat) (s t : Nat → Bool)
    (h : ∀ i, s i = t (i + 1)) :
    ∀ i, run gs k s i = run (gs.map promote) (k + 1) t (i + 1) := by
  induction gs generalizing k s t with
  | nil => exact h
  | cons g gs ih =>
    have he := promote_gate g s t h
    have hh : ∀ i, Function.update s k (evalGate g s) i =
        Function.update t (k + 1) (evalGate (promote g) t) (i + 1) := by
      intro i
      by_cases hi : i = k
      · subst i; simpa using he
      · have hi' : i + 1 ≠ k + 1 := by omega
        simpa [Function.update_of_ne hi, Function.update_of_ne hi'] using h i
    simpa only [run, List.map_cons] using ih (k + 1) _ _ hh

lemma promote_positive (gs : List Gate) : Positive (gs.map promote) := by
  intro g hg
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hg
  simp [promote]

def rawCircuit (n : Nat) (gs : List Gate) (output : Nat) : PCircuit :=
  projectCircuit n (gs.map promote) (output + 1)

lemma rawCircuit_description (n : Nat) (gs : List Gate) (output : Nat) :
    rawCircuit n gs output =
      ⟨gs.map (fun g => ⟨if g.1 then .and else .or, [g.2.1, g.2.2]⟩), output⟩ := by
  simp [rawCircuit, projectCircuit, projectGate, promote, List.map_map]

lemma rawCircuit_eval (gs : List Gate) (output : Nat) (w : List Bool) :
    (rawCircuit w.length gs output).eval w =
      run gs w.length (fun i => w.getD i false) output := by
  unfold rawCircuit
  rw [projectCircuit_eval _ _ _ (promote_positive gs)]
  exact (promote_run gs w.length (fun i => w.getD i false) (wireView w)
    (by intro i; simp [wireView]) output).symm

lemma pinned_getD (n : Nat) (v : Fin n) (x : Fin n → Bool) :
    (fun i => (List.ofFn (Function.update x v false)).getD i false) =
      pinnedState n v.val (fun i => (List.ofFn x).getD i false) := by
  funext i
  by_cases hi : i < n
  · by_cases hv : i = v.val
    · have hfin : (⟨i, hi⟩ : Fin n) = v := Fin.ext hv
      simp [pinnedState, hi, hv, hfin]
    · have hfin : (⟨i, hi⟩ : Fin n) ≠ v := fun h => hv (congrArg Fin.val h)
      simp [pinnedState, hi, hv, Function.update_of_ne hfin]
  · simp [pinnedState, hi]

lemma cofactorCircuit_pinned (n : Nat) (v : Fin n) (gs : List Gate)
    (output : Nat) (x : Fin n → Bool) :
    (cofactorCircuit n v.val gs output).eval (List.ofFn x) =
      (rawCircuit n gs output).eval (List.ofFn (Function.update x v false)) := by
  have hd := (cofactorCircuit_correct v.val gs output (List.ofFn x)).2.2
  have hc := rawCircuit_eval gs output (List.ofFn (Function.update x v false))
  simp only [List.length_ofFn] at hd hc
  rw [pinned_getD] at hc
  exact hd.trans hc.symm

lemma exists_cofactorCircuit (n : Nat) (v : Fin n) (gs : List Gate) (output : Nat) :
    ∃ D : PCircuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      D.size = survivors gs n (n + 1) (initialMap n v.val) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        (rawCircuit n gs output).eval (List.ofFn (Function.update x v false)) := by
  refine ⟨cofactorCircuit n v.val gs output, projectCircuit_mono _ _ _, ?_, ?_⟩
  · exact (projectCircuit_size _ _ _).trans (compile_length _ _ _ _)
  · exact cofactorCircuit_pinned n v gs output

end CofactorProjectBridge

namespace CofactorSparseProjectBridge

open CofactorSimplification CofactorProjectBridge CofactorCountBridge

lemma exists_sparse_cofactorCircuit (n : Nat) (v : Fin n) (gs : List Gate) (output : Nat) :
    ∃ D : PCircuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      D.size = sparseSurvivors gs n (n + 1) (initialMap n v.val) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        (rawCircuit n gs output).eval (List.ofFn (Function.update x v false)) := by
  obtain ⟨D, hmono, hsize, heval⟩ := exists_cofactorCircuit n v gs output
  have hcount := cofactor_length_sparse n v.val gs
  rw [cofactor, compile_length] at hcount
  exact ⟨D, hmono, hsize.trans hcount, heval⟩

end CofactorSparseProjectBridge

namespace CofactorOperationBridge

open CofactorSimplification CofactorProjectBridge CofactorCountBridge CofactorWeightedCount

def hasOperation (wanted : Bool) (g : PGate) : Bool :=
  match g.op with
  | .and => wanted
  | .or => !wanted
  | _ => false

lemma projectCircuit_opCount (n : Nat) (gs : List Gate) (rep : Nat) (wanted : Bool) :
    ((projectCircuit n gs rep).gates.filter (hasOperation wanted)).length =
      (gs.filter (fun g => g.1 == wanted)).length := by
  change ((gs.map projectGate).filter (hasOperation wanted)).length = _
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.filter_cons]
    cases wanted <;> cases hg : g.1 <;>
      simp_all [projectGate, hasOperation]

lemma cofactorCircuit_opCount (n v : Nat) (gs : List Gate) (output : Nat) (wanted : Bool) :
    ((cofactorCircuit n v gs output).gates.filter (hasOperation wanted)).length =
      sparseWeighted (fun op => if op = wanted then 1 else 0)
        gs n (n + 1) (initialMap n v) := by
  unfold cofactorCircuit
  rw [projectCircuit_opCount, ← weightedCount_eq_filter]
  exact cofactor_weight_sparse _ n v gs

lemma exists_sparse_counted_cofactorCircuit (n : Nat) (v : Fin n)
    (gs : List Gate) (output : Nat) :
    ∃ D : PCircuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      D.size = sparseSurvivors gs n (n + 1) (initialMap n v.val) ∧
      (∀ wanted : Bool, (D.gates.filter (hasOperation wanted)).length =
        sparseWeighted (fun op => if op = wanted then 1 else 0)
          gs n (n + 1) (initialMap n v.val)) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        (rawCircuit n gs output).eval (List.ofFn (Function.update x v false)) := by
  refine ⟨cofactorCircuit n v.val gs output, projectCircuit_mono _ _ _, ?_, ?_, ?_⟩
  · exact (projectCircuit_size _ _ _).trans (cofactor_length_sparse n v.val gs)
  · exact cofactorCircuit_opCount n v.val gs output
  · exact cofactorCircuit_pinned n v gs output

end CofactorOperationBridge

namespace CofactorDeletedInputBridge

open CofactorSimplification CofactorProjectBridge CofactorCountBridge
open CofactorWeightedCount CofactorOperationBridge

def skipMap (N v : Nat) : Nat → Nat :=
  fun i => if i < N then (if i = v then 0 else if i < v then i + 1 else i) else 0

lemma skipMap_bound (N v : Nat) (hv : v < N) (i : Nat) : skipMap N v i < N := by
  unfold skipMap
  split_ifs <;> omega

lemma skipMap_aliases (N v : Nat) (hv : v < N) :
    SameAliases (skipMap N v) (initialMap N v) := by
  constructor
  · intro i
    unfold skipMap initialMap
    split_ifs <;> simp_all <;> omega
  · intro i j
    unfold skipMap initialMap
    split_ifs <;> simp_all <;> omega

def deletedCofactor (n : Nat) (v : Fin (n + 1)) (gs : List Gate) :
    List Gate × (Nat → Nat) :=
  compile gs (n + 1) (n + 1) (skipMap (n + 1) v.val)

lemma deletedCofactor_length (n : Nat) (v : Fin (n + 1)) (gs : List Gate) :
    (deletedCofactor n v gs).1.length =
      sparseSurvivors gs (n + 1) (n + 2) (initialMap (n + 1) v.val) := by
  rw [deletedCofactor, compile_length]
  exact survivors_eq_sparse gs (n + 1) (n + 1) (n + 2)
    (skipMap (n + 1) v.val) (initialMap (n + 1) v.val) (by omega) (by omega)
    (skipMap_bound _ _ v.isLt) (initialMap_bound _ _) (skipMap_aliases _ _ v.isLt)

lemma deletedCofactor_weight (w : Bool → Nat) (n : Nat) (v : Fin (n + 1))
    (gs : List Gate) :
    weightedCount w (deletedCofactor n v gs).1 =
      sparseWeighted w gs (n + 1) (n + 2) (initialMap (n + 1) v.val) := by
  rw [deletedCofactor, compile_weighted]
  exact weighted_eq_sparse w gs (n + 1) (n + 1) (n + 2)
    (skipMap (n + 1) v.val) (initialMap (n + 1) v.val) (by omega) (by omega)
    (skipMap_bound _ _ v.isLt) (initialMap_bound _ _) (skipMap_aliases _ _ v.isLt)

def insertAssignment {n : Nat} (v : Fin (n + 1)) (x : Fin n → Bool) : Fin (n + 1) → Bool :=
  fun i => wireView (List.ofFn x) (skipMap (n + 1) v.val i.val)

lemma insertAssignment_formula {n : Nat} (v : Fin (n + 1)) (x : Fin n → Bool)
    (i : Fin (n + 1)) :
    insertAssignment v x i =
      if i.val = v.val then false
      else if i.val < v.val then (List.ofFn x).getD i.val false
      else (List.ofFn x).getD (i.val - 1) false := by
  by_cases hv : i.val = v.val
  · simp [insertAssignment, skipMap, wireView, i.isLt, hv]
  · by_cases hi : i.val < v.val
    · simp [insertAssignment, skipMap, wireView, i.isLt, hv, hi]
    · have hz : i.val ≠ 0 := by omega
      simp [insertAssignment, skipMap, wireView, i.isLt, hv, hi, hz]

lemma insertAssignment_at {n : Nat} (v : Fin (n + 1)) (x : Fin n → Bool) :
    insertAssignment v x v = false := by
  simp [insertAssignment_formula]

lemma insertAssignment_getD {n : Nat} (v : Fin (n + 1)) (x : Fin n → Bool) :
    ∀ i, (List.ofFn (insertAssignment v x)).getD i false =
      wireView (List.ofFn x) (skipMap (n + 1) v.val i) := by
  intro i
  by_cases hi : i < n + 1
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
    rfl
  · simp [hi, skipMap, wireView]

def deletedCircuit (n : Nat) (v : Fin (n + 1)) (gs : List Gate) (output : Nat) : PCircuit :=
  projectCircuit n (deletedCofactor n v gs).1 ((deletedCofactor n v gs).2 output)

lemma deletedCircuit_eval (n : Nat) (v : Fin (n + 1)) (gs : List Gate)
    (output : Nat) (x : Fin n → Bool) :
    (deletedCircuit n v gs output).eval (List.ofFn x) =
      (rawCircuit (n + 1) gs output).eval (List.ofFn (insertAssignment v x)) := by
  have hp : Positive (deletedCofactor n v gs).1 := compile_positive _ _ _ _
  have hd := projectCircuit_eval (deletedCofactor n v gs).1 (List.ofFn x)
    ((deletedCofactor n v gs).2 output) hp
  have h := (compile_correct gs (n + 1) (n + 1) (skipMap (n + 1) v.val)
    (fun i => (List.ofFn (insertAssignment v x)).getD i false) (wireView (List.ofFn x))
    (by omega) (by simp [wireView]) (skipMap_bound _ _ v.isLt)
    (insertAssignment_getD v x)).2 output
  have hc := rawCircuit_eval gs output (List.ofFn (insertAssignment v x))
  simp only [List.length_ofFn] at hd hc
  exact hd.trans (h.symm.trans hc.symm)

lemma exists_deleted_counted_circuit (n : Nat) (v : Fin (n + 1))
    (gs : List Gate) (output : Nat) :
    ∃ D : PCircuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      D.size = sparseSurvivors gs (n + 1) (n + 2) (initialMap (n + 1) v.val) ∧
      (∀ wanted : Bool, (D.gates.filter (hasOperation wanted)).length =
        sparseWeighted (fun op => if op = wanted then 1 else 0)
          gs (n + 1) (n + 2) (initialMap (n + 1) v.val)) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        (rawCircuit (n + 1) gs output).eval (List.ofFn (insertAssignment v x)) := by
  refine ⟨deletedCircuit n v gs output, projectCircuit_mono _ _ _, ?_, ?_, ?_⟩
  · exact (projectCircuit_size _ _ _).trans (deletedCofactor_length n v gs)
  · intro wanted
    unfold deletedCircuit
    rw [projectCircuit_opCount, ← weightedCount_eq_filter]
    exact deletedCofactor_weight _ n v gs
  · exact deletedCircuit_eval n v gs output

end CofactorDeletedInputBridge

namespace CleanWirePinAppend

open CofactorSimplification CofactorProjectBridge CofactorCountBridge
open CofactorWeightedCount CofactorOperationBridge

def reads (h : Nat) (g : Gate) : Bool := (g.2.1 == h) || (g.2.2 == h)

lemma survivors_reader_savings (gs : List Gate) (k m h : Nat) (rho : Nat → Nat)
    (hh : h < k) (hz : rho h = 0) :
    survivors gs k m rho + gs.countP (reads h) ≤ gs.length := by
  induction gs generalizing k m rho with
  | nil => simp [survivors]
  | cons g gs ih =>
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · have hn : rho g.2.1 ≠ 0 ∧ rho g.2.2 ≠ 0 ∧ rho g.2.1 ≠ rho g.2.2 := by
        simpa [Keep] using hk
      have ha : g.2.1 ≠ h := by
        intro he
        exact hn.1 (he ▸ hz)
      have hb : g.2.2 ≠ h := by
        intro he
        exact hn.2.1 (he ▸ hz)
      have hr : reads h g = false := by simp [reads, ha, hb]
      have hz' : Function.update rho k m h = 0 := by
        simpa [Function.update_of_ne (Nat.ne_of_lt hh)] using hz
      have hi := ih (k + 1) (m + 1) (Function.update rho k m) (by omega) hz'
      simp only [survivors, hk, ite_true, List.countP_cons, hr, Bool.false_eq_true,
        ite_false, Nat.zero_add, List.length_cons]
      omega
    · let r := replacement g.1 (rho g.2.1) (rho g.2.2)
      have hz' : Function.update rho k r h = 0 := by
        simpa [Function.update_of_ne (Nat.ne_of_lt hh)] using hz
      have hi := ih (k + 1) m (Function.update rho k r) (by omega) hz'
      cases hr : reads h g <;>
        simp only [survivors, hk, Bool.false_eq_true, ite_false, List.countP_cons,
          hr, ite_true, Nat.zero_add, List.length_cons]
      all_goals dsimp [r] at hi
      all_goals omega

lemma compile_reader_savings (gs : List Gate) (k m h : Nat) (rho : Nat → Nat)
    (hh : h < k) (hz : rho h = 0) :
    (compile gs k m rho).1.length + gs.countP (reads h) ≤ gs.length := by
  rw [compile_length]
  exact survivors_reader_savings gs k m h rho hh hz

lemma cofactor_reader_savings (n h : Nat) (gs : List Gate) (hh : h < n) :
    (cofactor n h gs).1.length + gs.countP (reads h) ≤ gs.length := by
  exact compile_reader_savings gs n (n + 1) h (initialMap n h) hh (by simp [initialMap, hh])

lemma compile_weighted_le (w : Bool → Nat) (gs : List Gate) (k m : Nat) (rho : Nat → Nat) :
    weightedCount w (compile gs k m rho).1 ≤ weightedCount w gs := by
  induction gs generalizing k m rho with
  | nil => simp [compile, weightedCount]
  | cons g gs ih =>
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · simp only [compile, hk, ite_true, weightedCount, mapped]
      exact Nat.add_le_add_left (ih (k + 1) (m + 1) (Function.update rho k m)) _
    · simp only [compile, hk, Bool.false_eq_true, ite_false, weightedCount]
      have hi := ih (k + 1) m
        (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2)))
      omega

lemma cofactor_opCount_le (n h : Nat) (gs : List Gate) (wanted : Bool) :
    ((cofactor n h gs).1.filter (fun g => g.1 == wanted)).length ≤
      (gs.filter (fun g => g.1 == wanted)).length := by
  rw [← weightedCount_eq_filter, ← weightedCount_eq_filter]
  exact compile_weighted_le _ gs n (n + 1) (initialMap n h)

lemma weightedCount_append (w : Bool → Nat) (gs hs : List Gate) :
    weightedCount w (gs ++ hs) = weightedCount w gs + weightedCount w hs := by
  induction gs with
  | nil => simp [weightedCount]
  | cons g gs ih => simp [weightedCount, ih, Nat.add_assoc]

lemma weightedCount_promote (w : Bool → Nat) (gs : List Gate) :
    weightedCount w (gs.map promote) = weightedCount w gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [weightedCount, promote, ih]

def appendGate (h rep : Nat) : Gate :=
  (false, h + 1, if rep = 0 then h + 1 else rep)

def pinGates (n : Nat) (pre suffix : List Gate) (h output : Nat) : List Gate :=
  let cr := cofactor (n + pre.length) h suffix
  pre.map promote ++ cr.1 ++ [appendGate h (cr.2 output)]

def pinAndAppend (n : Nat) (pre suffix : List Gate) (h output : Nat) : PCircuit :=
  projectCircuit n (pinGates n pre suffix h output)
    (n + pre.length + (cofactor (n + pre.length) h suffix).1.length + 1)

lemma pinGates_positive (n : Nat) (pre suffix : List Gate) (h output : Nat) :
    Positive (pinGates n pre suffix h output) := by
  intro g hg
  simp only [pinGates, List.mem_append, List.mem_singleton] at hg
  rcases hg with (hp | hs) | rfl
  · exact promote_positive pre g hp
  · exact compile_positive suffix (n + pre.length) (n + pre.length + 1)
      (initialMap (n + pre.length) h) g hs
  · simp only [appendGate]
    split_ifs <;> omega

lemma pinAndAppend_mono (n : Nat) (pre suffix : List Gate) (h output : Nat) :
    PEqualNP.MetaComplexity.Monotone2 (pinAndAppend n pre suffix h output) :=
  projectCircuit_mono _ _ _

lemma pinAndAppend_size (n : Nat) (pre suffix : List Gate) (h output : Nat) :
    (pinAndAppend n pre suffix h output).size =
      pre.length + (cofactor (n + pre.length) h suffix).1.length + 1 := by
  rw [pinAndAppend, projectCircuit_size]
  simp [pinGates, Nat.add_assoc]

lemma pinAndAppend_size_savings (n : Nat) (pre suffix : List Gate) (h output : Nat)
    (hh : h < n + pre.length) :
    (pinAndAppend n pre suffix h output).size + suffix.countP (reads h) ≤
      (pre ++ suffix).length + 1 := by
  rw [pinAndAppend_size, List.length_append]
  have hs := cofactor_reader_savings (n + pre.length) h suffix hh
  omega

lemma pinAndAppend_andCount (n : Nat) (pre suffix : List Gate) (h output : Nat) :
    ((pinAndAppend n pre suffix h output).gates.filter (hasOperation true)).length ≤
      ((pre ++ suffix).filter (fun g => g.1 == true)).length := by
  rw [pinAndAppend, projectCircuit_opCount, ← weightedCount_eq_filter,
    ← weightedCount_eq_filter]
  simp only [pinGates, weightedCount_append, weightedCount_promote, weightedCount,
    appendGate, Bool.false_eq_true, ite_false, Nat.zero_add, Nat.add_zero]
  exact Nat.add_le_add_left (compile_weighted_le _ suffix (n + pre.length)
    (n + pre.length + 1) (initialMap (n + pre.length) h)) _

lemma run_append (gs hs : List Gate) (k : Nat) (s : Nat → Bool) :
    run (gs ++ hs) k s = run hs (k + gs.length) (run gs k s) := by
  induction gs generalizing k s with
  | nil => simp [run]
  | cons g gs ih => simp [run, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma run_below (gs : List Gate) (k i : Nat) (s : Nat → Bool) (hi : i < k) :
    run gs k s i = s i := by
  induction gs generalizing k s with
  | nil => rfl
  | cons g gs ih =>
    rw [run, ih (k + 1) _ (by omega)]
    exact Function.update_of_ne (Nat.ne_of_lt hi) _ _

lemma projectRun_append (gs hs : List Gate) (w : List Bool) :
    projectRun (gs ++ hs) w = projectRun hs (projectRun gs w) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => exact ih _

lemma pinnedState_eq_getD (w : List Bool) (h : Nat) (hz : w.getD h false = false) :
    pinnedState w.length h (fun i => w.getD i false) = fun i => w.getD i false := by
  funext i
  by_cases hi : i < w.length
  · by_cases he : i = h
    · subst i; simp only [pinnedState, hi, ite_true]; exact hz.symm
    · simp [pinnedState, hi, he]
  · simp [pinnedState, hi, List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]

lemma appendGate_eval (h rep : Nat) (s : Nat → Bool) (hz : s 0 = false) :
    evalGate (appendGate h rep) s = (s (h + 1) || s rep) := by
  by_cases hr : rep = 0
  · subst rep; simp [evalGate, appendGate, hz]
  · simp [evalGate, appendGate, hr]

lemma pinAndAppend_eval (pre suffix : List Gate) (h output : Nat) (w : List Bool)
    (hh : h < w.length + pre.length) :
    (pinAndAppend w.length pre suffix h output).eval w =
      ((projectRun (pre.map promote) w).getD h false ||
      (cofactorCircuit (w.length + pre.length) h suffix output).eval
        (projectRun (pre.map promote) w)) := by
  let cr := cofactor (w.length + pre.length) h suffix
  let sp := run (pre.map promote) (w.length + 1) (wireView w)
  let st := run cr.1 (w.length + pre.length + 1) sp
  have he : (pinAndAppend w.length pre suffix h output).eval w =
      evalGate (appendGate h (cr.2 output)) st := by
    rw [pinAndAppend, projectCircuit_eval _ _ _ (pinGates_positive _ _ _ _ _)]
    simp only [pinGates, run_append, List.length_append, List.length_map,
      List.length_singleton, run]
    have hn : w.length + 1 + (pre.length + (cofactor (w.length + pre.length) h suffix).1.length) =
        w.length + pre.length + (cofactor (w.length + pre.length) h suffix).1.length + 1 := by omega
    have hm : w.length + 1 + pre.length = w.length + pre.length + 1 := by omega
    simp only [hn, hm]
    exact Function.update_self _ _ _
  have hsp : sp = wireView (projectRun (pre.map promote) w) :=
    (wireView_projectRun _ _ (promote_positive pre)).symm
  have hzero : st 0 = false := by
    rw [show st 0 = sp 0 from run_below _ _ _ _ (by omega), hsp]
    simp [wireView]
  have hwire : st (h + 1) = (projectRun (pre.map promote) w).getD h false := by
    rw [show st (h + 1) = sp (h + 1) from run_below _ _ _ _ (by omega), hsp]
    simp [wireView]
  have hc : (cofactorCircuit (w.length + pre.length) h suffix output).eval
      (projectRun (pre.map promote) w) = st (cr.2 output) := by
    unfold cofactorCircuit
    have ht := projectCircuit_eval cr.1 (projectRun (pre.map promote) w)
      (cr.2 output) (compile_positive suffix (w.length + pre.length)
        (w.length + pre.length + 1) (initialMap (w.length + pre.length) h))
    simp only [projectRun_length, List.length_map] at ht
    rw [← hsp] at ht
    exact ht
  rw [he, appendGate_eval _ _ _ hzero, hwire, hc]

lemma rawCircuit_split (pre suffix : List Gate) (output : Nat) (w : List Bool) :
    (rawCircuit w.length (pre ++ suffix) output).eval w =
      (rawCircuit (w.length + pre.length) suffix output).eval
        (projectRun (pre.map promote) w) := by
  have hs := rawCircuit_eval suffix output (projectRun (pre.map promote) w)
  simp only [projectRun_length, List.length_map] at hs
  rw [hs, rawCircuit_eval, run_append]
  congr 2
  funext i
  have hp := promote_run pre w.length (fun j => w.getD j false) (wireView w)
    (by intro j; simp [wireView]) i
  rw [← wireView_projectRun _ _ (promote_positive pre)] at hp
  simpa [wireView] using hp

lemma pinAndAppend_correct (pre suffix : List Gate) (h output : Nat) (w : List Bool)
    (hh : h < w.length + pre.length)
    (hclean : (projectRun (pre.map promote) w).getD h false = true →
      (rawCircuit w.length (pre ++ suffix) output).eval w = true) :
    (pinAndAppend w.length pre suffix h output).eval w =
      (rawCircuit w.length (pre ++ suffix) output).eval w := by
  rw [pinAndAppend_eval _ _ _ _ _ hh]
  cases hv : (projectRun (pre.map promote) w).getD h false with
  | true => simp [hclean hv]
  | false =>
    simp only [Bool.false_or]
    rw [rawCircuit_split]
    have hc := (cofactorCircuit_correct h suffix output (projectRun (pre.map promote) w)).2.2
    rw [pinnedState_eq_getD _ _ hv] at hc
    have hr := rawCircuit_eval suffix output (projectRun (pre.map promote) w)
    simp only [projectRun_length, List.length_map] at hc hr
    exact hc.trans hr.symm

lemma cofactor_map_bound (n h : Nat) (gs : List Gate) (i : Nat) :
    (cofactor n h gs).2 i < n + 1 + (cofactor n h gs).1.length := by
  exact (compile_correct gs n (n + 1) (initialMap n h)
    (pinnedState n h (fun _ => false)) (zeroState n (fun _ => false))
    (by omega) (by simp [zeroState]) (initialMap_bound n h)
    (initialMap_sound n h (fun _ => false))).1 i

lemma projectCircuit_wireView (n : Nat) (gs : List Gate) (rep : Nat)
    (w : List Bool) (hp : Positive gs) :
    wireView ((projectCircuit n gs rep).wires w) =
      run gs (w.length + 1) (wireView w) := by
  unfold projectCircuit PEqualNP.CircuitLowerBounds.Circuit.wires
  rw [← projectRun_fold, wireView_projectRun _ _ hp]

lemma pinAndAppend_rep_eq_cofactor (pre suffix : List Gate) (h output i : Nat)
    (w : List Bool) (hr : 0 < (cofactor (w.length + pre.length) h suffix).2 i) :
    ((pinAndAppend w.length pre suffix h output).wires w).getD
      ((cofactor (w.length + pre.length) h suffix).2 i - 1) false =
      (cofactorCircuit (w.length + pre.length) h suffix i).eval
        (projectRun (pre.map promote) w) := by
  let cr := cofactor (w.length + pre.length) h suffix
  let sp := run (pre.map promote) (w.length + 1) (wireView w)
  let st := run cr.1 (w.length + pre.length + 1) sp
  have hsp : sp = wireView (projectRun (pre.map promote) w) :=
    (wireView_projectRun _ _ (promote_positive pre)).symm
  have hrep := cofactor_map_bound (w.length + pre.length) h suffix i
  have he : wireView ((pinAndAppend w.length pre suffix h output).wires w) (cr.2 i) =
      st (cr.2 i) := by
    rw [pinAndAppend, projectCircuit_wireView _ _ _ _ (pinGates_positive _ _ _ _ _)]
    simp only [pinGates, run_append, List.length_append, List.length_map, run]
    have hm : w.length + 1 + pre.length = w.length + pre.length + 1 := by omega
    rw [hm, Function.update_of_ne (by dsimp [cr]; omega)]
  have hc : (cofactorCircuit (w.length + pre.length) h suffix i).eval
      (projectRun (pre.map promote) w) = st (cr.2 i) := by
    unfold cofactorCircuit
    have ht := projectCircuit_eval cr.1 (projectRun (pre.map promote) w)
      (cr.2 i) (compile_positive suffix (w.length + pre.length)
        (w.length + pre.length + 1) (initialMap (w.length + pre.length) h))
    simp only [projectRun_length, List.length_map] at ht
    rw [← hsp] at ht
    exact ht
  rw [wireView, if_neg (Nat.ne_of_gt hr)] at he
  exact he.trans hc.symm

lemma cofactor_suffix_zero_row (pre suffix : List Gate) (h i : Nat) (w : List Bool)
    (hz : (projectRun (pre.map promote) w).getD h false = false) :
    (cofactorCircuit (w.length + pre.length) h suffix i).eval
      (projectRun (pre.map promote) w) =
      (rawCircuit w.length (pre ++ suffix) i).eval w := by
  rw [rawCircuit_split]
  have hc := (cofactorCircuit_correct h suffix i (projectRun (pre.map promote) w)).2.2
  rw [pinnedState_eq_getD _ _ hz] at hc
  have hr := rawCircuit_eval suffix i (projectRun (pre.map promote) w)
  simp only [projectRun_length, List.length_map] at hc hr
  exact hc.trans hr.symm

lemma pinAndAppend_retained_wire (pre suffix : List Gate) (h output i : Nat)
    (w : List Bool) (hz : (projectRun (pre.map promote) w).getD h false = false)
    (hr : 0 < (cofactor (w.length + pre.length) h suffix).2 i) :
    ((pinAndAppend w.length pre suffix h output).wires w).getD
      ((cofactor (w.length + pre.length) h suffix).2 i - 1) false =
      (rawCircuit w.length (pre ++ suffix) i).eval w := by
  rw [pinAndAppend_rep_eq_cofactor _ _ _ _ _ _ hr]
  exact cofactor_suffix_zero_row pre suffix h i w hz

lemma pinAndAppend_high_row (pre suffix : List Gate) (h output i : Nat)
    (w : List Bool) (target : Bool)
    (hclean : (projectRun (pre.map promote) w).getD h false = true → target = true)
    (hn : target = false)
    (hr : 0 < (cofactor (w.length + pre.length) h suffix).2 i) :
    ((pinAndAppend w.length pre suffix h output).wires w).getD
      ((cofactor (w.length + pre.length) h suffix).2 i - 1) false =
      (rawCircuit w.length (pre ++ suffix) i).eval w := by
  apply pinAndAppend_retained_wire _ _ _ _ _ _ _ hr
  cases hv : (projectRun (pre.map promote) w).getD h false
  · rfl
  · have := hclean hv
    simp_all

lemma exists_pinAndAppend (n : Nat) (pre suffix : List Gate) (h output : Nat)
    (hh : h < n + pre.length)
    (hclean : ∀ x : Fin n → Bool,
      (projectRun (pre.map promote) (List.ofFn x)).getD h false = true →
        (rawCircuit n (pre ++ suffix) output).eval (List.ofFn x) = true) :
    ∃ D : PCircuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      D.size + suffix.countP (reads h) ≤ (pre ++ suffix).length + 1 ∧
      (D.gates.filter (hasOperation true)).length ≤
        ((pre ++ suffix).filter (fun g => g.1 == true)).length ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        (rawCircuit n (pre ++ suffix) output).eval (List.ofFn x) := by
  refine ⟨pinAndAppend n pre suffix h output, pinAndAppend_mono _ _ _ _ _,
    pinAndAppend_size_savings _ _ _ _ _ hh, pinAndAppend_andCount _ _ _ _ _, ?_⟩
  intro x
  simpa only [List.length_ofFn] using pinAndAppend_correct pre suffix h output
    (List.ofFn x) (by simpa only [List.length_ofFn] using hh)
    (by simpa only [List.length_ofFn] using hclean x)

lemma pinAndAppend_smaller (n : Nat) (pre suffix : List Gate) (h output : Nat)
    (hh : h < n + pre.length) (hr : 2 ≤ suffix.countP (reads h)) :
    (pinAndAppend n pre suffix h output).size < (pre ++ suffix).length := by
  have hs := pinAndAppend_size_savings n pre suffix h output hh
  omega

end CleanWirePinAppend

end PEqualNP.Outside.L_meta_9033_aux
