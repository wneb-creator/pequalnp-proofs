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

namespace CleanWireExactRetention

open CofactorSimplification CofactorProjectBridge CofactorCountBridge
open CofactorWeightedCount CofactorOperationBridge CleanWirePinAppend

def OnlyReaderDrops : List Gate → Nat → Nat → (Nat → Nat) → Nat → Prop
  | [], _, _, _, _ => True
  | g :: gs, k, m, rho, h =>
    (¬ Keep (rho g.2.1) (rho g.2.2) → reads h g = true) ∧
    if Keep (rho g.2.1) (rho g.2.2) then
      OnlyReaderDrops gs (k + 1) (m + 1) (Function.update rho k m) h
    else
      OnlyReaderDrops gs (k + 1) m
        (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2))) h

lemma keep_not_reader (g : Gate) (h : Nat) (rho : Nat → Nat) (hz : rho h = 0)
    (hk : Keep (rho g.2.1) (rho g.2.2)) : reads h g = false := by
  have hn : rho g.2.1 ≠ 0 ∧ rho g.2.2 ≠ 0 ∧ rho g.2.1 ≠ rho g.2.2 := by
    simpa [Keep] using hk
  have ha : g.2.1 ≠ h := by intro he; exact hn.1 (he ▸ hz)
  have hb : g.2.2 ≠ h := by intro he; exact hn.2.1 (he ▸ hz)
  simp [reads, ha, hb]

lemma onlyReaderDrops_of_exact (gs : List Gate) (k m h : Nat) (rho : Nat → Nat)
    (hh : h < k) (hz : rho h = 0)
    (hex : survivors gs k m rho + gs.countP (reads h) = gs.length) :
    OnlyReaderDrops gs k m rho h := by
  induction gs generalizing k m rho with
  | nil => trivial
  | cons g gs ih =>
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · have hr := keep_not_reader g h rho hz hk
      have hz' : Function.update rho k m h = 0 := by
        simpa [Function.update_of_ne (Nat.ne_of_lt hh)] using hz
      simp only [survivors, hk, ite_true, List.countP_cons, hr,
        Bool.false_eq_true, ite_false, List.length_cons] at hex
      refine ⟨by simp [hk], ?_⟩
      simp only [hk, ite_true]
      exact ih (k + 1) (m + 1) (Function.update rho k m) (by omega) hz' (by omega)
    · let r := replacement g.1 (rho g.2.1) (rho g.2.2)
      have hz' : Function.update rho k r h = 0 := by
        simpa [Function.update_of_ne (Nat.ne_of_lt hh)] using hz
      have hs := survivors_reader_savings gs (k + 1) m h (Function.update rho k r)
        (by omega) hz'
      have hr : reads h g = true := by
        cases hg : reads h g
        · simp only [survivors, hk, Bool.false_eq_true, ite_false, List.countP_cons,
            hg, List.length_cons] at hex
          dsimp [r] at hs
          omega
        · rfl
      simp only [survivors, hk, Bool.false_eq_true, ite_false, List.countP_cons,
        hr, ite_true, List.length_cons] at hex
      refine ⟨fun _ => hr, ?_⟩
      simp only [hk, Bool.false_eq_true, ite_false]
      exact ih (k + 1) m (Function.update rho k r) (by omega) hz' (by dsimp [r]; omega)

lemma minimal_single_reader_exact (n : Nat) (pre suffix : List Gate) (h output : Nat)
    (hh : h < n + pre.length) (hr : suffix.countP (reads h) = 1)
    (hmin : (pre ++ suffix).length ≤ (pinAndAppend n pre suffix h output).size) :
    survivors suffix (n + pre.length) (n + pre.length + 1)
        (initialMap (n + pre.length) h) + suffix.countP (reads h) = suffix.length := by
  have hs := pinAndAppend_size_savings n pre suffix h output hh
  rw [pinAndAppend_size, List.length_append] at hmin hs
  have hc := compile_length suffix (n + pre.length) (n + pre.length + 1)
    (initialMap (n + pre.length) h)
  change (cofactor (n + pre.length) h suffix).1.length = _ at hc
  omega

lemma minimal_single_reader_only_drops (n : Nat) (pre suffix : List Gate) (h output : Nat)
    (hh : h < n + pre.length) (hr : suffix.countP (reads h) = 1)
    (hmin : (pre ++ suffix).length ≤ (pinAndAppend n pre suffix h output).size) :
    OnlyReaderDrops suffix (n + pre.length) (n + pre.length + 1)
      (initialMap (n + pre.length) h) h := by
  exact onlyReaderDrops_of_exact suffix _ _ h _ hh (by simp [initialMap, hh])
    (minimal_single_reader_exact n pre suffix h output hh hr hmin)

def AndsKept : List Gate → Nat → Nat → (Nat → Nat) → Prop
  | [], _, _, _ => True
  | g :: gs, k, m, rho =>
    (g.1 = true → Keep (rho g.2.1) (rho g.2.2)) ∧
    if Keep (rho g.2.1) (rho g.2.2) then
      AndsKept gs (k + 1) (m + 1) (Function.update rho k m)
    else
      AndsKept gs (k + 1) m
        (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2)))

lemma andsKept_of_onlyReaderDrops (gs : List Gate) (k m h : Nat) (rho : Nat → Nat)
    (hd : OnlyReaderDrops gs k m rho h)
    (hor : ∀ g ∈ gs, reads h g = true → g.1 = false) : AndsKept gs k m rho := by
  induction gs generalizing k m rho with
  | nil => trivial
  | cons g gs ih =>
    obtain ⟨hhead, htail⟩ := hd
    refine ⟨?_, ?_⟩
    · intro hg
      by_contra hk
      have := hor g List.mem_cons_self (hhead hk)
      simp_all
    · have ht : ∀ g ∈ gs, reads h g = true → g.1 = false :=
        fun z hz => hor z (List.mem_cons_of_mem g hz)
      by_cases hk : Keep (rho g.2.1) (rho g.2.2)
      · simp only [hk, ite_true] at htail ⊢
        exact ih _ _ _ htail ht
      · simp only [hk, Bool.false_eq_true, ite_false] at htail ⊢
        exact ih _ _ _ htail ht

lemma compile_andCount_eq (gs : List Gate) (k m : Nat) (rho : Nat → Nat)
    (ha : AndsKept gs k m rho) :
    weightedCount (fun op => if op then 1 else 0) (compile gs k m rho).1 =
      weightedCount (fun op => if op then 1 else 0) gs := by
  induction gs generalizing k m rho with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨hhead, htail⟩ := ha
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · simp only [hk, ite_true] at htail
      simp only [compile, hk, ite_true, weightedCount, mapped]
      rw [ih _ _ _ htail]
    · have hg : g.1 = false := by
        cases hop : g.1
        · rfl
        · exact False.elim (hk (hhead hop))
      simp only [hk, Bool.false_eq_true, ite_false] at htail
      simp only [compile, hk, Bool.false_eq_true, ite_false, weightedCount, hg,
        Nat.zero_add]
      simpa only [hg] using ih _ _ _ htail

lemma minimal_single_or_reader_andsKept (n : Nat) (pre suffix : List Gate) (h output : Nat)
    (hh : h < n + pre.length) (hr : suffix.countP (reads h) = 1)
    (hmin : (pre ++ suffix).length ≤ (pinAndAppend n pre suffix h output).size)
    (hor : ∀ g ∈ suffix, reads h g = true → g.1 = false) :
    AndsKept suffix (n + pre.length) (n + pre.length + 1)
      (initialMap (n + pre.length) h) := by
  exact andsKept_of_onlyReaderDrops suffix _ _ h _
    (minimal_single_reader_only_drops n pre suffix h output hh hr hmin) hor

lemma minimal_single_reader_size (n : Nat) (pre suffix : List Gate) (h output : Nat)
    (hh : h < n + pre.length) (hr : suffix.countP (reads h) = 1)
    (hmin : (pre ++ suffix).length ≤ (pinAndAppend n pre suffix h output).size) :
    (pinAndAppend n pre suffix h output).size = (pre ++ suffix).length := by
  have hs := pinAndAppend_size_savings n pre suffix h output hh
  omega

lemma minimal_single_or_reader_andCount (n : Nat) (pre suffix : List Gate) (h output : Nat)
    (hh : h < n + pre.length) (hr : suffix.countP (reads h) = 1)
    (hmin : (pre ++ suffix).length ≤ (pinAndAppend n pre suffix h output).size)
    (hor : ∀ g ∈ suffix, reads h g = true → g.1 = false) :
    ((pinAndAppend n pre suffix h output).gates.filter (hasOperation true)).length =
      ((pre ++ suffix).filter (fun g => g.1 == true)).length := by
  have ha := minimal_single_or_reader_andsKept n pre suffix h output hh hr hmin hor
  rw [pinAndAppend, projectCircuit_opCount, ← weightedCount_eq_filter,
    ← weightedCount_eq_filter]
  simp only [pinGates, weightedCount_append, weightedCount_promote, weightedCount,
    appendGate, Bool.false_eq_true, ite_false, Nat.add_zero]
  exact congrArg (fun a => weightedCount (fun op => if op = true then 1 else 0) pre + a)
    (compile_andCount_eq suffix _ _ _ ha)

lemma rawCircuit_andCount (n : Nat) (gs : List Gate) (output : Nat) :
    ((rawCircuit n gs output).gates.filter (hasOperation true)).length =
      (gs.filter (fun g => g.1 == true)).length := by
  rw [rawCircuit, projectCircuit_opCount, ← weightedCount_eq_filter,
    weightedCount_promote, weightedCount_eq_filter]

def andOutputs : List Gate → Nat → List Nat
  | [], _ => []
  | g :: gs, k => if g.1 then k :: andOutputs gs (k + 1) else andOutputs gs (k + 1)

lemma andOutputs_append (gs hs : List Gate) (k : Nat) :
    andOutputs (gs ++ hs) k = andOutputs gs k ++ andOutputs hs (k + gs.length) := by
  induction gs generalizing k with
  | nil => simp [andOutputs]
  | cons g gs ih =>
    cases hop : g.1 <;>
      simp [andOutputs, hop, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma andOutputs_bounds (gs : List Gate) (k i : Nat) (hi : i ∈ andOutputs gs k) :
    k ≤ i ∧ i < k + gs.length := by
  induction gs generalizing k with
  | nil => simp [andOutputs] at hi
  | cons g gs ih =>
    cases hop : g.1
    · simp only [andOutputs, hop, Bool.false_eq_true, ite_false] at hi
      have hb := ih (k + 1) hi
      simp only [List.length_cons]
      omega
    · simp only [andOutputs, hop, ite_true, List.mem_cons] at hi
      rcases hi with rfl | hi
      · simp
      · have hb := ih (k + 1) hi
        simp only [List.length_cons]
        omega

end CleanWireExactRetention

namespace CompileEmissionTrace

open CofactorSimplification

def emissions : List Gate → Nat → Nat → (Nat → Nat) → List (Bool × Nat × Nat)
  | [], _, _, _ => []
  | g :: gs, k, m, rho =>
    if Keep (rho g.2.1) (rho g.2.2) then
      (g.1, k, m) :: emissions gs (k + 1) (m + 1) (Function.update rho k m)
    else
      emissions gs (k + 1) m
        (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2)))

lemma compile_map_below (gs : List Gate) (k m : Nat) (rho : Nat → Nat)
    (i : Nat) (hi : i < k) : (compile gs k m rho).2 i = rho i := by
  induction gs generalizing k m rho with
  | nil => rfl
  | cons g gs ih =>
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · simp only [compile, hk, ite_true]
      rw [ih (k + 1) (m + 1) (Function.update rho k m) (by omega)]
      exact Function.update_of_ne (Nat.ne_of_lt hi) _ _
    · simp only [compile, hk, Bool.false_eq_true, ite_false]
      rw [ih (k + 1) m
        (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2))) (by omega)]
      exact Function.update_of_ne (Nat.ne_of_lt hi) _ _

lemma emission_bounds (gs : List Gate) (k m : Nat) (rho : Nat → Nat)
    (e : Bool × Nat × Nat) (he : e ∈ emissions gs k m rho) :
    k ≤ e.2.1 ∧ m ≤ e.2.2 := by
  induction gs generalizing k m rho with
  | nil => simp [emissions] at he
  | cons g gs ih =>
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · simp only [emissions, hk, ite_true, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨le_rfl, le_rfl⟩
      · have hh := ih (k + 1) (m + 1) (Function.update rho k m) he
        exact ⟨by omega, by omega⟩
    · simp only [emissions, hk, Bool.false_eq_true, ite_false] at he
      have hh := ih (k + 1) m
        (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2))) he
      exact ⟨by omega, hh.2⟩

lemma emission_final_map (gs : List Gate) (k m : Nat) (rho : Nat → Nat)
    (e : Bool × Nat × Nat) (he : e ∈ emissions gs k m rho) :
    (compile gs k m rho).2 e.2.1 = e.2.2 := by
  induction gs generalizing k m rho with
  | nil => simp [emissions] at he
  | cons g gs ih =>
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · simp only [emissions, hk, ite_true, List.mem_cons] at he
      simp only [compile, hk, ite_true]
      rcases he with rfl | he
      · rw [compile_map_below gs (k + 1) (m + 1) (Function.update rho k m) k (by omega)]
        simp
      · exact ih (k + 1) (m + 1) (Function.update rho k m) he
    · simp only [emissions, hk, Bool.false_eq_true, ite_false] at he
      simp only [compile, hk, Bool.false_eq_true, ite_false]
      exact ih (k + 1) m
        (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2))) he

lemma emission_new_injective (gs : List Gate) (k m : Nat) (rho : Nat → Nat)
    (e f : Bool × Nat × Nat) (he : e ∈ emissions gs k m rho)
    (hf : f ∈ emissions gs k m rho) (h : e.2.2 = f.2.2) : e.2.1 = f.2.1 := by
  induction gs generalizing k m rho with
  | nil => simp [emissions] at he
  | cons g gs ih =>
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · simp only [emissions, hk, ite_true, List.mem_cons] at he hf
      rcases he with rfl | he <;> rcases hf with rfl | hf
      · rfl
      · have hb := (emission_bounds gs (k + 1) (m + 1) (Function.update rho k m) f hf).2
        simp only at h
        omega
      · have hb := (emission_bounds gs (k + 1) (m + 1) (Function.update rho k m) e he).2
        simp only at h
        omega
      · exact ih (k + 1) (m + 1) (Function.update rho k m) he hf
    · simp only [emissions, hk, Bool.false_eq_true, ite_false] at he hf
      exact ih (k + 1) m
        (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2))) he hf

lemma emission_compiled_lookup (gs : List Gate) (k m : Nat) (rho : Nat → Nat)
    (e : Bool × Nat × Nat) (he : e ∈ emissions gs k m rho) :
    ∃ g, (compile gs k m rho).1[e.2.2 - m]? = some g ∧ g.1 = e.1 := by
  induction gs generalizing k m rho with
  | nil => simp [emissions] at he
  | cons g gs ih =>
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · simp only [emissions, hk, ite_true, List.mem_cons] at he
      simp only [compile, hk, ite_true]
      rcases he with rfl | he
      · exact ⟨mapped rho g, by simp, rfl⟩
      · obtain ⟨g', hg', hop⟩ := ih (k + 1) (m + 1) (Function.update rho k m) he
        have hb := (emission_bounds gs (k + 1) (m + 1) (Function.update rho k m) e he).2
        have hoff : e.2.2 - m = (e.2.2 - (m + 1)) + 1 := by omega
        refine ⟨g', ?_, hop⟩
        simpa [hoff] using hg'
    · simp only [emissions, hk, Bool.false_eq_true, ite_false] at he
      simpa only [compile, hk, Bool.false_eq_true, ite_false] using ih (k + 1) m
        (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2))) he

lemma emissions_operations (gs : List Gate) (k m : Nat) (rho : Nat → Nat) :
    (emissions gs k m rho).map Prod.fst = (compile gs k m rho).1.map Prod.fst := by
  induction gs generalizing k m rho with
  | nil => rfl
  | cons g gs ih =>
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · simp [emissions, compile, mapped, hk, ih]
    · simp [emissions, compile, hk, ih]

end CompileEmissionTrace

namespace CleanWireDirtyRetention

open CofactorSimplification CofactorProjectBridge CofactorCountBridge
open CofactorWeightedCount CofactorOperationBridge CleanWirePinAppend CleanWireExactRetention
open CompileEmissionTrace

lemma rawCircuit_pre_wire (pre suffix : List Gate) (w : List Bool) (i : Nat)
    (hi : i < w.length + pre.length) :
    (rawCircuit w.length (pre ++ suffix) i).eval w =
      (projectRun (pre.map promote) w).getD i false := by
  rw [rawCircuit_split]
  have hr := rawCircuit_eval suffix i (projectRun (pre.map promote) w)
  simp only [projectRun_length, List.length_map] at hr
  rw [hr, run_below _ _ _ _ hi]

lemma dirty_wire_ne_clean (pre suffix : List Gate) (h i : Nat) (w : List Bool)
    (target : Bool) (hh : h < w.length + pre.length)
    (hclean : (projectRun (pre.map promote) w).getD h false = true → target = true)
    (hn : target = false) (hd : (rawCircuit w.length (pre ++ suffix) i).eval w = true) :
    i ≠ h := by
  intro he
  subst i
  rw [rawCircuit_pre_wire _ _ _ _ hh] at hd
  have := hclean hd
  simp_all

lemma andOutputs_promote (gs : List Gate) (k : Nat) :
    andOutputs (gs.map promote) (k + 1) = (andOutputs gs k).map (fun i => i + 1) := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih =>
    cases hop : g.1 <;> simp [andOutputs, promote, hop, ih]

lemma pinGates_andOutputs (n : Nat) (pre suffix : List Gate) (h output : Nat) :
    andOutputs (pinGates n pre suffix h output) (n + 1) =
      (andOutputs pre n).map (fun i => i + 1) ++
        andOutputs (cofactor (n + pre.length) h suffix).1 (n + pre.length + 1) := by
  simp only [pinGates, andOutputs_append, List.length_append, List.length_map,
    andOutputs_promote, andOutputs, appendGate, Bool.false_eq_true, ite_false,
    List.append_nil]
  congr 2
  omega

lemma andsKept_emitted (gs : List Gate) (k m : Nat) (rho : Nat → Nat)
    (ha : AndsKept gs k m rho) (i : Nat) (hi : i ∈ andOutputs gs k) :
    ∃ r, (true, i, r) ∈ emissions gs k m rho := by
  induction gs generalizing k m rho with
  | nil => simp [andOutputs] at hi
  | cons g gs ih =>
    obtain ⟨hhead, htail⟩ := ha
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · simp only [hk, ite_true] at htail
      simp only [emissions, hk, ite_true]
      cases hop : g.1
      · simp only [andOutputs, hop, Bool.false_eq_true, ite_false] at hi
        obtain ⟨r, hr⟩ := ih (k + 1) (m + 1) (Function.update rho k m) htail hi
        exact ⟨r, List.mem_cons_of_mem _ hr⟩
      · simp only [andOutputs, hop, ite_true, List.mem_cons] at hi
        rcases hi with rfl | hi
        · exact ⟨m, by simp [hop]⟩
        · obtain ⟨r, hr⟩ := ih (k + 1) (m + 1) (Function.update rho k m) htail hi
          exact ⟨r, List.mem_cons_of_mem _ hr⟩
    · have hop : g.1 = false := by
        cases hg : g.1
        · rfl
        · exact False.elim (hk (hhead hg))
      simp only [hk, Bool.false_eq_true, ite_false] at htail
      simp only [andOutputs, hop, Bool.false_eq_true, ite_false] at hi
      simpa only [emissions, hk, Bool.false_eq_true, ite_false] using
        ih (k + 1) m (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2)))
          htail hi

lemma emission_andOutput (gs : List Gate) (k m : Nat) (rho : Nat → Nat)
    (e : Bool × Nat × Nat) (he : e ∈ emissions gs k m rho) (hop : e.1 = true) :
    e.2.2 ∈ andOutputs (compile gs k m rho).1 m := by
  induction gs generalizing k m rho with
  | nil => simp [emissions] at he
  | cons g gs ih =>
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · simp only [emissions, hk, ite_true, List.mem_cons] at he
      simp only [compile, hk, ite_true, andOutputs, mapped]
      rcases he with rfl | he
      · simp only at hop
        simp [hop]
      · have hh := ih (k + 1) (m + 1) (Function.update rho k m) he
        split_ifs
        · exact List.mem_cons_of_mem _ hh
        · exact hh
    · simp only [emissions, hk, Bool.false_eq_true, ite_false] at he
      simp only [compile, hk, Bool.false_eq_true, ite_false]
      exact ih (k + 1) m
        (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2))) he

lemma and_rep_member (gs : List Gate) (k m : Nat) (rho : Nat → Nat)
    (ha : AndsKept gs k m rho) (i : Nat) (hi : i ∈ andOutputs gs k) :
    (compile gs k m rho).2 i ∈ andOutputs (compile gs k m rho).1 m ∧
      m ≤ (compile gs k m rho).2 i := by
  obtain ⟨r, hr⟩ := andsKept_emitted gs k m rho ha i hi
  have hf := emission_final_map gs k m rho (true, i, r) hr
  simp only at hf
  rw [hf]
  exact ⟨emission_andOutput gs k m rho (true, i, r) hr rfl,
    (emission_bounds gs k m rho (true, i, r) hr).2⟩

lemma and_rep_injective (gs : List Gate) (k m : Nat) (rho : Nat → Nat)
    (ha : AndsKept gs k m rho) (i j : Nat)
    (hi : i ∈ andOutputs gs k) (hj : j ∈ andOutputs gs k)
    (heq : (compile gs k m rho).2 i = (compile gs k m rho).2 j) : i = j := by
  obtain ⟨r, hr⟩ := andsKept_emitted gs k m rho ha i hi
  obtain ⟨s, hs⟩ := andsKept_emitted gs k m rho ha j hj
  have hir := emission_final_map gs k m rho (true, i, r) hr
  have hjs := emission_final_map gs k m rho (true, j, s) hs
  apply emission_new_injective gs k m rho (true, i, r) (true, j, s) hr hs
  exact hir.symm.trans (heq.trans hjs)

lemma cofactor_prefix_rep (n h : Nat) (gs : List Gate) (i : Nat)
    (hi : i < n) (hne : i ≠ h) : (cofactor n h gs).2 i = i + 1 := by
  unfold cofactor
  rw [compile_map_below _ _ _ _ _ hi]
  simp [initialMap, hi, hne]

lemma full_and_rep_member (n : Nat) (pre suffix : List Gate) (h output i : Nat)
    (ha : AndsKept suffix (n + pre.length) (n + pre.length + 1)
      (initialMap (n + pre.length) h))
    (hi : i ∈ andOutputs (pre ++ suffix) n) (hne : i ≠ h) :
    (cofactor (n + pre.length) h suffix).2 i ∈
      andOutputs (pinGates n pre suffix h output) (n + 1) ∧
      0 < (cofactor (n + pre.length) h suffix).2 i := by
  rw [andOutputs_append, List.mem_append] at hi
  rw [pinGates_andOutputs]
  rcases hi with hi | hi
  · have hb := andOutputs_bounds pre n i hi
    rw [cofactor_prefix_rep _ _ _ _ hb.2 hne]
    exact ⟨List.mem_append_left _ (List.mem_map.mpr ⟨i, hi, rfl⟩), by omega⟩
  · have hr := and_rep_member suffix (n + pre.length) (n + pre.length + 1)
      (initialMap (n + pre.length) h) ha i hi
    exact ⟨List.mem_append_right _ hr.1, lt_of_lt_of_le (by omega) hr.2⟩

lemma full_and_rep_injective (n : Nat) (pre suffix : List Gate) (h i j : Nat)
    (ha : AndsKept suffix (n + pre.length) (n + pre.length + 1)
      (initialMap (n + pre.length) h))
    (hi : i ∈ andOutputs (pre ++ suffix) n) (hj : j ∈ andOutputs (pre ++ suffix) n)
    (hne : i ≠ h) (hne' : j ≠ h)
    (heq : (cofactor (n + pre.length) h suffix).2 i =
      (cofactor (n + pre.length) h suffix).2 j) : i = j := by
  rw [andOutputs_append, List.mem_append] at hi hj
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · have hib := andOutputs_bounds pre n i hi
    have hjb := andOutputs_bounds pre n j hj
    rw [cofactor_prefix_rep _ _ _ _ hib.2 hne,
      cofactor_prefix_rep _ _ _ _ hjb.2 hne'] at heq
    omega
  · have hib := andOutputs_bounds pre n i hi
    have hjb := (and_rep_member suffix (n + pre.length) (n + pre.length + 1)
      (initialMap (n + pre.length) h) ha j hj).2
    rw [cofactor_prefix_rep _ _ _ _ hib.2 hne] at heq
    change n + pre.length + 1 ≤ (cofactor (n + pre.length) h suffix).2 j at hjb
    omega
  · have hjb := andOutputs_bounds pre n j hj
    have hib := (and_rep_member suffix (n + pre.length) (n + pre.length + 1)
      (initialMap (n + pre.length) h) ha i hi).2
    rw [cofactor_prefix_rep _ _ _ _ hjb.2 hne'] at heq
    change n + pre.length + 1 ≤ (cofactor (n + pre.length) h suffix).2 i at hib
    omega
  · exact and_rep_injective suffix _ _ _ ha i j hi hj heq

def OriginalDirty (n : Nat) (pre suffix : List Gate) (rows : Fin 40 → Fin n → Bool)
    (target : Fin 40 → Bool) (P : Fin 40 → Prop) (i : Nat) : Prop :=
  i ∈ andOutputs (pre ++ suffix) n ∧ ∃ r, P r ∧ target r = false ∧
    (rawCircuit n (pre ++ suffix) i).eval (List.ofFn (rows r)) = true

def CompiledDirty (n : Nat) (pre suffix : List Gate) (h output : Nat)
    (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool) (P : Fin 40 → Prop)
    (rep : Nat) : Prop :=
  rep ∈ andOutputs (pinGates n pre suffix h output) (n + 1) ∧
    ∃ r, P r ∧ target r = false ∧
      ((pinAndAppend n pre suffix h output).wires (List.ofFn (rows r))).getD
        (rep - 1) false = true

lemma originalDirty_ne_clean (n : Nat) (pre suffix : List Gate) (h i : Nat)
    (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool) (P : Fin 40 → Prop)
    (hh : h < n + pre.length)
    (hclean : ∀ r, (projectRun (pre.map promote) (List.ofFn (rows r))).getD h false = true →
      target r = true) (hd : OriginalDirty n pre suffix rows target P i) : i ≠ h := by
  obtain ⟨_, r, _, hn, hv⟩ := hd
  exact dirty_wire_ne_clean pre suffix h i (List.ofFn (rows r)) (target r)
    (by simpa only [List.length_ofFn] using hh) (hclean r) hn
    (by simpa only [List.length_ofFn] using hv)

lemma dirty_rep_preserved (n : Nat) (pre suffix : List Gate) (h output i : Nat)
    (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool) (P : Fin 40 → Prop)
    (hh : h < n + pre.length)
    (hclean : ∀ r, (projectRun (pre.map promote) (List.ofFn (rows r))).getD h false = true →
      target r = true)
    (ha : AndsKept suffix (n + pre.length) (n + pre.length + 1)
      (initialMap (n + pre.length) h))
    (hd : OriginalDirty n pre suffix rows target P i) :
    CompiledDirty n pre suffix h output rows target P
      ((cofactor (n + pre.length) h suffix).2 i) := by
  have hne := originalDirty_ne_clean n pre suffix h i rows target P hh hclean hd
  have hm := full_and_rep_member n pre suffix h output i ha hd.1 hne
  obtain ⟨_, r, hp, hn, hv⟩ := hd
  refine ⟨hm.1, r, hp, hn, ?_⟩
  have hc := pinAndAppend_high_row pre suffix h output i (List.ofFn (rows r))
    (target r) (hclean r) hn (by simpa only [List.length_ofFn] using hm.2)
  simp only [List.length_ofFn] at hc
  exact hc.trans hv

lemma two_dirty_reps_preserved (n : Nat) (pre suffix : List Gate) (h output i j : Nat)
    (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool) (P : Fin 40 → Prop)
    (hh : h < n + pre.length)
    (hclean : ∀ r, (projectRun (pre.map promote) (List.ofFn (rows r))).getD h false = true →
      target r = true)
    (ha : AndsKept suffix (n + pre.length) (n + pre.length + 1)
      (initialMap (n + pre.length) h))
    (hdi : OriginalDirty n pre suffix rows target P i)
    (hdj : OriginalDirty n pre suffix rows target P j) (hne : i ≠ j) :
    ∃ r s, r ≠ s ∧ CompiledDirty n pre suffix h output rows target P r ∧
      CompiledDirty n pre suffix h output rows target P s := by
  refine ⟨(cofactor (n + pre.length) h suffix).2 i,
    (cofactor (n + pre.length) h suffix).2 j, ?_,
    dirty_rep_preserved n pre suffix h output i rows target P hh hclean ha hdi,
    dirty_rep_preserved n pre suffix h output j rows target P hh hclean ha hdj⟩
  intro he
  apply hne
  exact full_and_rep_injective n pre suffix h i j ha hdi.1 hdj.1
    (originalDirty_ne_clean n pre suffix h i rows target P hh hclean hdi)
    (originalDirty_ne_clean n pre suffix h j rows target P hh hclean hdj) he

lemma minimal_single_or_reader_two_dirty (n : Nat) (pre suffix : List Gate)
    (h output i j : Nat) (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool)
    (P : Fin 40 → Prop) (hh : h < n + pre.length)
    (hr : suffix.countP (reads h) = 1)
    (hmin : (pre ++ suffix).length ≤ (pinAndAppend n pre suffix h output).size)
    (hor : ∀ g ∈ suffix, reads h g = true → g.1 = false)
    (hclean : ∀ r, (projectRun (pre.map promote) (List.ofFn (rows r))).getD h false = true →
      target r = true)
    (hdi : OriginalDirty n pre suffix rows target P i)
    (hdj : OriginalDirty n pre suffix rows target P j) (hne : i ≠ j) :
    (pinAndAppend n pre suffix h output).size = (pre ++ suffix).length ∧
    ((pinAndAppend n pre suffix h output).gates.filter (hasOperation true)).length =
      ((pre ++ suffix).filter (fun g => g.1 == true)).length ∧
    ∃ r s, r ≠ s ∧ CompiledDirty n pre suffix h output rows target P r ∧
      CompiledDirty n pre suffix h output rows target P s := by
  refine ⟨minimal_single_reader_size n pre suffix h output hh hr hmin,
    minimal_single_or_reader_andCount n pre suffix h output hh hr hmin hor, ?_⟩
  exact two_dirty_reps_preserved n pre suffix h output i j rows target P hh hclean
    (minimal_single_or_reader_andsKept n pre suffix h output hh hr hmin hor) hdi hdj hne

lemma andOutputs_lookup (gs : List Gate) (k i : Nat) (hi : i ∈ andOutputs gs k) :
    ∃ g, gs[i - k]? = some g ∧ g.1 = true := by
  induction gs generalizing k with
  | nil => simp [andOutputs] at hi
  | cons g gs ih =>
    cases hop : g.1
    · simp only [andOutputs, hop, Bool.false_eq_true, ite_false] at hi
      have hb := (andOutputs_bounds gs (k + 1) i hi).1
      have hoff : i - k = (i - (k + 1)) + 1 := by omega
      obtain ⟨z, hz, hzop⟩ := ih (k + 1) hi
      exact ⟨z, by simpa [hoff] using hz, hzop⟩
    · simp only [andOutputs, hop, ite_true, List.mem_cons] at hi
      rcases hi with rfl | hi
      · exact ⟨g, by simp, hop⟩
      · have hb := (andOutputs_bounds gs (k + 1) i hi).1
        have hoff : i - k = (i - (k + 1)) + 1 := by omega
        obtain ⟨z, hz, hzop⟩ := ih (k + 1) hi
        exact ⟨z, by simpa [hoff] using hz, hzop⟩

lemma andOutputs_project_gate (n : Nat) (gs : List Gate) (output rep : Nat)
    (hr : rep ∈ andOutputs gs (n + 1)) :
    n ≤ rep - 1 ∧ ∃ g : PGate,
      (projectCircuit n gs output).gates[rep - 1 - n]? = some g ∧ g.op = .and := by
  have hb := (andOutputs_bounds gs (n + 1) rep hr).1
  obtain ⟨g, hg, hop⟩ := andOutputs_lookup gs (n + 1) rep hr
  refine ⟨by omega, projectGate g, ?_, ?_⟩
  · change (gs.map projectGate)[rep - 1 - n]? = _
    have hoff : rep - 1 - n = rep - (n + 1) := by omega
    simp [hoff, hg]
  · simp [projectGate, hop]

def PhysicalDirty (n : Nat) (D : PCircuit) (rows : Fin 40 → Fin n → Bool)
    (target : Fin 40 → Bool) (P : Fin 40 → Prop) (wire : Nat) : Prop :=
  n ≤ wire ∧ (∃ g : PGate, D.gates[wire - n]? = some g ∧ g.op = .and) ∧
    ∃ r, P r ∧ target r = false ∧ (D.wires (List.ofFn (rows r))).getD wire false = true

lemma compiledDirty_physical (n : Nat) (pre suffix : List Gate) (h output rep : Nat)
    (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool) (P : Fin 40 → Prop)
    (hd : CompiledDirty n pre suffix h output rows target P rep) :
    PhysicalDirty n (pinAndAppend n pre suffix h output) rows target P (rep - 1) := by
  have hg := andOutputs_project_gate n (pinGates n pre suffix h output)
    (n + pre.length + (cofactor (n + pre.length) h suffix).1.length + 1) rep hd.1
  exact ⟨hg.1, hg.2, hd.2⟩

lemma minimal_single_or_reader_two_physical_dirty (n : Nat) (pre suffix : List Gate)
    (h output i j : Nat) (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool)
    (P : Fin 40 → Prop) (hh : h < n + pre.length)
    (hr : suffix.countP (reads h) = 1)
    (hmin : (pre ++ suffix).length ≤ (pinAndAppend n pre suffix h output).size)
    (hor : ∀ g ∈ suffix, reads h g = true → g.1 = false)
    (hclean : ∀ r, (projectRun (pre.map promote) (List.ofFn (rows r))).getD h false = true →
      target r = true)
    (hdi : OriginalDirty n pre suffix rows target P i)
    (hdj : OriginalDirty n pre suffix rows target P j) (hne : i ≠ j) :
    (pinAndAppend n pre suffix h output).size = (pre ++ suffix).length ∧
    ((pinAndAppend n pre suffix h output).gates.filter (hasOperation true)).length =
      ((pre ++ suffix).filter (fun g => g.1 == true)).length ∧
    ∃ u v, u ≠ v ∧ PhysicalDirty n (pinAndAppend n pre suffix h output) rows target P u ∧
      PhysicalDirty n (pinAndAppend n pre suffix h output) rows target P v := by
  obtain ⟨hs, ha, r, s, hrs, hdr, hds⟩ :=
    minimal_single_or_reader_two_dirty n pre suffix h output i j rows target P
      hh hr hmin hor hclean hdi hdj hne
  refine ⟨hs, ha, r - 1, s - 1, ?_,
    compiledDirty_physical n pre suffix h output r rows target P hdr,
    compiledDirty_physical n pre suffix h output s rows target P hds⟩
  have hrb := (andOutputs_bounds (pinGates n pre suffix h output) (n + 1) r hdr.1).1
  have hsb := (andOutputs_bounds (pinGates n pre suffix h output) (n + 1) s hds.1).1
  omega

end CleanWireDirtyRetention

namespace CleanWireCrossings

open CofactorSimplification CofactorProjectBridge CleanWirePinAppend CleanWireExactRetention

abbrev TableState := Nat → Fin 40 → Bool

def NegMapped (target : Fin 40 → Bool) (s t : TableState) (rho : Nat → Nat) : Prop :=
  ∀ i r, target r = false → s i r = t (rho i) r

noncomputable def crossings (target : Fin 40 → Bool) (s : TableState) (g : Gate) : Nat := by
  classical
  exact if Normalization.Clean target (Normalization.gate g s) then 0 else
    (if Normalization.Clean target (s g.2.1) then 1 else 0) +
    (if Normalization.Clean target (s g.2.2) then 1 else 0)

noncomputable def crossCount (target : Fin 40 → Bool) : List Gate → Nat → TableState → Nat
  | [], _, _ => 0
  | g :: gs, k, s => crossings target s g +
      crossCount target gs (k + 1) (Function.update s k (Normalization.gate g s))

noncomputable def droppedCrossCount (target : Fin 40 → Bool) :
    List Gate → Nat → Nat → (Nat → Nat) → TableState → Nat
  | [], _, _, _, _ => 0
  | g :: gs, k, m, rho, s =>
    if Keep (rho g.2.1) (rho g.2.2) then
      droppedCrossCount target gs (k + 1) (m + 1) (Function.update rho k m)
        (Function.update s k (Normalization.gate g s))
    else crossings target s g +
      droppedCrossCount target gs (k + 1) m
        (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2)))
        (Function.update s k (Normalization.gate g s))

lemma clean_congr_neg (target a b : Fin 40 → Bool)
    (h : ∀ r, target r = false → a r = b r) :
    Normalization.Clean target a ↔ Normalization.Clean target b := by
  constructor
  · intro ha r hr
    rw [← h r hr]
    exact ha r hr
  · intro hb r hr
    rw [h r hr]
    exact hb r hr

lemma mapped_gate_neg (target : Fin 40 → Bool) (s t : TableState) (rho : Nat → Nat)
    (h : NegMapped target s t rho) (g : Gate) (r : Fin 40) (hr : target r = false) :
    Normalization.gate g s r = Normalization.gate (mapped rho g) t r := by
  exact mapped_sound rho g (fun i => s i r) (fun i => t i r) (fun i => h i r hr)

lemma crossings_mapped (target : Fin 40 → Bool) (s t : TableState) (rho : Nat → Nat)
    (h : NegMapped target s t rho) (g : Gate) :
    crossings target s g = crossings target t (mapped rho g) := by
  classical
  have hg := clean_congr_neg target (Normalization.gate g s)
    (Normalization.gate (mapped rho g) t) (mapped_gate_neg target s t rho h g)
  have ha := clean_congr_neg target (s g.2.1) (t (rho g.2.1)) (h g.2.1)
  have hb := clean_congr_neg target (s g.2.2) (t (rho g.2.2)) (h g.2.2)
  simp only [crossings, mapped, hg, ha, hb]
  rfl

lemma negMapped_fresh (target : Fin 40 → Bool) (s t : TableState) (rho : Nat → Nat)
    (k m : Nat) (g : Gate) (h : NegMapped target s t rho) (hb : ∀ i, rho i < m) :
    NegMapped target (Function.update s k (Normalization.gate g s))
      (Function.update t m (Normalization.gate (mapped rho g) t))
      (Function.update rho k m) := by
  intro i r hr
  by_cases hi : i = k
  · subst i
    simp only [Function.update_self]
    exact mapped_gate_neg target s t rho h g r hr
  · simp only [Function.update_of_ne hi,
      Function.update_of_ne (Nat.ne_of_lt (hb i))]
    exact h i r hr

lemma negMapped_drop (target : Fin 40 → Bool) (s t : TableState) (rho : Nat → Nat)
    (k : Nat) (g : Gate) (h : NegMapped target s t rho)
    (hz : ∀ r, target r = false → t 0 r = false)
    (hk : ¬ Keep (rho g.2.1) (rho g.2.2)) :
    NegMapped target (Function.update s k (Normalization.gate g s)) t
      (Function.update rho k (replacement g.1 (rho g.2.1) (rho g.2.2))) := by
  intro i r hr
  by_cases hi : i = k
  · subst i
    simp only [Function.update_self]
    rw [mapped_gate_neg target s t rho h g r hr]
    exact (replacement_sound g.1 (rho g.2.1) (rho g.2.2) (fun i => t i r) (hz r hr) hk).symm
  · simpa only [Function.update_of_ne hi] using h i r hr

lemma compile_crossings_balance (target : Fin 40 → Bool) (gs : List Gate)
    (k m : Nat) (rho : Nat → Nat) (s t : TableState)
    (hm : 0 < m) (hb : ∀ i, rho i < m)
    (hz : ∀ r, target r = false → t 0 r = false) (h : NegMapped target s t rho) :
    crossCount target (compile gs k m rho).1 m t +
      droppedCrossCount target gs k m rho s = crossCount target gs k s := by
  induction gs generalizing k m rho s t with
  | nil => rfl
  | cons g gs ih =>
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · have hb' : ∀ i, Function.update rho k m i < m + 1 := by
        intro i
        by_cases hi : i = k
        · subst i; simp
        · simpa [Function.update_of_ne hi] using Nat.lt_succ_of_lt (hb i)
      have hz' : ∀ r, target r = false →
          Function.update t m (Normalization.gate (mapped rho g) t) 0 r = false := by
        intro r hr
        simpa [Function.update_of_ne (Nat.ne_of_lt hm)] using hz r hr
      have hi := ih (k + 1) (m + 1) (Function.update rho k m)
        (Function.update s k (Normalization.gate g s))
        (Function.update t m (Normalization.gate (mapped rho g) t))
        (by omega) hb' hz' (negMapped_fresh target s t rho k m g h hb)
      have hg := crossings_mapped target s t rho h g
      simp only [compile, hk, ite_true, crossCount, droppedCrossCount]
      omega
    · let z := replacement g.1 (rho g.2.1) (rho g.2.2)
      have hb' : ∀ i, Function.update rho k z i < m := by
        intro i
        by_cases hi : i = k
        · subst i; simpa [z] using replacement_lt g.1 (rho g.2.1) (rho g.2.2) m hm
            (hb g.2.1) (hb g.2.2)
        · simpa [Function.update_of_ne hi] using hb i
      have hi := ih (k + 1) m (Function.update rho k z)
        (Function.update s k (Normalization.gate g s)) t hm hb' hz
        (negMapped_drop target s t rho k g h hz hk)
      simp only [compile, hk, Bool.false_eq_true, ite_false, crossCount, droppedCrossCount]
      dsimp [z] at hi
      omega

lemma clean_or_iff (target : Fin 40 → Bool) (s : TableState) (g : Gate)
    (hop : g.1 = false) :
    Normalization.Clean target (Normalization.gate g s) ↔
      Normalization.Clean target (s g.2.1) ∧ Normalization.Clean target (s g.2.2) := by
  constructor
  · intro hc
    constructor
    · intro r hr
      have hv := hc r hr
      cases ha : s g.2.1 r <;> cases hb : s g.2.2 r <;>
        simp_all [Normalization.gate]
    · intro r hr
      have hv := hc r hr
      cases ha : s g.2.1 r <;> cases hb : s g.2.2 r <;>
        simp_all [Normalization.gate]
  · rintro ⟨ha, hb⟩ r hr
    simp [Normalization.gate, hop, ha r hr, hb r hr]

lemma crossings_reader_or_one (target : Fin 40 → Bool) (s : TableState)
    (g : Gate) (h : Nat) (hc : Normalization.Clean target (s h))
    (hr : reads h g = true) (hop : g.1 = false)
    (hd : ¬ Normalization.Clean target (Normalization.gate g s)) :
    crossings target s g = 1 := by
  classical
  have hr' : g.2.1 = h ∨ g.2.2 = h := by simpa [reads] using hr
  rcases hr' with ha | hb
  · have hca : Normalization.Clean target (s g.2.1) := by simpa [ha] using hc
    have hnb : ¬ Normalization.Clean target (s g.2.2) :=
      fun hcb => hd ((clean_or_iff target s g hop).mpr ⟨hca, hcb⟩)
    simp [crossings, hd, hca, hnb]
  · have hcb : Normalization.Clean target (s g.2.2) := by simpa [hb] using hc
    have hna : ¬ Normalization.Clean target (s g.2.1) :=
      fun hca => hd ((clean_or_iff target s g hop).mpr ⟨hca, hcb⟩)
    simp [crossings, hd, hcb, hna]

def ReadersDirty (target : Fin 40 → Bool) (h : Nat) : List Gate → Nat → TableState → Prop
  | [], _, _ => True
  | g :: gs, k, s =>
    (reads h g = true → ¬ Normalization.Clean target (Normalization.gate g s)) ∧
    ReadersDirty target h gs (k + 1) (Function.update s k (Normalization.gate g s))

lemma droppedCrossCount_eq_readers (target : Fin 40 → Bool) (gs : List Gate)
    (k m h : Nat) (rho : Nat → Nat) (s : TableState)
    (hh : h < k) (hz : rho h = 0) (hc : Normalization.Clean target (s h))
    (ho : ∀ g ∈ gs, reads h g = true → g.1 = false)
    (hd : ReadersDirty target h gs k s) (he : OnlyReaderDrops gs k m rho h) :
    droppedCrossCount target gs k m rho s = gs.countP (reads h) := by
  induction gs generalizing k m rho s with
  | nil => rfl
  | cons g gs ih =>
    obtain ⟨hdg, hdt⟩ := hd
    obtain ⟨heg, het⟩ := he
    have hc' : Normalization.Clean target (Function.update s k (Normalization.gate g s) h) := by
      simpa only [Function.update_of_ne (Nat.ne_of_lt hh)] using hc
    have hot : ∀ z ∈ gs, reads h z = true → z.1 = false :=
      fun z hz => ho z (List.mem_cons_of_mem g hz)
    by_cases hk : Keep (rho g.2.1) (rho g.2.2)
    · have hr := keep_not_reader g h rho hz hk
      have hz' : Function.update rho k m h = 0 := by
        simpa only [Function.update_of_ne (Nat.ne_of_lt hh)] using hz
      simp only [hk, ite_true] at het
      have hi := ih (k + 1) (m + 1) (Function.update rho k m)
        (Function.update s k (Normalization.gate g s)) (by omega) hz' hc' hot hdt het
      simpa only [droppedCrossCount, hk, ite_true, List.countP_cons, hr,
        Bool.false_eq_true, ite_false, Nat.add_zero] using hi
    · have hr := heg hk
      have hcg := crossings_reader_or_one target s g h hc hr
        (ho g List.mem_cons_self hr) (hdg hr)
      let z := replacement g.1 (rho g.2.1) (rho g.2.2)
      have hz' : Function.update rho k z h = 0 := by
        simpa only [Function.update_of_ne (Nat.ne_of_lt hh)] using hz
      simp only [hk, Bool.false_eq_true, ite_false] at het
      have hi := ih (k + 1) m (Function.update rho k z)
        (Function.update s k (Normalization.gate g s)) (by omega) hz' hc' hot hdt het
      simp only [droppedCrossCount, hk, Bool.false_eq_true, ite_false, List.countP_cons,
        hr, ite_true, hcg]
      rw [hi]
      omega

lemma compile_reader_crossings (target : Fin 40 → Bool) (gs : List Gate)
    (k m h : Nat) (rho : Nat → Nat) (s t : TableState)
    (hm : 0 < m) (hb : ∀ i, rho i < m)
    (ht : ∀ r, target r = false → t 0 r = false) (hmap : NegMapped target s t rho)
    (hh : h < k) (hz : rho h = 0) (hc : Normalization.Clean target (s h))
    (ho : ∀ g ∈ gs, reads h g = true → g.1 = false)
    (hd : ReadersDirty target h gs k s) (he : OnlyReaderDrops gs k m rho h) :
    crossCount target (compile gs k m rho).1 m t + gs.countP (reads h) =
      crossCount target gs k s := by
  rw [← droppedCrossCount_eq_readers target gs k m h rho s hh hz hc ho hd he]
  exact compile_crossings_balance target gs k m rho s t hm hb ht hmap

lemma table_run_apply (gs : List Gate) (k : Nat) (s : TableState) (i : Nat) (r : Fin 40) :
    Normalization.run gs k s i r = run gs k (fun j => s j r) i := by
  induction gs generalizing k s with
  | nil => rfl
  | cons g gs ih =>
    rw [Normalization.run, ih, run]
    congr 2
    funext j
    by_cases hj : j = k
    · subst j; simp only [Function.update_self]; rfl
    · simp [Function.update_of_ne hj]

lemma table_run_below (gs : List Gate) (k i : Nat) (s : TableState) (hi : i < k) :
    Normalization.run gs k s i = s i := by
  funext r
  rw [table_run_apply, run_below _ _ _ _ hi]

lemma compile_neg_correct (target : Fin 40 → Bool) (gs : List Gate)
    (k m : Nat) (rho : Nat → Nat) (s t : TableState)
    (hm : 0 < m) (hb : ∀ i, rho i < m)
    (ht : ∀ r, target r = false → t 0 r = false) (hmap : NegMapped target s t rho) :
    NegMapped target (Normalization.run gs k s)
      (Normalization.run (compile gs k m rho).1 m t) (compile gs k m rho).2 := by
  intro i r hr
  rw [table_run_apply, table_run_apply]
  exact (compile_correct gs k m rho (fun j => s j r) (fun j => t j r)
    hm (ht r hr) hb (fun j => hmap j r hr)).2 i

lemma crossCount_append (target : Fin 40 → Bool) (gs hs : List Gate)
    (k : Nat) (s : TableState) :
    crossCount target (gs ++ hs) k s = crossCount target gs k s +
      crossCount target hs (k + gs.length) (Normalization.run gs k s) := by
  induction gs generalizing k s with
  | nil => simp [crossCount, Normalization.run]
  | cons g gs ih =>
    simp [crossCount, Normalization.run, ih, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma appendGate_clean (target : Fin 40 → Bool) (s : TableState) (h rep : Nat)
    (hh : Normalization.Clean target (s (h + 1)))
    (hr : Normalization.Clean target (s rep)) :
    Normalization.Clean target (Normalization.gate (appendGate h rep) s) := by
  apply (clean_or_iff target s (appendGate h rep) rfl).mpr
  refine ⟨hh, ?_⟩
  simp only [appendGate]
  split_ifs
  · exact hh
  · exact hr

lemma compiled_suffix_sink_crossings (target : Fin 40 → Bool) (gs : List Gate)
    (k h output : Nat) (s t : TableState)
    (hmap : NegMapped target s t (initialMap k h))
    (ht : ∀ r, target r = false → t 0 r = false)
    (hh : h < k) (hc : Normalization.Clean target (s h))
    (hcopy : Normalization.Clean target (t (h + 1)))
    (hout : Normalization.Clean target (Normalization.run gs k s output))
    (ho : ∀ g ∈ gs, reads h g = true → g.1 = false)
    (hd : ReadersDirty target h gs k s)
    (he : OnlyReaderDrops gs k (k + 1) (initialMap k h) h) :
    crossCount target ((cofactor k h gs).1 ++ [appendGate h ((cofactor k h gs).2 output)])
        (k + 1) t + gs.countP (reads h) = crossCount target gs k s := by
  have hcpr := compile_reader_crossings target gs k (k + 1) h (initialMap k h) s t
    (by omega) (initialMap_bound k h) ht hmap hh (by simp [initialMap, hh]) hc ho hd he
  change crossCount target (cofactor k h gs).1 (k + 1) t + _ = _ at hcpr
  have hfinal := compile_neg_correct target gs k (k + 1) (initialMap k h) s t
    (by omega) (initialMap_bound k h) ht hmap
  have hrep : Normalization.Clean target
      (Normalization.run (cofactor k h gs).1 (k + 1) t ((cofactor k h gs).2 output)) :=
    (clean_congr_neg target _ _ (hfinal output)).mp hout
  have hkeep : Normalization.Clean target
      (Normalization.run (cofactor k h gs).1 (k + 1) t (h + 1)) := by
    rw [table_run_below _ _ _ _ (by omega)]
    exact hcopy
  have hg := appendGate_clean target (Normalization.run (cofactor k h gs).1 (k + 1) t)
    h ((cofactor k h gs).2 output) hkeep hrep
  rw [crossCount_append]
  simp only [crossCount, crossings, hg, ite_true, Nat.add_zero, Nat.zero_add]
  exact hcpr

lemma minimal_single_or_reader_crossings (target : Fin 40 → Bool)
    (n : Nat) (pre suffix : List Gate) (h output : Nat) (s t : TableState)
    (hmap : NegMapped target s t (initialMap (n + pre.length) h))
    (ht : ∀ r, target r = false → t 0 r = false)
    (hh : h < n + pre.length) (hc : Normalization.Clean target (s h))
    (hcopy : Normalization.Clean target (t (h + 1)))
    (hout : Normalization.Clean target (Normalization.run suffix (n + pre.length) s output))
    (hr : suffix.countP (reads h) = 1)
    (hmin : (pre ++ suffix).length ≤ (pinAndAppend n pre suffix h output).size)
    (ho : ∀ g ∈ suffix, reads h g = true → g.1 = false)
    (hd : ReadersDirty target h suffix (n + pre.length) s) :
    crossCount target ((cofactor (n + pre.length) h suffix).1 ++
        [appendGate h ((cofactor (n + pre.length) h suffix).2 output)])
        (n + pre.length + 1) t + 1 = crossCount target suffix (n + pre.length) s := by
  simpa only [hr] using compiled_suffix_sink_crossings target suffix (n + pre.length) h output
    s t hmap ht hh hc hcopy hout ho hd
    (minimal_single_reader_only_drops n pre suffix h output hh hr hmin)

lemma crossCount_promote (target : Fin 40 → Bool) (gs : List Gate) (k : Nat)
    (s t : TableState) (h : NegMapped target s t (fun i => i + 1)) :
    crossCount target gs k s = crossCount target (gs.map promote) (k + 1) t := by
  induction gs generalizing k s t with
  | nil => rfl
  | cons g gs ih =>
    have hm : mapped (fun i => i + 1) g = promote g := rfl
    have hg := crossings_mapped target s t (fun i => i + 1) h g
    rw [hm] at hg
    have ht : NegMapped target (Function.update s k (Normalization.gate g s))
        (Function.update t (k + 1) (Normalization.gate (promote g) t)) (fun i => i + 1) := by
      intro i r hr
      by_cases hi : i = k
      · subst i
        simp only [Function.update_self]
        exact mapped_gate_neg target s t (fun i => i + 1) h g r hr
      · have hi' : i + 1 ≠ k + 1 := by omega
        simp only [Function.update_of_ne hi, Function.update_of_ne hi']
        exact h i r hr
    simp only [crossCount, List.map_cons]
    rw [hg, ih (k + 1) _ _ ht]

def inputTable (n : Nat) (rows : Fin 40 → Fin n → Bool) : TableState :=
  fun i r => (List.ofFn (rows r)).getD i false

def inputOneTable (n : Nat) (rows : Fin 40 → Fin n → Bool) : TableState :=
  fun i r => wireView (List.ofFn (rows r)) i

def prefixTable (n : Nat) (pre : List Gate) (rows : Fin 40 → Fin n → Bool) : TableState :=
  fun i r => (projectRun (pre.map promote) (List.ofFn (rows r))).getD i false

def prefixOneTable (n : Nat) (pre : List Gate) (rows : Fin 40 → Fin n → Bool) : TableState :=
  fun i r => wireView (projectRun (pre.map promote) (List.ofFn (rows r))) i

lemma prefixTable_eq_run (n : Nat) (pre : List Gate) (rows : Fin 40 → Fin n → Bool) :
    prefixTable n pre rows = Normalization.run pre n (inputTable n rows) := by
  funext i r
  rw [table_run_apply]
  have hp := promote_run pre n (fun j => (List.ofFn (rows r)).getD j false)
    (wireView (List.ofFn (rows r))) (by intro j; simp [wireView]) i
  have hw := wireView_projectRun (pre.map promote) (List.ofFn (rows r)) (promote_positive pre)
  simp only [List.length_ofFn] at hw
  rw [← hw] at hp
  simpa [prefixTable, inputTable, wireView] using hp.symm

lemma prefixOneTable_eq_run (n : Nat) (pre : List Gate) (rows : Fin 40 → Fin n → Bool) :
    prefixOneTable n pre rows = Normalization.run (pre.map promote) (n + 1) (inputOneTable n rows) := by
  funext i r
  rw [table_run_apply]
  have hw := wireView_projectRun (pre.map promote) (List.ofFn (rows r)) (promote_positive pre)
  simp only [List.length_ofFn] at hw
  exact congrFun hw i

lemma prefixOneTable_zero (n : Nat) (pre : List Gate) (rows : Fin 40 → Fin n → Bool) (r : Fin 40) :
    prefixOneTable n pre rows 0 r = false := by simp [prefixOneTable, wireView]

lemma prefixOneTable_copy (n : Nat) (pre : List Gate) (rows : Fin 40 → Fin n → Bool)
    (i : Nat) : prefixOneTable n pre rows (i + 1) = prefixTable n pre rows i := by
  funext r
  simp [prefixOneTable, prefixTable, wireView]

lemma prefixTable_outside (n : Nat) (pre : List Gate) (rows : Fin 40 → Fin n → Bool)
    (i : Nat) (hi : n + pre.length ≤ i) (r : Fin 40) : prefixTable n pre rows i r = false := by
  apply List.getD_eq_default
  simpa only [projectRun_length, List.length_map, List.length_ofFn] using hi

lemma prefix_initial_negMapped (target : Fin 40 → Bool) (n : Nat) (pre : List Gate)
    (rows : Fin 40 → Fin n → Bool) (h : Nat)
    (hc : Normalization.Clean target (prefixTable n pre rows h)) :
    NegMapped target (prefixTable n pre rows) (prefixOneTable n pre rows)
      (initialMap (n + pre.length) h) := by
  intro i r hr
  by_cases hi : i < n + pre.length
  · simp only [initialMap, hi, ite_true]
    by_cases he : i = h
    · subst i
      simp only [ite_true, prefixOneTable_zero]
      exact hc r hr
    · simp only [he, ite_false, prefixOneTable_copy]
  · simp only [initialMap, hi, ite_false, prefixOneTable_zero]
    exact prefixTable_outside n pre rows i (Nat.le_of_not_gt hi) r

lemma pinAndAppend_crossings (target : Fin 40 → Bool) (n : Nat) (pre suffix : List Gate)
    (rows : Fin 40 → Fin n → Bool) (h output : Nat) (hh : h < n + pre.length)
    (hc : Normalization.Clean target (prefixTable n pre rows h))
    (hout : Normalization.Clean target
      (Normalization.run suffix (n + pre.length) (prefixTable n pre rows) output))
    (hr : suffix.countP (reads h) = 1)
    (hmin : (pre ++ suffix).length ≤ (pinAndAppend n pre suffix h output).size)
    (ho : ∀ g ∈ suffix, reads h g = true → g.1 = false)
    (hd : ReadersDirty target h suffix (n + pre.length) (prefixTable n pre rows)) :
    crossCount target (pinGates n pre suffix h output) (n + 1) (inputOneTable n rows) + 1 =
      crossCount target (pre ++ suffix) n (inputTable n rows) := by
  have hs := minimal_single_or_reader_crossings target n pre suffix h output
    (prefixTable n pre rows) (prefixOneTable n pre rows)
    (prefix_initial_negMapped target n pre rows h hc)
    (by intro r _; exact prefixOneTable_zero n pre rows r) hh hc
    (by rw [prefixOneTable_copy]; exact hc) hout hr hmin ho hd
  have hp := crossCount_promote target pre n (inputTable n rows) (inputOneTable n rows)
    (by intro i r _; simp [inputTable, inputOneTable, wireView])
  have hg : pinGates n pre suffix h output = pre.map promote ++
      ((cofactor (n + pre.length) h suffix).1 ++
        [appendGate h ((cofactor (n + pre.length) h suffix).2 output)]) := by
    simp only [pinGates, List.append_assoc]
  rw [hg, crossCount_append, crossCount_append target pre suffix]
  rw [List.length_map, ← prefixOneTable_eq_run, ← prefixTable_eq_run]
  have hm : n + 1 + pre.length = n + pre.length + 1 := by omega
  rw [hm]
  omega

end CleanWireCrossings

namespace CleanWireSinkStep

open CofactorSimplification CofactorProjectBridge CofactorOperationBridge
open CleanWirePinAppend CleanWireExactRetention CleanWireDirtyRetention CleanWireCrossings

def demote (g : Gate) : Gate := (g.1, g.2.1 - 1, g.2.2 - 1)

def liftedList (n : Nat) (pre suffix : List Gate) (h output : Nat) : List Gate :=
  (pinGates n pre suffix h output).map demote

def liftedOutput (n : Nat) (pre suffix : List Gate) (h : Nat) : Nat :=
  n + pre.length + (cofactor (n + pre.length) h suffix).1.length

lemma liftedCircuit_eq (n : Nat) (pre suffix : List Gate) (h output : Nat) :
    rawCircuit n (liftedList n pre suffix h output) (liftedOutput n pre suffix h) =
      pinAndAppend n pre suffix h output := by
  rw [rawCircuit_description]
  simp [liftedList, liftedOutput, pinAndAppend, projectCircuit, projectGate, demote,
    List.map_map]

lemma liftedList_length (n : Nat) (pre suffix : List Gate) (h output : Nat) :
    (liftedList n pre suffix h output).length = (pinAndAppend n pre suffix h output).size := by
  simp [liftedList, pinAndAppend, projectCircuit_size]

lemma andOutputs_demote (gs : List Gate) (k : Nat) :
    andOutputs (gs.map demote) k = (andOutputs gs (k + 1)).map (fun i => i - 1) := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih =>
    cases hop : g.1 <;> simp [andOutputs, demote, hop, ih]

lemma raw_demote_wire (n : Nat) (gs : List Gate) (output wire : Nat) (w : List Bool) :
    (rawCircuit n (gs.map demote) wire).eval w =
      ((projectCircuit n gs output).wires w).getD wire false := by
  rw [rawCircuit_description]
  simp [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
    projectCircuit, projectGate, demote, List.map_map]
  rfl

lemma compiledDirty_lifted (n : Nat) (pre suffix : List Gate) (h output rep : Nat)
    (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool) (P : Fin 40 → Prop)
    (hd : CompiledDirty n pre suffix h output rows target P rep) :
    OriginalDirty n [] (liftedList n pre suffix h output) rows target P (rep - 1) := by
  obtain ⟨hm, r, hp, hn, hv⟩ := hd
  refine ⟨?_, r, hp, hn, ?_⟩
  · simp only [List.nil_append, liftedList, andOutputs_demote]
    exact List.mem_map.mpr ⟨rep, hm, rfl⟩
  · simp only [List.nil_append, liftedList]
    rw [raw_demote_wire n (pinGates n pre suffix h output)
      (n + pre.length + (cofactor (n + pre.length) h suffix).1.length + 1)]
    exact hv

lemma promote_demote (g : Gate) (ha : 0 < g.2.1) (hb : 0 < g.2.2) :
    promote (demote g) = g := by
  rcases g with ⟨op, a, b⟩
  dsimp at ha hb
  exact Prod.ext rfl (Prod.ext (by dsimp [promote, demote]; omega)
    (by dsimp [promote, demote]; omega))

lemma promote_demote_list (gs : List Gate) (hp : Positive gs) :
    (gs.map demote).map promote = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hg := hp g List.mem_cons_self
    simp only [List.map_cons, promote_demote g hg.1 hg.2]
    rw [ih (fun z hz => hp z (List.mem_cons_of_mem g hz))]

lemma wellFormed_append (gs hs : List Gate) (k : Nat) :
    WellFormed (gs ++ hs) k ↔ WellFormed gs k ∧ WellFormed hs (k + gs.length) := by
  induction gs generalizing k with
  | nil => simp [WellFormed]
  | cons g gs ih =>
    simp only [List.cons_append, WellFormed, ih, List.length_cons]
    have hk : k + (gs.length + 1) = k + 1 + gs.length := by omega
    rw [hk]
    tauto

lemma wellFormed_promote (gs : List Gate) (k : Nat) (hw : WellFormed gs k) :
    WellFormed (gs.map promote) (k + 1) := by
  induction gs generalizing k with
  | nil => trivial
  | cons g gs ih =>
    obtain ⟨ha, hb, ht⟩ := hw
    exact ⟨by simpa [promote] using Nat.add_lt_add_right ha 1,
      by simpa [promote] using Nat.add_lt_add_right hb 1, ih (k + 1) ht⟩

lemma wellFormed_demote (gs : List Gate) (k : Nat)
    (hp : Positive gs) (hw : WellFormed gs (k + 1)) : WellFormed (gs.map demote) k := by
  induction gs generalizing k with
  | nil => trivial
  | cons g gs ih =>
    obtain ⟨ha, hb, ht⟩ := hw
    have hphead := hp g List.mem_cons_self
    have hptail : Positive gs := fun z hz => hp z (List.mem_cons_of_mem g hz)
    refine ⟨?_, ?_, ih (k + 1) hptail ht⟩ <;> dsimp [demote] <;> omega

lemma pinGates_wellFormed (n : Nat) (pre suffix : List Gate) (h output : Nat)
    (hp : WellFormed pre n) (hh : h < n + pre.length) :
    WellFormed (pinGates n pre suffix h output) (n + 1) := by
  have hc := (cofactor_correct (n + pre.length) h suffix).1
  have hb := cofactor_map_bound (n + pre.length) h suffix output
  rw [pinGates, wellFormed_append, wellFormed_append]
  refine ⟨⟨wellFormed_promote pre n hp, ?_⟩, ?_⟩
  · simpa [List.length_map, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc
  · simp only [List.length_append, List.length_map, WellFormed, and_true, appendGate]
    split_ifs <;> omega

lemma liftedList_wellFormed (n : Nat) (pre suffix : List Gate) (h output : Nat)
    (hp : WellFormed pre n) (hh : h < n + pre.length) :
    WellFormed (liftedList n pre suffix h output) n := by
  exact wellFormed_demote _ _ (pinGates_positive _ _ _ _ _)
    (pinGates_wellFormed n pre suffix h output hp hh)

lemma liftedOutput_bound (n : Nat) (pre suffix : List Gate) (h output : Nat) :
    liftedOutput n pre suffix h < n + (liftedList n pre suffix h output).length := by
  simp only [liftedOutput, liftedList_length, pinAndAppend_size]
  omega

def ExactRows (n : Nat) (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool)
    (gs : List Gate) (output : Nat) : Prop :=
  ∀ r, (rawCircuit n gs output).eval (List.ofFn (rows r)) = target r

def HasTwoDirty (n : Nat) (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool)
    (P : Fin 40 → Prop) (gs : List Gate) : Prop :=
  ∃ i j, i ≠ j ∧ OriginalDirty n [] gs rows target P i ∧
    OriginalDirty n [] gs rows target P j

def MinimalRows (n : Nat) (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool)
    (N : Nat) : Prop :=
  ∀ gs output, WellFormed gs n → ExactRows n rows target gs output → N ≤ gs.length

lemma clean_implies_target (target signal : Fin 40 → Bool)
    (hc : Normalization.Clean target signal) (r : Fin 40) (hv : signal r = true) :
    target r = true := by
  cases ht : target r
  · have hf := hc r ht
    simp_all
  · rfl

lemma lifted_exact (n : Nat) (pre suffix : List Gate) (h output : Nat)
    (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool)
    (hh : h < n + pre.length) (hc : Normalization.Clean target (prefixTable n pre rows h))
    (he : ExactRows n rows target (pre ++ suffix) output) :
    ExactRows n rows target (liftedList n pre suffix h output) (liftedOutput n pre suffix h) := by
  intro r
  rw [liftedCircuit_eq]
  have hv := pinAndAppend_correct pre suffix h output (List.ofFn (rows r))
    (by simpa only [List.length_ofFn] using hh) (by
      intro hhval
      have ht := clean_implies_target target (prefixTable n pre rows h) hc r hhval
      simpa only [List.length_ofFn] using (he r).trans ht)
  simp only [List.length_ofFn] at hv
  exact hv.trans (he r)

lemma exact_suffix_output_clean (n : Nat) (pre suffix : List Gate) (output : Nat)
    (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool)
    (he : ExactRows n rows target (pre ++ suffix) output) :
    Normalization.Clean target
      (Normalization.run suffix (n + pre.length) (prefixTable n pre rows) output) := by
  intro r hr
  rw [table_run_apply]
  have hs := rawCircuit_split pre suffix output (List.ofFn (rows r))
  have hv := rawCircuit_eval suffix output (projectRun (pre.map promote) (List.ofFn (rows r)))
  simp only [List.length_ofFn, projectRun_length, List.length_map] at hs hv
  exact (hv.symm.trans (hs.symm.trans (he r))).trans hr

lemma lifted_crossCount (target : Fin 40 → Bool) (n : Nat) (pre suffix : List Gate)
    (rows : Fin 40 → Fin n → Bool) (h output : Nat) :
    crossCount target (liftedList n pre suffix h output) n (inputTable n rows) =
      crossCount target (pinGates n pre suffix h output) (n + 1) (inputOneTable n rows) := by
  have hs := crossCount_promote target (liftedList n pre suffix h output) n
    (inputTable n rows) (inputOneTable n rows)
    (by intro i r _; simp [inputTable, inputOneTable, wireView])
  rw [liftedList, promote_demote_list _ (pinGates_positive _ _ _ _ _)] at hs
  exact hs

lemma lifted_two_dirty (n : Nat) (pre suffix : List Gate) (h output : Nat)
    (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool) (P : Fin 40 → Prop)
    (hh : h < n + pre.length) (hc : Normalization.Clean target (prefixTable n pre rows h))
    (hr : suffix.countP (reads h) = 1)
    (hmin : (pre ++ suffix).length ≤ (pinAndAppend n pre suffix h output).size)
    (ho : ∀ g ∈ suffix, reads h g = true → g.1 = false)
    (hd : HasTwoDirty n rows target P (pre ++ suffix)) :
    HasTwoDirty n rows target P (liftedList n pre suffix h output) := by
  obtain ⟨i, j, hij, hdi, hdj⟩ := hd
  have hdip : OriginalDirty n pre suffix rows target P i := hdi
  have hdjp : OriginalDirty n pre suffix rows target P j := hdj
  obtain ⟨_, _, r, s, hrs, hdr, hds⟩ :=
    minimal_single_or_reader_two_dirty n pre suffix h output i j rows target P hh hr hmin ho
      (fun r hv => clean_implies_target target (prefixTable n pre rows h) hc r hv) hdip hdjp hij
  refine ⟨r - 1, s - 1, ?_, compiledDirty_lifted n pre suffix h output r rows target P hdr,
    compiledDirty_lifted n pre suffix h output s rows target P hds⟩
  have hrb := (andOutputs_bounds (pinGates n pre suffix h output) (n + 1) r hdr.1).1
  have hsb := (andOutputs_bounds (pinGates n pre suffix h output) (n + 1) s hds.1).1
  omega

lemma sink_step (n : Nat) (pre suffix : List Gate) (h output : Nat)
    (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool) (P : Fin 40 → Prop)
    (hp : WellFormed pre n) (hh : h < n + pre.length)
    (he : ExactRows n rows target (pre ++ suffix) output)
    (hc : Normalization.Clean target (prefixTable n pre rows h))
    (hr : suffix.countP (reads h) = 1)
    (hmin : MinimalRows n rows target (pre ++ suffix).length)
    (ho : ∀ g ∈ suffix, reads h g = true → g.1 = false)
    (hcross : ReadersDirty target h suffix (n + pre.length) (prefixTable n pre rows))
    (hd : HasTwoDirty n rows target P (pre ++ suffix)) :
    ∃ gs out, WellFormed gs n ∧ out < n + gs.length ∧ ExactRows n rows target gs out ∧
      gs.length = (pre ++ suffix).length ∧ HasTwoDirty n rows target P gs ∧
      crossCount target gs n (inputTable n rows) + 1 =
        crossCount target (pre ++ suffix) n (inputTable n rows) := by
  have hw := liftedList_wellFormed n pre suffix h output hp hh
  have hex := lifted_exact n pre suffix h output rows target hh hc he
  have hm := hmin (liftedList n pre suffix h output) (liftedOutput n pre suffix h) hw hex
  rw [liftedList_length] at hm
  refine ⟨liftedList n pre suffix h output, liftedOutput n pre suffix h, hw,
    liftedOutput_bound _ _ _ _ _, hex, ?_, lifted_two_dirty n pre suffix h output rows target P
      hh hc hr hm ho hd, ?_⟩
  · rw [liftedList_length]
    exact minimal_single_reader_size n pre suffix h output hh hr hm
  · rw [lifted_crossCount]
    exact pinAndAppend_crossings target n pre suffix rows h output hh hc
      (exact_suffix_output_clean n pre suffix output rows target he) hr hm ho hcross

end CleanWireSinkStep

namespace CleanWireIteration

open CofactorSimplification CofactorProjectBridge CofactorOperationBridge
open CleanWirePinAppend CleanWireExactRetention CleanWireDirtyRetention CleanWireCrossings
open CleanWireSinkStep

lemma crossCount_pos_split (target : Fin 40 → Bool) (gs : List Gate) (k : Nat)
    (s : TableState) (hp : 0 < crossCount target gs k s) :
    ∃ pre g suffix, gs = pre ++ g :: suffix ∧
      0 < crossings target (Normalization.run pre k s) g := by
  induction gs generalizing k s with
  | nil => simp [crossCount] at hp
  | cons g gs ih =>
    by_cases hg : 0 < crossings target s g
    · exact ⟨[], g, gs, rfl, hg⟩
    · have ht : 0 < crossCount target gs (k + 1)
          (Function.update s k (Normalization.gate g s)) := by
        simp only [crossCount] at hp
        omega
      obtain ⟨pre, z, suffix, he, hz⟩ := ih (k + 1)
        (Function.update s k (Normalization.gate g s)) ht
      exact ⟨g :: pre, z, suffix, by simp [he], hz⟩

lemma crossing_data (target : Fin 40 → Bool) (s : TableState) (g : Gate)
    (hp : 0 < crossings target s g) :
    g.1 = false ∧ ¬ Normalization.Clean target (Normalization.gate g s) ∧
      ∃ h, reads h g = true ∧ Normalization.Clean target (s h) := by
  classical
  have hd : ¬ Normalization.Clean target (Normalization.gate g s) := by
    intro hc
    simp [crossings, hc] at hp
  have hh : Normalization.Clean target (s g.2.1) ∨ Normalization.Clean target (s g.2.2) := by
    by_cases ha : Normalization.Clean target (s g.2.1)
    · exact Or.inl ha
    · by_cases hb : Normalization.Clean target (s g.2.2)
      · exact Or.inr hb
      · simp [crossings, hd, ha, hb] at hp
  have hop : g.1 = false := by
    cases hg : g.1
    · rfl
    · exfalso
      apply hd
      intro r hr
      rcases hh with ha | hb
      · simp [Normalization.gate, hg, ha r hr]
      · simp [Normalization.gate, hg, hb r hr]
  refine ⟨hop, hd, ?_⟩
  rcases hh with ha | hb
  · exact ⟨g.2.1, by simp [reads], ha⟩
  · exact ⟨g.2.2, by simp [reads], hb⟩

lemma reads_bound (g : Gate) (h k : Nat) (ha : g.2.1 < k) (hb : g.2.2 < k)
    (hr : reads h g = true) : h < k := by
  have he : g.2.1 = h ∨ g.2.2 = h := by simpa [reads] using hr
  rcases he with he | he <;> omega

lemma no_readers_of_count_zero (gs : List Gate) (h : Nat) (hc : gs.countP (reads h) = 0) :
    ∀ g ∈ gs, reads h g = false := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.countP_cons] at hc
    have hg : reads h g = false := by cases hr : reads h g <;> simp_all
    have ht : gs.countP (reads h) = 0 := by simp_all
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hg
    · exact ih ht z hz

lemma readersDirty_of_none (target : Fin 40 → Bool) (gs : List Gate) (k h : Nat)
    (s : TableState) (hn : ∀ g ∈ gs, reads h g = false) : ReadersDirty target h gs k s := by
  induction gs generalizing k s with
  | nil => trivial
  | cons g gs ih =>
    refine ⟨?_, ?_⟩
    · simp [hn g List.mem_cons_self]
    · exact ih (k + 1) _ (fun z hz => hn z (List.mem_cons_of_mem g hz))

lemma crossing_head_unique (n : Nat) (pre : List Gate) (g : Gate) (suffix : List Gate)
    (h output : Nat) (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool)
    (hp : WellFormed pre n) (hh : h < n + pre.length)
    (he : ExactRows n rows target (pre ++ g :: suffix) output)
    (hc : Normalization.Clean target (prefixTable n pre rows h))
    (hread : reads h g = true)
    (hmin : MinimalRows n rows target (pre ++ g :: suffix).length) :
    (g :: suffix).countP (reads h) = 1 := by
  have hw := liftedList_wellFormed n pre (g :: suffix) h output hp hh
  have hx := lifted_exact n pre (g :: suffix) h output rows target hh hc he
  have hm := hmin _ _ hw hx
  rw [liftedList_length] at hm
  have hs := pinAndAppend_size_savings n pre (g :: suffix) h output hh
  have hl : 1 ≤ (g :: suffix).countP (reads h) := by simp [List.countP_cons, hread]
  omega

lemma positive_sink_step (n : Nat) (gs : List Gate) (output : Nat)
    (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool) (P : Fin 40 → Prop)
    (hw : WellFormed gs n) (he : ExactRows n rows target gs output)
    (hmin : MinimalRows n rows target gs.length) (hd : HasTwoDirty n rows target P gs)
    (hcpos : 0 < crossCount target gs n (inputTable n rows)) :
    ∃ gs' out, WellFormed gs' n ∧ out < n + gs'.length ∧ ExactRows n rows target gs' out ∧
      gs'.length = gs.length ∧ HasTwoDirty n rows target P gs' ∧
      crossCount target gs' n (inputTable n rows) + 1 =
        crossCount target gs n (inputTable n rows) := by
  obtain ⟨pre, g, suffix, hgs, hp⟩ := crossCount_pos_split target gs n (inputTable n rows) hcpos
  subst gs
  rw [wellFormed_append] at hw
  obtain ⟨hpre, ha, hb, htail⟩ := hw
  rw [← prefixTable_eq_run] at hp
  obtain ⟨hop, hgdirty, h, hread, hclean⟩ := crossing_data target (prefixTable n pre rows) g hp
  have hh := reads_bound g h (n + pre.length) ha hb hread
  have hr := crossing_head_unique n pre g suffix h output rows target hpre hh he hclean hread hmin
  have htailcount : suffix.countP (reads h) = 0 := by
    simp only [List.countP_cons, hread, ite_true] at hr
    omega
  have hnone := no_readers_of_count_zero suffix h htailcount
  have hor : ∀ z ∈ g :: suffix, reads h z = true → z.1 = false := by
    intro z hz hzr
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hop
    · have := hnone z hz
      simp_all
  have hcross : ReadersDirty target h (g :: suffix) (n + pre.length) (prefixTable n pre rows) :=
    ⟨fun _ => hgdirty, readersDirty_of_none target suffix (n + pre.length + 1) h _ hnone⟩
  exact sink_step n pre (g :: suffix) h output rows target P hpre hh he hclean hr hmin hor hcross hd

lemma zero_crossings_exists (n : Nat) (gs : List Gate) (output : Nat)
    (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool) (P : Fin 40 → Prop)
    (hw : WellFormed gs n) (he : ExactRows n rows target gs output)
    (hmin : MinimalRows n rows target gs.length) (hd : HasTwoDirty n rows target P gs) :
    ∃ gs' out, WellFormed gs' n ∧ ExactRows n rows target gs' out ∧
      gs'.length = gs.length ∧ HasTwoDirty n rows target P gs' ∧
      crossCount target gs' n (inputTable n rows) = 0 := by
  have normalize : ∀ m : Nat, ∀ (xs : List Gate) (out : Nat),
      crossCount target xs n (inputTable n rows) = m → WellFormed xs n →
      ExactRows n rows target xs out → MinimalRows n rows target xs.length →
      HasTwoDirty n rows target P xs →
      ∃ ys yout, WellFormed ys n ∧ ExactRows n rows target ys yout ∧ ys.length = xs.length ∧
        HasTwoDirty n rows target P ys ∧ crossCount target ys n (inputTable n rows) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro xs out hm hxs hex hmx hdx
      by_cases hz : m = 0
      · exact ⟨xs, out, hxs, hex, rfl, hdx, hm.trans hz⟩
      · have hp : 0 < crossCount target xs n (inputTable n rows) := by omega
        obtain ⟨ys, yout, hys, _, hey, hlen, hdy, hdrop⟩ :=
          positive_sink_step n xs out rows target P hxs hex hmx hdx hp
        have hmny : MinimalRows n rows target ys.length := by rw [hlen]; exact hmx
        have hlt : crossCount target ys n (inputTable n rows) < m := by omega
        obtain ⟨zs, zout, hzs, hez, hzlen, hdz, hzero⟩ :=
          ih (crossCount target ys n (inputTable n rows)) hlt ys yout rfl hys hey hmny hdy
        exact ⟨zs, zout, hzs, hez, hzlen.trans hlen, hdz, hzero⟩
  exact normalize _ gs output rfl hw he hmin hd

end CleanWireIteration

namespace FirstSplitWitness

def gate (k a b : Bool) : Bool := if k then a && b else a || b

def bad (a b c : Bool) : Prop := a = false ∧ b = false ∧ c = true

lemma local_split (xa ya za xb yb zb k : Bool)
    (ha : ¬bad xa ya za) (hb : ¬bad xb yb zb)
    (hx : gate k xa xb = false) (hy : gate k ya yb = false)
    (hz : gate k za zb = true) :
    k = true ∧
      ((xa = true ∧ ya = false ∧ xb = false ∧ yb = true) ∨
       (xa = false ∧ ya = true ∧ xb = true ∧ yb = false)) := by
  cases xa <;> cases ya <;> cases za <;> cases xb <;> cases yb <;>
    cases zb <;> cases k <;> simp_all [bad, gate]

lemma first_split
    (raw output : Nat) (op : Nat → Bool) (left right : Nat → Nat)
    (x y z : Nat → Bool)
    (hraw : ∀ i, i < raw → z i = (x i || y i))
    (hgate : ∀ i, raw ≤ i → i ≤ output →
      left i < i ∧ right i < i ∧
      x i = gate (op i) (x (left i)) (x (right i)) ∧
      y i = gate (op i) (y (left i)) (y (right i)) ∧
      z i = gate (op i) (z (left i)) (z (right i)))
    (hout : bad (x output) (y output) (z output)) :
    ∃ i, raw ≤ i ∧ i ≤ output ∧ op i = true ∧
      ((x (left i) = true ∧ y (left i) = false ∧
        x (right i) = false ∧ y (right i) = true) ∨
       (x (left i) = false ∧ y (left i) = true ∧
        x (right i) = true ∧ y (right i) = false)) := by
  classical
  let existsBad : ∃ i, i ≤ output ∧ bad (x i) (y i) (z i) :=
    ⟨output, le_rfl, hout⟩
  let i := Nat.find existsBad
  have hi : i ≤ output ∧ bad (x i) (y i) (z i) := Nat.find_spec existsBad
  have hbefore : ∀ j, j < i → ¬bad (x j) (y j) (z j) := by
    intro j hj hbad
    exact Nat.find_min' existsBad ⟨le_trans (Nat.le_of_lt hj) hi.1, hbad⟩ |>.not_gt hj
  have hcomputed : raw ≤ i := by
    by_contra h
    have hinput := hraw i (Nat.lt_of_not_ge h)
    rcases hi.2 with ⟨hx, hy, hz⟩
    simp [hx, hy, hz] at hinput
  rcases hgate i hcomputed hi.1 with ⟨hl, hr, hx, hy, hz⟩
  have hlbad := hbefore (left i) hl
  have hrbad := hbefore (right i) hr
  rcases hi.2 with ⟨hix, hiy, hiz⟩
  have hs := local_split (x (left i)) (y (left i)) (z (left i))
    (x (right i)) (y (right i)) (z (right i)) (op i) hlbad hrbad
    (hx.symm.trans hix) (hy.symm.trans hiy) (hz.symm.trans hiz)
  exact ⟨i, hcomputed, hi.1, hs.1, hs.2⟩

end FirstSplitWitness

namespace SingletonUnionTransport

def outputs {n : Nat} (out : Fin n → Nat) : Finset Nat := Finset.univ.image out

def paid {n : Nat} (atoms : Finset Nat) (out : Fin n → Nat) : Finset Nat :=
  outputs out \ atoms

def Available {n : Nat} (atoms : Finset Nat) (out : Fin n → Nat)
    (i : Fin n) (a : Nat) : Prop :=
  a ∈ atoms ∨ ∃ j : Fin n, j < i ∧ out j = a

def UnionTrace {n : Nat} (atoms : Finset Nat) (out : Fin n → Nat) : Prop :=
  ∀ i, ∃ a b, Available atoms out i a ∧ Available atoms out i b ∧ out i = a ||| b

def ProperUnion (available : Finset Nat) (v : Nat) : Prop :=
  ∃ a ∈ available, ∃ b ∈ available, a ≠ v ∧ b ≠ v ∧ v = a ||| b

lemma first_occurrence {n : Nat} (out : Fin n → Nat) (v : Nat)
    (hv : v ∈ outputs out) :
    ∃ i : Fin n, out i = v ∧ ∀ j : Fin n, j < i → out j ≠ v := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hv
  let hits := Finset.univ.filter (fun i : Fin n => out i = v)
  have hh : hits.Nonempty := ⟨j, by simp [hits, hj]⟩
  let i := hits.min' hh
  have hi : i ∈ hits := Finset.min'_mem hits hh
  refine ⟨i, (Finset.mem_filter.mp hi).2, ?_⟩
  intro k hk he
  have hm : k ∈ hits := by simp [hits, he]
  have hle : i ≤ k := Finset.min'_le hits k hm
  exact (not_le_of_gt hk) hle

lemma available_mem_union_paid {n : Nat} (atoms : Finset Nat) (out : Fin n → Nat)
    (i : Fin n) (a : Nat) (ha : Available atoms out i a) :
    a ∈ atoms ∪ paid atoms out := by
  rcases ha with ha | ⟨j, _, hj⟩
  · exact Finset.mem_union_left _ ha
  · by_cases ham : a ∈ atoms
    · exact Finset.mem_union_left _ ham
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩, ham⟩

lemma paid_proper_union {n : Nat} (atoms : Finset Nat) (out : Fin n → Nat)
    (ht : UnionTrace atoms out) (v : Nat) (hv : v ∈ paid atoms out) :
    ProperUnion (atoms ∪ paid atoms out) v := by
  obtain ⟨hvo, hva⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨i, hi, hfirst⟩ := first_occurrence out v hvo
  obtain ⟨a, b, ha, hb, he⟩ := ht i
  have hne : ∀ x, Available atoms out i x → x ≠ v := by
    intro x hx hxv
    rcases hx with hx | ⟨j, hj, hjx⟩
    · exact hva (hxv ▸ hx)
    · exact hfirst j hj (hjx.trans hxv)
  exact ⟨a, available_mem_union_paid atoms out i a ha,
    b, available_mem_union_paid atoms out i b hb, hne a ha, hne b hb, hi.symm.trans he⟩

lemma paid_card_le_length {n : Nat} (atoms : Finset Nat) (out : Fin n → Nat) :
    (paid atoms out).card ≤ n := by
  have hs : paid atoms out ⊆ outputs out := Finset.sdiff_subset
  have hc : (outputs out).card ≤ (Finset.univ : Finset (Fin n)).card :=
    Finset.card_image_le
  exact (Finset.card_le_card hs).trans (by simpa using hc)

lemma properUnion_mono {s t : Finset Nat} (hst : s ⊆ t) {v : Nat}
    (hv : ProperUnion s v) : ProperUnion t v := by
  obtain ⟨a, ha, b, hb, hav, hbv, he⟩ := hv
  exact ⟨a, hst ha, b, hst hb, hav, hbv, he⟩

lemma exact_budget {n : Nat} (atoms required : Finset Nat) (out : Fin n → Nat)
    (ht : UnionTrace atoms out) (hr : required ⊆ paid atoms out)
    (hc : (paid atoms out).card ≤ required.card) :
    paid atoms out = required ∧ ∀ v ∈ required, ProperUnion (atoms ∪ required) v := by
  have he : paid atoms out = required := (Finset.eq_of_subset_of_card_le hr hc).symm
  refine ⟨he, ?_⟩
  intro v hv
  simpa only [he] using paid_proper_union atoms out ht v (hr hv)

lemma one_extra_cover (required values : Finset Nat) (bound : Nat)
    (hb : 0 < bound) (hr : required ⊆ values)
    (hc : values.card ≤ required.card + 1)
    (hv : ∀ v ∈ values, v < bound) :
    ∃ extra, extra < bound ∧ values ⊆ insert extra required ∧
      (extra ∈ values ∨ values = required) := by
  classical
  by_cases hs : values ⊆ required
  · have he : values = required := Finset.Subset.antisymm hs hr
    refine ⟨0, hb, ?_, Or.inr he⟩
    intro v hmem
    exact Finset.mem_insert_of_mem (hs hmem)
  · change ¬ ∀ v, v ∈ values → v ∈ required at hs
    obtain ⟨extra, he⟩ := not_forall.mp hs
    obtain ⟨hem, hen⟩ := not_imp.mp he
    have hi : insert extra required ⊆ values := by
      intro v hm
      rcases Finset.mem_insert.mp hm with rfl | hm
      · exact hem
      · exact hr hm
    have hcard : values.card ≤ (insert extra required).card := by
      simpa only [Finset.card_insert_of_notMem hen] using hc
    have heq := Finset.eq_of_subset_of_card_le hi hcard
    exact ⟨extra, hv extra hem, by rw [heq], Or.inl hem⟩

lemma one_extra_budget {n : Nat} (atoms required : Finset Nat) (out : Fin n → Nat)
    (ht : UnionTrace atoms out) (hr : required ⊆ paid atoms out)
    (hc : (paid atoms out).card ≤ required.card + 1)
    (bound : Nat) (hb : 0 < bound) (hv : ∀ i, out i < bound) :
    ∃ extra, extra < bound ∧ paid atoms out ⊆ insert extra required ∧
      (extra ∈ paid atoms out ∨ paid atoms out = required) ∧
      (∀ v ∈ required, ProperUnion (atoms ∪ insert extra required) v) ∧
      (extra ∈ paid atoms out → ProperUnion (atoms ∪ insert extra required) extra) := by
  have hbound : ∀ v ∈ paid atoms out, v < bound := by
    intro v hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hmem).1
    exact hi ▸ hv i
  obtain ⟨extra, he, hcover, hactual⟩ :=
    one_extra_cover required (paid atoms out) bound hb hr hc hbound
  have hsub : atoms ∪ paid atoms out ⊆ atoms ∪ insert extra required := by
    intro v hmem
    rcases Finset.mem_union.mp hmem with ha | hp
    · exact Finset.mem_union_left _ ha
    · exact Finset.mem_union_right _ (hcover hp)
  have hp : ∀ v ∈ paid atoms out, ProperUnion (atoms ∪ insert extra required) v :=
    fun v hm => properUnion_mono hsub (paid_proper_union atoms out ht v hm)
  exact ⟨extra, he, hcover, hactual, fun v hm => hp v (hr hm), hp extra⟩

lemma five_required {n : Nat} (atoms required : Finset Nat) (out : Fin n → Nat)
    (ht : UnionTrace atoms out) (hn : n ≤ 5) (hr : required ⊆ paid atoms out)
    (hc : required.card = 5) :
    paid atoms out = required ∧ ∀ v ∈ required, ProperUnion (atoms ∪ required) v := by
  apply exact_budget atoms required out ht hr
  have := paid_card_le_length atoms out
  omega

lemma four_required {n : Nat} (atoms required : Finset Nat) (out : Fin n → Nat)
    (ht : UnionTrace atoms out) (hn : n ≤ 5) (hr : required ⊆ paid atoms out)
    (hc : required.card = 4) (hv : ∀ i, out i < 256) :
    ∃ extra, extra < 256 ∧ paid atoms out ⊆ insert extra required ∧
      (extra ∈ paid atoms out ∨ paid atoms out = required) ∧
      (∀ v ∈ required, ProperUnion (atoms ∪ insert extra required) v) ∧
      (extra ∈ paid atoms out → ProperUnion (atoms ∪ insert extra required) extra) := by
  apply one_extra_budget atoms required out ht hr _ 256 (by decide) hv
  have := paid_card_le_length atoms out
  omega

end SingletonUnionTransport

namespace NegativeRowReduction

open CofactorSimplification CofactorProjectBridge CleanWireCrossings

lemma evalGate_mono (g : Gate) (s t : Nat → Bool)
    (h : ∀ i, s i = true → t i = true) : evalGate g s = true → evalGate g t = true := by
  have ha := h g.2.1
  have hb := h g.2.2
  cases hop : g.1 <;> cases hsa : s g.2.1 <;> cases hsb : s g.2.2 <;>
    cases hta : t g.2.1 <;> cases htb : t g.2.2 <;> simp_all [evalGate]

lemma run_mono (gs : List Gate) (k : Nat) (s t : Nat → Bool)
    (h : ∀ i, s i = true → t i = true) :
    ∀ i, run gs k s i = true → run gs k t i = true := by
  induction gs generalizing k s t with
  | nil => exact h
  | cons g gs ih =>
    apply ih (k + 1)
    intro i
    by_cases hi : i = k
    · subst i
      simpa only [Function.update_self] using evalGate_mono g s t h
    · simpa only [Function.update_of_ne hi] using h i

lemma inputTable_mono (n : Nat) (rows : Fin 40 → Fin n → Bool) (r s : Fin 40)
    (h : ∀ i, rows r i = true → rows s i = true) :
    ∀ i, inputTable n rows i r = true → inputTable n rows i s = true := by
  intro i
  by_cases hi : i < n
  · simpa [inputTable, hi] using h ⟨i, hi⟩
  · simp [inputTable, hi]

lemma row_eval_mono (n : Nat) (rows : Fin 40 → Fin n → Bool) (r s : Fin 40)
    (h : ∀ i, rows r i = true → rows s i = true) (gs : List Gate) (output : Nat) :
    (rawCircuit n gs output).eval (List.ofFn (rows r)) = true →
      (rawCircuit n gs output).eval (List.ofFn (rows s)) = true := by
  have hr := rawCircuit_eval gs output (List.ofFn (rows r))
  have hs := rawCircuit_eval gs output (List.ofFn (rows s))
  simp only [List.length_ofFn] at hr hs
  rw [hr, hs]
  exact run_mono gs n _ _ (inputTable_mono n rows r s h) output

def NegativeDominated (n : Nat) (rows : Fin 40 → Fin n → Bool) (target : Fin 40 → Bool)
    (P : Fin 40 → Prop) : Prop :=
  ∀ r, target r = false → ∃ s, P s ∧ target s = false ∧
    ∀ i, rows r i = true → rows s i = true

lemma all_negative_iff_selected (n : Nat) (rows : Fin 40 → Fin n → Bool)
    (target : Fin 40 → Bool) (P : Fin 40 → Prop)
    (hd : NegativeDominated n rows target P) (gs : List Gate) (output : Nat) :
    Normalization.Clean target (fun r => (rawCircuit n gs output).eval (List.ofFn (rows r))) ↔
      ∀ r, P r → target r = false →
        (rawCircuit n gs output).eval (List.ofFn (rows r)) = false := by
  constructor
  · intro hc r _ hr
    exact hc r hr
  · intro hc r hr
    obtain ⟨s, hp, hs, hm⟩ := hd r hr
    cases hv : (rawCircuit n gs output).eval (List.ofFn (rows r))
    · exact hv
    · have hst := row_eval_mono n rows r s hm gs output hv
      have hsf := hc s hp hs
      simp_all

lemma negative_witness_to_selected (n : Nat) (rows : Fin 40 → Fin n → Bool)
    (target : Fin 40 → Bool) (P : Fin 40 → Prop)
    (hd : NegativeDominated n rows target P) (gs : List Gate) (output : Nat)
    (r : Fin 40) (hr : target r = false)
    (hv : (rawCircuit n gs output).eval (List.ofFn (rows r)) = true) :
    ∃ s, P s ∧ target s = false ∧
      (rawCircuit n gs output).eval (List.ofFn (rows s)) = true := by
  obtain ⟨s, hp, hs, hm⟩ := hd r hr
  exact ⟨s, hp, hs, row_eval_mono n rows r s hm gs output hv⟩

def gapInputMasks : List Nat :=
  [2147418115, 663661903884, 34144976944, 21653750532,
    103293914128, 414195942664, 581968119809, 1065151898146]

def gapRows (r : Fin 40) (i : Fin 8) : Bool := (gapInputMasks.getD i.val 0).testBit r.val

def gapTarget (r : Fin 40) : Bool := (36671 : Nat).testBit r.val

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma gap_negative_dominated :
    NegativeDominated 8 gapRows gapTarget (fun r => 16 ≤ r.val) := by
  unfold NegativeDominated
  decide

end NegativeRowReduction

namespace R3Finite

def atoms : List Nat := [1,2,4,8,16,32,64,128]

def constructAux : List Nat → List Nat → Bool
  | [], _ => true
  | s :: rest, available =>
      available.any (fun a => available.any (fun b => a ||| b == s)) &&
        constructAux rest (s :: available)

def insertMask (s : Nat) : List Nat → List Nat
  | [] => [s]
  | t :: ts => if s ≤ t then s :: t :: ts else t :: insertMask s ts

def sortMasks : List Nat → List Nat
  | [] => []
  | s :: rest => insertMask s (sortMasks rest)

def construct (targets : List Nat) : Bool :=
  constructAux (sortMasks targets) atoms

def nontrivial (s : Nat) : Bool := s &&& (s - 1) != 0

def usefulExtras (targets : List Nat) : List Nat :=
  (List.range 256).filter (fun s => nontrivial s && !targets.contains s &&
    targets.any (fun t => s &&& t == s))

def familyImpossible (targets : List Nat) : Bool :=
  decide (4 ≤ targets.length ∧ targets.length ≤ 5) && !construct targets &&
    (targets.length != 4 || (usefulExtras targets).all (fun s => !construct (s :: targets)))

def families : List (List Nat) := [
  [5,40,41,176,228],
  [5,40,44,177,224],
  [5,40,57,164,176],
  [5,40,57,176,228],
  [5,40,108,161,224],
  [5,40,108,177,224],
  [9,18,40,144,224],
  [9,18,40,176,224],
  [9,18,66,144,224],
  [9,18,74,144,224],
  [9,18,82,144,224],
  [9,18,90,144,192],
  [9,18,90,144,224],
  [9,18,144,176,224],
  [9,40,68,144,224],
  [9,40,144,160,177],
  [9,40,144,176,224],
  [9,40,144,177,224],
  [9,50,66,144,224],
  [9,50,74,144,224],
  [9,50,82,144,192],
  [9,50,82,144,224],
  [9,50,90,144,192],
  [9,50,90,144,224],
  [9,66,144,146,224],
  [9,66,144,178,224],
  [9,68,82,144,224],
  [9,68,90,144,192],
  [9,68,90,144,224],
  [9,74,144,146,224],
  [9,74,144,178,224],
  [9,82,144,146,224],
  [9,82,144,178,192],
  [9,82,144,178,224],
  [9,90,144,146,192],
  [9,90,144,146,224],
  [9,90,144,178,192],
  [9,90,144,178,224],
  [12,17,40,176,192],
  [12,17,82,176,192],
  [12,17,90,144,192],
  [12,17,90,176,192],
  [12,18,66,176,192],
  [12,18,98,176,192],
  [12,18,176,192,194],
  [12,18,176,192,226],
  [12,26,66,176,192],
  [12,26,98,176,192],
  [12,26,176,192,194],
  [12,26,176,192,226],
  [12,40,66,176,192],
  [12,40,66,176,224],
  [12,40,160,192,228],
  [12,40,176,192,224],
  [12,40,176,192,228],
  [12,66,82,176,192],
  [12,66,90,144,192],
  [12,66,90,176,192],
  [12,66,176,192,224],
  [12,82,98,144,192],
  [12,82,98,176,192],
  [12,82,144,192,226],
  [12,82,176,192,194],
  [12,82,176,192,226],
  [12,90,98,144,192],
  [12,90,98,176,192],
  [12,90,144,192,194],
  [12,90,144,192,226],
  [12,90,176,192,194],
  [12,90,176,192,226],
  [13,40,41,48,228],
  [13,40,41,176,228],
  [13,40,44,96,177],
  [13,40,44,177,224],
  [13,40,48,57,164],
  [13,40,48,57,228],
  [13,40,57,164,176],
  [13,40,57,176,228],
  [13,40,96,108,161],
  [13,40,96,108,177],
  [13,40,108,161,224],
  [13,40,108,177,224],
  [17,34,82,176,192],
  [17,34,83,144,192],
  [17,34,90,176,192],
  [17,34,91,144,192],
  [17,40,88,176,192],
  [17,40,89,144,192],
  [17,40,90,176,192],
  [17,40,91,144,192],
  [17,40,92,144,192],
  [17,66,90,144,192],
  [17,82,98,144,192],
  [17,82,144,192,226],
  [17,82,162,176,192],
  [17,82,176,192,224],
  [17,83,144,162,192],
  [17,83,144,176,192],
  [17,90,98,144,192],
  [17,90,130,176,192],
  [17,90,144,192,194],
  [17,90,144,192,226],
  [17,90,162,176,192],
  [17,90,176,192],
  [17,90,176,192,224],
  [17,91,130,144,192],
  [17,91,144,162,192],
  [17,91,144,176,192],
  [17,91,144,192],
  [18,68,90,144,192],
  [18,144,176,178,224],
  [18,176,192,226],
  [19,144,176,178,192],
  [21,33,40,108,224],
  [21,36,40,57,176],
  [21,40,41,100,176],
  [21,40,44,49,224],
  [21,40,49,108,224],
  [21,40,57,100,176],
  [22,144,176,192,226],
  [26,144,146,176,224],
  [26,144,176,178,224],
  [26,176,192,194],
  [26,176,192,226],
  [27,144,146,176,192],
  [27,144,176,178,192],
  [29,33,40,96,108],
  [29,33,40,108,224],
  [29,36,40,48,57],
  [29,36,40,57,176],
  [29,40,41,48,100],
  [29,40,41,100,176],
  [29,40,44,49,96],
  [29,40,44,49,224],
  [29,40,48,57,100],
  [29,40,49,96,108],
  [29,40,49,108,224],
  [29,40,57,100,176],
  [30,144,176,192,194],
  [30,144,176,192,226],
  [33,40,69,108,224],
  [33,40,77,96,108],
  [33,40,77,108,224],
  [33,40,85,108,224],
  [33,40,93,96,108],
  [33,40,93,108,224],
  [34,68,82,144,224],
  [34,68,86,144,192],
  [34,68,90,144,224],
  [34,68,94,144,192],
  [36,40,48,57,77],
  [36,40,48,57,93],
  [36,40,57,69,176],
  [36,40,57,77,176],
  [36,40,57,85,176],
  [36,40,57,93,176],
  [40,41,48,77,100],
  [40,41,48,93,100],
  [40,41,69,100,176],
  [40,41,77,100,176],
  [40,41,85,100,176],
  [40,41,93,100,176],
  [40,44,49,69,224],
  [40,44,49,77,96],
  [40,44,49,77,224],
  [40,44,49,85,224],
  [40,44,49,93,96],
  [40,44,49,93,224],
  [40,48,57,77,100],
  [40,48,57,93,100],
  [40,49,69,108,224],
  [40,49,77,96,108],
  [40,49,77,108,224],
  [40,49,85,108,224],
  [40,49,93,96,108],
  [40,49,93,108,224],
  [40,57,69,100,176],
  [40,57,77,100,176],
  [40,57,85,100,176],
  [40,57,93,100,176],
  [40,68,88,144,224],
  [40,68,89,144,192],
  [40,68,90,144,224],
  [40,68,92,144,192],
  [40,68,94,144,192],
  [50,68,82,144,192],
  [50,68,90,144,192],
  [66,144,178,224],
  [66,176,192,224,226],
  [67,144,178,192,224],
  [68,82,144,162,224],
  [68,82,144,176,224],
  [68,82,144,178,192],
  [68,86,144,162,192],
  [68,86,144,192,224],
  [68,90,130,144,224],
  [68,90,144,146,192],
  [68,90,144,162,224],
  [68,90,144,176,224],
  [68,90,144,178,192],
  [68,90,144,224],
  [68,94,130,144,192],
  [68,94,144,162,192],
  [68,94,144,192],
  [68,94,144,192,224],
  [70,144,192,224,226],
  [74,144,146,224],
  [74,144,178,224],
  [74,176,192,194,224],
  [74,176,192,224,226],
  [75,144,146,192,224],
  [75,144,178,192,224],
  [78,144,192,194,224],
  [78,144,192,224,226],
  [82,144,176,178,224],
  [82,144,176,192,226],
  [82,144,178,192,224],
  [82,144,178,224],
  [82,176,192,224,226],
  [82,176,192,226],
  [83,144,176,178,192],
  [83,144,178,192],
  [83,144,178,192,224],
  [86,144,176,192,226],
  [86,144,192,224,226],
  [86,144,192,226],
  [90,144,146,176,224],
  [90,144,146,192,224],
  [90,144,146,224],
  [90,144,176,178,224],
  [90,144,176,192,194],
  [90,144,176,192,226],
  [90,144,178,192,224],
  [90,144,178,224],
  [90,176,192,194],
  [90,176,192,194,224],
  [90,176,192,224,226],
  [90,176,192,226],
  [91,144,146,176,192],
  [91,144,146,192],
  [91,144,146,192,224],
  [91,144,176,178,192],
  [91,144,178,192],
  [91,144,178,192,224],
  [94,144,176,192,194],
  [94,144,176,192,226],
  [94,144,192,194],
  [94,144,192,194,224],
  [94,144,192,224,226],
  [94,144,192,226]
]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma families_impossible : families.all familyImpossible = true := by
  decide +kernel


abbrev Rect := Nat × Nat

def edges : List Rect := [(0,6),(0,7),(1,3),(1,5),(2,4),(2,7),(3,5),(3,7),(4,5),(4,6),(5,6)]

def filled (v : Nat) : List Rect :=
  if v == 0 then [(3,4),(2,5)] else
  if v == 1 then [(4,7),(6,7)] else
  if v == 2 then [(0,5),(3,6)] else []

def edgePresent (es : List Rect) (u v : Nat) : Bool :=
  es.any (fun e => (e.1 == u && e.2 == v) || (e.1 == v && e.2 == u))

def allowedRows (v : Nat) : List Nat :=
  if v == 0 then [192,40,176,178,108,94,49,13] else if v == 1 then [192,40,144,162,228,90,177,93] else
  if v == 2 then [224,40,144,226,100,91,57,13] else [192,40,144,162,100,90,49,13]

def adjacencyCheck : Bool :=
  (List.range 4).all (fun v => (List.range 8).all (fun u => (List.range 8).all (fun w =>
    ((allowedRows v).getD u 0).testBit w == edgePresent (edges ++ filled v) u w)))

def commonRows : List Nat → Nat → Nat
  | [], _ => 255
  | m :: rest, a => (if a % 2 == 1 then m else 255) &&& commonRows rest (a / 2)

def crossHas (es : List Rect) (a b : Nat) : Bool :=
  es.any (fun e => (a.testBit e.1 && b.testBit e.2) || (a.testBit e.2 && b.testBit e.1))

def validDirty (v available a b : Nat) : Bool :=
  decide (0 < a ∧ a < b) && (a &&& b == 0) &&
  ((a ||| b) &&& available == a ||| b) &&
  (b &&& commonRows (allowedRows v) a == b) && crossHas (filled v) a b

def validClean (a b : Nat) : Bool :=
  decide (0 < a ∧ a < b) && (a &&& b == 0) &&
    (b &&& commonRows (allowedRows 3) a == b)

def dirtyData : List (Nat × Nat × List Rect) := [(0,248,[(8,16),(8,48),(8,144),(8,176),(16,40),(16,72),(16,104),(48,72)]),(0,250,[(8,16),(8,18),(8,48),(8,50),(8,144),(8,146),(8,176),(8,178),(16,40),(16,72),(16,104),(18,40),(48,72)]),(0,252,[(4,32),(4,48),(4,160),(4,176),(8,16),(8,48),(8,144),(8,176),(12,16),(12,32),(12,48),(12,144),(12,160),(12,176),(16,40),(16,44),(16,72),(16,76),(16,104),(16,108),(20,32),(28,32),(32,68),(32,76),(32,84),(32,92),(48,68),(48,72),(48,76)]),(0,254,[(4,32),(4,48),(4,160),(4,176),(6,32),(8,16),(8,18),(8,48),(8,50),(8,144),(8,146),(8,176),(8,178),(12,16),(12,32),(12,48),(12,144),(12,160),(12,176),(14,32),(16,40),(16,44),(16,72),(16,76),(16,104),(16,108),(18,40),(20,32),(22,32),(28,32),(30,32),(32,68),(32,70),(32,76),(32,78),(32,84),(32,86),(32,92),(32,94),(48,68),(48,72),(48,76)]),(1,248,[(16,128),(16,160),(16,192),(16,224),(24,128),(24,160),(64,128),(64,144),(64,160),(64,176),(72,128),(72,160),(80,128),(80,160),(88,128),(88,160)]),(1,249,[(16,128),(16,160),(16,192),(16,224),(17,128),(17,192),(24,128),(24,160),(25,128),(64,128),(64,129),(64,144),(64,145),(64,160),(64,161),(64,176),(64,177),(65,128),(72,128),(72,160),(73,128),(80,128),(80,160),(81,128),(88,128),(88,160),(89,128)]),(1,252,[(16,128),(16,132),(16,160),(16,164),(16,192),(16,196),(16,224),(16,228),(20,128),(24,128),(24,160),(28,128),(64,128),(64,144),(64,160),(64,176),(68,128),(68,144),(72,128),(72,160),(76,128),(80,128),(80,160),(84,128),(88,128),(88,160),(92,128)]),(1,253,[(16,128),(16,132),(16,160),(16,164),(16,192),(16,196),(16,224),(16,228),(17,128),(17,192),(20,128),(21,128),(24,128),(24,160),(25,128),(28,128),(29,128),(64,128),(64,129),(64,144),(64,145),(64,160),(64,161),(64,176),(64,177),(65,128),(68,128),(68,144),(69,128),(72,128),(72,160),(73,128),(76,128),(77,128),(80,128),(80,160),(81,128),(84,128),(85,128),(88,128),(88,160),(89,128),(92,128),(93,128)]),(2,248,[(8,64),(8,96),(8,192),(8,224),(24,64),(24,96),(40,64),(56,64)]),(2,249,[(1,32),(1,96),(1,160),(1,224),(8,64),(8,96),(8,192),(8,224),(9,32),(9,64),(9,96),(9,160),(9,192),(9,224),(17,32),(17,96),(24,64),(24,96),(25,32),(25,64),(25,96),(32,65),(32,73),(32,81),(32,89),(40,64),(41,64),(56,64),(57,64)]),(2,250,[(8,64),(8,66),(8,96),(8,98),(8,192),(8,194),(8,224),(8,226),(24,64),(24,96),(40,64),(40,66),(56,64)]),(2,251,[(1,32),(1,96),(1,160),(1,224),(3,32),(8,64),(8,66),(8,96),(8,98),(8,192),(8,194),(8,224),(8,226),(9,32),(9,64),(9,96),(9,160),(9,192),(9,224),(11,32),(17,32),(17,96),(19,32),(24,64),(24,96),(25,32),(25,64),(25,96),(27,32),(32,65),(32,67),(32,73),(32,75),(32,81),(32,83),(32,89),(32,91),(40,64),(40,66),(41,64),(56,64),(57,64)])]

def dirtyFor (d : Nat × Nat × List Rect) : Bool :=
  (List.range 256).all (fun a => (List.range 256).all (fun b =>
    !validDirty d.1 d.2.1 a b || d.2.2.contains (a,b)))

def dirtyComplete : Bool := dirtyData.all dirtyFor

def cleanRects : List Rect := [(0,0),(1,64),(1,128),(1,192),(2,8),(2,32),(2,40),(4,16),(4,128),(4,144),(5,128),(8,32),(8,34),(8,128),(8,130),(8,160),(8,162),(9,128),(10,32),(12,128),(13,128),(16,32),(16,36),(16,64),(16,68),(16,96),(16,100),(17,64),(18,32),(24,32),(26,32),(32,64),(32,66),(32,72),(32,74),(32,80),(32,82),(32,88),(32,90),(33,64),(48,64),(49,64)]

def cleanComplete : Bool :=
  cleanRects.contains (0,0) && (List.range 256).all (fun a => (List.range 256).all (fun b =>
    !validClean a b || cleanRects.contains (a,b)))

def weightedEdges : List (Rect × Nat) := [((0,6),1),((0,7),2),((1,3),4),((1,5),8),((2,4),16),((2,7),32),((3,5),64),((3,7),128),((4,5),256),((4,6),512),((5,6),1024)]

def coverageAux : List (Rect × Nat) → Rect → Nat
  | [], _ => 0
  | (e,w) :: rest, r =>
      (if (r.1.testBit e.1 && r.2.testBit e.2) ||
          (r.1.testBit e.2 && r.2.testBit e.1) then w else 0) + coverageAux rest r

def coverage (r : Rect) : Nat := coverageAux weightedEdges r

def addMask (m : Nat) (targets : List Nat) : List Nat :=
  if nontrivial m && !targets.contains m then insertMask m targets else targets

def reqRect (r : Rect) : List Nat := addMask r.1 (addMask r.2 [])

def mergeReq (xs ys : List Nat) : List Nat := xs.foldl (fun acc s => addMask s acc) ys

set_option maxHeartbeats 0 in
def cleanCoverTable (n : Nat) : List (List Nat) := (if n < 1024 then (if n < 512 then (if n < 256 then (if n < 128 then (if n < 64 then (if n < 32 then (if n < 16 then (if n < 8 then (if n < 4 then (if n < 2 then [] else (if n < 3 then [] else [[],[5],[5,17],[5,33],[5,49],[5,192],[9],[9,17],[9,33],[9,49],[9,192],[10,192],[12,192],[13],[13,17],[13,33],[13,49],[13,192],[17],[17,192],[18,192],[24,192],[26,192],[33],[33,192],[34,192],[36,192],[40,192],[48,192],[49],[49,192],[66,192],[68,192],[72,192],[74,192],[80,192],[82,192],[88,192],[90,192],[96,192],[100,192],[130,192],[144,192],[160,192],[162,192],[192]])) else (if n < 6 then [] else (if n < 7 then [] else [[34,192],[40,192],[130,192],[162,192],[192]]))) else (if n < 12 then [] else (if n < 14 then (if n < 13 then [] else [[17,40],[33,40],[40],[40,49],[40,192]]) else (if n < 15 then [[5,40],[9,40],[13,40],[40],[40,192]] else [[40,192]])))) else (if n < 24 then (if n < 20 then (if n < 18 then [] else (if n < 19 then [] else [[36,192],[68,192],[100,192],[144,192],[192]])) else []) else (if n < 28 then [] else (if n < 30 then (if n < 29 then [[36,40],[40],[40,68],[40,100],[40,144]] else []) else [])))) else (if n < 48 then (if n < 40 then (if n < 36 then (if n < 34 then [] else (if n < 35 then [] else [[5],[5,17],[5,33],[5,49],[5,192],[12,192],[13],[13,17],[13,33],[13,49],[13,192],[144,192],[192]])) else []) else (if n < 44 then [] else (if n < 46 then (if n < 45 then [[5,40],[12,40],[13,40],[40],[40,144]] else []) else (if n < 47 then [[5,40],[13,40]] else [])))) else (if n < 56 then (if n < 52 then (if n < 50 then (if n < 49 then [[],[5],[5,36],[5,68],[5,100],[5,144],[9,144],[10,144],[12],[12,36],[12,68],[12,100],[12,144],[13],[13,36],[13,68],[13,100],[13,144],[17,144],[18,144],[24,144],[26,144],[33,144],[34,144],[36],[36,144],[40,144],[48,144],[49,144],[66,144],[68],[68,144],[72,144],[74,144],[80,144],[82,144],[88,144],[90,144],[96,144],[100],[100,144],[130,144],[144],[144,160],[144,162],[144,192]] else [[17,144],[33,144],[49,144],[144],[144,192]]) else (if n < 51 then [[5],[5,36],[5,68],[5,100],[5,144],[9,144],[13],[13,36],[13,68],[13,100],[13,144],[144],[144,192]] else [[144,192]])) else (if n < 54 then (if n < 53 then [[34,144],[40,144],[130,144],[144],[144,162]] else []) else [])) else (if n < 60 then [] else (if n < 62 then (if n < 61 then [[40,144]] else []) else []))))) else (if n < 96 then (if n < 80 then (if n < 72 then (if n < 68 then (if n < 66 then [] else (if n < 67 then [] else [[10,192],[24,192],[26,192],[34,192],[72,192],[74,192],[88,192],[90,192],[160,192],[162,192],[192]])) else (if n < 70 then [] else (if n < 71 then [] else [[34,192],[162,192]]))) else []) else []) else (if n < 112 then [] else (if n < 120 then (if n < 116 then (if n < 114 then (if n < 113 then [[10,144],[24,144],[26,144],[34,144],[72,144],[74,144],[88,144],[90,144],[144],[144,160],[144,162]] else []) else []) else (if n < 118 then (if n < 117 then [[34,144],[144,162]] else []) else [])) else [])))) else (if n < 192 then (if n < 160 then (if n < 144 then (if n < 136 then (if n < 132 then [] else (if n < 134 then [] else (if n < 135 then [] else [[130,192],[162,192]]))) else (if n < 140 then [] else (if n < 142 then [] else (if n < 143 then [[9,40],[13,40]] else [])))) else []) else (if n < 176 then (if n < 168 then (if n < 164 then (if n < 162 then [] else (if n < 163 then [] else [[12,192],[13],[13,17],[13,33],[13,49],[13,192]])) else []) else (if n < 172 then [] else (if n < 174 then (if n < 173 then [[12,40],[13,40]] else []) else (if n < 175 then [[13,40]] else [])))) else (if n < 184 then (if n < 180 then (if n < 178 then [] else (if n < 179 then [[9,144],[13],[13,36],[13,68],[13,100],[13,144]] else [])) else (if n < 182 then (if n < 181 then [[130,144],[144,162]] else []) else [])) else []))) else (if n < 224 then (if n < 208 then (if n < 200 then (if n < 196 then (if n < 194 then [] else (if n < 195 then [] else [[160,192],[162,192]])) else (if n < 198 then [] else (if n < 199 then [] else [[162,192]]))) else []) else []) else (if n < 240 then [] else (if n < 248 then (if n < 244 then (if n < 242 then (if n < 241 then [[144,160],[144,162]] else []) else []) else (if n < 246 then (if n < 245 then [[144,162]] else []) else [])) else []))))) else (if n < 384 then (if n < 320 then (if n < 288 then (if n < 272 then (if n < 264 then (if n < 260 then (if n < 258 then [] else (if n < 259 then [] else [[18,192],[24,192],[26,192],[36,192],[80,192],[82,192],[88,192],[90,192],[96,192],[100,192],[192]])) else []) else (if n < 268 then (if n < 266 then [] else (if n < 267 then [] else [[18,192],[26,192],[82,192],[90,192]])) else (if n < 270 then (if n < 269 then [[18],[18,34],[18,40],[18,130],[18,162],[24,40],[26],[26,34],[26,40],[26,130],[26,162],[34,82],[34,90],[36,40],[40],[40,80],[40,82],[40,88],[40,90],[40,96],[40,100],[82],[82,130],[82,162],[90],[90,130],[90,162]] else []) else []))) else (if n < 280 then (if n < 276 then (if n < 274 then [] else (if n < 275 then [] else [[36,192],[100,192]])) else []) else (if n < 284 then [] else (if n < 286 then (if n < 285 then [[36,40],[40,100]] else []) else [])))) else (if n < 304 then [] else (if n < 312 then (if n < 308 then (if n < 306 then (if n < 305 then [[5,36],[5,100],[12,36],[12,100],[13,36],[13,100],[18,144],[24,144],[26,144],[36],[36,144],[80,144],[82,144],[88,144],[90,144],[96,144],[100],[100,144],[144]] else []) else (if n < 307 then [[5,36],[5,100],[13,36],[13,100]] else [])) else []) else (if n < 316 then (if n < 314 then (if n < 313 then [[18,144],[26,144],[82,144],[90,144]] else []) else []) else [])))) else (if n < 352 then (if n < 336 then (if n < 328 then (if n < 324 then (if n < 322 then [] else (if n < 323 then [] else [[24,192],[26,192],[88,192],[90,192]])) else []) else (if n < 332 then (if n < 330 then [] else (if n < 331 then [] else [[26,192],[90,192]])) else (if n < 334 then (if n < 333 then [[18,34],[18,162],[24,40],[26],[26,34],[26,40],[26,130],[26,162],[34,82],[34,90],[40,88],[40,90],[82,162],[90],[90,130],[90,162]] else []) else []))) else []) else (if n < 368 then [] else (if n < 376 then (if n < 372 then (if n < 370 then (if n < 369 then [[24,144],[26,144],[88,144],[90,144]] else []) else []) else []) else (if n < 380 then (if n < 378 then (if n < 377 then [[26,144],[90,144]] else []) else []) else []))))) else (if n < 448 then (if n < 416 then (if n < 400 then (if n < 392 then [] else (if n < 396 then [] else (if n < 398 then (if n < 397 then [[18,130],[18,162],[26,130],[26,162],[82,130],[82,162],[90,130],[90,162]] else []) else []))) else []) else (if n < 432 then [] else (if n < 440 then (if n < 436 then (if n < 434 then (if n < 433 then [[12,36],[12,100],[13,36],[13,100]] else []) else (if n < 435 then [[13,36],[13,100]] else [])) else []) else []))) else (if n < 480 then (if n < 464 then (if n < 456 then [] else (if n < 460 then [] else (if n < 462 then (if n < 461 then [[18,162],[26,130],[26,162],[82,162],[90,130],[90,162]] else []) else []))) else []) else [])))) else (if n < 768 then (if n < 640 then (if n < 576 then (if n < 544 then (if n < 528 then (if n < 520 then (if n < 516 then (if n < 514 then [] else (if n < 515 then [] else [[5,17],[5,49],[9,17],[9,49],[13,17],[13,49],[17],[17,192],[48,192],[49],[49,192],[68,192],[96,192],[100,192],[192]])) else []) else []) else (if n < 536 then (if n < 532 then (if n < 530 then [] else (if n < 531 then [] else [[68,192],[100,192]])) else []) else [])) else (if n < 560 then (if n < 552 then (if n < 548 then (if n < 546 then [] else (if n < 547 then [] else [[5,17],[5,49],[13,17],[13,49]])) else []) else []) else (if n < 568 then (if n < 564 then (if n < 562 then (if n < 561 then [[5,68],[5,100],[12,68],[12,100],[13,68],[13,100],[17,144],[48,144],[49,144],[68],[68,144],[96,144],[100],[100,144],[144]] else [[17,144],[49,144]]) else (if n < 563 then [[5,68],[5,100],[13,68],[13,100]] else [])) else []) else []))) else []) else (if n < 704 then (if n < 672 then [] else (if n < 688 then (if n < 680 then (if n < 676 then (if n < 674 then [] else (if n < 675 then [] else [[13,17],[13,49]])) else []) else []) else (if n < 696 then (if n < 692 then (if n < 690 then [] else (if n < 691 then [[13,68],[13,100]] else [])) else []) else []))) else [])) else (if n < 896 then (if n < 832 then (if n < 800 then (if n < 784 then (if n < 776 then (if n < 772 then (if n < 770 then [] else (if n < 771 then [] else [[96,192],[100,192]])) else []) else []) else (if n < 792 then (if n < 788 then (if n < 786 then [] else (if n < 787 then [] else [[100,192]])) else []) else (if n < 796 then [] else (if n < 798 then (if n < 797 then [[40,100]] else []) else [])))) else (if n < 816 then [] else (if n < 824 then (if n < 820 then (if n < 818 then [] else (if n < 819 then [[5,100],[13,100]] else [])) else []) else []))) else []) else (if n < 960 then (if n < 928 then [] else (if n < 944 then [] else (if n < 952 then (if n < 948 then (if n < 946 then [] else (if n < 947 then [[13,100]] else [])) else []) else []))) else [])))) else (if n < 1536 then (if n < 1280 then (if n < 1152 then (if n < 1088 then (if n < 1056 then (if n < 1040 then (if n < 1032 then (if n < 1028 then (if n < 1026 then [] else (if n < 1027 then [] else [[5,33],[5,49],[9,33],[9,49],[13,33],[13,49],[33],[33,192],[48,192],[49],[49,192],[66,192],[72,192],[74,192],[80,192],[82,192],[88,192],[90,192],[192]])) else []) else (if n < 1036 then (if n < 1034 then [] else (if n < 1035 then [] else [[66,192],[74,192],[82,192],[90,192]])) else (if n < 1038 then (if n < 1037 then [[33,40],[34,66],[34,74],[34,82],[34,90],[40],[40,48],[40,49],[40,66],[40,72],[40,74],[40,80],[40,82],[40,88],[40,90],[66],[66,130],[66,162],[74],[74,130],[74,162],[82],[82,130],[82,162],[90],[90,130],[90,162]] else [[33,40],[40,49]]) else []))) else []) else (if n < 1072 then (if n < 1064 then (if n < 1060 then (if n < 1058 then [] else (if n < 1059 then [] else [[5,33],[5,49],[13,33],[13,49]])) else []) else []) else (if n < 1080 then (if n < 1076 then (if n < 1074 then (if n < 1073 then [[33,144],[48,144],[49,144],[66,144],[72,144],[74,144],[80,144],[82,144],[88,144],[90,144],[144]] else [[33,144],[49,144]]) else []) else []) else (if n < 1084 then (if n < 1082 then (if n < 1081 then [[66,144],[74,144],[82,144],[90,144]] else []) else []) else [])))) else (if n < 1120 then (if n < 1104 then (if n < 1096 then (if n < 1092 then (if n < 1090 then [] else (if n < 1091 then [] else [[72,192],[74,192],[88,192],[90,192]])) else []) else (if n < 1100 then (if n < 1098 then [] else (if n < 1099 then [] else [[74,192],[90,192]])) else (if n < 1102 then (if n < 1101 then [[34,66],[34,74],[34,82],[34,90],[40,72],[40,74],[40,88],[40,90],[66,162],[74],[74,130],[74,162],[82,162],[90],[90,130],[90,162]] else []) else []))) else []) else (if n < 1136 then [] else (if n < 1144 then (if n < 1140 then (if n < 1138 then (if n < 1137 then [[72,144],[74,144],[88,144],[90,144]] else []) else []) else []) else (if n < 1148 then (if n < 1146 then (if n < 1145 then [[74,144],[90,144]] else []) else []) else []))))) else (if n < 1216 then (if n < 1184 then (if n < 1168 then (if n < 1160 then (if n < 1156 then (if n < 1154 then [] else (if n < 1155 then [] else [[9,33],[9,49],[13,33],[13,49]])) else []) else (if n < 1164 then [] else (if n < 1166 then (if n < 1165 then [[66,130],[66,162],[74,130],[74,162],[82,130],[82,162],[90,130],[90,162]] else []) else []))) else []) else (if n < 1200 then (if n < 1192 then (if n < 1188 then (if n < 1186 then [] else (if n < 1187 then [] else [[13,33],[13,49]])) else []) else []) else [])) else (if n < 1248 then (if n < 1232 then (if n < 1224 then [] else (if n < 1228 then [] else (if n < 1230 then (if n < 1229 then [[66,162],[74,130],[74,162],[82,162],[90,130],[90,162]] else []) else []))) else []) else []))) else (if n < 1408 then (if n < 1344 then (if n < 1312 then (if n < 1296 then (if n < 1288 then [] else (if n < 1292 then (if n < 1290 then [] else (if n < 1291 then [] else [[82,192],[90,192]])) else (if n < 1294 then (if n < 1293 then [[34,82],[34,90],[40,80],[40,82],[40,88],[40,90],[82],[82,130],[82,162],[90],[90,130],[90,162]] else []) else []))) else []) else (if n < 1328 then [] else (if n < 1336 then [] else (if n < 1340 then (if n < 1338 then (if n < 1337 then [[82,144],[90,144]] else []) else []) else [])))) else (if n < 1376 then (if n < 1360 then (if n < 1352 then [] else (if n < 1356 then (if n < 1354 then [] else (if n < 1355 then [] else [[90,192]])) else (if n < 1358 then (if n < 1357 then [[34,82],[34,90],[40,88],[40,90],[82,162],[90],[90,130],[90,162]] else []) else []))) else []) else (if n < 1392 then [] else (if n < 1400 then [] else (if n < 1404 then (if n < 1402 then (if n < 1401 then [[90,144]] else []) else []) else []))))) else (if n < 1472 then (if n < 1440 then (if n < 1424 then (if n < 1416 then [] else (if n < 1420 then [] else (if n < 1422 then (if n < 1421 then [[82,130],[82,162],[90,130],[90,162]] else []) else []))) else []) else []) else (if n < 1504 then (if n < 1488 then (if n < 1480 then [] else (if n < 1484 then [] else (if n < 1486 then (if n < 1485 then [[82,162],[90,130],[90,162]] else []) else []))) else []) else [])))) else (if n < 1792 then (if n < 1664 then (if n < 1600 then (if n < 1568 then (if n < 1552 then (if n < 1544 then [] else (if n < 1548 then [] else (if n < 1550 then (if n < 1549 then [] else [[40,49]]) else []))) else []) else (if n < 1584 then (if n < 1576 then (if n < 1572 then (if n < 1570 then [] else (if n < 1571 then [] else [[5,49],[13,49]])) else []) else []) else (if n < 1592 then (if n < 1588 then (if n < 1586 then (if n < 1585 then [[48,144],[49,144]] else [[49,144]]) else []) else []) else []))) else []) else (if n < 1728 then (if n < 1696 then [] else (if n < 1712 then (if n < 1704 then (if n < 1700 then (if n < 1698 then [] else (if n < 1699 then [] else [[13,49]])) else []) else []) else [])) else [])) else [])))

def reachableMissing (n : Nat) : Bool := if n < 2048 then ((if n / 64 < 16 then (if n / 64 < 8 then (if n / 64 < 4 then (if n / 64 < 2 then (if n / 64 < 1 then 18230563083653800072 else 18230545491467739272) else (if n / 64 < 3 then 18229718658723143808 else 18230563083653800072)) else (if n / 64 < 6 then (if n / 64 < 5 then 18446735865901807752 else 18446735865901283464) else (if n / 64 < 7 then 18446735865901283456 else 18446735865901807752))) else (if n / 64 < 12 then (if n / 64 < 10 then (if n / 64 < 9 then 18442179488374097928 else 18442214674088372232) else (if n / 64 < 11 then 18441335063443441664 else 18442214674088372232)) else (if n / 64 < 14 then 18441933199111677960 else (if n / 64 < 15 then 18441933199111153664 else 18441933199111677960)))) else (if n / 64 < 24 then (if n / 64 < 20 then (if n / 64 < 18 then (if n / 64 < 17 then 18446735865901807752 else 18446172915948386440) else (if n / 64 < 19 then 18445891440971675784 else 18446735865901807752)) else 18444765506704570496) else (if n / 64 < 28 then (if n / 64 < 26 then 18442232266274416640 else (if n / 64 < 27 then 18441387841344284672 else 18442232266274416640)) else 18440261907077195776))) : Nat).testBit (n % 64) else false

def cleanCoverFor (a : Rect) : Bool :=
  cleanRects.all (fun b => (List.range 2048).all (fun need =>
    !reachableMissing need || need &&& (coverage a ||| coverage b) != need ||
      (cleanCoverTable need).contains (mergeReq (reqRect a) (reqRect b))))

def cleanCoverComplete : Bool := cleanRects.all cleanCoverFor

def orders : List (Nat × Nat × Nat) := [(0,1,2),(0,2,1),(1,0,2),(1,2,0),(2,0,1),(2,1,0)]

def caseIndices : List (Nat × Nat × Nat) := [(0,5,11),(0,9,7),(4,1,11),(4,10,3),(8,2,7),(8,6,3)]

def orderComplete : Bool :=
  (List.range 3).all (fun a => (List.range 3).all (fun b => (List.range 3).all (fun c =>
    !decide (a ≠ b ∧ a ≠ c ∧ b ≠ c) || orders.contains (a,b,c))))

def getData (i : Nat) : Nat × Nat × List Rect := dirtyData.getD i (0,0,[])

def casesCorrect : Bool :=
  orders.length == caseIndices.length &&
  (orders.zip caseIndices).all (fun p =>
    let o := p.1
    let c := p.2
    let a := getData c.1
    let b := getData c.2.1
    let d := getData c.2.2
    a.1 == o.1 && a.2.1 == 248 &&
    b.1 == o.2.1 && b.2.1 == (248 ||| (1 <<< o.1)) &&
    d.1 == o.2.2 && d.2.1 == (248 ||| (1 <<< o.1) ||| (1 <<< o.2.1)))

def caseCovered (c : Nat × Nat × Nat) : Bool :=
  (getData c.1).2.2.all (fun a => (getData c.2.1).2.2.all (fun b =>
    (getData c.2.2).2.2.all (fun d =>
      let required := mergeReq (reqRect a) (mergeReq (reqRect b) (reqRect d))
      let need := 2047 - (coverage a ||| coverage b ||| coverage d)
      decide (5 < required.length) ||
      (reachableMissing need && (cleanCoverTable need).all (fun extra =>
        let r := mergeReq required extra
        decide (5 < r.length) || families.contains r)))))

def coverageCheck : Bool := caseIndices.all caseCovered

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma adjacency_checked : adjacencyCheck = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma dirty_0 : dirtyFor (0,248,[(8,16),(8,48),(8,144),(8,176),(16,40),(16,72),(16,104),(48,72)]) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma dirty_1 : dirtyFor (0,250,[(8,16),(8,18),(8,48),(8,50),(8,144),(8,146),(8,176),(8,178),(16,40),(16,72),(16,104),(18,40),(48,72)]) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma dirty_2 : dirtyFor (0,252,[(4,32),(4,48),(4,160),(4,176),(8,16),(8,48),(8,144),(8,176),(12,16),(12,32),(12,48),(12,144),(12,160),(12,176),(16,40),(16,44),(16,72),(16,76),(16,104),(16,108),(20,32),(28,32),(32,68),(32,76),(32,84),(32,92),(48,68),(48,72),(48,76)]) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma dirty_3 : dirtyFor (0,254,[(4,32),(4,48),(4,160),(4,176),(6,32),(8,16),(8,18),(8,48),(8,50),(8,144),(8,146),(8,176),(8,178),(12,16),(12,32),(12,48),(12,144),(12,160),(12,176),(14,32),(16,40),(16,44),(16,72),(16,76),(16,104),(16,108),(18,40),(20,32),(22,32),(28,32),(30,32),(32,68),(32,70),(32,76),(32,78),(32,84),(32,86),(32,92),(32,94),(48,68),(48,72),(48,76)]) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma dirty_4 : dirtyFor (1,248,[(16,128),(16,160),(16,192),(16,224),(24,128),(24,160),(64,128),(64,144),(64,160),(64,176),(72,128),(72,160),(80,128),(80,160),(88,128),(88,160)]) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma dirty_5 : dirtyFor (1,249,[(16,128),(16,160),(16,192),(16,224),(17,128),(17,192),(24,128),(24,160),(25,128),(64,128),(64,129),(64,144),(64,145),(64,160),(64,161),(64,176),(64,177),(65,128),(72,128),(72,160),(73,128),(80,128),(80,160),(81,128),(88,128),(88,160),(89,128)]) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma dirty_6 : dirtyFor (1,252,[(16,128),(16,132),(16,160),(16,164),(16,192),(16,196),(16,224),(16,228),(20,128),(24,128),(24,160),(28,128),(64,128),(64,144),(64,160),(64,176),(68,128),(68,144),(72,128),(72,160),(76,128),(80,128),(80,160),(84,128),(88,128),(88,160),(92,128)]) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma dirty_7 : dirtyFor (1,253,[(16,128),(16,132),(16,160),(16,164),(16,192),(16,196),(16,224),(16,228),(17,128),(17,192),(20,128),(21,128),(24,128),(24,160),(25,128),(28,128),(29,128),(64,128),(64,129),(64,144),(64,145),(64,160),(64,161),(64,176),(64,177),(65,128),(68,128),(68,144),(69,128),(72,128),(72,160),(73,128),(76,128),(77,128),(80,128),(80,160),(81,128),(84,128),(85,128),(88,128),(88,160),(89,128),(92,128),(93,128)]) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma dirty_8 : dirtyFor (2,248,[(8,64),(8,96),(8,192),(8,224),(24,64),(24,96),(40,64),(56,64)]) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma dirty_9 : dirtyFor (2,249,[(1,32),(1,96),(1,160),(1,224),(8,64),(8,96),(8,192),(8,224),(9,32),(9,64),(9,96),(9,160),(9,192),(9,224),(17,32),(17,96),(24,64),(24,96),(25,32),(25,64),(25,96),(32,65),(32,73),(32,81),(32,89),(40,64),(41,64),(56,64),(57,64)]) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma dirty_10 : dirtyFor (2,250,[(8,64),(8,66),(8,96),(8,98),(8,192),(8,194),(8,224),(8,226),(24,64),(24,96),(40,64),(40,66),(56,64)]) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma dirty_11 : dirtyFor (2,251,[(1,32),(1,96),(1,160),(1,224),(3,32),(8,64),(8,66),(8,96),(8,98),(8,192),(8,194),(8,224),(8,226),(9,32),(9,64),(9,96),(9,160),(9,192),(9,224),(11,32),(17,32),(17,96),(19,32),(24,64),(24,96),(25,32),(25,64),(25,96),(27,32),(32,65),(32,67),(32,73),(32,75),(32,81),(32,83),(32,89),(32,91),(40,64),(40,66),(41,64),(56,64),(57,64)]) = true := by decide +kernel

lemma dirty_complete_checked : dirtyComplete = true := by
  simp only [dirtyComplete, dirtyData, List.all_cons, List.all_nil,
    dirty_0, dirty_1, dirty_2, dirty_3, dirty_4, dirty_5, dirty_6, dirty_7, dirty_8, dirty_9, dirty_10, dirty_11, Bool.and_true]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_complete_checked : cleanComplete = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_0 : cleanCoverFor (0,0) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_1 : cleanCoverFor (1,64) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_2 : cleanCoverFor (1,128) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_3 : cleanCoverFor (1,192) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_4 : cleanCoverFor (2,8) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_5 : cleanCoverFor (2,32) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_6 : cleanCoverFor (2,40) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_7 : cleanCoverFor (4,16) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_8 : cleanCoverFor (4,128) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_9 : cleanCoverFor (4,144) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_10 : cleanCoverFor (5,128) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_11 : cleanCoverFor (8,32) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_12 : cleanCoverFor (8,34) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_13 : cleanCoverFor (8,128) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_14 : cleanCoverFor (8,130) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_15 : cleanCoverFor (8,160) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_16 : cleanCoverFor (8,162) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_17 : cleanCoverFor (9,128) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_18 : cleanCoverFor (10,32) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_19 : cleanCoverFor (12,128) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_20 : cleanCoverFor (13,128) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_21 : cleanCoverFor (16,32) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_22 : cleanCoverFor (16,36) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_23 : cleanCoverFor (16,64) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_24 : cleanCoverFor (16,68) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_25 : cleanCoverFor (16,96) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_26 : cleanCoverFor (16,100) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_27 : cleanCoverFor (17,64) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_28 : cleanCoverFor (18,32) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_29 : cleanCoverFor (24,32) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_30 : cleanCoverFor (26,32) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_31 : cleanCoverFor (32,64) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_32 : cleanCoverFor (32,66) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_33 : cleanCoverFor (32,72) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_34 : cleanCoverFor (32,74) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_35 : cleanCoverFor (32,80) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_36 : cleanCoverFor (32,82) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_37 : cleanCoverFor (32,88) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_38 : cleanCoverFor (32,90) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_39 : cleanCoverFor (33,64) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_40 : cleanCoverFor (48,64) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma clean_cover_41 : cleanCoverFor (49,64) = true := by decide +kernel

lemma clean_cover_complete_checked : cleanCoverComplete = true := by
  simp only [cleanCoverComplete, cleanRects, List.all_cons, List.all_nil,
    clean_cover_0, clean_cover_1, clean_cover_2, clean_cover_3, clean_cover_4, clean_cover_5, clean_cover_6, clean_cover_7, clean_cover_8, clean_cover_9, clean_cover_10, clean_cover_11, clean_cover_12, clean_cover_13, clean_cover_14, clean_cover_15, clean_cover_16, clean_cover_17, clean_cover_18, clean_cover_19, clean_cover_20, clean_cover_21, clean_cover_22, clean_cover_23, clean_cover_24, clean_cover_25, clean_cover_26, clean_cover_27, clean_cover_28, clean_cover_29, clean_cover_30, clean_cover_31, clean_cover_32, clean_cover_33, clean_cover_34, clean_cover_35, clean_cover_36, clean_cover_37, clean_cover_38, clean_cover_39, clean_cover_40, clean_cover_41, Bool.and_true]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma orders_checked : orderComplete = true ∧ casesCorrect = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma coverage_0 : caseCovered (0,5,11) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma coverage_1 : caseCovered (0,9,7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma coverage_2 : caseCovered (4,1,11) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma coverage_3 : caseCovered (4,10,3) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma coverage_4 : caseCovered (8,2,7) = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma coverage_5 : caseCovered (8,6,3) = true := by decide +kernel

lemma coverage_checked : coverageCheck = true := by
  simp only [coverageCheck, caseIndices, List.all_cons, List.all_nil, coverage_0, coverage_1, coverage_2, coverage_3, coverage_4, coverage_5, Bool.and_true]

lemma finite_certificate :
    adjacencyCheck = true ∧ dirtyComplete = true ∧ cleanComplete = true ∧
    cleanCoverComplete = true ∧ orderComplete = true ∧ casesCorrect = true ∧
    coverageCheck = true ∧ families.all familyImpossible = true := by
  exact ⟨adjacency_checked, dirty_complete_checked, clean_complete_checked,
    clean_cover_complete_checked, orders_checked.1, orders_checked.2,
    coverage_checked, families_impossible⟩

end R3Finite


namespace R3Local

def atoms : List Nat := [1,2,4,8,16,32,64,128]

def distinct : List Nat → Bool
  | [] => true
  | v :: rest => !rest.contains v && distinct rest

def properSplit (paid : List Nat) (v : Nat) : Bool :=
  let available := atoms ++ paid
  available.any (fun a => a != v &&
    available.any (fun b => b != v && a ||| b == v))

def helps (required : List Nat) (v extra : Nat) : Bool :=
  !required.contains extra && extra != v &&
    (atoms ++ required).any (fun t => t != v && extra ||| t == v)

def certificateCheck (d : List Nat × Nat × Nat) : Bool :=
  let required := d.1
  let pivot := d.2.1
  let other := d.2.2
  distinct required &&
  required.all (fun v => decide (v < 256) && (v &&& (v - 1) != 0)) &&
  required.contains pivot && !properSplit required pivot &&
  (if required.length == 5 then other == 0 else
    required.length == 4 &&
    (if other == 0 then
      (List.range 256).all (fun extra =>
        !helps required pivot extra || !properSplit required extra)
    else
      required.contains other && !properSplit required other &&
      (List.range 256).all (fun extra =>
        !helps required pivot extra || !helps required other extra)))

def certificates : List (List Nat × Nat × Nat) := [
  ([5,40,41,176,228],176,0),
  ([5,40,44,177,224],177,0),
  ([5,40,57,164,176],57,0),
  ([5,40,57,176,228],57,0),
  ([5,40,108,161,224],108,0),
  ([5,40,108,177,224],108,0),
  ([9,18,40,144,224],224,0),
  ([9,18,40,176,224],176,0),
  ([9,18,66,144,224],224,0),
  ([9,18,74,144,224],74,0),
  ([9,18,82,144,224],224,0),
  ([9,18,90,144,192],90,0),
  ([9,18,90,144,224],90,0),
  ([9,18,144,176,224],224,0),
  ([9,40,68,144,224],224,0),
  ([9,40,144,160,177],177,0),
  ([9,40,144,176,224],224,0),
  ([9,40,144,177,224],177,0),
  ([9,50,66,144,224],50,0),
  ([9,50,74,144,224],50,0),
  ([9,50,82,144,192],50,0),
  ([9,50,82,144,224],50,0),
  ([9,50,90,144,192],50,0),
  ([9,50,90,144,224],50,0),
  ([9,66,144,146,224],224,0),
  ([9,66,144,178,224],178,0),
  ([9,68,82,144,224],82,0),
  ([9,68,90,144,192],90,0),
  ([9,68,90,144,224],90,0),
  ([9,74,144,146,224],74,0),
  ([9,74,144,178,224],74,0),
  ([9,82,144,146,224],82,0),
  ([9,82,144,178,192],82,0),
  ([9,82,144,178,224],82,0),
  ([9,90,144,146,192],90,0),
  ([9,90,144,146,224],90,0),
  ([9,90,144,178,192],90,0),
  ([9,90,144,178,224],90,0),
  ([12,17,40,176,192],176,0),
  ([12,17,82,176,192],82,0),
  ([12,17,90,144,192],90,0),
  ([12,17,90,176,192],90,0),
  ([12,18,66,176,192],176,0),
  ([12,18,98,176,192],98,0),
  ([12,18,176,192,194],176,0),
  ([12,18,176,192,226],176,0),
  ([12,26,66,176,192],26,0),
  ([12,26,98,176,192],26,0),
  ([12,26,176,192,194],26,0),
  ([12,26,176,192,226],26,0),
  ([12,40,66,176,192],176,0),
  ([12,40,66,176,224],176,0),
  ([12,40,160,192,228],228,0),
  ([12,40,176,192,224],176,0),
  ([12,40,176,192,228],176,0),
  ([12,66,82,176,192],176,0),
  ([12,66,90,144,192],90,0),
  ([12,66,90,176,192],90,0),
  ([12,66,176,192,224],176,0),
  ([12,82,98,144,192],82,0),
  ([12,82,98,176,192],82,0),
  ([12,82,144,192,226],82,0),
  ([12,82,176,192,194],82,0),
  ([12,82,176,192,226],82,0),
  ([12,90,98,144,192],90,0),
  ([12,90,98,176,192],90,0),
  ([12,90,144,192,194],90,0),
  ([12,90,144,192,226],90,0),
  ([12,90,176,192,194],90,0),
  ([12,90,176,192,226],90,0),
  ([13,40,41,48,228],13,0),
  ([13,40,41,176,228],13,0),
  ([13,40,44,96,177],13,0),
  ([13,40,44,177,224],13,0),
  ([13,40,48,57,164],13,0),
  ([13,40,48,57,228],13,0),
  ([13,40,57,164,176],13,0),
  ([13,40,57,176,228],13,0),
  ([13,40,96,108,161],13,0),
  ([13,40,96,108,177],13,0),
  ([13,40,108,161,224],13,0),
  ([13,40,108,177,224],13,0),
  ([17,34,82,176,192],82,0),
  ([17,34,83,144,192],83,0),
  ([17,34,90,176,192],90,0),
  ([17,34,91,144,192],91,0),
  ([17,40,88,176,192],88,0),
  ([17,40,89,144,192],89,0),
  ([17,40,90,176,192],90,0),
  ([17,40,91,144,192],91,0),
  ([17,40,92,144,192],92,0),
  ([17,66,90,144,192],90,0),
  ([17,82,98,144,192],82,0),
  ([17,82,144,192,226],82,0),
  ([17,82,162,176,192],82,0),
  ([17,82,176,192,224],82,0),
  ([17,83,144,162,192],83,0),
  ([17,83,144,176,192],83,0),
  ([17,90,98,144,192],90,0),
  ([17,90,130,176,192],90,0),
  ([17,90,144,192,194],90,0),
  ([17,90,144,192,226],90,0),
  ([17,90,162,176,192],90,0),
  ([17,90,176,192],90,176),
  ([17,90,176,192,224],90,0),
  ([17,91,130,144,192],91,0),
  ([17,91,144,162,192],91,0),
  ([17,91,144,176,192],91,0),
  ([17,91,144,192],91,0),
  ([18,68,90,144,192],90,0),
  ([18,144,176,178,224],224,0),
  ([18,176,192,226],176,226),
  ([19,144,176,178,192],19,0),
  ([21,33,40,108,224],21,0),
  ([21,36,40,57,176],21,0),
  ([21,40,41,100,176],21,0),
  ([21,40,44,49,224],21,0),
  ([21,40,49,108,224],21,0),
  ([21,40,57,100,176],21,0),
  ([22,144,176,192,226],22,0),
  ([26,144,146,176,224],26,0),
  ([26,144,176,178,224],26,0),
  ([26,176,192,194],26,176),
  ([26,176,192,226],26,176),
  ([27,144,146,176,192],27,0),
  ([27,144,176,178,192],27,0),
  ([29,33,40,96,108],29,0),
  ([29,33,40,108,224],29,0),
  ([29,36,40,48,57],29,0),
  ([29,36,40,57,176],29,0),
  ([29,40,41,48,100],29,0),
  ([29,40,41,100,176],29,0),
  ([29,40,44,49,96],29,0),
  ([29,40,44,49,224],29,0),
  ([29,40,48,57,100],29,0),
  ([29,40,49,96,108],29,0),
  ([29,40,49,108,224],29,0),
  ([29,40,57,100,176],29,0),
  ([30,144,176,192,194],30,0),
  ([30,144,176,192,226],30,0),
  ([33,40,69,108,224],69,0),
  ([33,40,77,96,108],77,0),
  ([33,40,77,108,224],77,0),
  ([33,40,85,108,224],85,0),
  ([33,40,93,96,108],93,0),
  ([33,40,93,108,224],93,0),
  ([34,68,82,144,224],82,0),
  ([34,68,86,144,192],86,0),
  ([34,68,90,144,224],90,0),
  ([34,68,94,144,192],94,0),
  ([36,40,48,57,77],57,0),
  ([36,40,48,57,93],57,0),
  ([36,40,57,69,176],57,0),
  ([36,40,57,77,176],57,0),
  ([36,40,57,85,176],57,0),
  ([36,40,57,93,176],57,0),
  ([40,41,48,77,100],77,0),
  ([40,41,48,93,100],93,0),
  ([40,41,69,100,176],69,0),
  ([40,41,77,100,176],77,0),
  ([40,41,85,100,176],85,0),
  ([40,41,93,100,176],93,0),
  ([40,44,49,69,224],49,0),
  ([40,44,49,77,96],49,0),
  ([40,44,49,77,224],49,0),
  ([40,44,49,85,224],49,0),
  ([40,44,49,93,96],49,0),
  ([40,44,49,93,224],49,0),
  ([40,48,57,77,100],57,0),
  ([40,48,57,93,100],57,0),
  ([40,49,69,108,224],49,0),
  ([40,49,77,96,108],49,0),
  ([40,49,77,108,224],49,0),
  ([40,49,85,108,224],49,0),
  ([40,49,93,96,108],49,0),
  ([40,49,93,108,224],49,0),
  ([40,57,69,100,176],57,0),
  ([40,57,77,100,176],57,0),
  ([40,57,85,100,176],57,0),
  ([40,57,93,100,176],57,0),
  ([40,68,88,144,224],88,0),
  ([40,68,89,144,192],89,0),
  ([40,68,90,144,224],90,0),
  ([40,68,92,144,192],92,0),
  ([40,68,94,144,192],94,0),
  ([50,68,82,144,192],50,0),
  ([50,68,90,144,192],50,0),
  ([66,144,178,224],178,224),
  ([66,176,192,224,226],176,0),
  ([67,144,178,192,224],67,0),
  ([68,82,144,162,224],82,0),
  ([68,82,144,176,224],82,0),
  ([68,82,144,178,192],82,0),
  ([68,86,144,162,192],86,0),
  ([68,86,144,192,224],86,0),
  ([68,90,130,144,224],90,0),
  ([68,90,144,146,192],90,0),
  ([68,90,144,162,224],90,0),
  ([68,90,144,176,224],90,0),
  ([68,90,144,178,192],90,0),
  ([68,90,144,224],90,224),
  ([68,94,130,144,192],94,0),
  ([68,94,144,162,192],94,0),
  ([68,94,144,192],94,0),
  ([68,94,144,192,224],94,0),
  ([70,144,192,224,226],70,0),
  ([74,144,146,224],74,224),
  ([74,144,178,224],74,178),
  ([74,176,192,194,224],74,0),
  ([74,176,192,224,226],74,0),
  ([75,144,146,192,224],75,0),
  ([75,144,178,192,224],75,0),
  ([78,144,192,194,224],78,0),
  ([78,144,192,224,226],78,0),
  ([82,144,176,178,224],82,0),
  ([82,144,176,192,226],82,0),
  ([82,144,178,192,224],82,0),
  ([82,144,178,224],82,178),
  ([82,176,192,224,226],82,0),
  ([82,176,192,226],82,176),
  ([83,144,176,178,192],83,0),
  ([83,144,178,192],83,178),
  ([83,144,178,192,224],83,0),
  ([86,144,176,192,226],86,0),
  ([86,144,192,224,226],86,0),
  ([86,144,192,226],86,226),
  ([90,144,146,176,224],90,0),
  ([90,144,146,192,224],90,0),
  ([90,144,146,224],90,224),
  ([90,144,176,178,224],90,0),
  ([90,144,176,192,194],90,0),
  ([90,144,176,192,226],90,0),
  ([90,144,178,192,224],90,0),
  ([90,144,178,224],90,178),
  ([90,176,192,194],90,176),
  ([90,176,192,194,224],90,0),
  ([90,176,192,224,226],90,0),
  ([90,176,192,226],90,176),
  ([91,144,146,176,192],91,0),
  ([91,144,146,192],91,0),
  ([91,144,146,192,224],91,0),
  ([91,144,176,178,192],91,0),
  ([91,144,178,192],91,178),
  ([91,144,178,192,224],91,0),
  ([94,144,176,192,194],94,0),
  ([94,144,176,192,226],94,0),
  ([94,144,192,194],94,0),
  ([94,144,192,194,224],94,0),
  ([94,144,192,224,226],94,0),
  ([94,144,192,226],94,226)
]

def allChecked : Bool := certificates.all certificateCheck

def covers (families : List (List Nat)) : Bool :=
  families.all (fun required => certificates.any (fun d => d.1 == required))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma all_checked : allChecked = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma covers_r3 : covers R3Finite.families = true := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
lemma exact_families : certificates.map Prod.fst = R3Finite.families := by decide +kernel

end R3Local

namespace R3Finite
lemma covered_family_impossible
    (hcoverage : coverageCheck = true)
    (hfamilies : families.all familyImpossible = true)
    {c : Nat × Nat × Nat} {a b d : Rect} {extra : List Nat}
    (hc : c ∈ caseIndices)
    (ha : a ∈ (getData c.1).2.2)
    (hb : b ∈ (getData c.2.1).2.2)
    (hd : d ∈ (getData c.2.2).2.2)
    (hsmall : (mergeReq (reqRect a) (mergeReq (reqRect b) (reqRect d))).length ≤ 5)
    (hextra : extra ∈ cleanCoverTable (2047 - (coverage a ||| coverage b ||| coverage d)))
    (hfull : (mergeReq (mergeReq (reqRect a) (mergeReq (reqRect b) (reqRect d))) extra).length ≤ 5) :
    familyImpossible (mergeReq (mergeReq (reqRect a) (mergeReq (reqRect b) (reqRect d))) extra) = true := by
  have hcase := (List.all_eq_true.mp hcoverage) c hc
  unfold caseCovered at hcase
  have hrect := (List.all_eq_true.mp ((List.all_eq_true.mp
    ((List.all_eq_true.mp hcase) a ha)) b hb)) d hd
  dsimp only at hrect
  have hs : decide (5 < (mergeReq (reqRect a) (mergeReq (reqRect b) (reqRect d))).length) = false := by
    simp [Nat.not_lt_of_ge hsmall]
  rw [hs, Bool.false_or] at hrect
  have hex := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hrect).2) extra hextra
  have hf : decide (5 < (mergeReq (mergeReq (reqRect a)
      (mergeReq (reqRect b) (reqRect d))) extra).length) = false := by
    simp [Nat.not_lt_of_ge hfull]
  rw [hf, Bool.false_or] at hex
  exact (List.all_eq_true.mp hfamilies) _ (List.contains_iff_mem.mp hex)

end R3Finite


namespace R3LocalSoundness

open SingletonUnionTransport

lemma properSplit_iff (required : List Nat) (v : Nat) :
    R3Local.properSplit required v = true ↔
      ProperUnion (R3Local.atoms.toFinset ∪ required.toFinset) v := by
  simp only [R3Local.properSplit, List.any_eq_true, Bool.and_eq_true_iff,
    bne_iff_ne, beq_iff_eq, List.mem_append]
  constructor
  · rintro ⟨a, ha, hav, b, hb, hbv, he⟩
    exact ⟨a, by simpa using ha, b, by simpa using hb, hav, hbv, he.symm⟩
  · rintro ⟨a, ha, b, hb, hav, hbv, he⟩
    exact ⟨a, by simpa using ha, hav, b, by simpa using hb, hbv, he.symm⟩

lemma helps_iff (required : List Nat) (v extra : Nat) :
    R3Local.helps required v extra = true ↔
      extra ∉ required ∧ extra ≠ v ∧
        ∃ t ∈ R3Local.atoms.toFinset ∪ required.toFinset,
          t ≠ v ∧ v = extra ||| t := by
  simp only [R3Local.helps, Bool.and_eq_true_iff,
    bne_iff_ne, List.any_eq_true, beq_iff_eq,
    List.mem_append]
  constructor
  · rintro ⟨⟨hs, hsv⟩, t, ht, htv, he⟩
    exact ⟨by simpa using hs, hsv, t, by simpa using ht, htv, he.symm⟩
  · rintro ⟨hs, hsv, t, ht, htv, he⟩
    exact ⟨⟨by simpa using hs, hsv⟩, t, by simpa using ht, htv, he.symm⟩

lemma distinct_nodup (required : List Nat)
    (h : R3Local.distinct required = true) : required.Nodup := by
  induction required with
  | nil => simp
  | cons v rest ih =>
    simp only [R3Local.distinct, Bool.and_eq_true_iff] at h
    exact List.nodup_cons.mpr ⟨by simpa using h.1, ih h.2⟩

lemma helps_of_proper_insert (required : List Nat) (v extra : Nat)
    (hv : v ∈ required) (hextra : extra ∉ required)
    (hblocked : ¬ ProperUnion (R3Local.atoms.toFinset ∪ required.toFinset) v)
    (hproper : ProperUnion (R3Local.atoms.toFinset ∪ insert extra required.toFinset) v) :
    R3Local.helps required v extra = true := by
  have hne : extra ≠ v := by
    intro he
    exact hextra (he ▸ hv)
  have hm : ∀ x ∈ R3Local.atoms.toFinset ∪ insert extra required.toFinset,
      x = extra ∨ x ∈ R3Local.atoms.toFinset ∪ required.toFinset := by
    intro x hx
    rcases Finset.mem_union.mp hx with ha | hp
    · exact Or.inr (Finset.mem_union_left _ ha)
    · rcases Finset.mem_insert.mp hp with he | hr
      · exact Or.inl he
      · exact Or.inr (Finset.mem_union_right _ hr)
  obtain ⟨a, ha, b, hb, hav, hbv, he⟩ := hproper
  rcases hm a ha with hae | ha
  · subst a
    rcases hm b hb with hbe | hb
    · subst b
      have hve : v = extra := by simpa using he
      exact False.elim (hav hve.symm)
    · exact (helps_iff required v extra).mpr ⟨hextra, hne, b, hb, hbv, he⟩
  · rcases hm b hb with hbe | hb
    · subst b
      apply (helps_iff required v extra).mpr
      exact ⟨hextra, hne, a, ha, hav, by simpa only [Nat.or_comm] using he⟩
    · exact False.elim (hblocked ⟨a, ha, b, hb, hav, hbv, he⟩)

lemma helps_bound (required : List Nat) (v extra : Nat)
    (h : R3Local.helps required v extra = true) (hv : v < 256) : extra < 256 := by
  obtain ⟨_, _, t, _, _, he⟩ := (helps_iff required v extra).mp h
  have hle : extra ≤ v := he ▸ Nat.left_le_or
  exact hle.trans_lt hv

lemma proper_extra_remove (required : List Nat) (extra : Nat)
    (h : ProperUnion (R3Local.atoms.toFinset ∪ insert extra required.toFinset) extra) :
    ProperUnion (R3Local.atoms.toFinset ∪ required.toFinset) extra := by
  obtain ⟨a, ha, b, hb, hav, hbv, he⟩ := h
  have hm : ∀ x, x ≠ extra →
      x ∈ R3Local.atoms.toFinset ∪ insert extra required.toFinset →
      x ∈ R3Local.atoms.toFinset ∪ required.toFinset := by
    intro x hne hx
    simpa [hne] using hx
  exact ⟨a, hm a hav ha, b, hm b hbv hb, hav, hbv, he⟩

lemma eq_or_one_extra (required values : Finset Nat)
    (hsub : required ⊆ values) (hcard : values.card ≤ required.card + 1) :
    values = required ∨ ∃ extra, extra ∉ required ∧ values = insert extra required := by
  classical
  by_cases hs : values ⊆ required
  · exact Or.inl (Finset.Subset.antisymm hs hsub)
  · change ¬ ∀ v, v ∈ values → v ∈ required at hs
    obtain ⟨extra, he⟩ := not_forall.mp hs
    obtain ⟨hem, hen⟩ := not_imp.mp he
    have hi : insert extra required ⊆ values := by
      intro v hm
      rcases Finset.mem_insert.mp hm with rfl | hm
      · exact hem
      · exact hsub hm
    have hc : values.card ≤ (insert extra required).card := by
      simpa only [Finset.card_insert_of_notMem hen] using hcard
    exact Or.inr ⟨extra, hen, (Finset.eq_of_subset_of_card_le hi hc).symm⟩

lemma not_proper_of_false (required : List Nat) (v : Nat)
    (h : R3Local.properSplit required v = false) :
    ¬ ProperUnion (R3Local.atoms.toFinset ∪ required.toFinset) v := by
  intro hp
  have ht := (properSplit_iff required v).mpr hp
  simp [h] at ht

lemma certificate_sound {d : List Nat × Nat × Nat}
    (hc : R3Local.certificateCheck d = true) (P : Finset Nat)
    (hr : d.1.toFinset ⊆ P) (hcard : P.card ≤ 5)
    (hproper : ∀ v ∈ P, ProperUnion (R3Local.atoms.toFinset ∪ P) v) : False := by
  classical
  rcases d with ⟨required, pivot, other⟩
  change required.toFinset ⊆ P at hr
  simp only [R3Local.certificateCheck, Bool.and_eq_true_iff] at hc
  rcases hc with ⟨⟨⟨⟨hdis, hbound⟩, hpivot⟩, hblocked⟩, hcases⟩
  have hp : pivot ∈ required := List.contains_iff_mem.mp hpivot
  have hbf : R3Local.properSplit required pivot = false := by simpa using hblocked
  have hbp := not_proper_of_false required pivot hbf
  have hnd := distinct_nodup required hdis
  have hrcard : required.toFinset.card = required.length :=
    List.toFinset_card_of_nodup hnd
  have hpP : pivot ∈ P := hr (List.mem_toFinset.mpr hp)
  have hpbound : pivot < 256 := by
    have hb := (List.all_eq_true.mp hbound) pivot hp
    exact of_decide_eq_true (Bool.and_eq_true_iff.mp hb).1
  by_cases h5 : required.length = 5
  · have heP : P = required.toFinset :=
      (Finset.eq_of_subset_of_card_le hr (by omega)).symm
    apply hbp
    simpa only [heP] using hproper pivot hpP
  · have h4 : required.length = 4 := by
      by_cases h4 : required.length = 4
      · exact h4
      · simp [h5, h4] at hcases
    rcases eq_or_one_extra required.toFinset P hr (by omega) with heP | ⟨extra, hen, heP⟩
    · apply hbp
      simpa only [heP] using hproper pivot hpP
    · have henList : extra ∉ required := by simpa using hen
      have hpInsert : ProperUnion
          (R3Local.atoms.toFinset ∪ insert extra required.toFinset) pivot := by
        simpa only [heP] using hproper pivot hpP
      have hhelp := helps_of_proper_insert required pivot extra hp henList hbp hpInsert
      have hextraBound := helps_bound required pivot extra hhelp hpbound
      by_cases hother : other = 0
      · have hall : (List.range 256).all (fun s =>
            !R3Local.helps required pivot s || !R3Local.properSplit required s) = true := by
          simpa [h5, h4, hother] using hcases
        have heval := (List.all_eq_true.mp hall) extra (List.mem_range.mpr hextraBound)
        have hesplit : R3Local.properSplit required extra = false := by
          simpa [hhelp] using heval
        have heMem : extra ∈ P := by simp [heP]
        have heInsert : ProperUnion
            (R3Local.atoms.toFinset ∪ insert extra required.toFinset) extra := by
          simpa only [heP] using hproper extra heMem
        exact not_proper_of_false required extra hesplit
          (proper_extra_remove required extra heInsert)
      · have hbranch : (required.contains other && !R3Local.properSplit required other &&
            (List.range 256).all (fun s =>
              !R3Local.helps required pivot s || !R3Local.helps required other s)) = true := by
          simpa [h5, h4, hother] using hcases
        have hb := Bool.and_eq_true_iff.mp hbranch
        have ho := Bool.and_eq_true_iff.mp hb.1
        have hom : other ∈ required := List.contains_iff_mem.mp ho.1
        have hosplit : R3Local.properSplit required other = false := by simpa using ho.2
        have hob := not_proper_of_false required other hosplit
        have hoInsert : ProperUnion
            (R3Local.atoms.toFinset ∪ insert extra required.toFinset) other := by
          simpa only [heP] using hproper other (hr (List.mem_toFinset.mpr hom))
        have hohelp := helps_of_proper_insert required other extra hom henList hob hoInsert
        have heval := (List.all_eq_true.mp hb.2) extra (List.mem_range.mpr hextraBound)
        simp [hhelp, hohelp] at heval

end R3LocalSoundness


namespace R3NoUnion

open SingletonUnionTransport

def freeAtoms : Finset Nat := insert 0 R3Local.atoms.toFinset

lemma proper_without_zero {s : Finset Nat} {v : Nat}
    (h : ProperUnion (insert 0 s) v) : ProperUnion s v := by
  obtain ⟨a, ha, b, hb, hav, hbv, he⟩ := h
  have ha0 : a ≠ 0 := by
    intro hz
    subst a
    exact hbv (by simpa using he.symm)
  have hb0 : b ≠ 0 := by
    intro hz
    subst b
    exact hav (by simpa using he.symm)
  exact ⟨a, (Finset.mem_insert.mp ha).resolve_left ha0,
    b, (Finset.mem_insert.mp hb).resolve_left hb0, hav, hbv, he⟩

lemma trace_paid_proper {n : Nat} (out : Fin n → Nat)
    (ht : UnionTrace freeAtoms out) (v : Nat) (hv : v ∈ paid freeAtoms out) :
    ProperUnion (R3Local.atoms.toFinset ∪ paid freeAtoms out) v := by
  apply proper_without_zero
  simpa only [freeAtoms, Finset.insert_union] using paid_proper_union freeAtoms out ht v hv

lemma family_certificate {required : List Nat} (hr : required ∈ R3Finite.families) :
    ∃ pivot other, R3Local.certificateCheck (required, pivot, other) = true := by
  have hm : required ∈ R3Local.certificates.map Prod.fst := by
    rw [R3Local.exact_families]
    exact hr
  obtain ⟨d, hd, he⟩ := List.mem_map.mp hm
  rcases d with ⟨r, pivot, other⟩
  change r = required at he
  subst required
  exact ⟨pivot, other, (List.all_eq_true.mp R3Local.all_checked) _ hd⟩

end R3NoUnion

namespace R3Finite

lemma covered_family_mem
    (hcoverage : coverageCheck = true)
    {c : Nat × Nat × Nat} {a b d : Rect} {extra : List Nat}
    (hc : c ∈ caseIndices)
    (ha : a ∈ (getData c.1).2.2)
    (hb : b ∈ (getData c.2.1).2.2)
    (hd : d ∈ (getData c.2.2).2.2)
    (hsmall : (mergeReq (reqRect a) (mergeReq (reqRect b) (reqRect d))).length ≤ 5)
    (hextra : extra ∈ cleanCoverTable (2047 - (coverage a ||| coverage b ||| coverage d)))
    (hfull : (mergeReq (mergeReq (reqRect a) (mergeReq (reqRect b) (reqRect d))) extra).length ≤ 5) :
    mergeReq (mergeReq (reqRect a) (mergeReq (reqRect b) (reqRect d))) extra ∈ families := by
  have hcase := (List.all_eq_true.mp hcoverage) c hc
  unfold caseCovered at hcase
  have hrect := (List.all_eq_true.mp ((List.all_eq_true.mp
    ((List.all_eq_true.mp hcase) a ha)) b hb)) d hd
  dsimp only at hrect
  have hs : decide (5 < (mergeReq (reqRect a) (mergeReq (reqRect b) (reqRect d))).length) = false := by
    simp [Nat.not_lt_of_ge hsmall]
  rw [hs, Bool.false_or] at hrect
  have hex := (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hrect).2) extra hextra
  have hf : decide (5 < (mergeReq (mergeReq (reqRect a)
      (mergeReq (reqRect b) (reqRect d))) extra).length) = false := by
    simp [Nat.not_lt_of_ge hfull]
  rw [hf, Bool.false_or] at hex
  exact List.contains_iff_mem.mp hex

lemma reachable_of_dirty {c : Nat × Nat × Nat} {a b d : Rect}
    (hc : c ∈ caseIndices)
    (ha : a ∈ (getData c.1).2.2)
    (hb : b ∈ (getData c.2.1).2.2)
    (hd : d ∈ (getData c.2.2).2.2)
    (hsmall : (mergeReq (reqRect a) (mergeReq (reqRect b) (reqRect d))).length ≤ 5) :
    reachableMissing (2047 - (coverage a ||| coverage b ||| coverage d)) = true := by
  have hcase := (List.all_eq_true.mp coverage_checked) c hc
  unfold caseCovered at hcase
  have hrect := (List.all_eq_true.mp ((List.all_eq_true.mp
    ((List.all_eq_true.mp hcase) a ha)) b hb)) d hd
  dsimp only at hrect
  have hs : decide (5 < (mergeReq (reqRect a) (mergeReq (reqRect b) (reqRect d))).length) = false := by
    simp [Nat.not_lt_of_ge hsmall]
  rw [hs, Bool.false_or] at hrect
  exact (Bool.and_eq_true_iff.mp hrect).1

lemma clean_table_mem {a b : Rect} {need : Nat}
    (ha : a ∈ cleanRects) (hb : b ∈ cleanRects) (hn : need < 2048)
    (hr : reachableMissing need = true)
    (hcover : need &&& (coverage a ||| coverage b) = need) :
    mergeReq (reqRect a) (reqRect b) ∈ cleanCoverTable need := by
  have ha' := (List.all_eq_true.mp clean_cover_complete_checked) a ha
  unfold cleanCoverFor at ha'
  have hn' := (List.all_eq_true.mp ((List.all_eq_true.mp ha') b hb)) need (List.mem_range.mpr hn)
  have hmem : (cleanCoverTable need).contains (mergeReq (reqRect a) (reqRect b)) = true := by
    simpa [hr, hcover] using hn'
  exact List.contains_iff_mem.mp hmem

lemma rectangle_family_mem {c : Nat × Nat × Nat} {a b d e f : Rect}
    (hc : c ∈ caseIndices)
    (ha : a ∈ (getData c.1).2.2)
    (hb : b ∈ (getData c.2.1).2.2)
    (hd : d ∈ (getData c.2.2).2.2)
    (he : e ∈ cleanRects) (hf : f ∈ cleanRects)
    (hsmall : (mergeReq (reqRect a) (mergeReq (reqRect b) (reqRect d))).length ≤ 5)
    (hcover : (2047 - (coverage a ||| coverage b ||| coverage d)) &&&
      (coverage e ||| coverage f) = 2047 - (coverage a ||| coverage b ||| coverage d))
    (hfull : (mergeReq (mergeReq (reqRect a) (mergeReq (reqRect b) (reqRect d)))
      (mergeReq (reqRect e) (reqRect f))).length ≤ 5) :
    mergeReq (mergeReq (reqRect a) (mergeReq (reqRect b) (reqRect d)))
      (mergeReq (reqRect e) (reqRect f)) ∈ families := by
  apply covered_family_mem coverage_checked hc ha hb hd hsmall _ hfull
  apply clean_table_mem he hf _ (reachable_of_dirty hc ha hb hd hsmall) hcover
  exact Nat.lt_succ_of_le (Nat.sub_le _ _)

end R3Finite


namespace R3NoUnion

open SingletonUnionTransport

lemma family_no_trace {n : Nat} (out : Fin n → Nat) {required : List Nat}
    (hr : required ∈ R3Finite.families) (hn : n ≤ 5)
    (ht : UnionTrace freeAtoms out) (hp : required.toFinset ⊆ paid freeAtoms out) : False := by
  obtain ⟨pivot, other, hc⟩ := family_certificate hr
  apply R3LocalSoundness.certificate_sound hc (paid freeAtoms out) hp
  · exact (paid_card_le_length freeAtoms out).trans hn
  · exact trace_paid_proper out ht

lemma no_union_trace_for_family {required : List Nat} (hr : required ∈ R3Finite.families) :
    ¬ ∃ (n : Nat) (out : Fin n → Nat), n ≤ 5 ∧ UnionTrace freeAtoms out ∧
      required.toFinset ⊆ paid freeAtoms out := by
  rintro ⟨n, out, hn, ht, hp⟩
  exact family_no_trace out hr hn ht hp

lemma rectangle_no_trace {c : Nat × Nat × Nat} {a b d e f : R3Finite.Rect}
    (hc : c ∈ R3Finite.caseIndices)
    (ha : a ∈ (R3Finite.getData c.1).2.2)
    (hb : b ∈ (R3Finite.getData c.2.1).2.2)
    (hd : d ∈ (R3Finite.getData c.2.2).2.2)
    (he : e ∈ R3Finite.cleanRects) (hf : f ∈ R3Finite.cleanRects)
    (hsmall : (R3Finite.mergeReq (R3Finite.reqRect a)
      (R3Finite.mergeReq (R3Finite.reqRect b) (R3Finite.reqRect d))).length ≤ 5)
    (hcover : (2047 - (R3Finite.coverage a ||| R3Finite.coverage b ||| R3Finite.coverage d)) &&&
      (R3Finite.coverage e ||| R3Finite.coverage f) =
        2047 - (R3Finite.coverage a ||| R3Finite.coverage b ||| R3Finite.coverage d))
    (hfull : (R3Finite.mergeReq (R3Finite.mergeReq (R3Finite.reqRect a)
      (R3Finite.mergeReq (R3Finite.reqRect b) (R3Finite.reqRect d)))
        (R3Finite.mergeReq (R3Finite.reqRect e) (R3Finite.reqRect f))).length ≤ 5) :
    ¬ ∃ (n : Nat) (out : Fin n → Nat), n ≤ 5 ∧ UnionTrace freeAtoms out ∧
      (R3Finite.mergeReq (R3Finite.mergeReq (R3Finite.reqRect a)
        (R3Finite.mergeReq (R3Finite.reqRect b) (R3Finite.reqRect d)))
          (R3Finite.mergeReq (R3Finite.reqRect e) (R3Finite.reqRect f))).toFinset ⊆ paid freeAtoms out := by
  apply no_union_trace_for_family
  exact R3Finite.rectangle_family_mem hc ha hb hd he hf hsmall hcover hfull

end R3NoUnion

end PEqualNP.Outside.L_meta_9033_aux
