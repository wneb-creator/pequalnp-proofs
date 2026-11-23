import Mathlib
import PEqualNP.Defs

namespace Pilot5bMeta1020Linear

abbrev Instruction := List ℕ ⊕ (ℕ × ℕ)

def step (labels : ℕ → Bool) (w : List Bool) : Instruction → Bool
  | Sum.inl rs => (rs.map fun r => w.getD r false).any id
  | Sum.inr (a, r) => labels a && w.getD r false

def run (gs : List Instruction) (labels : ℕ → Bool) (y : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [step labels w g]) y

lemma run_cons (g : Instruction) (gs : List Instruction) (labels : ℕ → Bool)
    (y : List Bool) :
    run (g :: gs) labels y = run gs labels (y ++ [step labels y g]) := rfl

lemma run_append (gs hs : List Instruction) (labels : ℕ → Bool) (y : List Bool) :
    run (gs ++ hs) labels y = run hs labels (run gs labels y) := by
  simp [run, List.foldl_append]

lemma run_prefix (gs : List Instruction) (labels : ℕ → Bool) :
    ∀ y : List Bool, ∃ t, run gs labels y = y ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro y; exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    intro y
    obtain ⟨t, ht, hl⟩ := ih (y ++ [step labels y g])
    refine ⟨step labels y g :: t, ?_, by simp [hl]⟩
    rw [run_cons, ht]
    simp

lemma run_length (gs : List Instruction) (labels : ℕ → Bool) (y : List Bool) :
    (run gs labels y).length = y.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs labels y
  simp [ht, hl]

lemma run_getD_lt (gs : List Instruction) (labels : ℕ → Bool) (y : List Bool)
    (w : ℕ) (hw : w < y.length) :
    (run gs labels y).getD w false = y.getD w false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs labels y
  rw [ht, List.getD_append _ _ _ _ hw]

lemma run_getD_ge (gs : List Instruction) (labels : ℕ → Bool) (y : List Bool)
    (w : ℕ) (hw : y.length + gs.length ≤ w) :
    (run gs labels y).getD w false = false := by
  apply List.getD_eq_default
  simpa only [run_length] using hw

lemma run_snoc (gs : List Instruction) (g : Instruction) (labels : ℕ → Bool)
    (y : List Bool) :
    run (gs ++ [g]) labels y = run gs labels y ++ [step labels (run gs labels y) g] := by
  simp [run, List.foldl_append]

lemma snoc_read_old (gs : List Instruction) (g : Instruction) (labels : ℕ → Bool)
    (y : List Bool) (w : ℕ) (hw : w < y.length + gs.length) :
    (run (gs ++ [g]) labels y).getD w false = (run gs labels y).getD w false := by
  rw [run_snoc, List.getD_append _ _ _ _ (by simpa only [run_length] using hw)]

lemma snoc_read_new (gs : List Instruction) (g : Instruction) (labels : ℕ → Bool)
    (y : List Bool) :
    (run (gs ++ [g]) labels y).getD (y.length + gs.length) false =
      step labels (run gs labels y) g := by
  rw [run_snoc, List.getD_append_right _ _ _ _ (by simp [run_length])]
  simp [run_length]

def queryStep {n : ℕ} (labels : ℕ → Bool) (w : List (Finset (Fin n))) :
    Instruction → Finset (Fin n)
  | Sum.inl rs => rs.toFinset.biUnion fun r => w.getD r ∅
  | Sum.inr (a, r) => if labels a then w.getD r ∅ else ∅

def queryRun {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (w : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun w g => w ++ [queryStep labels w g]) w

noncomputable def hits {n : ℕ} (y : Fin n → Bool) (S : Finset (Fin n)) : Bool :=
  S.toList.any y

lemma hits_true {n : ℕ} (y : Fin n → Bool) (S : Finset (Fin n)) :
    hits y S = true ↔ ∃ l ∈ S, y l = true := by
  simp [hits]

@[simp] lemma hits_empty {n : ℕ} (y : Fin n → Bool) : hits y ∅ = false := by
  simp [hits]

@[simp] lemma hits_singleton {n : ℕ} (y : Fin n → Bool) (l : Fin n) :
    hits y {l} = y l := by
  apply Bool.eq_iff_iff.mpr
  simp [hits_true]

lemma map_hits_getD {n : ℕ} (y : Fin n → Bool)
    (w : List (Finset (Fin n))) (r : ℕ) :
    (w.map (hits y)).getD r false = hits y (w.getD r ∅) := by
  induction w generalizing r with
  | nil => simp
  | cons S w ih =>
    cases r with
    | zero => rfl
    | succ r => exact ih r

lemma hits_queryStep {n : ℕ} (labels : ℕ → Bool) (y : Fin n → Bool)
    (w : List (Finset (Fin n))) (g : Instruction) :
    hits y (queryStep labels w g) = step labels (w.map (hits y)) g := by
  apply Bool.eq_iff_iff.mpr
  cases g with
  | inl rs =>
    simp only [queryStep, step, hits_true, Finset.mem_biUnion,
      List.mem_toFinset, List.any_eq_true, List.mem_map, id_eq]
    constructor
    · rintro ⟨l, ⟨r, hr, hl⟩, hy⟩
      refine ⟨(w.map (hits y)).getD r false, ⟨r, hr, rfl⟩, ?_⟩
      rw [map_hits_getD]
      exact (hits_true y _).mpr ⟨l, hl, hy⟩
    · rintro ⟨b, ⟨r, hr, rfl⟩, hb⟩
      rw [map_hits_getD] at hb
      obtain ⟨l, hl, hy⟩ := (hits_true y _).mp hb
      exact ⟨l, ⟨r, hr, hl⟩, hy⟩
  | inr ar =>
    rcases ar with ⟨a, r⟩
    cases ha : labels a with
    | false => simp [queryStep, step, ha]
    | true =>
      change hits y (if labels a then w.getD r ∅ else ∅) = true ↔
        (labels a && (w.map (hits y)).getD r false) = true
      rw [ha]
      simp only [Bool.true_and, ite_true]
      rw [map_hits_getD]

lemma run_queries {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (y : Fin n → Bool) (w : List (Finset (Fin n))) :
    run gs labels (w.map (hits y)) = (queryRun gs labels w).map (hits y) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change run gs labels (w.map (hits y) ++ [step labels (w.map (hits y)) g]) =
      (queryRun gs labels (w ++ [queryStep labels w g])).map (hits y)
    rw [← hits_queryStep]
    simpa only [List.map_append, List.map_singleton] using ih (w ++ [queryStep labels w g])

def queries {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool) :
    List (Finset (Fin n)) :=
  queryRun gs labels (List.ofFn fun l : Fin n => {l})

lemma run_input_queries {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (y : Fin n → Bool) :
    run gs labels (List.ofFn y) = (queries gs labels).map (hits y) := by
  have h := run_queries gs labels y (List.ofFn fun l : Fin n => {l})
  simpa only [queries, List.map_ofFn, Function.comp_def, hits_singleton] using h

lemma wire_query {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (y : Fin n → Bool) (w : ℕ) :
    (run gs labels (List.ofFn y)).getD w false =
      hits y ((queries gs labels).getD w ∅) := by
  rw [run_input_queries, map_hits_getD]

lemma wire_true {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (y : Fin n → Bool) (w : ℕ) :
    (run gs labels (List.ofFn y)).getD w false = true ↔
      ∃ l ∈ (queries gs labels).getD w ∅, y l = true := by
  rw [wire_query, hits_true]

lemma wire_zero {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool) (w : ℕ) :
    (run gs labels (List.ofFn fun _ : Fin n => false)).getD w false = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨l, _, hl⟩ := (wire_true (n := n) gs labels (fun _ => false) w).mp h
  contradiction

lemma wire_singleton {n : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (l : Fin n) (w : ℕ) :
    (run gs labels (List.ofFn fun t => decide (t = l))).getD w false = true ↔
      l ∈ (queries gs labels).getD w ∅ := by
  rw [wire_true]
  simp

end Pilot5bMeta1020Linear

namespace Pilot5bMeta1020Linear

lemma cleaning_getD_mono {u v : List Bool}
    (h : List.Forall₂ (fun a b => a = true → b = true) u v) (r : ℕ) :
    u.getD r false = true → v.getD r false = true := by
  induction h generalizing r with
  | nil => simp
  | cons hab huv ih =>
    cases r with
    | zero => exact hab
    | succ r => exact ih r

lemma cleaning_step_mono (L L' : ℕ → Bool)
    (hL : ∀ a, L a = true → L' a = true)
    {u v : List Bool}
    (huv : List.Forall₂ (fun a b => a = true → b = true) u v)
    (g : Instruction) : step L u g = true → step L' v g = true := by
  cases g with
  | inl rs =>
    simp only [step, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨r, hr, rfl⟩, hb⟩
    exact ⟨_, ⟨r, hr, rfl⟩, cleaning_getD_mono huv r hb⟩
  | inr ar =>
    rcases ar with ⟨a, r⟩
    simp only [step, Bool.and_eq_true]
    exact fun h => ⟨hL a h.1, cleaning_getD_mono huv r h.2⟩

lemma cleaning_run_rel (gs : List Instruction) (L L' : ℕ → Bool)
    (hL : ∀ a, L a = true → L' a = true)
    {u v : List Bool}
    (huv : List.Forall₂ (fun a b => a = true → b = true) u v) :
    List.Forall₂ (fun a b => a = true → b = true)
      (run gs L u) (run gs L' v) := by
  induction gs generalizing u v with
  | nil => exact huv
  | cons g gs ih =>
    change List.Forall₂ (fun a b => a = true → b = true)
      (run gs L (u ++ [step L u g])) (run gs L' (v ++ [step L' v g]))
    exact ih (List.rel_append huv (.cons (cleaning_step_mono L L' hL huv g) .nil))

lemma cleaning_run_mono {n : ℕ} (gs : List Instruction) (L L' : ℕ → Bool)
    (hL : ∀ a, L a = true → L' a = true)
    (y y' : Fin n → Bool) (hy : ∀ l, y l = true → y' l = true) (r : ℕ) :
    (run gs L (List.ofFn y)).getD r false = true →
      (run gs L' (List.ofFn y')).getD r false = true := by
  apply cleaning_getD_mono (cleaning_run_rel gs L L' hL ?_) r
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp, ?_⟩
  intro i hi hi'
  simpa using hy ⟨i, by simpa using hi⟩

noncomputable def maxNonneighbors {n : ℕ}
    (I : Fin n → Fin n → Prop) (S : Finset (Fin n)) (p : Fin n) : Bool := by
  classical
  exact decide (∀ l ∈ S, ¬ I p l)

def labelDead3 {n : ℕ} (I : Fin n → Fin n → Prop)
    (L : ℕ → (Fin n → Bool) → Bool) (a : ℕ) : Prop :=
  ∃ S : Finset (Fin n), S.card ≤ 3 ∧ L a (maxNonneighbors I S) = false

noncomputable def cleanedLabels {n : ℕ} (I : Fin n → Fin n → Prop)
    (L : ℕ → (Fin n → Bool) → Bool) (a : ℕ) (x : Fin n → Bool) : Bool := by
  classical
  exact if labelDead3 I L a then L a x else true

def LabelMonotone {n : ℕ} (L : ℕ → (Fin n → Bool) → Bool) : Prop :=
  ∀ a x x', (∀ p, x p = true → x' p = true) → L a x = true → L a x' = true

def LinearTripleSound {n : ℕ} (I : Fin n → Fin n → Prop)
    (gs : List Instruction) (L : ℕ → (Fin n → Bool) → Bool)
    (r0 r1 r2 : ℕ) : Prop :=
  ∀ x y : Fin n → Bool,
    (run gs (fun a => L a x) (List.ofFn y)).getD r0 false = true →
    (run gs (fun a => L a x) (List.ofFn y)).getD r1 false = true →
    (run gs (fun a => L a x) (List.ofFn y)).getD r2 false = true →
    ∃ p l, I p l ∧ x p = true ∧ y l = true

lemma cleanedLabels_mono {n : ℕ} (I : Fin n → Fin n → Prop)
    (L : ℕ → (Fin n → Bool) → Bool) (hL : LabelMonotone L) :
    LabelMonotone (cleanedLabels I L) := by
  classical
  intro a x x' hxx'
  by_cases ha : labelDead3 I L a
  · simpa [cleanedLabels, ha] using hL a x x' hxx'
  · simp [cleanedLabels, ha]

lemma cleanedLabels_ge {n : ℕ} (I : Fin n → Fin n → Prop)
    (L : ℕ → (Fin n → Bool) → Bool) (a : ℕ) (x : Fin n → Bool) :
    L a x = true → cleanedLabels I L a x = true := by
  classical
  by_cases ha : labelDead3 I L a <;> simp [cleanedLabels, ha]

lemma cleaned_wire_preserved {n : ℕ} (I : Fin n → Fin n → Prop)
    (gs : List Instruction) (L : ℕ → (Fin n → Bool) → Bool)
    (x y : Fin n → Bool) (r : ℕ) :
    (run gs (fun a => L a x) (List.ofFn y)).getD r false = true →
      (run gs (fun a => cleanedLabels I L a x) (List.ofFn y)).getD r false = true :=
  cleaning_run_mono gs _ _ (fun a => cleanedLabels_ge I L a x) y y (fun _ => id) r

lemma cleanedLabels_at_small_dead_input {n : ℕ} (I : Fin n → Fin n → Prop)
    (L : ℕ → (Fin n → Bool) → Bool) (S : Finset (Fin n)) (hS : S.card ≤ 3)
    (a : ℕ) :
    cleanedLabels I L a (maxNonneighbors I S) = L a (maxNonneighbors I S) := by
  classical
  by_cases ha : labelDead3 I L a
  · simp [cleanedLabels, ha]
  · have ht : L a (maxNonneighbors I S) = true :=
      Bool.eq_true_of_not_eq_false (fun hf => ha ⟨S, hS, hf⟩)
    simp [cleanedLabels, ha, ht]

lemma retained_label_false_empty {n : ℕ} (I : Fin n → Fin n → Prop)
    (L : ℕ → (Fin n → Bool) → Bool) (hL : LabelMonotone L)
    (a : ℕ) (ha : labelDead3 I L a) : L a (fun _ => false) = false := by
  obtain ⟨S, _, hfalse⟩ := ha
  apply Bool.eq_false_of_not_eq_true
  intro ht
  have hm := hL a (fun _ => false) (maxNonneighbors I S) (by simp) ht
  simp [hfalse] at hm

theorem cleaned_triple_sound {n : ℕ} (I : Fin n → Fin n → Prop)
    (gs : List Instruction) (L : ℕ → (Fin n → Bool) → Bool)
    (hL : LabelMonotone L) (r0 r1 r2 : ℕ)
    (hsound : LinearTripleSound I gs L r0 r1 r2) :
    LinearTripleSound I gs (cleanedLabels I L) r0 r1 r2 := by
  classical
  intro x y h0 h1 h2
  by_contra hbad
  obtain ⟨l0, hm0, hy0⟩ := (wire_true gs (fun a => cleanedLabels I L a x) y r0).mp h0
  obtain ⟨l1, hm1, hy1⟩ := (wire_true gs (fun a => cleanedLabels I L a x) y r1).mp h1
  obtain ⟨l2, hm2, hy2⟩ := (wire_true gs (fun a => cleanedLabels I L a x) y r2).mp h2
  let S : Finset (Fin n) := {l0, l1, l2}
  have hS : S.card ≤ 3 := by
    calc
      S.card ≤ ({l1, l2} : Finset (Fin n)).card + 1 := Finset.card_insert_le _ _
      _ ≤ ({l2} : Finset (Fin n)).card + 1 + 1 :=
        Nat.add_le_add_right (Finset.card_insert_le _ _) 1
      _ = 3 := by simp
  let ys : Fin n → Bool := fun l => decide (l ∈ S)
  let xs := maxNonneighbors I S
  have hSY : ∀ l ∈ S, y l = true := by
    intro l hl
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact hy0
    · exact hy1
    · exact hy2
  have hx : ∀ p, x p = true → xs p = true := by
    intro p hp
    simp only [xs, maxNonneighbors, decide_eq_true_eq]
    intro l hl hI
    exact hbad ⟨p, l, hI, hp, hSY l hl⟩
  have ht0 : (run gs (fun a => cleanedLabels I L a x) (List.ofFn ys)).getD r0 false = true := by
    apply (wire_true gs _ ys r0).mpr
    exact ⟨l0, hm0, by simp [ys, S]⟩
  have ht1 : (run gs (fun a => cleanedLabels I L a x) (List.ofFn ys)).getD r1 false = true := by
    apply (wire_true gs _ ys r1).mpr
    exact ⟨l1, hm1, by simp [ys, S]⟩
  have ht2 : (run gs (fun a => cleanedLabels I L a x) (List.ofFn ys)).getD r2 false = true := by
    apply (wire_true gs _ ys r2).mpr
    exact ⟨l2, hm2, by simp [ys, S]⟩
  have label_eq : (fun a => cleanedLabels I L a xs) = (fun a => L a xs) := by
    funext a
    exact cleanedLabels_at_small_dead_input I L S hS a
  have lift (r : ℕ)
      (ht : (run gs (fun a => cleanedLabels I L a x) (List.ofFn ys)).getD r false = true) :
      (run gs (fun a => L a xs) (List.ofFn ys)).getD r false = true := by
    have hm := cleaning_run_mono gs _ _
      (fun a => cleanedLabels_mono I L hL a x xs hx) ys ys (fun _ => id) r ht
    simpa only [label_eq] using hm
  obtain ⟨p, l, hI, hp, hl⟩ := hsound xs ys (lift r0 ht0) (lift r1 ht1) (lift r2 ht2)
  have hpn : ∀ l ∈ S, ¬ I p l := of_decide_eq_true hp
  have hls : l ∈ S := of_decide_eq_true hl
  exact hpn l hls hI

end Pilot5bMeta1020Linear
