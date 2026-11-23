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


namespace Pilot5bMeta1020FirstQuery

open Finset

variable {P L G : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]
  [DecidableEq G]

def fiber (I : P → L → Prop) [DecidableRel I] (S : Finset P)
    (E : Finset (P × L)) (l : L) : Finset P :=
  S.filter fun p => I p l ∧ (p, l) ∉ E

lemma fiber_small (I : P → L → Prop) [DecidableRel I] (S : Finset P)
    (E : Finset (P × L)) (l : L)
    (hheavy : ∀ p ∈ S, I p l → 4 ≤ (S.filter fun q => I q l).card → (p, l) ∈ E) :
    (fiber I S E l).card ≤ 3 := by
  by_cases hlarge : 4 ≤ (S.filter fun q => I q l).card
  · have hempty : fiber I S E l = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hpS, hpI, hpE⟩ := Finset.mem_filter.mp hp
      exact hpE (hheavy p hpS hpI hlarge)
    simp [hempty]
  · have hsub : fiber I S E l ⊆ S.filter fun q => I q l := by
      intro p hp
      obtain ⟨hpS, hpI, _⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hpS, hpI⟩
    have := Finset.card_le_card hsub
    omega

def smallPairs (I : P → L → Prop) [DecidableRel I]
    (gs : Finset G) (S : G → Finset P) (A : G → Finset L)
    (E : Finset (P × L)) : Finset (P × L) :=
  Finset.univ.filter fun e => e ∉ E ∧ I e.1 e.2 ∧
    ∃ g ∈ gs, e.1 ∈ S g ∧ e.2 ∈ A g ∧ (A g).card ≤ 4

lemma smallPairs_bound_of_fibers (I : P → L → Prop) [DecidableRel I]
    (gs : Finset G) (S : G → Finset P) (A : G → Finset L)
    (E : Finset (P × L))
    (hfiber : ∀ g ∈ gs, ∀ l, (fiber I (S g) E l).card ≤ 3) :
    (smallPairs I gs S A E).card ≤ 12 * gs.card := by
  classical
  let B : G → Finset (P × L) := fun g =>
    if (A g).card ≤ 4 then
      (A g).biUnion fun l => (fiber I (S g) E l).image fun p => (p, l)
    else ∅
  have hB : ∀ g ∈ gs, (B g).card ≤ 12 := by
    intro g hg
    dsimp only [B]
    split_ifs with hsmall
    · have hcard := Finset.card_biUnion_le_card_mul (A g)
        (fun l => (fiber I (S g) E l).image fun p => (p, l)) 3 (by
          intro l _
          exact Finset.card_image_le.trans (hfiber g hg l))
      omega
    · simp
  have hsub : smallPairs I gs S A E ⊆ gs.biUnion B := by
    intro e he
    obtain ⟨_, heE, heI, g, hg, hp, hl, hsmall⟩ := Finset.mem_filter.mp he
    apply Finset.mem_biUnion.mpr
    refine ⟨g, hg, ?_⟩
    simp only [B, if_pos hsmall, Finset.mem_biUnion]
    refine ⟨e.2, hl, Finset.mem_image.mpr ⟨e.1, ?_, by simp⟩⟩
    exact Finset.mem_filter.mpr ⟨hp, heI, heE⟩
  exact (Finset.card_le_card hsub).trans
    ((Finset.card_biUnion_le_card_mul gs B 12 hB).trans (by omega))

theorem small_first_query_bound (I : P → L → Prop) [DecidableRel I]
    (gs : Finset G) (S : G → Finset P) (A : G → Finset L)
    (E : Finset (P × L))
    (hheavy : ∀ g ∈ gs, ∀ l p, p ∈ S g → I p l →
      4 ≤ ((S g).filter fun q => I q l).card → (p, l) ∈ E) :
    (smallPairs I gs S A E).card ≤ 12 * gs.card := by
  apply smallPairs_bound_of_fibers I gs S A E
  intro g hg l
  exact fiber_small I (S g) E l fun p hp hI hcard => hheavy g hg l p hp hI hcard

def pencil (I : P → L → Prop) [DecidableRel I] (p : P) : Finset L :=
  Finset.univ.filter (I p)

def coveredByTwo (I : P → L → Prop) [DecidableRel I] (A : Finset L) : Prop :=
  ∃ T : Finset P, T.card ≤ 2 ∧ A ⊆ T.biUnion (pencil I)

def goodFirst (I : P → L → Prop) [DecidableRel I] (A : Finset L) (p : P) : Prop :=
  5 ≤ A.card ∧ ¬ (coveredByTwo I A ∧ 3 ≤ (A.filter (I p)).card)

noncomputable def ownHeavyPairs (I : P → L → Prop) [DecidableRel I]
    (gs : Finset G) (A : G → Finset L) : Finset (P × L) := by
  classical
  exact Finset.univ.filter fun e => I e.1 e.2 ∧ ∃ g ∈ gs,
    e.2 ∈ A g ∧ coveredByTwo I (A g) ∧ 3 ≤ ((A g).filter (I e.1)).card

lemma goodFirst_of_uncharged (I : P → L → Prop) [DecidableRel I]
    (gs : Finset G) (S : G → Finset P) (A : G → Finset L)
    (E : Finset (P × L)) (p : P) (l : L) (g : G)
    (hg : g ∈ gs) (hp : p ∈ S g) (hl : l ∈ A g) (hI : I p l)
    (hE : (p, l) ∉ E)
    (hsmall : (p, l) ∉ smallPairs I gs S A E)
    (hown : (p, l) ∉ ownHeavyPairs I gs A) : goodFirst I (A g) p := by
  classical
  constructor
  · by_contra! hc
    apply hsmall
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE, hI,
      g, hg, hp, hl, by omega⟩
  · rintro ⟨hcover, hheavy⟩
    apply hown
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI,
      g, hg, hl, hcover, hheavy⟩

section Network

variable (I : P → L → Prop) [DecidableRel I]
  (orG labelG : Finset ℕ) (kids : ℕ → Finset ℕ) (child : ℕ → ℕ)
  (alive retained : ℕ → Finset P) (bare : ℕ → Finset L)
  (row : ℕ → P → Finset L)
  (or_lower : ∀ i ∈ orG, ∀ c ∈ kids i, c < i)
  (label_lower : ∀ i ∈ labelG, child i < i)
  (retained_or : ∀ i ∈ orG, ∀ p, p ∈ retained i ↔ ∃ c ∈ kids i, p ∈ retained c)
  (retained_label : ∀ i ∈ labelG, ∀ p, p ∈ retained i ↔ p ∈ alive i ∧
    (p ∈ retained (child i) ∨ goodFirst I (bare (child i)) p))
  (retained_other : ∀ i, i ∉ orG → i ∉ labelG → retained i = ∅)
  (row_or : ∀ i ∈ orG, ∀ p l, l ∈ row i p ↔ ∃ c ∈ kids i, l ∈ row c p)
  (row_label : ∀ i ∈ labelG, ∀ p l, l ∈ row i p ↔ p ∈ alive i ∧ l ∈ row (child i) p)
  (row_other : ∀ i, i ∉ orG → i ∉ labelG → ∀ p, row i p = bare i)
  (bare_or : ∀ i ∈ orG, ∀ l, l ∈ bare i ↔ ∃ c ∈ kids i, l ∈ bare c)
  (bare_sub_row : ∀ i p, bare i ⊆ row i p)

include or_lower label_lower row_or row_label row_other bare_or bare_sub_row in
theorem first_origin (i : ℕ) (p : P) (l : L) (hl : l ∈ row i p) :
    l ∈ bare i ∨ ∃ g ∈ labelG, p ∈ alive g ∧ l ∈ bare (child g) ∧
      bare (child g) ⊆ row i p := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hor : i ∈ orG
    · obtain ⟨c, hc, hlc⟩ := (row_or i hor p l).mp hl
      rcases ih c (or_lower i hor c hc) hlc with hbare | ⟨g, hg, hpa, hline, hsub⟩
      · exact Or.inl ((bare_or i hor l).mpr ⟨c, hc, hbare⟩)
      · refine Or.inr ⟨g, hg, hpa, hline, ?_⟩
        intro u hu
        exact (row_or i hor p u).mpr ⟨c, hc, hsub hu⟩
    · by_cases hlabel : i ∈ labelG
      · obtain ⟨hpa, hlc⟩ := (row_label i hlabel p l).mp hl
        rcases ih (child i) (label_lower i hlabel) hlc with hbare | ⟨g, hg, hpag, hline, hsub⟩
        · refine Or.inr ⟨i, hlabel, hpa, hbare, ?_⟩
          intro u hu
          exact (row_label i hlabel p u).mpr ⟨hpa, bare_sub_row (child i) p hu⟩
        · refine Or.inr ⟨g, hg, hpag, hline, ?_⟩
          intro u hu
          exact (row_label i hlabel p u).mpr ⟨hpa, hsub hu⟩
      · exact Or.inl (by simpa only [row_other i hor hlabel p] using hl)

include or_lower label_lower retained_or retained_label retained_other row_or row_label
  bare_sub_row in
theorem retained_origin (i : ℕ) (p : P) (hp : p ∈ retained i) :
    ∃ g ∈ labelG, p ∈ alive g ∧ goodFirst I (bare (child g)) p ∧
      bare (child g) ⊆ row i p := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases hor : i ∈ orG
    · obtain ⟨c, hc, hpc⟩ := (retained_or i hor p).mp hp
      obtain ⟨g, hg, hpa, hgood, hsub⟩ := ih c (or_lower i hor c hc) hpc
      refine ⟨g, hg, hpa, hgood, ?_⟩
      intro l hl
      exact (row_or i hor p l).mpr ⟨c, hc, hsub hl⟩
    · by_cases hlabel : i ∈ labelG
      · obtain ⟨hpa, hprev | hgood⟩ := (retained_label i hlabel p).mp hp
        · obtain ⟨g, hg, hpag, hgood, hsub⟩ := ih (child i) (label_lower i hlabel) hprev
          refine ⟨g, hg, hpag, hgood, ?_⟩
          intro l hl
          exact (row_label i hlabel p l).mpr ⟨hpa, hsub hl⟩
        · refine ⟨i, hlabel, hpa, hgood, ?_⟩
          intro l hl
          exact (row_label i hlabel p l).mpr ⟨hpa, bare_sub_row (child i) p hl⟩
      · rw [retained_other i hor hlabel] at hp
        exact (Finset.notMem_empty _ hp).elim

include or_lower label_lower retained_or retained_label row_or row_label row_other bare_or in
theorem uncharged_pair_retained (E : Finset (P × L)) (p : P) (l : L)
    (hI : I p l) (hE : (p, l) ∉ E)
    (hsmall : (p, l) ∉ smallPairs I labelG alive (fun g => bare (child g)) E)
    (hown : (p, l) ∉ ownHeavyPairs I labelG (fun g => bare (child g))) :
    ∀ i, l ∈ row i p → l ∉ bare i → p ∈ retained i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hl hbare
    by_cases hor : i ∈ orG
    · obtain ⟨c, hc, hlc⟩ := (row_or i hor p l).mp hl
      have hbc : l ∉ bare c := fun h => hbare ((bare_or i hor l).mpr ⟨c, hc, h⟩)
      exact (retained_or i hor p).mpr ⟨c, hc, ih c (or_lower i hor c hc) hlc hbc⟩
    · by_cases hlabel : i ∈ labelG
      · obtain ⟨hpa, hlc⟩ := (row_label i hlabel p l).mp hl
        apply (retained_label i hlabel p).mpr
        refine ⟨hpa, ?_⟩
        by_cases hbc : l ∈ bare (child i)
        · exact Or.inr (goodFirst_of_uncharged I labelG alive
            (fun g => bare (child g)) E p l i hlabel hpa hbc hI hE hsmall hown)
        · exact Or.inl (ih (child i) (label_lower i hlabel) hlc hbc)
      · rw [row_other i hor hlabel p] at hl
        exact (hbare hl).elim

end Network

end Pilot5bMeta1020FirstQuery

namespace Pilot5bMeta1020LinearDAG

open Pilot5bMeta1020Linear
open Pilot5bMeta1020FirstQuery

def query {N : ℕ} (gs : List Instruction) (labels : ℕ → Bool) (w : ℕ) : Finset (Fin N) :=
  (queries gs labels).getD w ∅

def gateAt (gs : List Instruction) (N w : ℕ) : Instruction :=
  gs.getD (w - N) (Sum.inl [])

def queryOp {N : ℕ} (labels : ℕ → Bool) (read : ℕ → Finset (Fin N)) :
    Instruction → Finset (Fin N)
  | .inl rs => rs.toFinset.biUnion read
  | .inr (a, r) => if labels a then read r else ∅

lemma queryRun_cons {N : ℕ} (g : Instruction) (gs : List Instruction)
    (labels : ℕ → Bool) (w : List (Finset (Fin N))) :
    queryRun (g :: gs) labels w = queryRun gs labels (w ++ [queryStep labels w g]) := rfl

lemma queryRun_length {N : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (w : List (Finset (Fin N))) : (queryRun gs labels w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [queryRun]
  | cons g gs ih => rw [queryRun_cons, ih]; simp; omega

lemma queryRun_getD {N : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (w : List (Finset (Fin N))) (r : ℕ) (hr : r < w.length) :
    (queryRun gs labels w).getD r ∅ = w.getD r ∅ := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [queryRun_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hr]

lemma queryRun_split {N : ℕ} (gs : List Instruction) (labels : ℕ → Bool)
    (w : List (Finset (Fin N))) (j : ℕ) :
    queryRun gs labels w = queryRun (gs.drop j) labels (queryRun (gs.take j) labels w) := by
  simpa only [queryRun, List.foldl_append] using congrArg
    (fun hs : List Instruction => queryRun hs labels w) (List.take_append_drop j gs).symm

lemma query_input {N : ℕ} (gs : List Instruction) (labels : ℕ → Bool) (p : Fin N) :
    query gs labels p = {p} := by
  unfold query queries
  rw [queryRun_getD _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp)]
  simp

lemma query_missing {N : ℕ} (gs : List Instruction) (labels : ℕ → Bool) (w : ℕ)
    (hw : N + gs.length ≤ w) : query (N := N) gs labels w = ∅ := by
  unfold query queries
  exact List.getD_eq_default _ _ (by simpa [queryRun_length] using hw)

lemma query_gate {N : ℕ} (gs : List Instruction) (labels : ℕ → Bool) (w : ℕ)
    (hn : N ≤ w) (hw : w < N + gs.length) :
    query gs labels w = queryOp labels
      (fun r => if r < w then query (N := N) gs labels r else ∅) (gateAt gs N w) := by
  let j := w - N
  have hj : j < gs.length := by dsimp [j]; omega
  let g := gs[j]
  let initial : List (Finset (Fin N)) := List.ofFn fun l : Fin N => {l}
  let earlier := queryRun (gs.take j) labels initial
  have plen : earlier.length = w := by
    simp [earlier, initial, queryRun_length, Nat.min_eq_left hj.le, j]
    omega
  have split : queryRun gs labels initial =
      queryRun (g :: gs.drop (j + 1)) labels earlier := by
    rw [queryRun_split gs labels initial j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r ∅ =
      if r < w then query (N := N) gs labels r else ∅ := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r ∅ = (queryRun gs labels initial).getD r ∅
      rw [split]
      exact (queryRun_getD _ labels earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  have hg : gateAt gs N w = g := List.getD_eq_getElem _ _ hj
  rw [hg]
  change (queryRun gs labels initial).getD w ∅ = _
  rw [split, queryRun_cons, queryRun_getD _ _ _ _ (by simp [plen]),
    List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero]
  cases g <;> simp only [queryStep, queryOp, read]

lemma gateAt_first (gs : List Instruction) (hhead : gs.head? = some (Sum.inl [])) (N : ℕ) :
    gateAt gs N N = Sum.inl [] := by
  cases gs with
  | nil => simp at hhead
  | cons g gs =>
    have hg : g = Sum.inl [] := by simpa using hhead
    simp [gateAt, hg]

lemma head_nonempty (gs : List Instruction) (hhead : gs.head? = some (Sum.inl [])) :
    0 < gs.length := by
  cases gs <;> simp_all

lemma query_false_wire {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (labels : ℕ → Bool) :
    query (N := N) gs labels N = ∅ := by
  rw [query_gate gs labels N (by omega) (by have := head_nonempty gs hhead; omega),
    gateAt_first gs hhead N]
  simp [queryOp]

def IsOr (α : ℕ → Bool) : Instruction → Prop
  | .inl _ => True
  | .inr (a, _) => α a = true

def IsLabel (α : ℕ → Bool) : Instruction → Prop
  | .inl _ => False
  | .inr (a, _) => α a = false

noncomputable def orG (gs : List Instruction) (N : ℕ) (α : ℕ → Bool) : Finset ℕ := by
  classical
  exact (Finset.Ico N (N + gs.length)).filter fun w => IsOr α (gateAt gs N w)

noncomputable def labelG (gs : List Instruction) (N : ℕ) (α : ℕ → Bool) : Finset ℕ := by
  classical
  exact (Finset.Ico N (N + gs.length)).filter fun w => IsLabel α (gateAt gs N w)

def clamp (N w r : ℕ) : ℕ := if r < w then r else N

def child (gs : List Instruction) (N w : ℕ) : ℕ :=
  match gateAt gs N w with
  | .inl _ => N
  | .inr (_, r) => clamp N w r

def labelID (gs : List Instruction) (N w : ℕ) : ℕ :=
  match gateAt gs N w with
  | .inl _ => 0
  | .inr (a, _) => a

def kids (gs : List Instruction) (N w : ℕ) : Finset ℕ :=
  match gateAt gs N w with
  | .inl rs => rs.toFinset.filter (· < w)
  | .inr (_, r) => {clamp N w r}

lemma gateAt_mem (gs : List Instruction) (N w : ℕ)
    (hn : N ≤ w) (hw : w < N + gs.length) : gateAt gs N w ∈ gs := by
  have hj : w - N < gs.length := by omega
  rw [gateAt, List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem _

lemma label_after_first (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (N w a r : ℕ)
    (hn : N ≤ w) (hgate : gateAt gs N w = Sum.inr (a, r)) : N < w := by
  by_contra h
  have heq : w = N := by omega
  rw [heq, gateAt_first gs hhead N] at hgate
  contradiction

lemma clamp_lower (N w r : ℕ) (h : N < w) : clamp N w r < w := by
  unfold clamp
  split_ifs <;> omega

lemma query_clamp {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (labels : ℕ → Bool) (w r : ℕ) :
    query (N := N) gs labels (clamp N w r) =
      if r < w then query gs labels r else ∅ := by
  unfold clamp
  split_ifs
  · rfl
  · exact query_false_wire gs hhead labels

lemma or_lower (gs : List Instruction) (hhead : gs.head? = some (Sum.inl []))
    (N : ℕ) (α : ℕ → Bool) :
    ∀ w ∈ orG gs N α, ∀ c ∈ kids gs N w, c < w := by
  classical
  intro w hw c hc
  obtain ⟨hwI, _⟩ := Finset.mem_filter.mp hw
  have hwn := (Finset.mem_Ico.mp hwI).1
  cases hgate : gateAt gs N w with
  | inl rs =>
    have hc' : c ∈ rs.toFinset.filter (· < w) := by simpa only [kids, hgate] using hc
    exact (Finset.mem_filter.mp hc').2
  | inr ar =>
    rcases ar with ⟨a, r⟩
    have hcw : c = clamp N w r := by simpa only [kids, hgate, Finset.mem_singleton] using hc
    rw [hcw]
    exact clamp_lower N w r (label_after_first gs hhead N w a r hwn hgate)

lemma label_lower (gs : List Instruction) (hhead : gs.head? = some (Sum.inl []))
    (N : ℕ) (α : ℕ → Bool) :
    ∀ w ∈ labelG gs N α, child gs N w < w := by
  classical
  intro w hw
  obtain ⟨hwI, hkind⟩ := Finset.mem_filter.mp hw
  have hwn := (Finset.mem_Ico.mp hwI).1
  cases hgate : gateAt gs N w with
  | inl rs => simp [IsLabel, hgate] at hkind
  | inr ar =>
    rcases ar with ⟨a, r⟩
    simp only [child, hgate]
    exact clamp_lower N w r (label_after_first gs hhead N w a r hwn hgate)

lemma gates_disjoint (gs : List Instruction) (N : ℕ) (α : ℕ → Bool) :
    Disjoint (orG gs N α) (labelG gs N α) := by
  classical
  apply Finset.disjoint_left.mpr
  intro w ho hl
  have ho' := (Finset.mem_filter.mp ho).2
  have hl' := (Finset.mem_filter.mp hl).2
  cases hgate : gateAt gs N w with
  | inl rs => simp [IsLabel, hgate] at hl'
  | inr ar =>
    rcases ar with ⟨a, r⟩
    simp only [IsOr, hgate] at ho'
    simp only [IsLabel, hgate] at hl'
    rw [ho'] at hl'
    contradiction

lemma gate_partition (gs : List Instruction) (N : ℕ) (α : ℕ → Bool) (w : ℕ)
    (hw : w ∈ Finset.Ico N (N + gs.length)) :
    w ∈ orG gs N α ∨ w ∈ labelG gs N α := by
  classical
  cases hgate : gateAt gs N w with
  | inl rs => exact Or.inl (Finset.mem_filter.mpr ⟨hw, by simp [IsOr, hgate]⟩)
  | inr ar =>
    rcases ar with ⟨a, r⟩
    cases ha : α a
    · exact Or.inr (Finset.mem_filter.mpr ⟨hw, by simp [IsLabel, hgate, ha]⟩)
    · exact Or.inl (Finset.mem_filter.mpr ⟨hw, by simp [IsOr, hgate, ha]⟩)

lemma gate_counts (gs : List Instruction) (N : ℕ) (α : ℕ → Bool) :
    (orG gs N α).card + (labelG gs N α).card = gs.length := by
  classical
  have heq : orG gs N α ∪ labelG gs N α = Finset.Ico N (N + gs.length) := by
    ext w
    constructor
    · intro hw
      rcases Finset.mem_union.mp hw with hw | hw <;> exact (Finset.mem_filter.mp hw).1
    · intro hw
      exact Finset.mem_union.mpr (gate_partition gs N α w hw)
  rw [← Finset.card_union_of_disjoint (gates_disjoint gs N α), heq]
  simp

lemma kids_card (gs : List Instruction) (N : ℕ) (α : ℕ → Bool)
    (hfanin : ∀ rs, Sum.inl rs ∈ gs → rs.length ≤ 2) :
    ∀ w ∈ orG gs N α, (kids gs N w).card ≤ 2 := by
  classical
  intro w hw
  obtain ⟨hwI, _⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwn, hwb⟩ := Finset.mem_Ico.mp hwI
  cases hgate : gateAt gs N w with
  | inl rs =>
    have hlen := hfanin rs (by simpa only [hgate] using gateAt_mem gs N w hwn hwb)
    simp only [kids, hgate]
    exact (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hlen)
  | inr ar => simp [kids, hgate]

lemma query_or_eq {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (α β : ℕ → Bool)
    (hαβ : ∀ a, α a = true → β a = true) (w : ℕ) (hw : w ∈ orG gs N α) :
    query gs β w = (kids gs N w).biUnion (query (N := N) gs β) := by
  classical
  obtain ⟨hwI, hkind⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwn, hwb⟩ := Finset.mem_Ico.mp hwI
  rw [query_gate gs β w hwn hwb]
  cases hgate : gateAt gs N w with
  | inl rs =>
    simp only [queryOp, kids, hgate]
    ext l
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨r, hr, hl⟩
      by_cases hrw : r < w
      · exact ⟨r, ⟨hr, hrw⟩, by simpa only [ite_eq_left hrw] using hl⟩
      · simp [hrw] at hl
    · rintro ⟨r, ⟨hr, hrw⟩, hl⟩
      exact ⟨r, hr, by simpa only [ite_eq_left hrw] using hl⟩
  | inr ar =>
    rcases ar with ⟨a, r⟩
    have ha : α a = true := by simpa only [IsOr, hgate] using hkind
    have hb := hαβ a ha
    simp only [queryOp, hb, ite_true, kids, hgate, Finset.singleton_biUnion]
    exact (query_clamp gs hhead β w r).symm

lemma query_label_eq {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (α β : ℕ → Bool)
    (w : ℕ) (hw : w ∈ labelG gs N α) :
    query (N := N) gs β w =
      if β (labelID gs N w) then query gs β (child gs N w) else ∅ := by
  classical
  obtain ⟨hwI, hkind⟩ := Finset.mem_filter.mp hw
  obtain ⟨hwn, hwb⟩ := Finset.mem_Ico.mp hwI
  rw [query_gate gs β w hwn hwb]
  cases hgate : gateAt gs N w with
  | inl rs => simp [IsLabel, hgate] at hkind
  | inr ar =>
    rcases ar with ⟨a, r⟩
    simp only [queryOp, labelID, child, hgate]
    rw [query_clamp gs hhead β w r]

lemma query_other_eq {N : ℕ} (gs : List Instruction) (α β γ : ℕ → Bool)
    (w : ℕ) (hor : w ∉ orG gs N α) (hlab : w ∉ labelG gs N α) :
    query (N := N) gs β w = query gs γ w := by
  by_cases hwn : w < N
  · exact (query_input gs β ⟨w, hwn⟩).trans (query_input gs γ ⟨w, hwn⟩).symm
  · have hwb : N + gs.length ≤ w := by
      by_contra h
      rcases gate_partition gs N α w (Finset.mem_Ico.mpr ⟨by omega, by omega⟩) with ho | hl
      · exact hor ho
      · exact hlab hl
    rw [query_missing gs β w hwb, query_missing gs γ w hwb]

lemma query_mono {N : ℕ} (gs : List Instruction) (α β : ℕ → Bool)
    (h : ∀ a, α a = true → β a = true) (w : ℕ) :
    query (N := N) gs α w ⊆ query gs β w := by
  intro l hl
  have hv := (wire_singleton gs α l w).mpr hl
  have hm := cleaning_run_mono gs α β h (fun t => decide (t = l))
    (fun t => decide (t = l)) (fun _ => id) w hv
  exact (wire_singleton gs β l w).mp hm

def bare {N : ℕ} (gs : List Instruction) (α : ℕ → Bool) : ℕ → Finset (Fin N) :=
  query gs α

def row {N : ℕ} (gs : List Instruction) (L : ℕ → (Fin N → Bool) → Bool)
    (w : ℕ) (p : Fin N) : Finset (Fin N) :=
  query gs (fun a => L a (fun q => decide (q = p))) w

def alive {N : ℕ} (gs : List Instruction) (L : ℕ → (Fin N → Bool) → Bool)
    (w : ℕ) : Finset (Fin N) :=
  Finset.univ.filter fun p => L (labelID gs N w) (fun q => decide (q = p)) = true

lemma bare_or_law {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (α : ℕ → Bool)
    (w : ℕ) (hw : w ∈ orG gs N α) (l : Fin N) :
    l ∈ bare gs α w ↔ ∃ c ∈ kids gs N w, l ∈ bare gs α c := by
  change l ∈ query gs α w ↔ _
  rw [query_or_eq gs hhead α α (fun _ => id) w hw]
  exact Finset.mem_biUnion

lemma row_or_law {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (α : ℕ → Bool)
    (L : ℕ → (Fin N → Bool) → Bool)
    (hα : ∀ a x, α a = true → L a x = true)
    (w : ℕ) (hw : w ∈ orG gs N α) (p l : Fin N) :
    l ∈ row gs L w p ↔ ∃ c ∈ kids gs N w, l ∈ row gs L c p := by
  change l ∈ query gs (fun a => L a (fun q => decide (q = p))) w ↔ _
  rw [query_or_eq gs hhead α _ (fun a => hα a _) w hw]
  exact Finset.mem_biUnion

lemma row_label_law {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (α : ℕ → Bool)
    (L : ℕ → (Fin N → Bool) → Bool)
    (w : ℕ) (hw : w ∈ labelG gs N α) (p l : Fin N) :
    l ∈ row gs L w p ↔ p ∈ alive gs L w ∧ l ∈ row gs L (child gs N w) p := by
  change l ∈ query gs (fun a => L a (fun q => decide (q = p))) w ↔ _
  rw [query_label_eq gs hhead α _ w hw]
  by_cases h : L (labelID gs N w) (fun q => decide (q = p)) = true
  · simp [h, alive, row]
  · simp [h, alive, row]

lemma row_other_law {N : ℕ} (gs : List Instruction) (α : ℕ → Bool)
    (L : ℕ → (Fin N → Bool) → Bool) (w : ℕ)
    (hor : w ∉ orG gs N α) (hlab : w ∉ labelG gs N α) (p : Fin N) :
    row gs L w p = bare gs α w :=
  query_other_eq gs α _ α w hor hlab

lemma bare_sub_row {N : ℕ} (gs : List Instruction) (α : ℕ → Bool)
    (L : ℕ → (Fin N → Bool) → Bool)
    (hα : ∀ a x, α a = true → L a x = true) (w : ℕ) (p : Fin N) :
    bare gs α w ⊆ row gs L w p :=
  query_mono gs α _ (fun a => hα a _) w

lemma bare_label_empty {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (α : ℕ → Bool)
    (w : ℕ) (hw : w ∈ labelG gs N α) : bare (N := N) gs α w = ∅ := by
  classical
  have hk := (Finset.mem_filter.mp hw).2
  have hf : α (labelID gs N w) = false := by
    cases he : gateAt gs N w with
    | inl rs => simp [IsLabel, he] at hk
    | inr ar => simpa [IsLabel, labelID, he] using hk
  exact (query_label_eq gs hhead α α w hw).trans (by simp [hf])

attribute [local instance] Classical.propDecidable

noncomputable def retained {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : List Instruction) (α : ℕ → Bool) (L : ℕ → (Fin N → Bool) → Bool)
    (w : ℕ) : Finset (Fin N) := by
  classical
  exact Nat.strongRecOn w fun i prev =>
    if i ∈ orG gs N α then
      (kids gs N i).biUnion fun c => if h : c < i then prev c h else ∅
    else if i ∈ labelG gs N α then
      (alive gs L i).filter fun p =>
        (if h : child gs N i < i then p ∈ prev (child gs N i) h else False) ∨
          goodFirst I (bare gs α (child gs N i)) p
    else ∅

lemma retained_eq {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : List Instruction) (α : ℕ → Bool) (L : ℕ → (Fin N → Bool) → Bool)
    (w : ℕ) :
    retained I gs α L w =
    if w ∈ orG gs N α then
      (kids gs N w).biUnion fun c => if c < w then retained I gs α L c else ∅
    else if w ∈ labelG gs N α then
      (alive gs L w).filter fun p =>
        (if child gs N w < w then p ∈ retained I gs α L (child gs N w) else False) ∨
          goodFirst I (bare gs α (child gs N w)) p
    else ∅ := by
  classical
  unfold retained
  rw [Nat.strongRecOn_eq]
  rfl

lemma retained_or_law {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : List Instruction) (hhead : gs.head? = some (Sum.inl []))
    (α : ℕ → Bool) (L : ℕ → (Fin N → Bool) → Bool)
    (w : ℕ) (hw : w ∈ orG gs N α) (p : Fin N) :
    p ∈ retained I gs α L w ↔ ∃ c ∈ kids gs N w, p ∈ retained I gs α L c := by
  classical
  rw [retained_eq, ite_eq_left hw]
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hc, hp⟩
    exact ⟨c, hc, by simpa [or_lower gs hhead N α w hw c hc] using hp⟩
  · rintro ⟨c, hc, hp⟩
    exact ⟨c, hc, by simpa [or_lower gs hhead N α w hw c hc] using hp⟩

lemma retained_label_law {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : List Instruction) (hhead : gs.head? = some (Sum.inl []))
    (α : ℕ → Bool) (L : ℕ → (Fin N → Bool) → Bool)
    (w : ℕ) (hw : w ∈ labelG gs N α) (p : Fin N) :
    p ∈ retained I gs α L w ↔ p ∈ alive gs L w ∧
      (p ∈ retained I gs α L (child gs N w) ∨
        goodFirst I (bare gs α (child gs N w)) p) := by
  classical
  have hn : w ∉ orG gs N α := fun ho => Finset.disjoint_left.mp (gates_disjoint gs N α) ho hw
  rw [retained_eq, ite_eq_right hn, ite_eq_left hw]
  simp only [Finset.mem_filter, ite_eq_left (label_lower gs hhead N α w hw)]

lemma retained_other_law {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : List Instruction) (α : ℕ → Bool) (L : ℕ → (Fin N → Bool) → Bool)
    (w : ℕ) (hor : w ∉ orG gs N α) (hlab : w ∉ labelG gs N α) :
    retained I gs α L w = ∅ := by
  classical
  rw [retained_eq, ite_eq_right hor, ite_eq_right hlab]

lemma first_origin {N : ℕ} (gs : List Instruction)
    (hhead : gs.head? = some (Sum.inl [])) (α : ℕ → Bool)
    (L : ℕ → (Fin N → Bool) → Bool)
    (hα : ∀ a x, α a = true → L a x = true)
    (i : ℕ) (p l : Fin N) (hl : l ∈ row gs L i p) :
    l ∈ bare gs α i ∨ ∃ g ∈ labelG gs N α, p ∈ alive gs L g ∧
      l ∈ bare gs α (child gs N g) ∧ bare gs α (child gs N g) ⊆ row gs L i p := by
  exact Pilot5bMeta1020FirstQuery.first_origin
    (orG gs N α) (labelG gs N α) (kids gs N) (child gs N)
    (alive gs L) (bare gs α) (row gs L)
    (or_lower gs hhead N α) (label_lower gs hhead N α)
    (row_or_law gs hhead α L hα) (row_label_law gs hhead α L)
    (row_other_law gs α L) (bare_or_law gs hhead α) (bare_sub_row gs α L hα) i p l hl

lemma retained_origin {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : List Instruction) (hhead : gs.head? = some (Sum.inl [])) (α : ℕ → Bool)
    (L : ℕ → (Fin N → Bool) → Bool)
    (hα : ∀ a x, α a = true → L a x = true)
    (i : ℕ) (p : Fin N) (hp : p ∈ retained I gs α L i) :
    ∃ g ∈ labelG gs N α, p ∈ alive gs L g ∧ goodFirst I (bare gs α (child gs N g)) p ∧
      bare gs α (child gs N g) ⊆ row gs L i p := by
  exact Pilot5bMeta1020FirstQuery.retained_origin I
    (orG gs N α) (labelG gs N α) (kids gs N) (child gs N)
    (alive gs L) (retained I gs α L) (bare gs α) (row gs L)
    (or_lower gs hhead N α) (label_lower gs hhead N α)
    (retained_or_law I gs hhead α L) (retained_label_law I gs hhead α L)
    (retained_other_law I gs α L)
    (row_or_law gs hhead α L hα) (row_label_law gs hhead α L)
    (bare_sub_row gs α L hα) i p hp

lemma uncharged_pair_retained {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (gs : List Instruction) (hhead : gs.head? = some (Sum.inl [])) (α : ℕ → Bool)
    (L : ℕ → (Fin N → Bool) → Bool)
    (hα : ∀ a x, α a = true → L a x = true)
    (E : Finset (Fin N × Fin N)) (p l : Fin N) (hI : I p l) (hE : (p, l) ∉ E)
    (hsmall : (p, l) ∉ smallPairs I (labelG gs N α) (alive gs L)
      (fun g => bare gs α (child gs N g)) E)
    (hown : (p, l) ∉ ownHeavyPairs I (labelG gs N α)
      (fun g => bare gs α (child gs N g)))
    (i : ℕ) (hl : l ∈ row gs L i p) (hbare : l ∉ bare gs α i) :
    p ∈ retained I gs α L i := by
  exact Pilot5bMeta1020FirstQuery.uncharged_pair_retained I
    (orG gs N α) (labelG gs N α) (kids gs N) (child gs N)
    (alive gs L) (retained I gs α L) (bare gs α) (row gs L)
    (or_lower gs hhead N α) (label_lower gs hhead N α)
    (retained_or_law I gs hhead α L) (retained_label_law I gs hhead α L)
    (row_or_law gs hhead α L hα) (row_label_law gs hhead α L)
    (row_other_law gs α L) (bare_or_law gs hhead α)
    E p l hI hE hsmall hown i hl hbare

end Pilot5bMeta1020LinearDAG
