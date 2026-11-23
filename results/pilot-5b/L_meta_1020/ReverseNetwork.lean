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

/-! Append after LinearNetwork. -/
namespace Pilot5bMeta1020OrAggregate

open Pilot5bMeta1020Linear

def appendOrs (n : ℕ) (gs : List Instruction) (r : ℕ) : List ℕ → List Instruction × ℕ
  | [] => (gs, r)
  | s :: rs => appendOrs n (gs ++ [Sum.inl [r, s]]) (n + gs.length) rs

def aggregate (n : ℕ) (gs : List Instruction) : List ℕ → List Instruction × ℕ
  | [] => (gs, n)
  | r :: rs => appendOrs n gs r rs

@[simp] lemma aggregate_nil (n : ℕ) (gs : List Instruction) :
    aggregate n gs [] = (gs, n) := rfl

@[simp] lemma aggregate_singleton (n : ℕ) (gs : List Instruction) (r : ℕ) :
    aggregate n gs [r] = (gs, r) := rfl

lemma appendOrs_extension (n : ℕ) (gs : List Instruction) (r : ℕ) (rs : List ℕ) :
    ∃ hs : List Instruction, (appendOrs n gs r rs).1 = gs ++ hs ∧
      hs.length = rs.length ∧ ∀ g ∈ hs, ∃ us, g = Sum.inl us ∧ us.length = 2 := by
  induction rs generalizing gs r with
  | nil => exact ⟨[], by simp [appendOrs], rfl, by simp⟩
  | cons s rs ih =>
    obtain ⟨hs, heq, hlen, hor⟩ := ih (gs ++ [Sum.inl [r, s]]) (n + gs.length)
    refine ⟨Sum.inl [r, s] :: hs, ?_, by simp [hlen], ?_⟩
    · simpa only [appendOrs, List.append_assoc, List.singleton_append] using heq
    · intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact ⟨[r, s], rfl, rfl⟩
      · exact hor g hg

lemma aggregate_extension (n : ℕ) (gs : List Instruction) (rs : List ℕ) :
    ∃ hs : List Instruction, (aggregate n gs rs).1 = gs ++ hs ∧
      hs.length = rs.length - 1 ∧
      ∀ g ∈ hs, ∃ us, g = Sum.inl us ∧ us.length = 2 := by
  cases rs with
  | nil => exact ⟨[], by simp, rfl, by simp⟩
  | cons r rs => simpa only [aggregate, List.length_cons, Nat.add_sub_cancel] using
      appendOrs_extension n gs r rs

lemma aggregate_length (n : ℕ) (gs : List Instruction) (rs : List ℕ) :
    (aggregate n gs rs).1.length = gs.length + (rs.length - 1) := by
  obtain ⟨hs, heq, hlen, _⟩ := aggregate_extension n gs rs
  simp [heq, hlen]

lemma aggregate_prefix (n : ℕ) (gs : List Instruction) (rs : List ℕ) :
    gs <+: (aggregate n gs rs).1 := by
  obtain ⟨hs, heq, _, _⟩ := aggregate_extension n gs rs
  exact ⟨hs, heq.symm⟩

lemma appendOrs_root_valid (n : ℕ) (gs : List Instruction) (r : ℕ) (rs : List ℕ)
    (hr : r < n + gs.length) :
    (appendOrs n gs r rs).2 < n + (appendOrs n gs r rs).1.length := by
  induction rs generalizing gs r with
  | nil => exact hr
  | cons s rs ih =>
    apply ih
    simp

lemma aggregate_root_valid (n : ℕ) (gs : List Instruction) (rs : List ℕ)
    (hz : gs.head? = some (Sum.inl []))
    (hrs : ∀ r ∈ rs, r < n + gs.length) :
    (aggregate n gs rs).2 < n + (aggregate n gs rs).1.length := by
  cases rs with
  | nil =>
    have hpos : 0 < gs.length := by
      cases gs with
      | nil => simp at hz
      | cons g gs => simp
    simpa only [aggregate] using (show n < n + gs.length by omega)
  | cons r rs => exact appendOrs_root_valid n gs r rs (hrs r (by simp))

lemma aggregate_old_read (n : ℕ) (gs : List Instruction) (rs : List ℕ)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (w : ℕ) (hw : w < n + gs.length) :
    (run (aggregate n gs rs).1 labels y).getD w false =
      (run gs labels y).getD w false := by
  obtain ⟨hs, heq, _, _⟩ := aggregate_extension n gs rs
  rw [heq, run_append]
  apply run_getD_lt
  simpa only [run_length, hy] using hw

lemma false_wire (n : ℕ) (gs : List Instruction)
    (hz : gs.head? = some (Sum.inl []))
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n) :
    (run gs labels y).getD n false = false := by
  cases gs with
  | nil => simp at hz
  | cons g gs =>
    have hg : g = Sum.inl [] := Option.some.inj hz
    subst g
    rw [run_cons]
    simp only [step, List.map_nil, List.any_nil]
    rw [run_getD_lt gs labels (y ++ [false]) n (by simp [hy])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    simp [hy]

lemma appendOrs_true (n : ℕ) (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (gs : List Instruction) (r : ℕ) (rs : List ℕ)
    (hr : r < n + gs.length) (hrs : ∀ s ∈ rs, s < n + gs.length) :
    (run (appendOrs n gs r rs).1 labels y).getD (appendOrs n gs r rs).2 false = true ↔
      (run gs labels y).getD r false = true ∨
        ∃ s ∈ rs, (run gs labels y).getD s false = true := by
  induction rs generalizing gs r with
  | nil => simp [appendOrs]
  | cons s rs ih =>
    have hs : s < n + gs.length := hrs s (by simp)
    have htail : ∀ t ∈ rs, t < n + (gs ++ [Sum.inl [r, s]]).length := by
      intro t ht
      have h := hrs t (by simp [ht])
      simpa only [List.length_append, List.length_singleton] using (show t < n + (gs.length + 1) by omega)
    have hnew : n + gs.length < n + (gs ++ [Sum.inl [r, s]]).length := by simp
    rw [appendOrs, ih _ _ hnew htail]
    have hnewval : (run (gs ++ [Sum.inl [r, s]]) labels y).getD (n + gs.length) false =
        ((run gs labels y).getD r false || (run gs labels y).getD s false) := by
      simpa [hy, step] using snoc_read_new gs (Sum.inl [r, s]) labels y
    rw [hnewval, Bool.or_eq_true]
    have hold (t : ℕ) (ht : t ∈ rs) :
        (run (gs ++ [Sum.inl [r, s]]) labels y).getD t false =
          (run gs labels y).getD t false := by
      apply snoc_read_old
      have h := hrs t (by simp [ht])
      simpa only [hy] using h
    constructor
    · rintro ((hr | hs) | ⟨t, ht, hv⟩)
      · exact Or.inl hr
      · exact Or.inr ⟨s, by simp, hs⟩
      · exact Or.inr ⟨t, by simp [ht], (hold t ht) ▸ hv⟩
    · rintro (hr | ⟨t, ht, htval⟩)
      · exact Or.inl (Or.inl hr)
      · rcases List.mem_cons.mp ht with hts | ht
        · subst t
          exact Or.inl (Or.inr htval)
        · exact Or.inr ⟨t, ht, (hold t ht).symm ▸ htval⟩

lemma aggregate_true (n : ℕ) (gs : List Instruction) (rs : List ℕ)
    (hz : gs.head? = some (Sum.inl []))
    (hrs : ∀ r ∈ rs, r < n + gs.length)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n) :
    (run (aggregate n gs rs).1 labels y).getD (aggregate n gs rs).2 false = true ↔
      ∃ r ∈ rs, (run gs labels y).getD r false = true := by
  cases rs with
  | nil =>
    change (run gs labels y).getD n false = true ↔
      ∃ r ∈ ([] : List ℕ), (run gs labels y).getD r false = true
    rw [false_wire n gs hz labels y hy]
    simp
  | cons r rs =>
    rw [aggregate, appendOrs_true n labels y hy gs r rs (hrs r (by simp))
      (fun s hs => hrs s (by simp [hs]))]
    simp

lemma aggregate_fanin (n : ℕ) (gs : List Instruction) (rs : List ℕ)
    (hfan : ∀ us, Sum.inl us ∈ gs → us.length ≤ 2) :
    ∀ us, Sum.inl us ∈ (aggregate n gs rs).1 → us.length ≤ 2 := by
  obtain ⟨hs, heq, _, hor⟩ := aggregate_extension n gs rs
  intro us hu
  rw [heq] at hu
  rcases List.mem_append.mp hu with hu | hu
  · exact hfan us hu
  · obtain ⟨vs, he, hv⟩ := hor (Sum.inl us) hu
    have huvs : us = vs := Sum.inl.inj he
    simp [huvs, hv]

lemma aggregate_head (n : ℕ) (gs : List Instruction) (rs : List ℕ)
    (hz : gs.head? = some (Sum.inl [])) :
    (aggregate n gs rs).1.head? = some (Sum.inl []) := by
  obtain ⟨hs, heq, _, _⟩ := aggregate_extension n gs rs
  rw [heq]
  cases gs with
  | nil => simp at hz
  | cons g gs => simpa using hz

end Pilot5bMeta1020OrAggregate

namespace Pilot5bMeta1020Reverse

open Pilot5bMeta1020Linear Pilot5bMeta1020OrAggregate

abbrev State := List Instruction × ((ℕ → ℕ) × (ℕ → ℕ))

def net (s : State) : List Instruction := s.1
def context (s : State) : ℕ → ℕ := s.2.1
def message (s : State) : ℕ → ℕ := s.2.2

def initial (n : ℕ) (gs : List Instruction) : State := (gs, (fun _ => n, fun _ => n))

def incoming (seeds edges : List (ℕ × ℕ)) (messages : ℕ → ℕ) (v : ℕ) : List ℕ :=
  ((seeds.filter fun e => decide (e.1 = v)).map Prod.snd) ++
    ((edges.filter fun e => decide (e.2 = v)).map fun e => messages e.1)

def incomingCount (seeds edges : List (ℕ × ℕ)) (v : ℕ) : ℕ :=
  (seeds.filter fun e => decide (e.1 = v)).length +
    (edges.filter fun e => decide (e.2 = v)).length

lemma incoming_length (seeds edges : List (ℕ × ℕ)) (messages : ℕ → ℕ) (v : ℕ) :
    (incoming seeds edges messages v).length = incomingCount seeds edges v := by
  simp [incoming, incomingCount]

lemma mem_incoming (seeds edges : List (ℕ × ℕ)) (messages : ℕ → ℕ) (v r : ℕ) :
    r ∈ incoming seeds edges messages v ↔
      (∃ e ∈ seeds, e.1 = v ∧ e.2 = r) ∨
      (∃ e ∈ edges, e.2 = v ∧ messages e.1 = r) := by
  simp [incoming, and_assoc]

def step (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) : State :=
  let a := aggregate n (net s) (incoming seeds edges (message s) v)
  match weight v with
  | none => (a.1, (Function.update (context s) v a.2, Function.update (message s) v a.2))
  | some z => (a.1 ++ [Sum.inr (z, a.2)],
      (Function.update (context s) v a.2,
       Function.update (message s) v (n + a.1.length)))

def build (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ) : ℕ → State → State
  | 0, s => s
  | k + 1, s => build n seeds edges weight k (step n seeds edges weight k s)

def valid (n : ℕ) (s : State) : Prop :=
  (net s).head? = some (Sum.inl []) ∧
    (∀ v, context s v < n + (net s).length) ∧
    (∀ v, message s v < n + (net s).length)

lemma initial_valid (n : ℕ) (gs : List Instruction)
    (h : gs.head? = some (Sum.inl [])) : valid n (initial n gs) := by
  have hp : 0 < gs.length := by
    cases gs with
    | nil => simp at h
    | cons g gs => simp
  exact ⟨h, fun _ => by simpa [initial, context, net] using (show n < n + gs.length by omega),
    fun _ => by simpa [initial, message, net] using (show n < n + gs.length by omega)⟩

lemma incoming_valid (n : ℕ) (seeds edges : List (ℕ × ℕ)) (v : ℕ) (s : State)
    (hs : valid n s) (hseeds : ∀ e ∈ seeds, e.2 < n + (net s).length) :
    ∀ r ∈ incoming seeds edges (message s) v, r < n + (net s).length := by
  intro r hr
  rcases (mem_incoming seeds edges (message s) v r).mp hr with h | h
  · obtain ⟨e, he, _, rfl⟩ := h
    exact hseeds e he
  · obtain ⟨e, _, _, rfl⟩ := h
    exact hs.2.2 e.1

lemma step_extension (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) :
    ∃ hs, net (step n seeds edges weight v s) = net s ++ hs := by
  obtain ⟨hs, h, _, _⟩ := aggregate_extension n (net s) (incoming seeds edges (message s) v)
  cases hw : weight v with
  | none => exact ⟨hs, by simpa [step, net, hw] using h⟩
  | some z =>
    refine ⟨hs ++ [Sum.inr (z, (aggregate n (net s) (incoming seeds edges (message s) v)).2)], ?_⟩
    simp only [step, hw, net]
    simp only [net] at h
    rw [h, List.append_assoc]

lemma step_length (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) :
    (net (step n seeds edges weight v s)).length =
      (net s).length + (incomingCount seeds edges v - 1) +
        (if (weight v).isSome then 1 else 0) := by
  cases hw : weight v <;>
    simp [step, net, hw, aggregate_length, incoming_length]

lemma step_length_le (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) :
    (net s).length ≤ (net (step n seeds edges weight v s)).length := by
  rw [step_length]
  omega

lemma step_old_read (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (r : ℕ) (hr : r < n + (net s).length) :
    (run (net (step n seeds edges weight v s)) labels y).getD r false =
      (run (net s) labels y).getD r false := by
  obtain ⟨hs, he⟩ := step_extension n seeds edges weight v s
  rw [he, run_append]
  exact run_getD_lt hs labels _ r (by simpa only [run_length, hy] using hr)

lemma step_context_eq (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) :
    context (step n seeds edges weight v s) v =
      (aggregate n (net s) (incoming seeds edges (message s) v)).2 := by
  cases hw : weight v <;> simp [step, context, hw]

lemma step_context_ne (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (u : ℕ) (hu : u ≠ v) :
    context (step n seeds edges weight v s) u = context s u := by
  cases hw : weight v <;> simp [step, context, hw, hu]

lemma step_message_ne (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (u : ℕ) (hu : u ≠ v) :
    message (step n seeds edges weight v s) u = message s u := by
  cases hw : weight v <;> simp [step, message, hw, hu]

lemma step_valid (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (hs : valid n s)
    (hseeds : ∀ e ∈ seeds, e.2 < n + (net s).length) :
    valid n (step n seeds edges weight v s) := by
  let a := aggregate n (net s) (incoming seeds edges (message s) v)
  have ha : a.2 < n + a.1.length :=
    aggregate_root_valid n (net s) _ hs.1 (incoming_valid n seeds edges v s hs hseeds)
  have hh : a.1.head? = some (Sum.inl []) := aggregate_head n (net s) _ hs.1
  have hl : (net s).length ≤ a.1.length := by
    dsimp [a]
    rw [aggregate_length]
    omega
  cases hw : weight v with
  | none =>
    change (net (step n seeds edges weight v s)).head? = _ ∧ _
    refine ⟨by simpa only [step, net, hw, a] using hh, ?_, ?_⟩
    · intro u
      simp only [context, step, hw, net]
      change Function.update (context s) v a.2 u < n + a.1.length
      by_cases hu : u = v
      · simpa [hu] using ha
      · simpa [hu] using (show context s u < n + a.1.length by have := hs.2.1 u; omega)
    · intro u
      simp only [message, step, hw, net]
      change Function.update (message s) v a.2 u < n + a.1.length
      by_cases hu : u = v
      · simpa [hu] using ha
      · simpa [hu] using (show message s u < n + a.1.length by have := hs.2.2 u; omega)
  | some z =>
    have hhead : (a.1 ++ [Sum.inr (z, a.2)]).head? = some (Sum.inl []) := by
      cases he : a.1 with
      | nil => simp [he] at hh
      | cons g gs => simpa [he] using hh
    refine ⟨by simpa only [step, net, hw, a] using hhead, ?_, ?_⟩
    · intro u
      simp only [context, step, hw, net]
      change Function.update (context s) v a.2 u < n + (a.1 ++ [Sum.inr (z, a.2)]).length
      simp only [List.length_append, List.length_singleton]
      by_cases hu : u = v
      · simpa [hu] using (show a.2 < n + (a.1.length + 1) by omega)
      · simpa [hu] using (show context s u < n + (a.1.length + 1) by have := hs.2.1 u; omega)
    · intro u
      simp only [message, step, hw, net]
      change Function.update (message s) v (n + a.1.length) u <
        n + (a.1 ++ [Sum.inr (z, a.2)]).length
      simp only [List.length_append, List.length_singleton]
      by_cases hu : u = v
      · simp [hu]
      · simpa [hu] using (show message s u < n + (a.1.length + 1) by have := hs.2.2 u; omega)

def weightValue (labels : ℕ → Bool) (weight : ℕ → Option ℕ) (v : ℕ) : Bool :=
  (weight v).elim true labels

lemma step_context_true (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (hs : valid n s)
    (hseeds : ∀ e ∈ seeds, e.2 < n + (net s).length)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n) :
    (run (net (step n seeds edges weight v s)) labels y).getD
      (context (step n seeds edges weight v s) v) false = true ↔
        ∃ r ∈ incoming seeds edges (message s) v,
          (run (net s) labels y).getD r false = true := by
  let rs := incoming seeds edges (message s) v
  have hrs := incoming_valid n seeds edges v s hs hseeds
  have ht := aggregate_true n (net s) rs hs.1 hrs labels y hy
  have hr := aggregate_root_valid n (net s) rs hs.1 hrs
  rw [step_context_eq]
  cases hw : weight v with
  | none => simpa only [step, net, hw, rs] using ht
  | some z =>
    change (run (net (step n seeds edges weight v s)) labels y).getD
      (aggregate n (net s) rs).2 false = true ↔ _
    have hn : net (step n seeds edges weight v s) =
        (aggregate n (net s) rs).1 ++ [Sum.inr (z, (aggregate n (net s) rs).2)] := by
      simp only [step, net, hw, rs]
    rw [hn, snoc_read_old _ _ labels y _ (by simpa only [hy] using hr)]
    exact ht

lemma step_message_true (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (hs : valid n s)
    (hseeds : ∀ e ∈ seeds, e.2 < n + (net s).length)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n) :
    (run (net (step n seeds edges weight v s)) labels y).getD
      (message (step n seeds edges weight v s) v) false = true ↔
        weightValue labels weight v = true ∧
        (run (net (step n seeds edges weight v s)) labels y).getD
          (context (step n seeds edges weight v s) v) false = true := by
  let a := aggregate n (net s) (incoming seeds edges (message s) v)
  have ha : a.2 < n + a.1.length :=
    aggregate_root_valid n (net s) _ hs.1 (incoming_valid n seeds edges v s hs hseeds)
  cases hw : weight v with
  | none => simp [step, net, context, message, hw, weightValue]
  | some z =>
    simp only [step, net, context, message, hw, Function.update_self, weightValue,
      Option.elim_some]
    change (run (a.1 ++ [Sum.inr (z, a.2)]) labels y).getD (n + a.1.length) false = true ↔
      labels z = true ∧ (run (a.1 ++ [Sum.inr (z, a.2)]) labels y).getD a.2 false = true
    have hn := snoc_read_new a.1 (Sum.inr (z, a.2)) labels y
    rw [hy] at hn
    rw [hn, snoc_read_old _ _ labels y _ (by simpa only [hy] using ha)]
    simp [Pilot5bMeta1020Linear.step]

lemma step_context_read_ne (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (hs : valid n s) (labels : ℕ → Bool)
    (y : List Bool) (hy : y.length = n) (u : ℕ) (hu : u ≠ v) :
    (run (net (step n seeds edges weight v s)) labels y).getD
      (context (step n seeds edges weight v s) u) false =
        (run (net s) labels y).getD (context s u) false := by
  rw [step_context_ne _ _ _ _ _ _ _ hu]
  exact step_old_read n seeds edges weight v s labels y hy _ (hs.2.1 u)

lemma step_message_read_ne (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (hs : valid n s) (labels : ℕ → Bool)
    (y : List Bool) (hy : y.length = n) (u : ℕ) (hu : u ≠ v) :
    (run (net (step n seeds edges weight v s)) labels y).getD
      (message (step n seeds edges weight v s) u) false =
        (run (net s) labels y).getD (message s u) false := by
  rw [step_message_ne _ _ _ _ _ _ _ hu]
  exact step_old_read n seeds edges weight v s labels y hy _ (hs.2.2 u)

end Pilot5bMeta1020Reverse
