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

namespace Pilot5bMeta1020ReverseRecurrence

def descend {σ : Type*} (step : ℕ → σ → σ) : ℕ → σ → σ
  | 0, s => s
  | k + 1, s => descend step k (step k s)

def Correct {σ : Type*} (V : ℕ) (ctx msg : σ → ℕ → Bool)
    (weight target : ℕ → Bool) (k : ℕ) (s : σ) : Prop :=
  ∀ u, k ≤ u → u < V → ctx s u = target u ∧ msg s u = (weight u && target u)

lemma descend_invariant {σ : Type*} (V : ℕ) (step : ℕ → σ → σ)
    (ctx msg : σ → ℕ → Bool) (weight target : ℕ → Bool) (Valid : σ → Prop)
    (hvalid : ∀ v, v < V → ∀ s, Valid s → Valid (step v s))
    (hother : ∀ v, v < V → ∀ s, Valid s → ∀ u, u ≠ v →
      ctx (step v s) u = ctx s u ∧ msg (step v s) u = msg s u)
    (hnew : ∀ v, v < V → ∀ s, Valid s →
      (∀ u, v < u → u < V → msg s u = (weight u && target u)) →
      ctx (step v s) v = target v ∧ msg (step v s) v = (weight v && target v)) :
    ∀ k, k ≤ V → ∀ s, Valid s → Correct V ctx msg weight target k s →
      Valid (descend step k s) ∧ Correct V ctx msg weight target 0 (descend step k s) := by
  intro k
  induction k with
  | zero =>
    intro _ s hs hc
    exact ⟨hs, hc⟩
  | succ k ih =>
    intro hk s hs hc
    have hkv : k < V := by omega
    have hn := hnew k hkv s hs (by
      intro u hku hu
      exact (hc u (by omega) hu).2)
    have hnext : Correct V ctx msg weight target k (step k s) := by
      intro u hku hu
      by_cases huk : u = k
      · subst u
        exact hn
      · obtain ⟨hctx, hmsg⟩ := hother k hkv s hs u huk
        obtain ⟨hct, hmt⟩ := hc u (by omega) hu
        exact ⟨hctx.trans hct, hmsg.trans hmt⟩
    exact ih (by omega) (step k s) (hvalid k hkv s hs) hnext

def incomingValue (edges : List (ℕ × ℕ)) (v : ℕ) (msg : ℕ → Bool) : Bool :=
  edges.any fun e => decide (e.2 = v) && msg e.1

lemma incoming_congr (V : ℕ) (edges : List (ℕ × ℕ))
    (hedge : ∀ e ∈ edges, e.2 < e.1 ∧ e.1 < V)
    (v : ℕ) (msg msg' : ℕ → Bool)
    (hmsg : ∀ u, v < u → u < V → msg u = msg' u) :
    incomingValue edges v msg = incomingValue edges v msg' := by
  have hpoint : ∀ e ∈ edges,
      (decide (e.2 = v) && msg e.1) = (decide (e.2 = v) && msg' e.1) := by
    intro e he
    by_cases hev : e.2 = v
    · obtain ⟨hlt, hb⟩ := hedge e he
      have hp : v < e.1 := by omega
      simp [hev, hmsg e.1 hp hb]
    · simp [hev]
  apply Bool.eq_iff_iff.mpr
  simp only [incomingValue, List.any_eq_true]
  constructor
  · rintro ⟨e, he, hv⟩
    exact ⟨e, he, (hpoint e he) ▸ hv⟩
  · rintro ⟨e, he, hv⟩
    exact ⟨e, he, (hpoint e he).symm ▸ hv⟩

theorem descend_recurrence {σ : Type*} (V : ℕ) (step : ℕ → σ → σ)
    (ctx msg : σ → ℕ → Bool) (weight target seed : ℕ → Bool)
    (edges : List (ℕ × ℕ)) (Valid : σ → Prop)
    (hedge : ∀ e ∈ edges, e.2 < e.1 ∧ e.1 < V)
    (hvalid : ∀ v, v < V → ∀ s, Valid s → Valid (step v s))
    (hother : ∀ v, v < V → ∀ s, Valid s → ∀ u, u ≠ v →
      ctx (step v s) u = ctx s u ∧ msg (step v s) u = msg s u)
    (hctx : ∀ v, v < V → ∀ s, Valid s →
      ctx (step v s) v = (seed v || incomingValue edges v (msg s)))
    (hmsg : ∀ v, v < V → ∀ s, Valid s →
      msg (step v s) v = (weight v && ctx (step v s) v))
    (htarget : ∀ v, v < V →
      target v = (seed v || incomingValue edges v (fun u => weight u && target u)))
    (initial : σ) (hinitial : Valid initial) :
    Valid (descend step V initial) ∧
      ∀ u, u < V → ctx (descend step V initial) u = target u ∧
        msg (descend step V initial) u = (weight u && target u) := by
  have hn : ∀ v, v < V → ∀ s, Valid s →
      (∀ u, v < u → u < V → msg s u = (weight u && target u)) →
      ctx (step v s) v = target v ∧ msg (step v s) v = (weight v && target v) := by
    intro v hv s hs hparents
    have hc : ctx (step v s) v = target v := by
      rw [hctx v hv s hs,
        incoming_congr V edges hedge v (msg s) (fun u => weight u && target u) hparents]
      exact (htarget v hv).symm
    exact ⟨hc, by rw [hmsg v hv s hs, hc]⟩
  obtain ⟨hf, hc⟩ := descend_invariant V step ctx msg weight target Valid hvalid hother hn
    V le_rfl initial hinitial (by
      intro u hlu huu
      omega)
  exact ⟨hf, fun u hu => hc u (Nat.zero_le _) hu⟩

end Pilot5bMeta1020ReverseRecurrence
/-! Append after ReverseNetwork and ReverseRecurrence. -/
namespace Pilot5bMeta1020ReverseCorrectness

open Pilot5bMeta1020Linear Pilot5bMeta1020Reverse

abbrev read (labels : ℕ → Bool) (y : List Bool) (s : State) (w : ℕ) : Bool :=
  (run (net s) labels y).getD w false

abbrev ctxRead (labels : ℕ → Bool) (y : List Bool) (s : State) (v : ℕ) : Bool :=
  read labels y s (context s v)

abbrev msgRead (labels : ℕ → Bool) (y : List Bool) (s : State) (v : ℕ) : Bool :=
  read labels y s (message s v)

def seedValue (seeds : List (ℕ × ℕ)) (baseRead : ℕ → Bool) (v : ℕ) : Bool :=
  seeds.any fun e => decide (e.1 = v) && baseRead e.2

lemma seedValue_true (seeds : List (ℕ × ℕ)) (baseRead : ℕ → Bool) (v : ℕ) :
    seedValue seeds baseRead v = true ↔
      ∃ e ∈ seeds, e.1 = v ∧ baseRead e.2 = true := by
  simp [seedValue]

lemma incomingValue_true (edges : List (ℕ × ℕ)) (values : ℕ → Bool) (v : ℕ) :
    Pilot5bMeta1020ReverseRecurrence.incomingValue edges v values = true ↔
      ∃ e ∈ edges, e.2 = v ∧ values e.1 = true := by
  simp [Pilot5bMeta1020ReverseRecurrence.incomingValue]

def Stable (n : ℕ) (seeds : List (ℕ × ℕ)) (labels : ℕ → Bool)
    (y : List Bool) (baseRead : ℕ → Bool) (s : State) : Prop :=
  valid n s ∧ ∀ e ∈ seeds,
    e.2 < n + (net s).length ∧ read labels y s e.2 = baseRead e.2

lemma stable_step (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (baseRead : ℕ → Bool) (v : ℕ) (s : State)
    (hs : Stable n seeds labels y baseRead s) :
    Stable n seeds labels y baseRead (Pilot5bMeta1020Reverse.step n seeds edges weight v s) := by
  refine ⟨step_valid n seeds edges weight v s hs.1 (fun e he => (hs.2 e he).1), ?_⟩
  intro e he
  obtain ⟨hev, her⟩ := hs.2 e he
  have hlen := step_length_le n seeds edges weight v s
  refine ⟨by omega, ?_⟩
  exact (step_old_read n seeds edges weight v s labels y hy e.2 hev).trans her

lemma context_step (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (baseRead : ℕ → Bool) (v : ℕ) (s : State)
    (hs : Stable n seeds labels y baseRead s) :
    ctxRead labels y (Pilot5bMeta1020Reverse.step n seeds edges weight v s) v =
      (seedValue seeds baseRead v ||
        Pilot5bMeta1020ReverseRecurrence.incomingValue edges v (msgRead labels y s)) := by
  apply Bool.eq_iff_iff.mpr
  rw [step_context_true n seeds edges weight v s hs.1
    (fun e he => (hs.2 e he).1) labels y hy]
  rw [Bool.or_eq_true, seedValue_true, incomingValue_true]
  constructor
  · rintro ⟨r, hr, hv⟩
    rcases (mem_incoming seeds edges (message s) v r).mp hr with hh | hh
    · obtain ⟨e, he, hev, rfl⟩ := hh
      exact Or.inl ⟨e, he, hev, (hs.2 e he).2 ▸ hv⟩
    · obtain ⟨e, he, hev, rfl⟩ := hh
      exact Or.inr ⟨e, he, hev, hv⟩
  · rintro (⟨e, he, hev, hv⟩ | ⟨e, he, hev, hv⟩)
    · refine ⟨e.2, (mem_incoming seeds edges (message s) v e.2).mpr
        (Or.inl ⟨e, he, hev, rfl⟩), ?_⟩
      change read labels y s e.2 = true
      rw [(hs.2 e he).2]
      exact hv
    · exact ⟨message s e.1, (mem_incoming seeds edges (message s) v _).mpr
        (Or.inr ⟨e, he, hev, rfl⟩), hv⟩

lemma message_step (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (baseRead : ℕ → Bool) (v : ℕ) (s : State)
    (hs : Stable n seeds labels y baseRead s) :
    msgRead labels y (Pilot5bMeta1020Reverse.step n seeds edges weight v s) v =
      (weightValue labels weight v &&
        ctxRead labels y (Pilot5bMeta1020Reverse.step n seeds edges weight v s) v) := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.and_eq_true]
  exact step_message_true n seeds edges weight v s hs.1
    (fun e he => (hs.2 e he).1) labels y hy

lemma build_eq_descend (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) :
    build n seeds edges weight k s =
      Pilot5bMeta1020ReverseRecurrence.descend
        (Pilot5bMeta1020Reverse.step n seeds edges weight) k s := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => exact ih _

theorem build_correct (n V : ℕ) (seeds edges : List (ℕ × ℕ))
    (weight : ℕ → Option ℕ) (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (baseRead target : ℕ → Bool)
    (hedge : ∀ e ∈ edges, e.2 < e.1 ∧ e.1 < V)
    (htarget : ∀ v, v < V → target v =
      (seedValue seeds baseRead v ||
        Pilot5bMeta1020ReverseRecurrence.incomingValue edges v
          (fun u => weightValue labels weight u && target u)))
    (initial : State) (hinitial : Stable n seeds labels y baseRead initial) :
    Stable n seeds labels y baseRead (build n seeds edges weight V initial) ∧
      ∀ u, u < V →
        ctxRead labels y (build n seeds edges weight V initial) u = target u ∧
        msgRead labels y (build n seeds edges weight V initial) u =
          (weightValue labels weight u && target u) := by
  have h := Pilot5bMeta1020ReverseRecurrence.descend_recurrence V
    (Pilot5bMeta1020Reverse.step n seeds edges weight) (ctxRead labels y) (msgRead labels y)
    (weightValue labels weight) target (seedValue seeds baseRead) edges
    (Stable n seeds labels y baseRead) hedge
    (fun v _ s hs => stable_step n seeds edges weight labels y hy baseRead v s hs)
    (fun v _ s hs u hu => ⟨
      step_context_read_ne n seeds edges weight v s hs.1 labels y hy u hu,
      step_message_read_ne n seeds edges weight v s hs.1 labels y hy u hu⟩)
    (fun v _ s hs => context_step n seeds edges weight labels y hy baseRead v s hs)
    (fun v _ s hs => message_step n seeds edges weight labels y hy baseRead v s hs)
    htarget initial hinitial
  simpa only [build_eq_descend] using h

lemma stable_initial (n : ℕ) (gs : List Instruction) (seeds : List (ℕ × ℕ))
    (hz : gs.head? = some (Sum.inl []))
    (hseeds : ∀ e ∈ seeds, e.2 < n + gs.length)
    (labels : ℕ → Bool) (y : List Bool) :
    Stable n seeds labels y (fun r => (run gs labels y).getD r false) (initial n gs) := by
  refine ⟨initial_valid n gs hz, ?_⟩
  intro e he
  exact ⟨hseeds e he, rfl⟩

end Pilot5bMeta1020ReverseCorrectness

namespace Pilot5bMeta1020Weighted

def activeEdge (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (u v : ℕ) : Prop := (u, v) ∈ edges ∧ weightEval u = true

def seedReachable (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ) : Prop :=
  ∃ s ∈ seeds, seedEval s.2 = true ∧
    Relation.ReflTransGen (activeEdge edges weightEval) s.1 v

noncomputable def target (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ) : Bool := by
  classical
  exact decide (seedReachable edges weightEval seeds seedEval v)

@[simp] lemma target_true (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ) :
    target edges weightEval seeds seedEval v = true ↔
      seedReachable edges weightEval seeds seedEval v := by
  classical
  simp [target]

theorem target_recurrence (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ) :
    target edges weightEval seeds seedEval v = true ↔
      (∃ s ∈ seeds, s.1 = v ∧ seedEval s.2 = true) ∨
      ∃ e ∈ edges, e.2 = v ∧ weightEval e.1 = true ∧
        target edges weightEval seeds seedEval e.1 = true := by
  constructor
  · intro ht
    obtain ⟨s, hs, hb, hp⟩ := (target_true edges weightEval seeds seedEval v).mp ht
    rcases hp.cases_tail with h | ⟨u, hsu, huv⟩
    · exact Or.inl ⟨s, hs, h.symm, hb⟩
    · refine Or.inr ⟨(u, v), huv.1, rfl, huv.2, ?_⟩
      exact (target_true edges weightEval seeds seedEval u).mpr ⟨s, hs, hb, hsu⟩
  · rintro (⟨s, hs, hv, hb⟩ | ⟨e, he, hv, hw, hu⟩)
    · apply (target_true edges weightEval seeds seedEval v).mpr
      refine ⟨s, hs, hb, ?_⟩
      simpa only [hv] using
        (Relation.ReflTransGen.refl : Relation.ReflTransGen (activeEdge edges weightEval) s.1 s.1)
    · obtain ⟨s, hs, hb, hsu⟩ := (target_true edges weightEval seeds seedEval e.1).mp hu
      apply (target_true edges weightEval seeds seedEval v).mpr
      refine ⟨s, hs, hb, hsu.tail ?_⟩
      exact ⟨by simpa only [← hv] using he, hw⟩

theorem target_recurrence_eq (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ) :
    target edges weightEval seeds seedEval v =
      ((seeds.any fun s => decide (s.1 = v) && seedEval s.2) ||
        (edges.any fun e => decide (e.2 = v) &&
          (weightEval e.1 && target edges weightEval seeds seedEval e.1))) := by
  apply Bool.eq_iff_iff.mpr
  rw [target_recurrence]
  simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]

lemma target_of_seed (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (s : ℕ × ℕ)
    (hs : s ∈ seeds) (hb : seedEval s.2 = true) :
    target edges weightEval seeds seedEval s.1 = true :=
  (target_true edges weightEval seeds seedEval s.1).mpr ⟨s, hs, hb, .refl⟩

lemma target_of_edge (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (u v : ℕ)
    (he : (u, v) ∈ edges) (hw : weightEval u = true)
    (hu : target edges weightEval seeds seedEval u = true) :
    target edges weightEval seeds seedEval v = true :=
  (target_recurrence edges weightEval seeds seedEval v).mpr
    (Or.inr ⟨(u, v), he, rfl, hw, hu⟩)

lemma rtc_backward {α : Type*} {R : α → α → Prop} {F : α → Prop}
    (hstep : ∀ u v, R u v → F v → F u) {s v : α}
    (hpath : Relation.ReflTransGen R s v) : F v → F s := by
  induction hpath with
  | refl => exact id
  | @tail u v hsu huv ih => exact fun hv => ih (hstep u v huv hv)

theorem backward_propagation (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (F : ℕ → Prop)
    (hstep : ∀ u v, (u, v) ∈ edges → weightEval u = true → F v → F u)
    {s v : ℕ} (hpath : Relation.ReflTransGen (activeEdge edges weightEval) s v)
    (hv : F v) : F s :=
  rtc_backward (fun u v h => hstep u v h.1 h.2) hpath hv

lemma target_backward_seed (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (F : ℕ → Prop)
    (hstep : ∀ u v, (u, v) ∈ edges → weightEval u = true → F v → F u)
    (v : ℕ) (ht : target edges weightEval seeds seedEval v = true) (hv : F v) :
    ∃ s ∈ seeds, seedEval s.2 = true ∧ F s.1 := by
  obtain ⟨s, hs, hb, hpath⟩ := (target_true edges weightEval seeds seedEval v).mp ht
  exact ⟨s, hs, hb, backward_propagation edges weightEval F hstep hpath hv⟩

lemma rtc_forward {α : Type*} {R : α → α → Prop} {F : α → Prop}
    (hstep : ∀ u v, R u v → F u → F v) {s v : α}
    (hpath : Relation.ReflTransGen R s v) : F s → F v := by
  induction hpath with
  | refl => exact id
  | @tail u v hsu huv ih => exact fun hs => hstep u v huv (ih hs)

theorem target_cover (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (F : ℕ → Prop)
    (hseed : ∀ s ∈ seeds, seedEval s.2 = true → F s.1)
    (hstep : ∀ u v, (u, v) ∈ edges → weightEval u = true → F u → F v)
    (v : ℕ) (ht : target edges weightEval seeds seedEval v = true) : F v := by
  obtain ⟨s, hs, hb, hpath⟩ := (target_true edges weightEval seeds seedEval v).mp ht
  exact rtc_forward (fun u v h => hstep u v h.1 h.2) hpath (hseed s hs hb)

lemma target_true_iff_seed_of_no_active_incoming
    (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ)
    (hin : ∀ u, ¬ activeEdge edges weightEval u v) :
    target edges weightEval seeds seedEval v = true ↔
      ∃ s ∈ seeds, s.1 = v ∧ seedEval s.2 = true := by
  rw [target_recurrence]
  constructor
  · rintro (hs | ⟨e, he, hv, hw, _⟩)
    · exact hs
    · exact (hin e.1 ⟨by simpa only [← hv] using he, hw⟩).elim
  · exact Or.inl

lemma target_true_iff_seed_of_no_incoming
    (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ)
    (hin : ∀ e ∈ edges, e.2 ≠ v) :
    target edges weightEval seeds seedEval v = true ↔
      ∃ s ∈ seeds, s.1 = v ∧ seedEval s.2 = true := by
  apply target_true_iff_seed_of_no_active_incoming
  intro u hu
  exact hin (u, v) hu.1 rfl

lemma target_false_of_no_incoming_no_seed
    (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ)
    (hin : ∀ e ∈ edges, e.2 ≠ v)
    (hseed : ∀ s ∈ seeds, s.1 = v → seedEval s.2 = false) :
    target edges weightEval seeds seedEval v = false := by
  apply Bool.eq_false_of_not_eq_true
  intro ht
  obtain ⟨s, hs, hv, hb⟩ :=
    (target_true_iff_seed_of_no_incoming edges weightEval seeds seedEval v hin).mp ht
  simp [hseed s hs hv] at hb

@[simp] lemma target_empty_seeds (edges : List (ℕ × ℕ)) (weightEval : ℕ → Bool)
    (seedEval : ℕ → Bool) (v : ℕ) : target edges weightEval [] seedEval v = false := by
  classical
  simp [target, seedReachable]

lemma target_empty_edges (weightEval : ℕ → Bool)
    (seeds : List (ℕ × ℕ)) (seedEval : ℕ → Bool) (v : ℕ) :
    target [] weightEval seeds seedEval v = true ↔
      ∃ s ∈ seeds, s.1 = v ∧ seedEval s.2 = true :=
  target_true_iff_seed_of_no_incoming [] weightEval seeds seedEval v (by simp)

end Pilot5bMeta1020Weighted
/-! Append after WeightedReachability and ReverseCorrectness. -/
namespace Pilot5bMeta1020ReverseWeightedCorrectness

open Pilot5bMeta1020Linear Pilot5bMeta1020Reverse Pilot5bMeta1020ReverseCorrectness

 theorem build_weighted (n V : ℕ) (seeds edges : List (ℕ × ℕ))
    (weight : ℕ → Option ℕ) (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (baseRead : ℕ → Bool)
    (hedge : ∀ e ∈ edges, e.2 < e.1 ∧ e.1 < V)
    (s : State) (hs : Stable n seeds labels y baseRead s) :
    Stable n seeds labels y baseRead (build n seeds edges weight V s) ∧
      ∀ u, u < V →
        ctxRead labels y (build n seeds edges weight V s) u =
          Pilot5bMeta1020Weighted.target edges (weightValue labels weight) seeds baseRead u ∧
        msgRead labels y (build n seeds edges weight V s) u =
          (weightValue labels weight u &&
            Pilot5bMeta1020Weighted.target edges (weightValue labels weight) seeds baseRead u) := by
  apply build_correct n V seeds edges weight labels y hy baseRead
    (Pilot5bMeta1020Weighted.target edges (weightValue labels weight) seeds baseRead) hedge
    (fun v _ => ?_) s hs
  exact Pilot5bMeta1020Weighted.target_recurrence_eq edges (weightValue labels weight)
    seeds baseRead v

 theorem build_initial (n V : ℕ) (gs : List Instruction) (seeds edges : List (ℕ × ℕ))
    (weight : ℕ → Option ℕ) (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (hz : gs.head? = some (Sum.inl []))
    (hseeds : ∀ e ∈ seeds, e.2 < n + gs.length)
    (hedge : ∀ e ∈ edges, e.2 < e.1 ∧ e.1 < V) :
    valid n (build n seeds edges weight V (initial n gs)) ∧
      ∀ u, u < V →
        ctxRead labels y (build n seeds edges weight V (initial n gs)) u =
          Pilot5bMeta1020Weighted.target edges (weightValue labels weight) seeds
            (fun r => (run gs labels y).getD r false) u ∧
        msgRead labels y (build n seeds edges weight V (initial n gs)) u =
          (weightValue labels weight u &&
            Pilot5bMeta1020Weighted.target edges (weightValue labels weight) seeds
              (fun r => (run gs labels y).getD r false) u) := by
  have h := build_weighted n V seeds edges weight labels y hy
    (fun r => (run gs labels y).getD r false) hedge (initial n gs)
    (stable_initial n gs seeds hz hseeds labels y)
  exact ⟨h.1.1, h.2⟩

 theorem context_true_iff (n V : ℕ) (gs : List Instruction) (seeds edges : List (ℕ × ℕ))
    (weight : ℕ → Option ℕ) (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (hz : gs.head? = some (Sum.inl []))
    (hseeds : ∀ e ∈ seeds, e.2 < n + gs.length)
    (hedge : ∀ e ∈ edges, e.2 < e.1 ∧ e.1 < V) (v : ℕ) (hv : v < V) :
    ctxRead labels y (build n seeds edges weight V (initial n gs)) v = true ↔
      Pilot5bMeta1020Weighted.seedReachable edges (weightValue labels weight) seeds
        (fun r => (run gs labels y).getD r false) v := by
  rw [((build_initial n V gs seeds edges weight labels y hy hz hseeds hedge).2 v hv).1]
  exact Pilot5bMeta1020Weighted.target_true edges (weightValue labels weight) seeds
    (fun r => (run gs labels y).getD r false) v

end Pilot5bMeta1020ReverseWeightedCorrectness