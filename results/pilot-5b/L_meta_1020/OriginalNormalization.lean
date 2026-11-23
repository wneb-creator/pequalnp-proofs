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

namespace Pilot5bMeta1020Forward

open PEqualNP.CircuitLowerBounds
open Pilot5bMeta1020Linear

abbrev State := List Instruction × (List ℕ × List ℕ)

def net (s : State) : List Instruction := s.1
def one (s : State) : List ℕ := s.2.1
def degrees (s : State) : List ℕ := s.2.2

def initial (N : ℕ) : State :=
  ([Sum.inl []],
    (List.replicate N N ++ List.range N,
     List.replicate N 0 ++ List.replicate N 1))

def labelRead (zeroLabel : ℕ) (s : State) (r : ℕ) : ℕ :=
  if r < (one s).length then r else zeroLabel

def payload (N zeroLabel : ℕ) (s : State) (g : Gate) : List Instruction :=
  let d := g.lineDegree (degrees s)
  let a := fun r => (one s).getD r N
  let z := labelRead zeroLabel s
  if d = 1 ∨ d = 2 then
    match g.op, g.inputs with
    | .or, rs => [Sum.inl (rs.map a)]
    | .and, [r] => [Sum.inl [a r]]
    | .and, [r, t] =>
        if (degrees s).getD r 0 = 1 ∧ (degrees s).getD t 0 = 1 then
          [Sum.inr (z r, a t), Sum.inr (z t, a r),
            Sum.inl [N + (net s).length, N + (net s).length + 1]]
        else if (degrees s).getD r 0 = 0 then [Sum.inr (z r, a t)]
        else if (degrees s).getD t 0 = 0 then [Sum.inr (z t, a r)]
        else []
    | _, _ => []
  else []

def out (N zeroLabel : ℕ) (s : State) (g : Gate) : ℕ :=
  let ps := payload N zeroLabel s g
  if ps = [] then N else N + (net s).length + ps.length - 1

def advance (N zeroLabel : ℕ) (s : State) (g : Gate) : State :=
  (net s ++ payload N zeroLabel s g,
    (one s ++ [out N zeroLabel s g],
     degrees s ++ [g.lineDegree (degrees s)]))

def build (N zeroLabel : ℕ) (gs : List Gate) : State :=
  gs.foldl (advance N zeroLabel) (initial N)

def normalize (N : ℕ) (C : Circuit) : State :=
  build N (N + N + C.size) C.gates

def forwardWeight (s : State) (g : Gate) : ℕ :=
  let d := g.lineDegree (degrees s)
  if d = 1 then 1 else if d = 2 then
    match g.op, g.inputs with
    | .and, [r, t] =>
      if (degrees s).getD r 0 = 1 ∧ (degrees s).getD t 0 = 1 then 3 else 1
    | _, _ => 1
  else 0

lemma advance_net (N z : ℕ) (s : State) (g : Gate) :
    net (advance N z s g) = net s ++ payload N z s g := rfl

lemma advance_one (N z : ℕ) (s : State) (g : Gate) :
    one (advance N z s g) = one s ++ [out N z s g] := rfl

lemma advance_degrees (N z : ℕ) (s : State) (g : Gate) :
    degrees (advance N z s g) = degrees s ++ [g.lineDegree (degrees s)] := rfl

lemma payload_length_le_three (N z : ℕ) (s : State) (g : Gate) :
    (payload N z s g).length ≤ 3 := by
  unfold payload
  dsimp only
  split_ifs
  all_goals try split
  all_goals try split_ifs
  all_goals simp_all

lemma payload_length_le_weight (N z : ℕ) (s : State) (g : Gate) :
    (payload N z s g).length ≤ forwardWeight s g := by
  unfold payload forwardWeight
  dsimp only
  split_ifs
  all_goals try split
  all_goals try split_ifs
  all_goals simp_all [Gate.lineDegree]

lemma weight_le_three (s : State) (g : Gate) : forwardWeight s g ≤ 3 := by
  unfold forwardWeight
  dsimp only
  split_ifs
  all_goals try split
  all_goals try split_ifs
  all_goals omega

lemma build_one_length (N z : ℕ) (gs : List Gate) :
    (one (build N z gs)).length = N + N + gs.length := by
  have hgen : ∀ (s : State),
      (one (gs.foldl (advance N z) s)).length = (one s).length + gs.length := by
    induction gs with
    | nil => intro s; simp
    | cons g gs ih =>
      intro s
      rw [List.foldl_cons, ih, advance_one]
      simp
      omega
  simpa [build, initial, one, List.length_replicate, List.length_range, Nat.add_assoc]
    using hgen (initial N)

lemma build_degrees_length (N z : ℕ) (gs : List Gate) :
    (degrees (build N z gs)).length = N + N + gs.length := by
  have hgen : ∀ (s : State),
      (degrees (gs.foldl (advance N z) s)).length = (degrees s).length + gs.length := by
    induction gs with
    | nil => intro s; simp
    | cons g gs ih =>
      intro s
      rw [List.foldl_cons, ih, advance_degrees]
      simp
      omega
  simpa [build, initial, degrees, List.length_replicate, Nat.add_assoc]
    using hgen (initial N)

lemma build_net_length (N z : ℕ) (gs : List Gate) :
    (net (build N z gs)).length ≤ 1 + 3 * gs.length := by
  have hgen : ∀ (s : State),
      (net (gs.foldl (advance N z) s)).length ≤ (net s).length + 3 * gs.length := by
    induction gs with
    | nil => intro s; simp
    | cons g gs ih =>
      intro s
      rw [List.foldl_cons]
      have h := ih (advance N z s g)
      rw [advance_net, List.length_append] at h
      have hp := payload_length_le_three N z s g
      simp only [List.length_cons]
      omega
  simpa [build, initial, net] using hgen (initial N)

def coefficient (g : Gate) (Z P : ℕ → Bool) : Bool :=
  match g.op, g.inputs with
  | .or, rs => (rs.map P).any id
  | .and, [] => false
  | .and, [r] => P r
  | .and, [r, t] => (Z r && P t) || (P r && Z t)
  | _, _ => false

lemma coefficient_congr (g : Gate) (Z P Z' P' : ℕ → Bool)
    (hZ : ∀ r ∈ g.inputs, Z r = Z' r)
    (hP : ∀ r ∈ g.inputs, P r = P' r) :
    coefficient g Z P = coefficient g Z' P' := by
  rcases g with ⟨op, rs⟩
  cases op with
  | or =>
    simp only [coefficient]
    congr 1
    apply List.map_congr_left
    intro r hr
    exact hP r hr
  | and =>
    cases rs with
    | nil => rfl
    | cons r rs =>
      cases rs with
      | nil => exact hP r (by simp)
      | cons t rs =>
        cases rs with
        | nil =>
          simp only [coefficient]
          rw [hZ r (by simp), hZ t (by simp), hP r (by simp), hP t (by simp)]
        | cons u rs => rfl
  | not => rfl
  | mod n => rfl
  | maj => rfl

lemma coefficient_zero_of_children (g : Gate) (Z P : ℕ → Bool)
    (hP : ∀ r ∈ g.inputs, P r = false) : coefficient g Z P = false := by
  have heq := coefficient_congr g Z P Z (fun _ => false)
    (fun _ _ => rfl) hP
  rw [heq]
  rcases g with ⟨op, rs⟩
  cases op with
  | or => simp [coefficient]
  | and =>
    cases rs with
    | nil => rfl
    | cons r rs =>
      cases rs with
      | nil => rfl
      | cons t rs => cases rs <;> simp [coefficient]
  | not => rfl
  | mod n => rfl
  | maj => rfl

lemma run_one_read (g : Instruction) (labels : ℕ → Bool) (v : List Bool) :
    (run [g] labels v).getD v.length false = step labels v g := by
  simpa [run] using snoc_read_new [] g labels v

lemma run_two_labels_or (labels : ℕ → Bool) (v : List Bool)
    (a b c d : ℕ) (hb : b < v.length) (hd : d < v.length) :
    (run [Sum.inr (a, b), Sum.inr (c, d),
      Sum.inl [v.length, v.length + 1]] labels v).getD (v.length + 2) false =
      ((labels a && v.getD b false) || (labels c && v.getD d false)) := by
  have hlast := snoc_read_new [Sum.inr (a, b), Sum.inr (c, d)]
    (Sum.inl [v.length, v.length + 1]) labels v
  have hfirst := snoc_read_old [Sum.inr (a, b)] (Sum.inr (c, d)) labels v
    v.length (by simp)
  have hsecond := snoc_read_new [Sum.inr (a, b)] (Sum.inr (c, d)) labels v
  have hbase := run_one_read (Sum.inr (a, b)) labels v
  have hold := run_getD_lt [Sum.inr (a, b)] labels v d hd
  simp only [List.length_cons, List.length_nil, Nat.add_zero, Nat.zero_add,
    List.cons_append, List.nil_append] at hlast hfirst hsecond
  change (run [Sum.inr (a, b), Sum.inr (c, d),
    Sum.inl [v.length, v.length + 1]] labels v).getD (v.length + 2) false = _ at hlast
  rw [hlast]
  simp only [step, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    id_eq, Bool.or_false] at hfirst hsecond hbase ⊢
  rw [hfirst, hbase, hsecond, hold]

lemma payload_value (N zeroLabel : ℕ) (s : State) (g : Gate)
    (labels : ℕ → Bool) (v : List Bool)
    (hlen : v.length = N + (net s).length)
    (hfalse : v.getD N false = false)
    (hN : N < v.length)
    (hmap : ∀ r, (one s).getD r N < v.length)
    (hzero : ∀ r, (degrees s).getD r 0 = 0 →
      v.getD ((one s).getD r N) false = false)
    (hmono : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hfan : g.inputs.length ≤ 2) :
    (run (payload N zeroLabel s g) labels v).getD (out N zeroLabel s g) false =
      if g.lineDegree (degrees s) = 1 ∨ g.lineDegree (degrees s) = 2 then
        coefficient g (fun r => labels (labelRead zeroLabel s r))
          (fun r => v.getD ((one s).getD r N) false)
      else false := by
  classical
  by_cases hdeg : g.lineDegree (degrees s) = 1 ∨ g.lineDegree (degrees s) = 2
  · rw [if_pos hdeg]
    rcases g with ⟨op, rs⟩
    rcases hmono with hop | hop <;> dsimp only at hop hfan <;> subst op
    · cases rs with
      | nil => simp [Gate.lineDegree] at hdeg
      | cons r rs =>
        cases rs with
        | nil =>
          have hp : payload N zeroLabel s ⟨.and, [r]⟩ =
              [Sum.inl [(one s).getD r N]] := by
            simp only [payload, hdeg, ↓reduceIte]
          rw [show out N zeroLabel s ⟨.and, [r]⟩ = v.length by
            simp only [out, hp, List.cons_ne_nil, ↓reduceIte,
              List.length_cons, List.length_nil]
            omega]
          rw [hp, run_one_read]
          simp only [step, coefficient, List.map_cons, List.map_nil,
            List.any_cons, List.any_nil, id_eq, Bool.or_false]
        | cons t rs =>
          cases rs with
          | cons u rs => simp at hfan
          | nil =>
            have hd : (degrees s).getD r 0 + (degrees s).getD t 0 = 1 ∨
                (degrees s).getD r 0 + (degrees s).getD t 0 = 2 := by
              simpa [Gate.lineDegree] using hdeg
            by_cases hf : (degrees s).getD r 0 = 1 ∧ (degrees s).getD t 0 = 1
            · have hp : payload N zeroLabel s ⟨.and, [r, t]⟩ =
                  [Sum.inr (labelRead zeroLabel s r, (one s).getD t N),
                   Sum.inr (labelRead zeroLabel s t, (one s).getD r N),
                   Sum.inl [v.length, v.length + 1]] := by
                simp only [payload, hdeg, ↓reduceIte, hf, hlen] <;> simp
              rw [show out N zeroLabel s ⟨.and, [r, t]⟩ = v.length + 2 by
                simp only [out, hp, List.cons_ne_nil, ↓reduceIte,
                  List.length_cons, List.length_nil]
                omega]
              rw [hp, run_two_labels_or labels v _ _ _ _ (hmap t) (hmap r)]
              simp [coefficient, Bool.and_comm]
            · have hz : (degrees s).getD r 0 = 0 ∨ (degrees s).getD t 0 = 0 := by omega
              rcases hz with hz | hz
              · have hp : payload N zeroLabel s ⟨.and, [r, t]⟩ =
                    [Sum.inr (labelRead zeroLabel s r, (one s).getD t N)] := by
                  simp only [payload, hdeg, ↓reduceIte, hf, hz] <;> simp
                rw [show out N zeroLabel s ⟨.and, [r, t]⟩ = v.length by
                  simp only [out, hp, List.cons_ne_nil, ↓reduceIte,
                    List.length_cons, List.length_nil]
                  omega]
                rw [hp, run_one_read]
                simp only [step, coefficient]
                rw [hzero r hz]
                simp
              · have hr : (degrees s).getD r 0 ≠ 0 := by omega
                have hp : payload N zeroLabel s ⟨.and, [r, t]⟩ =
                    [Sum.inr (labelRead zeroLabel s t, (one s).getD r N)] := by
                  simp only [payload, hdeg, ↓reduceIte, hf, hr, hz] <;> simp
                rw [show out N zeroLabel s ⟨.and, [r, t]⟩ = v.length by
                  simp only [out, hp, List.cons_ne_nil, ↓reduceIte,
                    List.length_cons, List.length_nil]
                  omega]
                rw [hp, run_one_read]
                simp only [step, coefficient]
                rw [hzero t hz]
                simp [Bool.and_comm]
    · have hp : payload N zeroLabel s ⟨.or, rs⟩ =
          [Sum.inl (rs.map fun r => (one s).getD r N)] := by
        simp only [payload, hdeg, ↓reduceIte]
      rw [show out N zeroLabel s ⟨.or, rs⟩ = v.length by
        simp only [out, hp, List.cons_ne_nil, ↓reduceIte,
          List.length_cons, List.length_nil]
        omega]
      rw [hp, run_one_read]
      simp [step, coefficient, List.map_map, Function.comp_def]
  · simpa only [payload, out, hdeg, ↓reduceIte, run, List.foldl_nil] using hfalse

lemma advance_correct (N zeroLabel : ℕ) (s : State) (g : Gate)
    (labels : ℕ → Bool) (v P : List Bool)
    (hlen : v.length = N + (net s).length)
    (hdlen : (degrees s).length = (one s).length)
    (hplen : P.length = (one s).length)
    (hfalse : v.getD N false = false)
    (hN : N < v.length)
    (hmap : ∀ r, (one s).getD r N < v.length)
    (hzero : ∀ r, (degrees s).getD r 0 = 0 →
      v.getD ((one s).getD r N) false = false)
    (hold : ∀ r, (degrees s).getD r 0 ≤ 2 →
      v.getD ((one s).getD r N) false = P.getD r false)
    (hchild : ∀ r ∈ g.inputs, (degrees s).getD r 0 ≤ g.lineDegree (degrees s))
    (hmono : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hfan : g.inputs.length ≤ 2) :
    ∀ r, (degrees (advance N zeroLabel s g)).getD r 0 ≤ 2 →
      (run (payload N zeroLabel s g) labels v).getD
          ((one (advance N zeroLabel s g)).getD r N) false =
        (P ++ [coefficient g (fun t => labels (labelRead zeroLabel s t))
          (fun t => P.getD t false)]).getD r false := by
  intro r hr
  by_cases hlt : r < (one s).length
  · have hd : (degrees (advance N zeroLabel s g)).getD r 0 =
        (degrees s).getD r 0 := by
      rw [advance_degrees, List.getD_append _ _ _ _ (by omega)]
    rw [hd] at hr
    rw [advance_one, List.getD_append _ _ _ _ hlt,
      run_getD_lt _ _ _ _ (hmap r), List.getD_append _ _ _ _ (by omega)]
    exact hold r hr
  · by_cases heq : r = (one s).length
    · subst r
      have hd : (degrees (advance N zeroLabel s g)).getD (one s).length 0 =
          g.lineDegree (degrees s) := by
        rw [advance_degrees, List.getD_append_right _ _ _ _ (by omega)]
        simp only [hdlen, Nat.sub_self, List.getD_cons_zero]
      rw [hd] at hr
      rw [advance_one, List.getD_append_right _ _ _ _ (by omega)]
      simp only [Nat.sub_self, List.getD_cons_zero]
      rw [List.getD_append_right _ _ _ _ (by omega)]
      simp only [hplen, Nat.sub_self, List.getD_cons_zero]
      rw [payload_value N zeroLabel s g labels v hlen hfalse hN hmap hzero hmono hfan]
      by_cases hz : g.lineDegree (degrees s) = 0
      · have hc : coefficient g (fun t => labels (labelRead zeroLabel s t))
            (fun t => P.getD t false) = false := by
          apply coefficient_zero_of_children
          intro t ht
          have hdt : (degrees s).getD t 0 = 0 := by
            have := hchild t ht
            omega
          rw [← hold t (by omega), hzero t hdt]
        rw [hz, hc]
        simp
      · have hp : g.lineDegree (degrees s) = 1 ∨ g.lineDegree (degrees s) = 2 := by omega
        rw [if_pos hp]
        apply coefficient_congr
        · intro t ht; rfl
        · intro t ht
          exact hold t ((hchild t ht).trans hr)
    · have hge : (one s).length + 1 ≤ r := by omega
      have hm : (one (advance N zeroLabel s g)).getD r N = N := by
        apply List.getD_eq_default
        simp only [advance_one, List.length_append, List.length_singleton]
        exact hge
      have hp : (P ++ [coefficient g (fun t => labels (labelRead zeroLabel s t))
          (fun t => P.getD t false)]).getD r false = false := by
        apply List.getD_eq_default
        simp only [List.length_append, List.length_singleton, hplen]
        exact hge
      rw [hm, hp, run_getD_lt _ _ _ _ hN, hfalse]

end Pilot5bMeta1020Forward

namespace Pilot5bMeta1020Forward

open PEqualNP.CircuitLowerBounds
open Pilot5bMeta1020Linear

lemma fold_degrees (N z : ℕ) (gs : List Gate) (s : State) :
    degrees (gs.foldl (advance N z) s) =
      gs.foldl (fun d g => d ++ [g.lineDegree d]) (degrees s) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih, advance_degrees]
    rfl

lemma build_degrees_eq (N z : ℕ) (gs : List Gate) :
    degrees (build N z gs) = gs.foldl (fun d g => d ++ [g.lineDegree d])
      (List.replicate N 0 ++ List.replicate N 1) := by
  exact fold_degrees N z gs (initial N)

lemma initial_degrees_eq (N : ℕ) :
    degrees (initial N) =
      (List.range (N + N)).map (fun i => if i ∈ Finset.Ico N (N + N) then 1 else 0) := by
  change List.replicate N 0 ++ List.replicate N 1 = _
  rw [List.range_add, List.map_append, List.map_map]
  have hleft : (List.range N).map (fun i => if i ∈ Finset.Ico N (N + N) then 1 else 0) =
      List.replicate N 0 := by
    have h : (List.range N).map (fun i => if i ∈ Finset.Ico N (N + N) then 1 else 0) =
        (List.range N).map (fun _ => 0) := by
      apply List.map_congr_left
      intro i hi
      have hi' := List.mem_range.mp hi
      simp only [Finset.mem_Ico]
      split_ifs <;> omega
    simpa using h
  have hright : (List.range N).map
      ((fun i => if i ∈ Finset.Ico N (N + N) then 1 else 0) ∘ (fun i => N + i)) =
      List.replicate N 1 := by
    have h : (List.range N).map
        ((fun i => if i ∈ Finset.Ico N (N + N) then 1 else 0) ∘ (fun i => N + i)) =
        (List.range N).map (fun _ => 1) := by
      apply List.map_congr_left
      intro i hi
      have hi' := List.mem_range.mp hi
      simp only [Function.comp_apply, Finset.mem_Ico]
      split_ifs <;> omega
    simpa using h
  rw [hleft, hright]

lemma normalize_degrees_eq (N : ℕ) (C : Circuit) :
    degrees (normalize N C) = C.lineDegrees (N + N) (Finset.Ico N (N + N)) := by
  rw [normalize, build, fold_degrees, initial_degrees_eq]
  rfl

lemma fold_net_append (N z : ℕ) (gs : List Gate) (s : State) :
    ∃ t, net (gs.foldl (advance N z) s) = net s ++ t := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (advance N z s g)
    refine ⟨payload N z s g ++ t, ?_⟩
    rw [List.foldl_cons, ht, advance_net, List.append_assoc]

lemma fold_one_append (N z : ℕ) (gs : List Gate) (s : State) :
    ∃ t, one (gs.foldl (advance N z) s) = one s ++ t ∧ t.length = gs.length := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (advance N z s g)
    refine ⟨out N z s g :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht, advance_one]
    simp only [List.append_assoc, List.singleton_append]

lemma fold_degrees_append (N z : ℕ) (gs : List Gate) (s : State) :
    ∃ t, degrees (gs.foldl (advance N z) s) = degrees s ++ t ∧ t.length = gs.length := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (advance N z s g)
    refine ⟨g.lineDegree (degrees s) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht, advance_degrees]
    simp only [List.append_assoc, List.singleton_append]

lemma fold_one_getD_old (N z : ℕ) (gs : List Gate) (s : State) (r d : ℕ)
    (hr : r < (one s).length) :
    (one (gs.foldl (advance N z) s)).getD r d = (one s).getD r d := by
  obtain ⟨t, ht, _⟩ := fold_one_append N z gs s
  rw [ht, List.getD_append _ _ _ _ hr]

lemma fold_degrees_getD_old (N z : ℕ) (gs : List Gate) (s : State) (r d : ℕ)
    (hr : r < (degrees s).length) :
    (degrees (gs.foldl (advance N z) s)).getD r d = (degrees s).getD r d := by
  obtain ⟨t, ht, _⟩ := fold_degrees_append N z gs s
  rw [ht, List.getD_append _ _ _ _ hr]

lemma build_append (N z : ℕ) (gs hs : List Gate) :
    build N z (gs ++ hs) = hs.foldl (advance N z) (build N z gs) := by
  simp only [build, List.foldl_append]

lemma build_snoc (N z : ℕ) (gs : List Gate) (g : Gate) :
    build N z (gs ++ [g]) = advance N z (build N z gs) g := by
  rw [build_append]
  rfl

lemma build_one_getD_prefix (N z : ℕ) (gs hs : List Gate) (r d : ℕ)
    (hr : r < N + N + gs.length) :
    (one (build N z (gs ++ hs))).getD r d = (one (build N z gs)).getD r d := by
  rw [build_append]
  apply fold_one_getD_old
  simpa only [build_one_length] using hr

lemma build_degrees_getD_prefix (N z : ℕ) (gs hs : List Gate) (r d : ℕ)
    (hr : r < N + N + gs.length) :
    (degrees (build N z (gs ++ hs))).getD r d = (degrees (build N z gs)).getD r d := by
  rw [build_append]
  apply fold_degrees_getD_old
  simpa only [build_degrees_length] using hr

lemma build_net_false_prefix (N z : ℕ) (gs : List Gate) :
    ∃ t, net (build N z gs) = Sum.inl [] :: t := by
  obtain ⟨t, ht⟩ := fold_net_append N z gs (initial N)
  exact ⟨t, by simpa only [build, initial, net, List.singleton_append] using ht⟩

lemma build_net_pos (N z : ℕ) (gs : List Gate) : 0 < (net (build N z gs)).length := by
  obtain ⟨t, ht⟩ := build_net_false_prefix N z gs
  simp [ht]

def OneBound (N : ℕ) (s : State) : Prop :=
  ∀ r ∈ one s, r < N + (net s).length

lemma initial_one_bound (N : ℕ) : OneBound N (initial N) := by
  intro r hr
  change r ∈ List.replicate N N ++ List.range N at hr
  change r < N + 1
  rcases List.mem_append.mp hr with h | h
  · have hrN := List.eq_of_mem_replicate h
    omega
  · have hrN := List.mem_range.mp h
    omega

lemma out_bound (N z : ℕ) (s : State) (g : Gate) (hs : 0 < (net s).length) :
    out N z s g < N + (net (advance N z s g)).length := by
  rw [advance_net, List.length_append]
  unfold out
  dsimp only
  split_ifs with h
  · simp only [h, List.length_nil]
    omega
  · have hp : 0 < (payload N z s g).length := List.length_pos_iff.mpr h
    omega

lemma advance_one_bound (N z : ℕ) (s : State) (g : Gate)
    (hs : 0 < (net s).length) (hb : OneBound N s) : OneBound N (advance N z s g) := by
  intro r hr
  rw [advance_one, List.mem_append, List.mem_singleton] at hr
  rcases hr with hr | rfl
  · have h := hb r hr
    rw [advance_net, List.length_append]
    omega
  · exact out_bound N z s g hs

lemma fold_net_pos (N z : ℕ) (gs : List Gate) (s : State)
    (hs : 0 < (net s).length) : 0 < (net (gs.foldl (advance N z) s)).length := by
  obtain ⟨t, ht⟩ := fold_net_append N z gs s
  rw [ht, List.length_append]
  omega

lemma fold_one_bound (N z : ℕ) (gs : List Gate) (s : State)
    (hs : 0 < (net s).length) (hb : OneBound N s) :
    OneBound N (gs.foldl (advance N z) s) := by
  induction gs generalizing s with
  | nil => exact hb
  | cons g gs ih =>
    rw [List.foldl_cons]
    apply ih
    · rw [advance_net, List.length_append]
      omega
    · exact advance_one_bound N z s g hs hb

lemma build_one_bound (N z : ℕ) (gs : List Gate) : OneBound N (build N z gs) :=
  fold_one_bound N z gs (initial N) (by simp [initial, net]) (initial_one_bound N)

lemma getD_bound_of_mem (xs : List ℕ) (d b : ℕ)
    (hm : ∀ r ∈ xs, r < b) (hd : d < b) (r : ℕ) : xs.getD r d < b := by
  induction xs generalizing r with
  | nil => simpa using hd
  | cons a xs ih =>
    cases r with
    | zero => exact hm a (by simp)
    | succ r =>
      exact ih (fun t ht => hm t (by simp [ht])) r

lemma build_one_getD_bound (N z : ℕ) (gs : List Gate) (r : ℕ) :
    (one (build N z gs)).getD r N < N + (net (build N z gs)).length := by
  apply getD_bound_of_mem
  · exact build_one_bound N z gs
  · have h := build_net_pos N z gs
    omega

lemma normalize_one_getD_bound (N : ℕ) (C : Circuit) (r : ℕ) :
    (one (normalize N C)).getD r N < N + (net (normalize N C)).length :=
  build_one_getD_bound N (N + N + C.size) C.gates r

lemma initial_one_point (N p : ℕ) (hp : p < N) :
    (one (initial N)).getD p N = N := by
  change (List.replicate N N ++ List.range N).getD p N = N
  rw [List.getD_append _ _ _ _ (by simpa using hp)]
  exact List.getD_replicate N hp

lemma initial_one_line (N l : ℕ) (hl : l < N) :
    (one (initial N)).getD (N + l) N = l := by
  change (List.replicate N N ++ List.range N).getD (N + l) N = l
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp only [List.length_replicate, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simpa using hl)]
  exact List.getElem_range _

lemma build_one_point (N z : ℕ) (gs : List Gate) (p : ℕ) (hp : p < N) :
    (one (build N z gs)).getD p N = N := by
  change (one (gs.foldl (advance N z) (initial N))).getD p N = N
  rw [fold_one_getD_old N z gs (initial N) p N (by simp [initial, one]; omega)]
  exact initial_one_point N p hp

lemma build_one_line (N z : ℕ) (gs : List Gate) (l : ℕ) (hl : l < N) :
    (one (build N z gs)).getD (N + l) N = l := by
  change (one (gs.foldl (advance N z) (initial N))).getD (N + l) N = l
  rw [fold_one_getD_old N z gs (initial N) (N + l) N (by simp [initial, one]; omega)]
  exact initial_one_line N l hl

lemma labelRead_of_lt (z : ℕ) (s : State) (r : ℕ) (hr : r < (one s).length) :
    labelRead z s r = r := by simp [labelRead, hr]

lemma labelRead_of_ge (z : ℕ) (s : State) (r : ℕ) (hr : (one s).length ≤ r) :
    labelRead z s r = z := by simp [labelRead, Nat.not_lt.mpr hr]

lemma build_labelRead_of_ge (N z : ℕ) (gs : List Gate) (r : ℕ)
    (hr : N + N + gs.length ≤ r) : labelRead z (build N z gs) r = z := by
  apply labelRead_of_ge
  simpa only [build_one_length] using hr

def ZeroMap (N : ℕ) (s : State) : Prop :=
  ∀ r, (degrees s).getD r 0 = 0 → (one s).getD r N = N

lemma initial_zero_map (N : ℕ) : ZeroMap N (initial N) := by
  intro r hd
  change (List.replicate N 0 ++ List.replicate N 1).getD r 0 = 0 at hd
  change (List.replicate N N ++ List.range N).getD r N = N
  by_cases hr : r < N
  · rw [List.getD_append _ _ _ _ (by simpa using hr)]
    exact List.getD_replicate N hr
  · have hNr : N ≤ r := by omega
    by_cases hr2 : r < N + N
    · rw [List.getD_append_right _ _ _ _ (by simpa using hNr)] at hd
      simp only [List.length_replicate] at hd
      rw [List.getD_replicate 1 (by omega : r - N < N)] at hd
      omega
    · apply List.getD_eq_default
      simp only [List.length_append, List.length_replicate, List.length_range]
      omega

lemma out_of_zero_degree (N z : ℕ) (s : State) (g : Gate)
    (hd : g.lineDegree (degrees s) = 0) : out N z s g = N := by
  have hp : payload N z s g = [] := by simp [payload, hd]
  simp [out, hp]

lemma structure_getD_snoc_length {α : Type*} (xs : List α) (a d : α) :
    (xs ++ [a]).getD xs.length d = a := by
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  simp

lemma advance_zero_map (N z : ℕ) (s : State) (g : Gate)
    (hlen : (one s).length = (degrees s).length) (hz : ZeroMap N s) :
    ZeroMap N (advance N z s g) := by
  intro r hd
  by_cases hr : r < (one s).length
  · rw [advance_one, List.getD_append _ _ _ _ hr]
    rw [advance_degrees, List.getD_append _ _ _ _ (by omega)] at hd
    exact hz r hd
  · by_cases he : r = (one s).length
    · subst r
      rw [advance_one, structure_getD_snoc_length]
      rw [advance_degrees, hlen, structure_getD_snoc_length] at hd
      exact out_of_zero_degree N z s g hd
    · apply List.getD_eq_default
      rw [advance_one, List.length_append, List.length_singleton]
      omega

lemma fold_zero_map (N z : ℕ) (gs : List Gate) (s : State)
    (hlen : (one s).length = (degrees s).length) (hz : ZeroMap N s) :
    ZeroMap N (gs.foldl (advance N z) s) := by
  induction gs generalizing s with
  | nil => exact hz
  | cons g gs ih =>
    rw [List.foldl_cons]
    apply ih
    · simp only [advance_one, advance_degrees, List.length_append,
        List.length_singleton, hlen]
    · exact advance_zero_map N z s g hlen hz

lemma build_zero_map (N z : ℕ) (gs : List Gate) : ZeroMap N (build N z gs) := by
  apply fold_zero_map N z gs (initial N)
  · simp [initial, one, degrees]
  · exact initial_zero_map N

lemma build_one_eq_false_of_degree_zero (N z : ℕ) (gs : List Gate) (r : ℕ)
    (hd : (degrees (build N z gs)).getD r 0 = 0) :
    (one (build N z gs)).getD r N = N := build_zero_map N z gs r hd

lemma normalize_one_eq_false_of_degree_zero (N : ℕ) (C : Circuit) (r : ℕ)
    (hd : (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD r 0 = 0) :
    (one (normalize N C)).getD r N = N := by
  apply build_zero_map N (N + N + C.size) C.gates r
  change (degrees (normalize N C)).getD r 0 = 0
  rw [normalize_degrees_eq]
  exact hd

lemma build_false_wire (N z : ℕ) (gs : List Gate) (labels : ℕ → Bool)
    (y : List Bool) (hy : y.length = N) :
    (run (net (build N z gs)) labels y).getD N false = false := by
  obtain ⟨t, ht⟩ := build_net_false_prefix N z gs
  rw [ht, run_cons]
  change (run t labels (y ++ [false])).getD N false = false
  rw [run_getD_lt _ _ _ _ (by simp [hy])]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hy]

lemma normalize_false_wire (N : ℕ) (C : Circuit) (labels : ℕ → Bool)
    (y : List Bool) (hy : y.length = N) :
    (run (net (normalize N C)) labels y).getD N false = false :=
  build_false_wire N (N + N + C.size) C.gates labels y hy

lemma initial_map_value (N : ℕ) (labels : ℕ → Bool) (y : List Bool) (hy : y.length = N) :
    ∀ r, (run (net (initial N)) labels y).getD ((one (initial N)).getD r N) false =
      (List.replicate N false ++ y).getD r false := by
  intro r
  have hfalse : (run (net (initial N)) labels y).getD N false = false := by
    simpa only [build, List.foldl_nil] using build_false_wire N 0 [] labels y hy
  by_cases hr : r < N
  · rw [initial_one_point N r hr, hfalse,
      List.getD_append _ _ _ _ (by simpa using hr), List.getD_replicate false hr]
  · have hNr : N ≤ r := by omega
    by_cases hr2 : r < N + N
    · have hl : r - N < N := by omega
      have he : N + (r - N) = r := by omega
      have hm := initial_one_line N (r - N) hl
      rw [he] at hm
      rw [hm, run_getD_lt _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by simpa using hNr)]
      simp only [List.length_replicate]
    · have hm : (one (initial N)).getD r N = N := by
        apply List.getD_eq_default
        simp only [initial, one, List.length_append, List.length_replicate, List.length_range]
        omega
      rw [hm, hfalse]
      symm
      apply List.getD_eq_default
      simp only [List.length_append, List.length_replicate, hy]
      omega

def forkAt (d : List ℕ) (g : Gate) : Bool :=
  if g.lineDegree d = 2 then
    match g.op, g.inputs with
    | .and, [r, t] => decide (d.getD r 0 = 1 ∧ d.getD t 0 = 1)
    | _, _ => false
  else false

def degreeCountFrom (k : ℕ) : List ℕ → List Gate → ℕ
  | _, [] => 0
  | d, g :: gs => (if g.lineDegree d = k then 1 else 0) +
      degreeCountFrom k (d ++ [g.lineDegree d]) gs

def forkCountFrom : List ℕ → List Gate → ℕ
  | _, [] => 0
  | d, g :: gs => (if forkAt d g then 1 else 0) +
      forkCountFrom (d ++ [g.lineDegree d]) gs

def degreeCount (N k : ℕ) (gs : List Gate) : ℕ :=
  degreeCountFrom k (degrees (initial N)) gs

def forkCount (N : ℕ) (gs : List Gate) : ℕ :=
  forkCountFrom (degrees (initial N)) gs

lemma forwardWeight_eq_classified (s : State) (g : Gate) :
    forwardWeight s g =
      (if g.lineDegree (degrees s) = 1 then 1 else 0) +
      (if g.lineDegree (degrees s) = 2 then 1 else 0) +
      2 * (if forkAt (degrees s) g then 1 else 0) := by
  unfold forwardWeight forkAt
  dsimp only
  split_ifs
  all_goals try split
  all_goals try split_ifs
  all_goals simp_all

lemma forkAt_true_degree_two (d : List ℕ) (g : Gate) (hf : forkAt d g = true) :
    g.lineDegree d = 2 := by
  unfold forkAt at hf
  split_ifs at hf with hd
  exact hd

lemma forkAt_iff (d : List ℕ) (g : Gate) : forkAt d g = true ↔
    ∃ r t, g.op = GateOp.and ∧ g.inputs = [r, t] ∧
      d.getD r 0 = 1 ∧ d.getD t 0 = 1 := by
  classical
  constructor
  · intro hf
    unfold forkAt at hf
    split_ifs at hf
    split at hf
    · rename_i r t hop hrs
      exact ⟨r, t, hop, hrs, by simpa using hf⟩
    · contradiction
  · rintro ⟨r, t, hop, hrs, hr, ht⟩
    have hd : g.lineDegree d = 2 := by
      unfold Gate.lineDegree
      rw [hop, hrs]
      simp only [ite_true, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [hr, ht]
    rw [forkAt, ite_eq_left hd, hop, hrs]
    exact decide_eq_true ⟨hr, ht⟩

lemma fold_net_length_classified (N z : ℕ) (gs : List Gate) (s : State) :
    (net (gs.foldl (advance N z) s)).length ≤ (net s).length +
      degreeCountFrom 1 (degrees s) gs + degreeCountFrom 2 (degrees s) gs +
      2 * forkCountFrom (degrees s) gs := by
  induction gs generalizing s with
  | nil => simp [degreeCountFrom, forkCountFrom]
  | cons g gs ih =>
    have h := ih (advance N z s g)
    rw [advance_net, List.length_append, advance_degrees] at h
    have hp := payload_length_le_weight N z s g
    rw [forwardWeight_eq_classified] at hp
    simp only [List.foldl_cons, degreeCountFrom, forkCountFrom]
    omega

lemma build_net_length_classified (N z : ℕ) (gs : List Gate) :
    (net (build N z gs)).length ≤
      1 + degreeCount N 1 gs + degreeCount N 2 gs + 2 * forkCount N gs := by
  simpa only [build, degreeCount, forkCount, initial, net, List.length_singleton]
    using fold_net_length_classified N z gs (initial N)

lemma normalize_net_length_classified (N : ℕ) (C : Circuit) :
    (net (normalize N C)).length ≤ 1 + degreeCount N 1 C.gates +
      degreeCount N 2 C.gates + 2 * forkCount N C.gates :=
  build_net_length_classified N (N + N + C.size) C.gates

lemma forkCountFrom_le_degree_two (d : List ℕ) (gs : List Gate) :
    forkCountFrom d gs ≤ degreeCountFrom 2 d gs := by
  induction gs generalizing d with
  | nil => rfl
  | cons g gs ih =>
    have h := ih (d ++ [g.lineDegree d])
    have hstep : (if forkAt d g then 1 else 0) ≤ (if g.lineDegree d = 2 then 1 else 0) := by
      by_cases hf : forkAt d g = true
      · simp [hf, forkAt_true_degree_two d g hf]
      · simp [hf]
    simp only [forkCountFrom, degreeCountFrom]
    omega

lemma forkCount_le_degree_two (N : ℕ) (gs : List Gate) :
    forkCount N gs ≤ degreeCount N 2 gs := forkCountFrom_le_degree_two _ _

lemma degree_counts_le_length (d : List ℕ) (gs : List Gate) :
    degreeCountFrom 0 d gs + degreeCountFrom 1 d gs + degreeCountFrom 2 d gs ≤ gs.length := by
  induction gs generalizing d with
  | nil => rfl
  | cons g gs ih =>
    have h := ih (d ++ [g.lineDegree d])
    simp only [degreeCountFrom, List.length_cons]
    split_ifs <;> omega

lemma degreeCount_zero_one_two_le_length (N : ℕ) (gs : List Gate) :
    degreeCount N 0 gs + degreeCount N 1 gs + degreeCount N 2 gs ≤ gs.length :=
  degree_counts_le_length _ _

end Pilot5bMeta1020Forward


namespace PEqualNP.Outside.L_meta_1020.OneLineCoefficient

open PEqualNP.CircuitLowerBounds

def value (g : Gate) (w : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def coeff (g : Gate) (z p : List Bool) : Bool :=
  match g.op, g.inputs with
  | .or, ins => (ins.map fun i => p.getD i false).any id
  | .and, [] => false
  | .and, [a] => p.getD a false
  | .and, [a, b] =>
      (z.getD a false && p.getD b false) || (p.getD a false && z.getD b false)
  | _, _ => false

def At (z p w : Bool) (d : ℕ) : Prop :=
  (z = true → w = true) ∧ (p = true → w = true) ∧
  (d = 0 → p = false) ∧ (d ≤ 1 → w = (z || p))

lemma at_false : At false false false 0 := by simp [At]

lemma at_and {za pa wa zb pb wb : Bool} {da db : ℕ}
    (ha : At za pa wa da) (hb : At zb pb wb db) :
    At (za && zb) ((za && pb) || (pa && zb)) (wa && wb) (da + db) := by
  obtain ⟨hza, hpa, hpa0, ha1⟩ := ha
  obtain ⟨hzb, hpb, hpb0, hb1⟩ := hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    rw [Bool.and_eq_true] at h
    obtain ⟨ha, hb⟩ := h
    simpa only [Bool.and_eq_true] using And.intro (hza ha) (hzb hb)
  · intro h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Bool.and_eq_true] at h
      obtain ⟨ha, hb⟩ := h
      simpa only [Bool.and_eq_true] using And.intro (hza ha) (hpb hb)
    · rw [Bool.and_eq_true] at h
      obtain ⟨ha, hb⟩ := h
      simpa only [Bool.and_eq_true] using And.intro (hpa ha) (hzb hb)
  · intro h
    have ha0 : da = 0 := by omega
    have hb0 : db = 0 := by omega
    simp [hpa0 ha0, hpb0 hb0]
  · intro h
    have ha' : da ≤ 1 := by omega
    have hb' : db ≤ 1 := by omega
    rw [ha1 ha', hb1 hb']
    have hz : da = 0 ∨ db = 0 := by omega
    rcases hz with hz | hz
    · rw [hpa0 hz]
      cases za <;> cases zb <;> cases pb <;> rfl
    · rw [hpb0 hz]
      cases za <;> cases zb <;> cases pa <;> rfl

lemma at_or {za pa wa zb pb wb : Bool} {da db : ℕ}
    (ha : At za pa wa da) (hb : At zb pb wb db) :
    At (za || zb) (pa || pb) (wa || wb) (max da db) := by
  obtain ⟨hza, hpa, hpa0, ha1⟩ := ha
  obtain ⟨hzb, hpb, hpb0, hb1⟩ := hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · simpa only [Bool.or_eq_true] using Or.inl (b := wb = true) (hza h)
    · simpa only [Bool.or_eq_true] using Or.inr (a := wa = true) (hzb h)
  · intro h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · simpa only [Bool.or_eq_true] using Or.inl (b := wb = true) (hpa h)
    · simpa only [Bool.or_eq_true] using Or.inr (a := wa = true) (hpb h)
  · intro h
    have ha0 : da = 0 := by omega
    have hb0 : db = 0 := by omega
    simp [hpa0 ha0, hpb0 hb0]
  · intro h
    have ha' : da ≤ 1 := le_trans (le_max_left _ _) h
    have hb' : db ≤ 1 := le_trans (le_max_right _ _) h
    rw [ha1 ha', hb1 hb']
    cases za <;> cases zb <;> cases pa <;> cases pb <;> rfl

def AllAt (z p w : List Bool) (d : List ℕ) : Prop :=
  ∀ i, At (z.getD i false) (p.getD i false) (w.getD i false) (d.getD i 0)

lemma gate_at (g : Gate) (z p w : List Bool) (d : List ℕ)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2)
    (h : AllAt z p w d) :
    At (value g z) (coeff g z p) (value g w) (g.lineDegree d) := by
  rcases g with ⟨op, ins⟩
  change op = .and ∨ op = .or at hm
  change ins.length ≤ 2 at hl
  rcases hm with rfl | rfl
  · cases ins with
    | nil => simp [At, value, coeff, GateOp.eval, Gate.lineDegree]
    | cons a as =>
      cases as with
      | nil => simpa [value, coeff, GateOp.eval, Gate.lineDegree] using h a
      | cons b bs =>
        cases bs with
        | nil => simpa [value, coeff, GateOp.eval, Gate.lineDegree] using at_and (h a) (h b)
        | cons c cs => simp only [List.length_cons] at hl; omega
  · cases ins with
    | nil => simp [At, value, coeff, GateOp.eval, Gate.lineDegree]
    | cons a as =>
      cases as with
      | nil => simpa [value, coeff, GateOp.eval, Gate.lineDegree] using h a
      | cons b bs =>
        cases bs with
        | nil => simpa [value, coeff, GateOp.eval, Gate.lineDegree] using at_or (h a) (h b)
        | cons c cs => simp only [List.length_cons] at hl; omega

lemma gate_coeff_sound (g : Gate) (z p w : List Bool) (d : List ℕ)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2)
    (h : AllAt z p w d) : coeff g z p = true → value g w = true :=
  (gate_at g z p w d hm hl h).2.1

lemma gate_coeff_zero (g : Gate) (z p w : List Bool) (d : List ℕ)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2)
    (h : AllAt z p w d) : g.lineDegree d = 0 → coeff g z p = false :=
  (gate_at g z p w d hm hl h).2.2.1

lemma gate_coeff_complete (g : Gate) (z p w : List Bool) (d : List ℕ)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2)
    (h : AllAt z p w d) (hd : g.lineDegree d ≤ 1)
    (hw : value g w = true) (hz : value g z = false) : coeff g z p = true := by
  have heq := (gate_at g z p w d hm hl h).2.2.2 hd
  simpa [hw, hz] using heq.symm

lemma input_degree_le (g : Gate) (d : List ℕ) (r : ℕ)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2)
    (hr : r ∈ g.inputs) : d.getD r 0 ≤ g.lineDegree d := by
  rcases g with ⟨op, ins⟩
  change op = .and ∨ op = .or at hm
  change ins.length ≤ 2 at hl
  change r ∈ ins at hr
  rcases hm with rfl | rfl
  · cases ins with
    | nil => simp at hr
    | cons a as =>
      cases as with
      | nil =>
        simp only [List.mem_singleton] at hr
        subst r
        simp [Gate.lineDegree]
      | cons b bs =>
        cases bs with
        | nil =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> simp [Gate.lineDegree]
        | cons c cs => simp only [List.length_cons] at hl; omega

  · cases ins with
    | nil => simp at hr
    | cons a as =>
      cases as with
      | nil =>
        simp only [List.mem_singleton] at hr
        subst r
        simp [Gate.lineDegree]
      | cons b bs =>
        cases bs with
        | nil =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl <;> simp [Gate.lineDegree]
        | cons c cs => simp only [List.length_cons] at hl; omega

lemma coeff_congr (g : Gate) (z p z' p' : List Bool)
    (hz : ∀ r ∈ g.inputs, z.getD r false = z'.getD r false)
    (hp : ∀ r ∈ g.inputs, p.getD r false = p'.getD r false) :
    coeff g z p = coeff g z' p' := by
  rcases g with ⟨op, ins⟩
  cases op with
  | and =>
    cases ins with
    | nil => rfl
    | cons a as =>
      cases as with
      | nil => exact hp a (by simp)
      | cons b bs =>
        cases bs with
        | nil => simp only [coeff, hz a (by simp), hz b (by simp), hp a (by simp), hp b (by simp)]
        | cons c cs => rfl
  | or =>
    change (ins.map (fun r => p.getD r false)).any id = (ins.map (fun r => p'.getD r false)).any id
    congr 1
    apply List.map_congr_left
    intro r hr
    exact hp r hr
  | not => rfl
  | mod m => rfl
  | maj => rfl

lemma coeff_false_of_reads (g : Gate) (z p : List Bool)
    (hp : ∀ r ∈ g.inputs, p.getD r false = false) : coeff g z p = false := by
  rcases g with ⟨op, ins⟩
  cases op with
  | and =>
    cases ins with
    | nil => rfl
    | cons a as =>
      cases as with
      | nil => exact hp a (by simp)
      | cons b bs =>
        cases bs with
        | nil =>
          change ((z.getD a false && p.getD b false) || (p.getD a false && z.getD b false)) = false
          rw [hp a (by simp), hp b (by simp)]
          simp
        | cons c cs => rfl
  | or =>
    have heq : ins.map (fun r => p.getD r false) = ins.map (fun _ => false) := by
      apply List.map_congr_left
      intro r hr
      exact hp r hr
    change (ins.map (fun r => p.getD r false)).any id = false
    rw [heq]
    simp
  | not => rfl
  | mod m => rfl
  | maj => rfl

lemma coeff_zero_of_reads (g : Gate) (z p : List Bool) (d : List ℕ)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2)
    (hp : ∀ r ∈ g.inputs, d.getD r 0 = 0 → p.getD r false = false)
    (hd : g.lineDegree d = 0) : coeff g z p = false := by
  apply coeff_false_of_reads
  intro r hr
  apply hp r hr
  have hle := input_degree_le g d r hm hl hr
  omega

lemma append_allAt (z p w : List Bool) (d : List ℕ)
    (hzp : z.length = p.length) (hzw : z.length = w.length) (hzd : z.length = d.length)
    (h : AllAt z p w d) (zn pn wn : Bool) (dn : ℕ) (hn : At zn pn wn dn) :
    AllAt (z ++ [zn]) (p ++ [pn]) (w ++ [wn]) (d ++ [dn]) := by
  intro i
  by_cases hi : i < z.length
  · have hip : i < p.length := by omega
    have hiw : i < w.length := by omega
    have hid : i < d.length := by omega
    rw [List.getD_append z [zn] false i hi, List.getD_append p [pn] false i hip,
      List.getD_append w [wn] false i hiw, List.getD_append d [dn] 0 i hid]
    exact h i
  · by_cases he : i = z.length
    · have hp : p.length ≤ i := by omega
      have hw : w.length ≤ i := by omega
      have hd : d.length ≤ i := by omega
      rw [List.getD_append_right z [zn] false i (by omega),
        List.getD_append_right p [pn] false i hp,
        List.getD_append_right w [wn] false i hw,
        List.getD_append_right d [dn] 0 i hd]
      have ez : i - z.length = 0 := by omega
      have ep : i - p.length = 0 := by omega
      have ew : i - w.length = 0 := by omega
      have ed : i - d.length = 0 := by omega
      simpa only [ez, ep, ew, ed, List.getD_cons_zero] using hn
    · have hz : (z ++ [zn]).length ≤ i := by simp only [List.length_append, List.length_singleton]; omega
      have hp : (p ++ [pn]).length ≤ i := by simp only [List.length_append, List.length_singleton]; omega
      have hw : (w ++ [wn]).length ≤ i := by simp only [List.length_append, List.length_singleton]; omega
      have hd : (d ++ [dn]).length ≤ i := by simp only [List.length_append, List.length_singleton]; omega
      rw [List.getD_eq_default _ _ hz, List.getD_eq_default _ _ hp,
        List.getD_eq_default _ _ hw, List.getD_eq_default _ _ hd]
      exact at_false

abbrev State := List Bool × List Bool × List Bool × List ℕ

def step (s : State) (g : Gate) : State :=
  (s.1 ++ [value g s.1],
    s.2.1 ++ [coeff g s.1 s.2.1],
    s.2.2.1 ++ [value g s.2.2.1],
    s.2.2.2 ++ [g.lineDegree s.2.2.2])

def Valid (s : State) : Prop :=
  s.1.length = s.2.1.length ∧ s.1.length = s.2.2.1.length ∧
  s.1.length = s.2.2.2.length ∧ AllAt s.1 s.2.1 s.2.2.1 s.2.2.2

lemma step_valid (s : State) (g : Gate) (hs : Valid s)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2) : Valid (step s g) := by
  rcases s with ⟨z, p, w, d⟩
  rcases hs with ⟨hzp, hzw, hzd, h⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [step, List.length_append, List.length_singleton] using congrArg (fun n => n + 1) hzp
  · simpa only [step, List.length_append, List.length_singleton] using congrArg (fun n => n + 1) hzw
  · simpa only [step, List.length_append, List.length_singleton] using congrArg (fun n => n + 1) hzd
  · exact append_allAt z p w d hzp hzw hzd h _ _ _ _ (gate_at g z p w d hm hl h)

lemma fold_valid (gs : List Gate) (s : State) (hs : Valid s)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    Valid (gs.foldl step s) := by
  induction gs generalizing s with
  | nil => exact hs
  | cons g gs ih =>
    have hg := hm g List.mem_cons_self
    exact ih (step s g) (step_valid s g hs hg.1 hg.2)
      (fun h hh => hm h (List.mem_cons_of_mem g hh))

def run (gs : List Gate) (z p w : List Bool) (d : List ℕ) : State :=
  gs.foldl step (z, p, w, d)

lemma run_valid (gs : List Gate) (z p w : List Bool) (d : List ℕ)
    (hzp : z.length = p.length) (hzw : z.length = w.length) (hzd : z.length = d.length)
    (h : AllAt z p w d)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    Valid (run gs z p w d) :=
  fold_valid gs (z, p, w, d) ⟨hzp, hzw, hzd, h⟩ hm

lemma fold_lengths (gs : List Gate) (s : State) :
    (gs.foldl step s).1.length = s.1.length + gs.length ∧
    (gs.foldl step s).2.1.length = s.2.1.length + gs.length ∧
    (gs.foldl step s).2.2.1.length = s.2.2.1.length + gs.length ∧
    (gs.foldl step s).2.2.2.length = s.2.2.2.length + gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    simpa only [List.foldl_cons, List.length_cons, step, List.length_append,
      List.length_singleton, List.length_nil, Nat.zero_add, Nat.add_assoc, Nat.add_comm 1] using ih (step s g)

lemma fold_p_getD (gs : List Gate) (s : State) (i : ℕ) (hi : i < s.2.1.length) :
    (gs.foldl step s).2.1.getD i false = s.2.1.getD i false := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    have hi' : i < (step s g).2.1.length := by simp only [step, List.length_append, List.length_singleton]; omega
    change (gs.foldl step (step s g)).2.1.getD i false = s.2.1.getD i false
    rw [ih (step s g) hi']
    exact List.getD_append _ _ _ _ hi

lemma fold_z_getD (gs : List Gate) (s : State) (i : ℕ) (hi : i < s.1.length) :
    (gs.foldl step s).1.getD i false = s.1.getD i false := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    have hi' : i < (step s g).1.length := by simp only [step, List.length_append, List.length_singleton]; omega
    change (gs.foldl step (step s g)).1.getD i false = s.1.getD i false
    rw [ih (step s g) hi']
    exact List.getD_append _ _ _ _ hi

lemma fold_prefix_p_getD (pre post : List Gate) (s : State) (i : ℕ)
    (hi : i < (pre.foldl step s).2.1.length) :
    ((pre ++ post).foldl step s).2.1.getD i false = (pre.foldl step s).2.1.getD i false := by
  rw [List.foldl_append]
  exact fold_p_getD post (pre.foldl step s) i hi

lemma fold_prefix_z_getD (pre post : List Gate) (s : State) (i : ℕ)
    (hi : i < (pre.foldl step s).1.length) :
    ((pre ++ post).foldl step s).1.getD i false = (pre.foldl step s).1.getD i false := by
  rw [List.foldl_append]
  exact fold_z_getD post (pre.foldl step s) i hi

lemma fold_zero_eq (gs : List Gate) (s : State) :
    (gs.foldl step s).1 = gs.foldl (fun z g => z ++ [value g z]) s.1 := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih => simpa only [List.foldl_cons, step] using ih (step s g)

lemma fold_full_eq (gs : List Gate) (s : State) :
    (gs.foldl step s).2.2.1 = gs.foldl (fun w g => w ++ [value g w]) s.2.2.1 := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih => simpa only [List.foldl_cons, step] using ih (step s g)

lemma fold_degree_eq (gs : List Gate) (s : State) :
    (gs.foldl step s).2.2.2 = gs.foldl (fun d g => d ++ [g.lineDegree d]) s.2.2.2 := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih => simpa only [List.foldl_cons, step] using ih (step s g)

lemma run_zero_circuit (C : Circuit) (z p w : List Bool) (d : List ℕ) :
    (run C.gates z p w d).1 = C.wires z :=
  fold_zero_eq C.gates (z, p, w, d)

lemma run_full_circuit (C : Circuit) (z p w : List Bool) (d : List ℕ) :
    (run C.gates z p w d).2.2.1 = C.wires w :=
  fold_full_eq C.gates (z, p, w, d)

lemma at_point (b : Bool) : At b false b 0 := by cases b <;> simp [At]

lemma at_line (b : Bool) : At false b b 1 := by cases b <;> simp [At]

def initial (x y : List Bool) : State :=
  (x ++ List.replicate y.length false,
    List.replicate x.length false ++ y,
    x ++ y,
    List.replicate x.length 0 ++ List.replicate y.length 1)

lemma initial_allAt (x y : List Bool) :
    AllAt (x ++ List.replicate y.length false) (List.replicate x.length false ++ y)
      (x ++ y) (List.replicate x.length 0 ++ List.replicate y.length 1) := by
  intro i
  by_cases hi : i < x.length
  · rw [List.getD_append x _ false i hi,
      List.getD_append (List.replicate x.length false) y false i (by simpa using hi),
      List.getD_append x y false i hi,
      List.getD_append (List.replicate x.length 0) _ 0 i (by simpa using hi),
      List.getD_replicate false hi, List.getD_replicate 0 hi]
    exact at_point (x.getD i false)
  · by_cases hj : i - x.length < y.length
    · rw [List.getD_append_right x _ false i (by omega),
        List.getD_append_right (List.replicate x.length false) y false i (by simpa using Nat.le_of_not_gt hi),
        List.getD_append_right x y false i (by omega),
        List.getD_append_right (List.replicate x.length 0) _ 0 i (by simpa using Nat.le_of_not_gt hi)]
      simp only [List.length_replicate]
      rw [List.getD_replicate false hj, List.getD_replicate 1 hj]
      exact at_line (y.getD (i - x.length) false)
    · have hxy : x.length + y.length ≤ i := by omega
      have hz : (x ++ List.replicate y.length false).length ≤ i := by simpa using hxy
      have hp : (List.replicate x.length false ++ y).length ≤ i := by simpa using hxy
      have hw : (x ++ y).length ≤ i := by simpa using hxy
      have hd : (List.replicate x.length 0 ++ List.replicate y.length 1).length ≤ i := by simpa using hxy
      rw [List.getD_eq_default _ _ hz, List.getD_eq_default _ _ hp,
        List.getD_eq_default _ _ hw, List.getD_eq_default _ _ hd]
      exact at_false

lemma initial_valid (x y : List Bool) : Valid (initial x y) := by
  refine ⟨by simp [initial], by simp [initial], by simp [initial], ?_⟩
  exact initial_allAt x y

lemma circuit_fold_valid (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) : Valid (C.gates.foldl step (initial x y)) := by
  apply fold_valid C.gates (initial x y) (initial_valid x y)
  intro g hg
  obtain ⟨hop, hlen⟩ := hm g hg
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop, hlen⟩

lemma at_coeff_complete {z p w : Bool} {d : ℕ} (h : At z p w d)
    (hd : d ≤ 1) (hw : w = true) (hz : z = false) : p = true := by
  have heq := h.2.2.2 hd
  simpa [hw, hz] using heq.symm

lemma at_zero_value {z p w : Bool} {d : ℕ} (h : At z p w d) (hd : d = 0) : w = z := by
  have heq := h.2.2.2 (by omega : d ≤ 1)
  simpa [h.2.2.1 hd] using heq

end PEqualNP.Outside.L_meta_1020.OneLineCoefficient

namespace Pilot5bMeta1020Forward

open PEqualNP.CircuitLowerBounds
open Pilot5bMeta1020Linear

abbrev CoeffState := PEqualNP.Outside.L_meta_1020.OneLineCoefficient.State
abbrev coeffStep := PEqualNP.Outside.L_meta_1020.OneLineCoefficient.step
abbrev CoeffValid := PEqualNP.Outside.L_meta_1020.OneLineCoefficient.Valid

lemma coefficient_eq_list (g : Gate) (Z P : List Bool) :
    coefficient g (fun r => Z.getD r false) (fun r => P.getD r false) =
      PEqualNP.Outside.L_meta_1020.OneLineCoefficient.coeff g Z P := by
  rcases g with ⟨op, rs⟩
  cases op with
  | or => rfl
  | and =>
    cases rs with
    | nil => rfl
    | cons r rs =>
      cases rs with
      | nil => rfl
      | cons t rs => cases rs <;> rfl
  | not => rfl
  | mod n => rfl
  | maj => rfl

lemma labels_agree_prefix (z : ℕ) (gs : List Gate) (s : State) (c : CoeffState)
    (labels : ℕ → Bool)
    (hz : c.1.length + gs.length ≤ z)
    (hlen : (one s).length = c.1.length)
    (hl : ∀ r, labels r = (gs.foldl coeffStep c).1.getD r false) (r : ℕ) :
    labels (labelRead z s r) = c.1.getD r false := by
  by_cases hr : r < (one s).length
  · rw [labelRead_of_lt z s r hr, hl]
    exact PEqualNP.Outside.L_meta_1020.OneLineCoefficient.fold_z_getD gs c r (by omega)
  · rw [labelRead_of_ge z s r (by omega), hl]
    have hz' : (gs.foldl coeffStep c).1.length ≤ z := by
      rw [(PEqualNP.Outside.L_meta_1020.OneLineCoefficient.fold_lengths gs c).1]
      exact hz
    rw [List.getD_eq_default _ _ hz', List.getD_eq_default _ _ (by omega : c.1.length ≤ r)]

lemma fold_map_correct (N z : ℕ) (gs : List Gate) (s : State) (c : CoeffState)
    (labels : ℕ → Bool) (y : List Bool)
    (hy : y.length = N) (hc : CoeffValid c)
    (hd : degrees s = c.2.2.2) (hlen : (one s).length = c.1.length)
    (hn : 0 < (net s).length) (hb : OneBound N s) (hzm : ZeroMap N s)
    (hz : c.1.length + gs.length ≤ z)
    (hl : ∀ r, labels r = (gs.foldl coeffStep c).1.getD r false)
    (hf : (run (net s) labels y).getD N false = false)
    (hmap : ∀ r, (degrees s).getD r 0 ≤ 2 →
      (run (net s) labels y).getD ((one s).getD r N) false = c.2.1.getD r false)
    (hm : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    ∀ r, (degrees (gs.foldl (advance N z) s)).getD r 0 ≤ 2 →
      (run (net (gs.foldl (advance N z) s)) labels y).getD
          ((one (gs.foldl (advance N z) s)).getD r N) false =
        (gs.foldl coeffStep c).2.1.getD r false := by
  induction gs generalizing s c with
  | nil => exact hmap
  | cons g gs ih =>
    have hg := hm g List.mem_cons_self
    have hc' : CoeffValid (coeffStep c g) :=
      PEqualNP.Outside.L_meta_1020.OneLineCoefficient.step_valid c g hc hg.1 hg.2
    have hd' : degrees (advance N z s g) = (coeffStep c g).2.2.2 := by
      simp only [advance_degrees, coeffStep,
        PEqualNP.Outside.L_meta_1020.OneLineCoefficient.step, hd]
    have hlen' : (one (advance N z s g)).length = (coeffStep c g).1.length := by
      simp only [advance_one, coeffStep,
        PEqualNP.Outside.L_meta_1020.OneLineCoefficient.step,
        List.length_append, List.length_singleton, hlen]
    have hn' : 0 < (net (advance N z s g)).length := by
      rw [advance_net, List.length_append]
      omega
    have hb' := advance_one_bound N z s g hn hb
    have hzm' := advance_zero_map N z s g (by rw [hd]; exact hlen.trans hc.2.2.1) hzm
    have hz' : (coeffStep c g).1.length + gs.length ≤ z := by
      have hclen : (coeffStep c g).1.length = c.1.length + 1 := by
        simp [coeffStep, PEqualNP.Outside.L_meta_1020.OneLineCoefficient.step]
      rw [hclen]
      simp only [List.length_cons] at hz
      omega
    have hl' : ∀ r, labels r = (gs.foldl coeffStep (coeffStep c g)).1.getD r false := hl
    have hvlen : (run (net s) labels y).length = N + (net s).length := by
      rw [run_length, hy]
    have hN : N < (run (net s) labels y).length := by rw [hvlen]; omega
    have hbget : ∀ r, (one s).getD r N < (run (net s) labels y).length := by
      intro r
      rw [hvlen]
      exact getD_bound_of_mem (one s) N (N + (net s).length) hb (by omega) r
    have hf' : (run (net (advance N z s g)) labels y).getD N false = false := by
      rw [advance_net, run_append, run_getD_lt _ _ _ _ hN, hf]
    have hlocal := advance_correct N z s g labels (run (net s) labels y) c.2.1
      hvlen (by rw [hd]; exact hc.2.2.1.symm.trans hlen.symm)
      (hc.1.symm.trans hlen.symm) hf hN hbget
      (fun r hr => by rw [hzm r hr]; exact hf) hmap
      (fun r hr => PEqualNP.Outside.L_meta_1020.OneLineCoefficient.input_degree_le
        g (degrees s) r hg.1 hg.2 hr) hg.1 hg.2
    have hco : coefficient g (fun r => labels (labelRead z s r))
        (fun r => c.2.1.getD r false) =
          PEqualNP.Outside.L_meta_1020.OneLineCoefficient.coeff g c.1 c.2.1 := by
      rw [← coefficient_eq_list]
      apply coefficient_congr
      · intro r hr
        exact labels_agree_prefix z (g :: gs) s c labels hz hlen hl r
      · intro r hr; rfl
    have hmap' : ∀ r, (degrees (advance N z s g)).getD r 0 ≤ 2 →
        (run (net (advance N z s g)) labels y).getD
            ((one (advance N z s g)).getD r N) false =
          (coeffStep c g).2.1.getD r false := by
      intro r hr
      rw [advance_net, run_append]
      simpa only [coeffStep, PEqualNP.Outside.L_meta_1020.OneLineCoefficient.step, hco]
        using hlocal r hr
    exact ih (advance N z s g) (coeffStep c g) hc' hd' hlen' hn' hb' hzm'
      hz' hl' hf' hmap' (fun h hh => hm h (List.mem_cons_of_mem g hh))

def pointLabels (N : ℕ) (C : Circuit) (x : List Bool) : ℕ → Bool :=
  fun r => (C.wires (x ++ List.replicate N false)).getD r false

def coefficientState (C : Circuit) (x y : List Bool) : CoeffState :=
  C.gates.foldl coeffStep (PEqualNP.Outside.L_meta_1020.OneLineCoefficient.initial x y)

lemma coefficientState_zero (N : ℕ) (C : Circuit) (x y : List Bool)
    (hy : y.length = N) :
    (coefficientState C x y).1 = C.wires (x ++ List.replicate N false) := by
  unfold coefficientState
  rw [PEqualNP.Outside.L_meta_1020.OneLineCoefficient.fold_zero_eq]
  simp only [PEqualNP.Outside.L_meta_1020.OneLineCoefficient.initial, hy]
  rfl

lemma coefficientState_full (C : Circuit) (x y : List Bool) :
    (coefficientState C x y).2.2.1 = C.wires (x ++ y) := by
  unfold coefficientState
  rw [PEqualNP.Outside.L_meta_1020.OneLineCoefficient.fold_full_eq]
  rfl

lemma coefficientState_degrees (N : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) :
    (coefficientState C x y).2.2.2 =
      C.lineDegrees (N + N) (Finset.Ico N (N + N)) := by
  unfold coefficientState
  rw [PEqualNP.Outside.L_meta_1020.OneLineCoefficient.fold_degree_eq]
  change C.gates.foldl (fun d g => d ++ [g.lineDegree d])
      (List.replicate x.length 0 ++ List.replicate y.length 1) = _
  rw [hx, hy]
  change C.gates.foldl (fun d g => d ++ [g.lineDegree d]) (degrees (initial N)) = _
  rw [initial_degrees_eq N]
  rfl

lemma normalize_correct (N : ℕ) (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (r : ℕ) (hr : (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD r 0 ≤ 2) :
    (run (net (normalize N C)) (pointLabels N C x) y).getD
        ((one (normalize N C)).getD r N) false =
      (coefficientState C x y).2.1.getD r false := by
  have h := fold_map_correct N (N + N + C.size) C.gates (initial N)
    (PEqualNP.Outside.L_meta_1020.OneLineCoefficient.initial x y)
    (pointLabels N C x) y hy
    (PEqualNP.Outside.L_meta_1020.OneLineCoefficient.initial_valid x y)
    (by simp [initial, degrees, PEqualNP.Outside.L_meta_1020.OneLineCoefficient.initial, hx, hy])
    (by simp [initial, one, PEqualNP.Outside.L_meta_1020.OneLineCoefficient.initial, hx, hy])
    (by simp [initial, net]) (initial_one_bound N) (initial_zero_map N)
    (by simp [PEqualNP.Outside.L_meta_1020.OneLineCoefficient.initial, hx, hy, Circuit.size])
    (by
      intro i
      change (C.wires (x ++ List.replicate N false)).getD i false =
        (coefficientState C x y).1.getD i false
      rw [coefficientState_zero N C x y hy])
    (by
      simpa only [build, List.foldl_nil] using
        build_false_wire N (N + N + C.size) [] (pointLabels N C x) y hy)
    (by
      intro i hi
      simpa only [PEqualNP.Outside.L_meta_1020.OneLineCoefficient.initial, hx] using
        initial_map_value N (pointLabels N C x) y hy i)
    (by
      intro g hg
      obtain ⟨hop, hfan⟩ := hm g hg
      exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop, hfan⟩)
    r
  apply h
  change (degrees (normalize N C)).getD r 0 ≤ 2
  rw [normalize_degrees_eq]
  exact hr

lemma normalize_sound (N : ℕ) (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (r : ℕ) (hr : (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD r 0 ≤ 2)
    (hv : (run (net (normalize N C)) (pointLabels N C x) y).getD
      ((one (normalize N C)).getD r N) false = true) :
    (C.wires (x ++ y)).getD r false = true := by
  rw [normalize_correct N C hm x y hx hy r hr] at hv
  have ha := (PEqualNP.Outside.L_meta_1020.OneLineCoefficient.circuit_fold_valid C hm x y).2.2.2 r
  have hw := ha.2.1 hv
  change (coefficientState C x y).2.2.1.getD r false = true at hw
  rw [coefficientState_full] at hw
  exact hw

lemma normalize_complete_degree_one (N : ℕ) (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (r : ℕ) (hr : (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD r 0 ≤ 1)
    (hw : (C.wires (x ++ y)).getD r false = true)
    (hz : (C.wires (x ++ List.replicate N false)).getD r false = false) :
    (run (net (normalize N C)) (pointLabels N C x) y).getD
      ((one (normalize N C)).getD r N) false = true := by
  rw [normalize_correct N C hm x y hx hy r (by omega)]
  have ha := (PEqualNP.Outside.L_meta_1020.OneLineCoefficient.circuit_fold_valid C hm x y).2.2.2 r
  apply PEqualNP.Outside.L_meta_1020.OneLineCoefficient.at_coeff_complete ha
  · change (coefficientState C x y).2.2.2.getD r 0 ≤ 1
    rw [coefficientState_degrees N C x y hx hy]
    exact hr
  · change (coefficientState C x y).2.2.1.getD r false = true
    rw [coefficientState_full]
    exact hw
  · change (coefficientState C x y).1.getD r false = false
    rw [coefficientState_zero N C x y hy]
    exact hz

end Pilot5bMeta1020Forward
namespace Pilot5bMeta1020Forward

open PEqualNP.CircuitLowerBounds
open Pilot5bMeta1020Linear

def pointList {N : ℕ} (z : Fin (N + N) → Bool) : List Bool :=
  List.ofFn (fun p : Fin N => z (Fin.castAdd N p))

def lineList {N : ℕ} (z : Fin (N + N) → Bool) : List Bool :=
  List.ofFn (fun l : Fin N => z (Fin.natAdd N l))

lemma ofFn_split {N : ℕ} (z : Fin (N + N) → Bool) :
    List.ofFn z = pointList z ++ lineList z := by
  exact List.ofFn_add (f := z)

lemma pointList_length {N : ℕ} (z : Fin (N + N) → Bool) :
    (pointList z).length = N := by simp [pointList]

lemma lineList_length {N : ℕ} (z : Fin (N + N) → Bool) :
    (lineList z).length = N := by simp [lineList]

def pairInput {N : ℕ} (p l : Fin N) : Fin (N + N) → Bool :=
  fun v => if v = Fin.castAdd N p then true
    else if v = Fin.natAdd N l then true else false

def pointInput {N : ℕ} (p : Fin N) : Fin (N + N) → Bool :=
  fun v => decide (v = Fin.castAdd N p)

lemma castAdd_ne_natAdd {N : ℕ} (p l : Fin N) :
    Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma pairInput_point {N : ℕ} (p l q : Fin N) :
    pairInput p l (Fin.castAdd N q) = decide (q = p) := by
  simp only [pairInput, castAdd_ne_natAdd, ↓reduceIte, Fin.castAdd_inj]
  split <;> simp_all

lemma pairInput_line {N : ℕ} (p l u : Fin N) :
    pairInput p l (Fin.natAdd N u) = decide (u = l) := by
  have hn : Fin.natAdd N u ≠ Fin.castAdd N p := (castAdd_ne_natAdd p u).symm
  simp only [pairInput, hn, ↓reduceIte, Fin.natAdd_inj]
  split <;> simp_all

lemma pointInput_point {N : ℕ} (p q : Fin N) :
    pointInput p (Fin.castAdd N q) = decide (q = p) := by
  simp [pointInput]

lemma pointInput_line {N : ℕ} (p u : Fin N) :
    pointInput p (Fin.natAdd N u) = false := by
  have hn : Fin.natAdd N u ≠ Fin.castAdd N p := (castAdd_ne_natAdd p u).symm
  simp only [pointInput, hn, decide_false]

lemma pointList_pair {N : ℕ} (p l : Fin N) :
    pointList (pairInput p l) = List.ofFn (fun q : Fin N => decide (q = p)) := by
  simp only [pointList, pairInput_point]

lemma lineList_pair {N : ℕ} (p l : Fin N) :
    lineList (pairInput p l) = List.ofFn (fun u : Fin N => decide (u = l)) := by
  simp only [lineList, pairInput_line]

lemma pointInput_list {N : ℕ} (p : Fin N) :
    List.ofFn (pointInput p) =
      List.ofFn (fun q : Fin N => decide (q = p)) ++ List.replicate N false := by
  rw [ofFn_split]
  simp only [pointList, lineList, pointInput_point, pointInput_line, List.ofFn_const]

lemma pairInput_list {N : ℕ} (p l : Fin N) :
    List.ofFn (pairInput p l) =
      List.ofFn (fun q : Fin N => decide (q = p)) ++
        List.ofFn (fun u : Fin N => decide (u = l)) := by
  rw [ofFn_split, pointList_pair, lineList_pair]

lemma normalize_sound_fn (N : ℕ) (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (z : Fin (N + N) → Bool) (r : ℕ)
    (hr : (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD r 0 ≤ 2)
    (hv : (run (net (normalize N C)) (pointLabels N C (pointList z))
      (lineList z)).getD ((one (normalize N C)).getD r N) false = true) :
    (C.wires (List.ofFn z)).getD r false = true := by
  rw [ofFn_split]
  exact normalize_sound N C hm (pointList z) (lineList z)
    (pointList_length z) (lineList_length z) r hr hv

lemma normalize_complete_pair (N : ℕ) (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (p l : Fin N) (r : ℕ)
    (hr : (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD r 0 ≤ 1)
    (hw : (C.wires (List.ofFn (pairInput p l))).getD r false = true)
    (hz : (C.wires (List.ofFn (pointInput p))).getD r false = false) :
    (run (net (normalize N C))
      (pointLabels N C (List.ofFn (fun q : Fin N => decide (q = p))))
      (List.ofFn (fun u : Fin N => decide (u = l)))).getD
        ((one (normalize N C)).getD r N) false = true := by
  rw [pairInput_list] at hw
  rw [pointInput_list] at hz
  exact normalize_complete_degree_one N C hm _ _ (by simp) (by simp) r hr hw hz

end Pilot5bMeta1020Forward

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


namespace PEqualNP.Outside.L_meta_1020.ReverseBudget

lemma aggregate_pred_budget {α : Type*} [DecidableEq α]
    (V F : Finset α) (n : α → ℕ) (hF : F ⊆ V)
    (hn : ∀ v ∈ F, 1 ≤ n v) :
    (∑ v ∈ V, (n v - 1)) + F.card ≤ ∑ v ∈ V, n v := by
  classical
  have hcount : (∑ v ∈ V, if v ∈ F then (1 : ℕ) else 0) = F.card := by
    have hfilter : V.filter (fun v => v ∈ F) = F := by
      ext v
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hF h, h⟩⟩
    rw [← Finset.sum_filter]
    simp [hfilter]
  rw [← hcount, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v hv
  by_cases hf : v ∈ F
  · simp only [hf, ↓reduceIte]
    have := hn v hf
    omega
  · simp [hf]

lemma positive_network_budget
    (g1 m k f J f' hCost kCost total : ℕ)
    (hh : hCost ≤ m + k + 3 * f)
    (hk : kCost + f' ≤ 2 * m + 2 * k + J)
    (ht : total ≤ g1 + hCost + kCost) :
    total + f' ≤ g1 + 3 * (m + k + f) + J := by
  omega

lemma final_budget
    (s J g0 g1 g2 s0 s1 jobs forks : ℕ)
    (h0 : s0 ≤ g0 + g1)
    (h1 : s1 + forks ≤ g1 + 3 * g2 + J)
    (hj : jobs ≤ J + forks)
    (hg : g0 + g1 + g2 ≤ s) :
    18 * s0 + 28 * s1 + 27 * jobs ≤ 84 * s + 55 * J := by
  omega

lemma posted_budget
    (s J N s0 s1 jobs forks g0 g1 g2 : ℕ)
    (h0 : s0 ≤ g0 + g1)
    (h1 : s1 + forks ≤ g1 + 3 * g2 + J)
    (hj : jobs ≤ J + forks)
    (hg : g0 + g1 + g2 ≤ s) :
    18 * s0 + 28 * s1 + 27 * jobs ≤ 100 * (s + J) + 4 * N := by
  have := final_budget s J g0 g1 g2 s0 s1 jobs forks h0 h1 hj hg
  omega

end PEqualNP.Outside.L_meta_1020.ReverseBudget

namespace PEqualNP.Outside.L_meta_1020.ReverseBudget

def incomingAt {α : Type*} (target : α → ℕ) (xs : List α) (v : ℕ) : ℕ :=
  (xs.filter fun x => decide (target x = v)).length

lemma incomingAt_cons {α : Type*} (target : α → ℕ) (a : α) (xs : List α) (v : ℕ) :
    incomingAt target (a :: xs) v =
      (if target a = v then 1 else 0) + incomingAt target xs v := by
  by_cases h : target a = v <;> simp [incomingAt, h, Nat.add_comm]

lemma incomingAt_sum {α : Type*} (target : α → ℕ) (xs : List α) (B : ℕ) :
    (∑ v ∈ Finset.range B, incomingAt target xs v) =
      (xs.filter fun x => decide (target x < B)).length := by
  induction xs with
  | nil => simp [incomingAt]
  | cons a xs ih =>
    simp_rw [incomingAt_cons]
    rw [Finset.sum_add_distrib, ih]
    have hdelta : (∑ v ∈ Finset.range B, if target a = v then (1 : ℕ) else 0) =
        if target a < B then 1 else 0 := by
      simp [eq_comm]
    rw [hdelta]
    by_cases h : target a < B <;> simp [h, Nat.add_comm]

theorem incomingAt_sum_le {α : Type*} (target : α → ℕ) (xs : List α) (B : ℕ) :
    (∑ v ∈ Finset.range B, incomingAt target xs v) ≤ xs.length := by
  rw [incomingAt_sum]
  exact List.length_filter_le _ _

theorem incomingAt_sum_eq {α : Type*} (target : α → ℕ) (xs : List α) (B : ℕ)
    (h : ∀ x ∈ xs, target x < B) :
    (∑ v ∈ Finset.range B, incomingAt target xs v) = xs.length := by
  rw [incomingAt_sum]
  congr 1
  exact List.filter_eq_self.mpr (by intro x hx; exact decide_eq_true (h x hx))

def messageCount (seeds edges : List (ℕ × ℕ)) (v : ℕ) : ℕ :=
  incomingAt Prod.fst seeds v + incomingAt Prod.snd edges v

def incomingMessages (seeds edges : List (ℕ × ℕ)) (message : ℕ → ℕ) (v : ℕ) : List ℕ :=
  ((seeds.filter fun e => decide (e.1 = v)).map Prod.snd) ++
    ((edges.filter fun e => decide (e.2 = v)).map fun e => message e.1)

lemma incomingMessages_length (seeds edges : List (ℕ × ℕ)) (message : ℕ → ℕ) (v : ℕ) :
    (incomingMessages seeds edges message v).length = messageCount seeds edges v := by
  simp [incomingMessages, messageCount, incomingAt]

theorem messageCount_sum_le (seeds edges : List (ℕ × ℕ)) (B : ℕ) :
    (∑ v ∈ Finset.range B, messageCount seeds edges v) ≤ seeds.length + edges.length := by
  simp only [messageCount, Finset.sum_add_distrib]
  exact Nat.add_le_add (incomingAt_sum_le Prod.fst seeds B) (incomingAt_sum_le Prod.snd edges B)

theorem messageCount_sum_eq (seeds edges : List (ℕ × ℕ)) (B : ℕ)
    (hseeds : ∀ e ∈ seeds, e.1 < B) (hedges : ∀ e ∈ edges, e.2 < B) :
    (∑ v ∈ Finset.range B, messageCount seeds edges v) = seeds.length + edges.length := by
  simp only [messageCount, Finset.sum_add_distrib]
  rw [incomingAt_sum_eq Prod.fst seeds B hseeds, incomingAt_sum_eq Prod.snd edges B hedges]

theorem static_aggregate_budget (seeds edges : List (ℕ × ℕ)) (B : ℕ)
    (usedForks : Finset ℕ) (hF : usedForks ⊆ Finset.range B)
    (hpositive : ∀ v ∈ usedForks, 1 ≤ messageCount seeds edges v) :
    (∑ v ∈ Finset.range B, (messageCount seeds edges v - 1)) + usedForks.card ≤
      seeds.length + edges.length := by
  exact (aggregate_pred_budget (Finset.range B) usedForks (messageCount seeds edges) hF hpositive).trans
    (messageCount_sum_le seeds edges B)

theorem static_net_budget (seeds edges : List (ℕ × ℕ)) (B : ℕ)
    (usedForks : Finset ℕ) (hF : usedForks ⊆ Finset.range B)
    (hpositive : ∀ v ∈ usedForks, 1 ≤ messageCount seeds edges v)
    (initial final weighted : ℕ)
    (hcost : final ≤ initial +
      (∑ v ∈ Finset.range B, (messageCount seeds edges v - 1)) + weighted) :
    final + usedForks.card ≤ initial + seeds.length + edges.length + weighted := by
  have := static_aggregate_budget seeds edges B usedForks hF hpositive
  omega

lemma foldl_cost_bound {σ α : Type*} (step : σ → α → σ) (measure : σ → ℕ)
    (cost : α → ℕ) (xs : List α)
    (hstep : ∀ a ∈ xs, ∀ s, measure (step s a) ≤ measure s + cost a) (s : σ) :
    measure (xs.foldl step s) ≤ measure s + (xs.map cost).sum := by
  induction xs generalizing s with
  | nil => simp
  | cons a xs ih =>
    have htail : ∀ b ∈ xs, ∀ t, measure (step t b) ≤ measure t + cost b := by
      intro b hb t
      exact hstep b (List.mem_cons_of_mem a hb) t
    have hh := hstep a (by simp) s
    have ht := ih htail (step s a)
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    omega

lemma range_cost_sum (cost : ℕ → ℕ) (B : ℕ) :
    ((List.range B).map cost).sum = ∑ v ∈ Finset.range B, cost v := by
  induction B with
  | zero => simp
  | succ B ih => simp [List.range_succ, Finset.sum_range_succ, ih]

lemma descending_cost_sum (cost : ℕ → ℕ) (B : ℕ) :
    ((List.range B).reverse.map cost).sum = ∑ v ∈ Finset.range B, cost v := by
  simpa only [List.map_reverse, List.sum_reverse] using range_cost_sum cost B

theorem descending_reverse_budget {σ : Type*}
    (step : σ → ℕ → σ) (measure : σ → ℕ)
    (seeds edges : List (ℕ × ℕ)) (weighted : ℕ → ℕ) (B : ℕ)
    (usedForks : Finset ℕ) (hF : usedForks ⊆ Finset.range B)
    (hpositive : ∀ v ∈ usedForks, 1 ≤ messageCount seeds edges v)
    (hstep : ∀ v ∈ Finset.range B, ∀ s,
      measure (step s v) ≤ measure s + (messageCount seeds edges v - 1) + weighted v)
    (s : σ) :
    measure ((List.range B).reverse.foldl step s) + usedForks.card ≤
      measure s + seeds.length + edges.length + ∑ v ∈ Finset.range B, weighted v := by
  have hfold := foldl_cost_bound step measure
    (fun v => (messageCount seeds edges v - 1) + weighted v) (List.range B).reverse
    (by
      intro v hv t
      have hv' : v ∈ Finset.range B := by simpa using hv
      have hh := hstep v hv' t
      omega) s
  rw [descending_cost_sum, Finset.sum_add_distrib] at hfold
  have hsum := static_aggregate_budget seeds edges B usedForks hF hpositive
  omega

end PEqualNP.Outside.L_meta_1020.ReverseBudget

namespace Pilot5bMeta1020ReverseStructure

open Pilot5bMeta1020Linear Pilot5bMeta1020OrAggregate Pilot5bMeta1020Reverse

lemma build_extension (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) :
    ∃ hs, net (build n seeds edges weight k s) = net s ++ hs := by
  induction k generalizing s with
  | zero => exact ⟨[], by simp [build]⟩
  | succ k ih =>
    obtain ⟨hs, he⟩ := step_extension n seeds edges weight k s
    obtain ⟨ts, ht⟩ := ih (step n seeds edges weight k s)
    exact ⟨hs ++ ts, by simpa only [build, he, List.append_assoc] using ht⟩

lemma build_prefix (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) : net s <+: net (build n seeds edges weight k s) := by
  obtain ⟨hs, he⟩ := build_extension n seeds edges weight k s
  exact ⟨hs, he.symm⟩

lemma build_old_read (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) (labels : ℕ → Bool) (y : List Bool) (hy : y.length = n)
    (r : ℕ) (hr : r < n + (net s).length) :
    (run (net (build n seeds edges weight k s)) labels y).getD r false =
      (run (net s) labels y).getD r false := by
  obtain ⟨hs, he⟩ := build_extension n seeds edges weight k s
  rw [he, run_append]
  exact run_getD_lt hs labels _ r (by simpa only [run_length, hy] using hr)

lemma step_fanin (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (v : ℕ) (s : State) (hfan : ∀ us, Sum.inl us ∈ net s → us.length ≤ 2) :
    ∀ us, Sum.inl us ∈ net (step n seeds edges weight v s) → us.length ≤ 2 := by
  have ha := aggregate_fanin n (net s) (incoming seeds edges (message s) v) hfan
  cases hw : weight v with
  | none => simpa only [Pilot5bMeta1020Reverse.step, net, hw] using ha
  | some z =>
    intro us hu
    simp only [Pilot5bMeta1020Reverse.step, hw, net, List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at hu
    exact ha us hu

lemma build_fanin (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) (hfan : ∀ us, Sum.inl us ∈ net s → us.length ≤ 2) :
    ∀ us, Sum.inl us ∈ net (build n seeds edges weight k s) → us.length ≤ 2 := by
  induction k generalizing s with
  | zero => exact hfan
  | succ k ih =>
    exact ih (step n seeds edges weight k s) (step_fanin n seeds edges weight k s hfan)

lemma build_length (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) :
    (net (build n seeds edges weight k s)).length = (net s).length +
      ∑ v ∈ Finset.range k, ((incomingCount seeds edges v - 1) +
        (if (weight v).isSome then 1 else 0)) := by
  induction k generalizing s with
  | zero => simp [build]
  | succ k ih =>
    rw [build, ih, step_length, Finset.sum_range_succ]
    omega

lemma build_length_le (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) :
    (net s).length ≤ (net (build n seeds edges weight k s)).length := by
  rw [build_length]
  omega

def weightedCount (weight : ℕ → Option ℕ) (k : ℕ) : ℕ :=
  ∑ v ∈ Finset.range k, if (weight v).isSome then 1 else 0

def usedForks (seeds edges : List (ℕ × ℕ)) (forks : Finset ℕ) : Finset ℕ :=
  forks.filter fun v => 0 < incomingCount seeds edges v

lemma weightedCount_eq_card (weight : ℕ → Option ℕ) (k : ℕ) :
    weightedCount weight k = ((Finset.range k).filter fun v => (weight v).isSome).card := by
  classical
  simp [weightedCount, Finset.sum_boole]

lemma incomingCount_eq_messageCount (seeds edges : List (ℕ × ℕ)) (v : ℕ) :
    incomingCount seeds edges v =
      PEqualNP.Outside.L_meta_1020.ReverseBudget.messageCount seeds edges v := rfl

lemma build_budget_used (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) (F : Finset ℕ) (hF : F ⊆ Finset.range k)
    (hpositive : ∀ v ∈ F, 0 < incomingCount seeds edges v) :
    (net (build n seeds edges weight k s)).length + F.card ≤
      (net s).length + seeds.length + edges.length + weightedCount weight k := by
  apply PEqualNP.Outside.L_meta_1020.ReverseBudget.static_net_budget
    seeds edges k F hF
  · intro v hv
    simpa only [← incomingCount_eq_messageCount] using (Nat.succ_le_iff.mpr (hpositive v hv))
  · rw [build_length, Finset.sum_add_distrib]
    simp only [weightedCount, incomingCount_eq_messageCount]
    omega

lemma build_budget (n : ℕ) (seeds edges : List (ℕ × ℕ)) (weight : ℕ → Option ℕ)
    (k : ℕ) (s : State) (forks : Finset ℕ) (hF : forks ⊆ Finset.range k) :
    (net (build n seeds edges weight k s)).length + (usedForks seeds edges forks).card ≤
      (net s).length + seeds.length + edges.length + weightedCount weight k := by
  apply build_budget_used n seeds edges weight k s (usedForks seeds edges forks)
  · exact fun _ hv => hF (Finset.mem_filter.mp hv).1
  · exact fun _ hv => (Finset.mem_filter.mp hv).2

end Pilot5bMeta1020ReverseStructure


namespace Pilot5bMeta1020Fold

open PEqualNP.CircuitLowerBounds

def grow {α β : Type*} (f : List α → β → α) (gs : List β) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) w

theorem grow_append {α β : Type*} (f : List α → β → α)
    (gs hs : List β) (w : List α) :
    grow f (gs ++ hs) w = grow f hs (grow f gs w) := by
  simp [grow, List.foldl_append]

theorem grow_prefix {α β : Type*} (f : List α → β → α) (gs : List β) :
    ∀ w : List α, ∃ t : List α, grow f gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [grow], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [f w g])
    refine ⟨f w g :: t, ?_, by simp [hl]⟩
    change grow f gs (w ++ [f w g]) = w ++ f w g :: t
    rw [ht]
    simp

theorem grow_length {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) :
    (grow f gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := grow_prefix f gs w
  rw [ht]
  simp [hl]

theorem grow_getD_lt {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) (i : ℕ) (d : α) (h : i < w.length) :
    (grow f gs w).getD i d = w.getD i d := by
  obtain ⟨t, ht, _⟩ := grow_prefix f gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem grow_getD_ge {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) (i : ℕ) (d : α)
    (h : w.length + gs.length ≤ i) :
    (grow f gs w).getD i d = d := by
  apply List.getD_eq_default
  simpa only [grow_length] using h

theorem grow_snoc {α β : Type*} (f : List α → β → α)
    (gs : List β) (g : β) (w : List α) :
    grow f (gs ++ [g]) w = grow f gs w ++ [f (grow f gs w) g] := by
  simp [grow, List.foldl_append]

theorem grow_gate {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) (d : α) (j : ℕ) (hj : j < gs.length) :
    (grow f gs w).getD (w.length + j) d = f (grow f (gs.take j) w) gs[j] := by
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  set A := grow f (gs.take j) w with hA
  have hAl : A.length = w.length + j := by
    rw [hA, grow_length]
    simp
    omega
  have hw : grow f gs w = grow f (gs.drop (j + 1)) (A ++ [f A gs[j]]) := by
    conv_lhs => rw [hsplit]
    rw [grow_append]
    rfl
  rw [hw, grow_getD_lt _ _ _ _ _ (by simp [hAl]),
    List.getD_append_right _ _ _ _ (by omega)]
  simp [hAl]

theorem grow_take_read {α β : Type*} (f : List α → β → α)
    (gs : List β) (w : List α) (d : α) (j i : ℕ) (hj : j ≤ gs.length) :
    (grow f (gs.take j) w).getD i d =
      if i < w.length + j then (grow f gs w).getD i d else d := by
  have hlen : (grow f (gs.take j) w).length = w.length + j := by
    rw [grow_length, List.length_take, Nat.min_eq_left hj]
  by_cases hi : i < w.length + j
  · rw [ite_eq_left hi]
    conv_rhs => rw [← List.take_append_drop j gs, grow_append]
    exact (grow_getD_lt _ _ _ _ _ (by omega)).symm
  · rw [ite_eq_right hi]
    apply List.getD_eq_default
    omega

def gateValue (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def initialDegrees (n : ℕ) (marked : Finset ℕ) : List ℕ :=
  (List.range n).map fun i => if i ∈ marked then 1 else 0

theorem wires_eq_grow (C : Circuit) (x : List Bool) :
    C.wires x = grow gateValue C.gates x := rfl

theorem lineDegrees_eq_grow (C : Circuit) (n : ℕ) (marked : Finset ℕ) :
    C.lineDegrees n marked = grow (fun d g => g.lineDegree d) C.gates
      (initialDegrees n marked) := rfl

@[simp] theorem initialDegrees_length (n : ℕ) (marked : Finset ℕ) :
    (initialDegrees n marked).length = n := by simp [initialDegrees]

theorem wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  rw [wires_eq_grow, grow_length]
  rfl

theorem lineDegrees_length (C : Circuit) (n : ℕ) (marked : Finset ℕ) :
    (C.lineDegrees n marked).length = n + C.size := by
  rw [lineDegrees_eq_grow, grow_length, initialDegrees_length]
  rfl

theorem wires_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false := grow_getD_lt _ _ _ _ _ hi

theorem wires_gate_prefix (C : Circuit) (x : List Bool)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      gateValue (grow gateValue (C.gates.take j) x) C.gates[j] :=
  grow_gate _ _ _ _ _ hj

theorem lineDegrees_gate_prefix (C : Circuit) (n : ℕ) (marked : Finset ℕ)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.lineDegrees n marked).getD (n + j) 0 =
      C.gates[j].lineDegree
        (grow (fun d g => g.lineDegree d) (C.gates.take j) (initialDegrees n marked)) := by
  rw [lineDegrees_eq_grow]
  simpa only [initialDegrees_length] using
    grow_gate (fun d g => g.lineDegree d) C.gates (initialDegrees n marked) 0 j hj

theorem wires_gate (C : Circuit) (x : List Bool)
    (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < x.length + j then (C.wires x).getD i false else false) := by
  rw [wires_gate_prefix C x j hj]
  unfold gateValue
  congr 1
  apply List.map_congr_left
  intro i _
  exact grow_take_read _ _ _ _ j i (Nat.le_of_lt hj)

end Pilot5bMeta1020Fold

namespace PEqualNP.Outside.L_meta_1020.OriginalGraph

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1020.OneLineCoefficient

def bound (N : ℕ) (C : Circuit) : ℕ := N + N + C.size

def degrees (N : ℕ) (C : Circuit) : List ℕ :=
  C.lineDegrees (N + N) (Finset.Ico N (N + N))

def degree (N : ℕ) (C : Circuit) (r : ℕ) : ℕ := (degrees N C).getD r 0

def readDegree (N : ℕ) (C : Circuit) (w r : ℕ) : ℕ :=
  if r < w then degree N C r else 0

def gateAt (N : ℕ) (C : Circuit) (w : ℕ) : Option Gate :=
  if N + N ≤ w then C.gates[w - (N + N)]? else none

def children (N : ℕ) (C : Circuit) (w : ℕ) : List ℕ :=
  match gateAt N C w with
  | none => []
  | some g => if degree N C w = 2 then
      g.inputs.filter (fun r => decide (r < w ∧ degree N C r = 2)) else []

def edges (N : ℕ) (C : Circuit) : List (ℕ × ℕ) :=
  (List.range (bound N C)).flatMap (fun w => (children N C w).map (fun r => (w, r)))

def weight (N : ℕ) (C : Circuit) (w : ℕ) : Option ℕ :=
  match gateAt N C w with
  | none => none
  | some g => if degree N C w = 2 then
      match g.op with
      | .and => (g.inputs.find? (fun r => decide (readDegree N C w r = 0))).map
          (fun r => if r < w then r else bound N C)
      | _ => none
    else none

def ForkWith (N : ℕ) (C : Circuit) (w a b : ℕ) : Prop :=
  ∃ g, gateAt N C w = some g ∧ g.op = .and ∧ g.inputs = [a, b] ∧
    readDegree N C w a = 1 ∧ readDegree N C w b = 1

def Fork (N : ℕ) (C : Circuit) (w : ℕ) : Prop := ∃ a b, ForkWith N C w a b

def gateWeight (g : Gate) (d : List ℕ) : Option ℕ :=
  match g.op with
  | .and => g.inputs.find? (fun r => decide (d.getD r 0 = 0))
  | _ => none

def active (z : List Bool) (v : Option ℕ) : Bool :=
  v.elim true (fun r => z.getD r false)

lemma value_and_pair (a b : ℕ) (w : List Bool) :
    value ⟨.and, [a, b]⟩ w = (w.getD a false && w.getD b false) := by
  simp only [value, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true]

lemma gateWeight_pair (a b : ℕ) (d : List ℕ) :
    gateWeight ⟨.and, [a, b]⟩ d =
      if d.getD a 0 = 0 then some a else if d.getD b 0 = 0 then some b else none := by
  by_cases ha : d.getD a 0 = 0 <;> by_cases hb : d.getD b 0 = 0 <;>
    simp only [gateWeight, List.find?_cons, List.find?_nil, ha, hb,
      decide_true, decide_false, ite_true, ite_false]

lemma gateWeight_single (a : ℕ) (d : List ℕ) :
    gateWeight ⟨.and, [a]⟩ d = if d.getD a 0 = 0 then some a else none := by
  by_cases ha : d.getD a 0 = 0 <;>
    simp only [gateWeight, List.find?_cons, List.find?_nil, ha,
      decide_true, decide_false, ite_true, ite_false]

lemma gate_up (g : Gate) (z p w : List Bool) (d : List ℕ)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2)
    (h : AllAt z p w d) (hd : g.lineDegree d = 2)
    (r : ℕ) (hr : r ∈ g.inputs) (hrd : d.getD r 0 = 2)
    (hrw : w.getD r false = true) (hz : active z (gateWeight g d) = true) :
    value g w = true := by
  rcases g with ⟨op, ins⟩
  change op = .and ∨ op = .or at hm
  change ins.length ≤ 2 at hl
  change r ∈ ins at hr
  rcases hm with rfl | rfl
  · cases ins with
    | nil => simp at hr
    | cons a as =>
      cases as with
      | nil =>
        simp only [List.mem_singleton] at hr
        subst r
        simpa [value, GateOp.eval] using hrw
      | cons b bs =>
        cases bs with
        | nil =>
          have hab : d.getD a 0 + d.getD b 0 = 2 := by simpa [Gate.lineDegree] using hd
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · have hb0 : d.getD b 0 = 0 := by omega
            have hzb : z.getD b false = true := by
              rw [gateWeight_pair, hrd, hb0] at hz
              exact hz
            have hwb := (h b).1 hzb
            rw [value_and_pair, hrw, hwb]
            rfl
          · have ha0 : d.getD a 0 = 0 := by omega
            have hza : z.getD a false = true := by
              rw [gateWeight_pair, ha0] at hz
              exact hz
            have hwa := (h a).1 hza
            rw [value_and_pair, hwa, hrw]
            rfl
        | cons c cs => simp only [List.length_cons] at hl; omega
  · have hmem : true ∈ ins.map (fun i => w.getD i false) := List.mem_map.mpr ⟨r, hr, hrw⟩
    simpa [value, GateOp.eval, List.any_eq_true] using hmem

lemma fork_coeff_true {za pa wa zb pb wb : Bool}
    (ha : At za pa wa 1) (hb : At zb pb wb 1)
    (hw : (wa && wb) = true) (hz : (za && zb) = false)
    (hp : ((za && pb) || (pa && zb)) = false) : pa = true ∧ pb = true := by
  have hea := ha.2.2.2 (by omega)
  have heb := hb.2.2.2 (by omega)
  rw [Bool.and_eq_true] at hw
  obtain ⟨rfl, rfl⟩ := hw
  clear ha hb
  cases za <;> cases zb <;> cases pa <;> cases pb <;>
    first | contradiction | exact ⟨rfl, rfl⟩

lemma gate_down (g : Gate) (z p w : List Bool) (d : List ℕ)
    (hm : g.op = .and ∨ g.op = .or) (hl : g.inputs.length ≤ 2)
    (h : AllAt z p w d) (hd : g.lineDegree d = 2)
    (hw : value g w = true) (hz : value g z = false) (hp : coeff g z p = false) :
    (∃ a b, g.op = .and ∧ g.inputs = [a, b] ∧ d.getD a 0 = 1 ∧ d.getD b 0 = 1 ∧
      p.getD a false = true ∧ p.getD b false = true) ∨
    ∃ r ∈ g.inputs, d.getD r 0 = 2 ∧ w.getD r false = true ∧
      z.getD r false = false ∧ p.getD r false = false ∧ active z (gateWeight g d) = true := by
  rcases g with ⟨op, ins⟩
  change op = .and ∨ op = .or at hm
  change ins.length ≤ 2 at hl
  rcases hm with rfl | rfl
  · cases ins with
    | nil => simp [Gate.lineDegree] at hd
    | cons a as =>
      cases as with
      | nil =>
        have ha2 : d.getD a 0 = 2 := by simpa [Gate.lineDegree] using hd
        right
        refine ⟨a, by simp, ha2, ?_, ?_, ?_, ?_⟩
        · simpa [value, GateOp.eval] using hw
        · simpa [value, GateOp.eval] using hz
        · simpa [coeff] using hp
        · rw [gateWeight_single, ha2]
          rfl
      | cons b bs =>
        cases bs with
        | nil =>
          have hab : d.getD a 0 + d.getD b 0 = 2 := by simpa [Gate.lineDegree] using hd
          have hwpair : w.getD a false = true ∧ w.getD b false = true := by
            simpa only [value_and_pair, Bool.and_eq_true] using hw
          have hwa := hwpair.1
          have hwb := hwpair.2
          by_cases ha0 : d.getD a 0 = 0
          · have hb2 : d.getD b 0 = 2 := by omega
            have hza : z.getD a false = true := (at_zero_value (h a) ha0).symm.trans hwa
            have hpa : p.getD a false = false := (h a).2.2.1 ha0
            right
            refine ⟨b, by simp, hb2, hwb, ?_, ?_, ?_⟩
            · rw [value_and_pair, hza] at hz
              exact hz
            · change ((z.getD a false && p.getD b false) || (p.getD a false && z.getD b false)) = false at hp
              rw [hza, hpa] at hp
              simpa only [Bool.true_and, Bool.false_and, Bool.or_false] using hp
            · rw [gateWeight_pair, ha0]
              exact hza
          · by_cases hb0 : d.getD b 0 = 0
            · have ha2 : d.getD a 0 = 2 := by omega
              have hzb : z.getD b false = true := (at_zero_value (h b) hb0).symm.trans hwb
              have hpb : p.getD b false = false := (h b).2.2.1 hb0
              right
              refine ⟨a, by simp, ha2, hwa, ?_, ?_, ?_⟩
              · rw [value_and_pair, hzb] at hz
                simpa only [Bool.and_true] using hz
              · change ((z.getD a false && p.getD b false) || (p.getD a false && z.getD b false)) = false at hp
                rw [hzb, hpb] at hp
                simpa only [Bool.and_false, Bool.and_true, Bool.false_or] using hp
              · rw [gateWeight_pair, ha2, hb0]
                exact hzb
            · have ha1 : d.getD a 0 = 1 := by omega
              have hb1 : d.getD b 0 = 1 := by omega
              left
              refine ⟨a, b, rfl, rfl, ha1, hb1, ?_⟩
              apply fork_coeff_true (by simpa only [ha1] using h a) (by simpa only [hb1] using h b)
              · simpa [value, GateOp.eval] using hw
              · simpa [value, GateOp.eval] using hz
              · exact hp
        | cons c cs => simp only [List.length_cons] at hl; omega
  · have hsome : ∃ r ∈ ins, w.getD r false = true := by simpa [value, GateOp.eval, List.any_eq_true] using hw
    obtain ⟨r, hr, hrw⟩ := hsome
    have hrz : z.getD r false = false := by
      have hall : ∀ r ∈ ins, z.getD r false = false := by simpa [value, GateOp.eval, List.any_eq_false] using hz
      exact hall r hr
    have hrp : p.getD r false = false := by
      have hall : ∀ r ∈ ins, p.getD r false = false := by simpa [coeff, List.any_eq_false] using hp
      exact hall r hr
    have hrle : d.getD r 0 ≤ 2 := by
      have he := input_degree_le ⟨.or, ins⟩ d r (Or.inr rfl) hl hr
      omega
    have hr2 : d.getD r 0 = 2 := by
      by_contra hh
      have hle : d.getD r 0 ≤ 1 := by omega
      have he := (h r).2.2.2 hle
      rw [hrw, hrz, hrp] at he
      contradiction
    exact Or.inr ⟨r, hr, hr2, hrw, hrz, hrp, by simp [active, gateWeight]⟩

lemma getD_take_guard {α : Type*} (xs : List α) (n i : ℕ) (d : α) :
    (xs.take n).getD i d = if i < n then xs.getD i d else d := by
  by_cases hi : i < n
  · rw [ite_eq_left hi]
    change ((xs.take n)[i]?).getD d = (xs[i]?).getD d
    rw [List.getElem?_take_of_lt hi]
  · rw [ite_eq_right hi]
    apply List.getD_eq_default
    have hn : (xs.take n).length ≤ n := by simp
    omega

lemma take_allAt (z p w : List Bool) (d : List ℕ) (n : ℕ) (h : AllAt z p w d) :
    AllAt (z.take n) (p.take n) (w.take n) (d.take n) := by
  intro i
  simp only [getD_take_guard]
  by_cases hi : i < n
  · simpa only [ite_eq_left hi] using h i
  · simpa only [ite_eq_right hi] using at_false

lemma fold_p_extends (gs : List Gate) (s : State) :
    ∃ t, (gs.foldl step s).2.1 = s.2.1 ++ t ∧ t.length = gs.length := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hlen⟩ := ih (step s g)
    refine ⟨coeff g s.1 s.2.1 :: t, ?_, by simp [hlen]⟩
    change (gs.foldl step (step s g)).2.1 = _
    rw [ht]
    simp [step, List.append_assoc]

lemma fold_z_extends (gs : List Gate) (s : State) :
    ∃ t, (gs.foldl step s).1 = s.1 ++ t ∧ t.length = gs.length := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hlen⟩ := ih (step s g)
    refine ⟨value g s.1 :: t, ?_, by simp [hlen]⟩
    change (gs.foldl step (step s g)).1 = _
    rw [ht]
    simp [step, List.append_assoc]

lemma fold_p_take (gs : List Gate) (s : State) (j : ℕ) (hj : j ≤ gs.length) :
    ((gs.take j).foldl step s).2.1 = (gs.foldl step s).2.1.take (s.2.1.length + j) := by
  have hlen : ((gs.take j).foldl step s).2.1.length = s.2.1.length + j := by
    simpa only [List.length_take, Nat.min_eq_left hj] using (fold_lengths (gs.take j) s).2.1
  obtain ⟨t, ht, _⟩ := fold_p_extends (gs.drop j) ((gs.take j).foldl step s)
  have heq : (gs.foldl step s).2.1 = ((gs.take j).foldl step s).2.1 ++ t := by
    conv_lhs => rw [← List.take_append_drop j gs, List.foldl_append]
    exact ht
  rw [heq, ← hlen]
  simp

lemma fold_z_take (gs : List Gate) (s : State) (j : ℕ) (hj : j ≤ gs.length) :
    ((gs.take j).foldl step s).1 = (gs.foldl step s).1.take (s.1.length + j) := by
  have hlen : ((gs.take j).foldl step s).1.length = s.1.length + j := by
    simpa only [List.length_take, Nat.min_eq_left hj] using (fold_lengths (gs.take j) s).1
  obtain ⟨t, ht, _⟩ := fold_z_extends (gs.drop j) ((gs.take j).foldl step s)
  have heq : (gs.foldl step s).1 = ((gs.take j).foldl step s).1 ++ t := by
    conv_lhs => rw [← List.take_append_drop j gs, List.foldl_append]
    exact ht
  rw [heq, ← hlen]
  simp

lemma fold_p_gate (gs : List Gate) (s : State) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl step s).2.1.getD (s.2.1.length + j) false =
      coeff gs[j] ((gs.take j).foldl step s).1 ((gs.take j).foldl step s).2.1 := by
  let pre := (gs.take j).foldl step s
  have hlen : pre.2.1.length = s.2.1.length + j := by
    simpa only [pre, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)] using
      (fold_lengths (gs.take j) s).2.1
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
  have hfull : gs.foldl step s = (gs.drop (j + 1)).foldl step (step pre gs[j]) := by
    conv_lhs => rw [hsplit, List.foldl_append]
    rfl
  rw [hfull, fold_p_getD _ _ _ (by simp only [step, List.length_append, List.length_singleton]; omega)]
  change (pre.2.1 ++ [coeff gs[j] pre.1 pre.2.1]).getD (s.2.1.length + j) false = _
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hlen, pre]

lemma fold_p_gate_take (gs : List Gate) (s : State) (j : ℕ) (hj : j < gs.length)
    (hlen : s.1.length = s.2.1.length) :
    (gs.foldl step s).2.1.getD (s.2.1.length + j) false =
      coeff gs[j] ((gs.foldl step s).1.take (s.2.1.length + j))
        ((gs.foldl step s).2.1.take (s.2.1.length + j)) := by
  rw [fold_p_gate gs s j hj, fold_z_take gs s j (Nat.le_of_lt hj),
    fold_p_take gs s j (Nat.le_of_lt hj), hlen]

lemma grow_take_eq {α β : Type*} (f : List α → β → α) (gs : List β)
    (xs : List α) (j : ℕ) (hj : j ≤ gs.length) :
    Pilot5bMeta1020Fold.grow f (gs.take j) xs =
      (Pilot5bMeta1020Fold.grow f gs xs).take (xs.length + j) := by
  obtain ⟨t, ht, _⟩ := Pilot5bMeta1020Fold.grow_prefix f (gs.drop j)
    (Pilot5bMeta1020Fold.grow f (gs.take j) xs)
  have hlen : (Pilot5bMeta1020Fold.grow f (gs.take j) xs).length = xs.length + j := by
    simp only [Pilot5bMeta1020Fold.grow_length, List.length_take, Nat.min_eq_left hj]
  have heq : Pilot5bMeta1020Fold.grow f gs xs =
      Pilot5bMeta1020Fold.grow f (gs.take j) xs ++ t := by
    conv_lhs => rw [← List.take_append_drop j gs, Pilot5bMeta1020Fold.grow_append]
    exact ht
  rw [heq, ← hlen]
  simp

lemma wires_gate_take (C : Circuit) (xs : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires xs).getD (xs.length + j) false = value C.gates[j] ((C.wires xs).take (xs.length + j)) := by
  rw [Pilot5bMeta1020Fold.wires_gate_prefix C xs j hj,
    grow_take_eq _ _ _ _ (Nat.le_of_lt hj)]
  rfl

lemma degrees_gate_take (N : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    degree N C (N + N + j) = C.gates[j].lineDegree ((degrees N C).take (N + N + j)) := by
  unfold degree degrees
  rw [Pilot5bMeta1020Fold.lineDegrees_gate_prefix C (N + N) _ j hj,
    grow_take_eq _ _ _ _ (Nat.le_of_lt hj), Pilot5bMeta1020Fold.initialDegrees_length]
  rfl

lemma initial_degrees (N : ℕ) :
    Pilot5bMeta1020Fold.initialDegrees (N + N) (Finset.Ico N (N + N)) =
      List.replicate N 0 ++ List.replicate N 1 := by
  unfold Pilot5bMeta1020Fold.initialDegrees
  rw [List.range_add, List.map_append, List.map_map]
  have h0 : (List.range N).map (fun i => if i ∈ Finset.Ico N (N + N) then 1 else 0) =
      List.replicate N 0 := by
    calc
      _ = (List.range N).map (fun _ => 0) := by
        apply List.map_congr_left
        intro i hi
        have hi' := List.mem_range.mp hi
        have hn : i ∉ Finset.Ico N (N + N) := by simp only [Finset.mem_Ico]; omega
        simp only [ite_eq_right hn]
      _ = _ := by simp
  have h1 : (List.range N).map (fun i => if N + i ∈ Finset.Ico N (N + N) then 1 else 0) =
      List.replicate N 1 := by
    calc
      _ = (List.range N).map (fun _ => 1) := by
        apply List.map_congr_left
        intro i hi
        have hi' := List.mem_range.mp hi
        have hn : N + i ∈ Finset.Ico N (N + N) := by simp only [Finset.mem_Ico]; omega
        simp only [ite_eq_left hn]
      _ = _ := by simp
  exact congrArg₂ List.append h0 h1

def fullState (C : Circuit) (x y : List Bool) : State := C.gates.foldl step (initial x y)

def zeroValues (N : ℕ) (C : Circuit) (x : List Bool) : List Bool :=
  C.wires (x ++ List.replicate N false)

def positiveValues (C : Circuit) (x y : List Bool) : List Bool := (fullState C x y).2.1

def fullValues (C : Circuit) (x y : List Bool) : List Bool := C.wires (x ++ y)

lemma fullState_zero (N : ℕ) (C : Circuit) (x y : List Bool) (hy : y.length = N) :
    (fullState C x y).1 = zeroValues N C x := by
  rw [fullState, fold_zero_eq]
  simp only [initial, hy]
  rfl

lemma fullState_full (C : Circuit) (x y : List Bool) :
    (fullState C x y).2.2.1 = fullValues C x y :=
  fold_full_eq C.gates (initial x y)

lemma fullState_degrees (N : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) :
    (fullState C x y).2.2.2 = degrees N C := by
  rw [fullState, fold_degree_eq]
  simp only [initial, hx, hy]
  rw [← initial_degrees N]
  rfl

lemma actual_allAt (N : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N) :
    AllAt (zeroValues N C x) (positiveValues C x y) (fullValues C x y) (degrees N C) := by
  have h := (circuit_fold_valid C hm x y).2.2.2
  change AllAt (fullState C x y).1 (positiveValues C x y) (fullState C x y).2.2.1
    (fullState C x y).2.2.2 at h
  rwa [fullState_zero N C x y hy, fullState_full C x y, fullState_degrees N C x y hx hy] at h

lemma positive_gate_take (N : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) (j : ℕ) (hj : j < C.gates.length) :
    (positiveValues C x y).getD (N + N + j) false =
      coeff C.gates[j] ((zeroValues N C x).take (N + N + j))
        ((positiveValues C x y).take (N + N + j)) := by
  have heq := fold_p_gate_take C.gates (initial x y) j hj (by simp [initial])
  change (positiveValues C x y).getD _ false = coeff _ ((fullState C x y).1.take _)
    ((positiveValues C x y).take _) at heq
  rw [fullState_zero N C x y hy] at heq
  simpa only [initial, List.length_append, List.length_replicate, hx, hy] using heq

lemma prefix_degree_read (N : ℕ) (C : Circuit) (j r : ℕ) (hj : j ≤ C.gates.length) :
    (Pilot5bMeta1020Fold.grow (fun d g => g.lineDegree d) (C.gates.take j)
      (Pilot5bMeta1020Fold.initialDegrees (N + N) (Finset.Ico N (N + N)))).getD r 0 =
      readDegree N C (N + N + j) r := by
  rw [grow_take_eq _ _ _ _ hj, Pilot5bMeta1020Fold.initialDegrees_length,
    getD_take_guard]
  rfl

lemma take_degree_read (N : ℕ) (C : Circuit) (w r : ℕ) :
    ((degrees N C).take w).getD r 0 = readDegree N C w r :=
  getD_take_guard (degrees N C) w r 0

lemma gateAt_index (N : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt N C (N + N + j) = some C.gates[j] := by
  simp [gateAt, hj]

lemma gateAt_some (N : ℕ) (C : Circuit) (w : ℕ) (g : Gate)
    (hg : gateAt N C w = some g) :
    ∃ j : ℕ, ∃ hj : j < C.gates.length, w = N + N + j ∧ C.gates[j] = g := by
  unfold gateAt at hg
  split_ifs at hg with hw
  · obtain ⟨hj, heq⟩ := List.getElem?_eq_some_iff.mp hg
    exact ⟨w - (N + N), hj, by omega, heq⟩

lemma gateAt_degree (N : ℕ) (C : Circuit) (w : ℕ) (g : Gate)
    (hg : gateAt N C w = some g) :
    degree N C w = g.lineDegree ((degrees N C).take w) := by
  obtain ⟨j, hj, rfl, rfl⟩ := gateAt_some N C w g hg
  exact degrees_gate_take N C j hj

lemma gateAt_mono (N : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (w : ℕ) (g : Gate) (hg : gateAt N C w = some g) :
    (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  obtain ⟨j, hj, _, rfl⟩ := gateAt_some N C w g hg
  obtain ⟨hop, hlen⟩ := hm C.gates[j] (List.getElem_mem hj)
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop, hlen⟩

lemma fork_degree (N : ℕ) (C : Circuit) (w : ℕ) (hf : Fork N C w) : degree N C w = 2 := by
  obtain ⟨a, b, g, hg, hop, hins, ha, hb⟩ := hf
  rw [gateAt_degree N C w g hg]
  rcases g with ⟨op, ins⟩
  change op = .and at hop
  change ins = [a, b] at hins
  subst op
  subst ins
  simp only [Gate.lineDegree, ite_true, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, take_degree_read, ha, hb]
  rfl

lemma children_of_gateAt (N : ℕ) (C : Circuit) (w r : ℕ) (g : Gate)
    (hg : gateAt N C w = some g) (hd : degree N C w = 2) :
    r ∈ children N C w ↔ r ∈ g.inputs ∧ r < w ∧ degree N C r = 2 := by
  simp [children, hg, hd]

lemma mem_edges (N : ℕ) (C : Circuit) (w r : ℕ) :
    (w, r) ∈ edges N C ↔ w < bound N C ∧ r ∈ children N C w := by
  simp [edges]

lemma degrees_length (N : ℕ) (C : Circuit) : (degrees N C).length = bound N C :=
  Pilot5bMeta1020Fold.lineDegrees_length C (N + N) _

lemma zeroValues_length (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) :
    (zeroValues N C x).length = bound N C := by
  simp only [zeroValues, Pilot5bMeta1020Fold.wires_length, List.length_append,
    List.length_replicate, hx, bound]

lemma fullValues_length (N : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) : (fullValues C x y).length = bound N C := by
  simp only [fullValues, Pilot5bMeta1020Fold.wires_length, List.length_append, hx, hy, bound]

lemma positiveValues_length (N : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) : (positiveValues C x y).length = bound N C := by
  have h := (fold_lengths C.gates (initial x y)).2.1
  simpa only [positiveValues, fullState, initial, List.length_append, List.length_replicate,
    hx, hy, bound, Circuit.size] using h

lemma degree_input_le_one (N : ℕ) (C : Circuit) (r : ℕ) (hr : r < N + N) :
    degree N C r ≤ 1 := by
  unfold degree degrees
  rw [Pilot5bMeta1020Fold.lineDegrees_eq_grow,
    Pilot5bMeta1020Fold.grow_getD_lt _ _ _ _ _ (by simpa using hr)]
  rw [List.getD_eq_getElem _ _ (by simpa using hr)]
  simp only [Pilot5bMeta1020Fold.initialDegrees, List.getElem_map, List.getElem_range]
  split_ifs <;> omega

lemma degree_two_bounds (N : ℕ) (C : Circuit) (w : ℕ) (hd : degree N C w = 2) :
    N + N ≤ w ∧ w < bound N C := by
  constructor
  · by_contra h
    have he := degree_input_le_one N C w (by omega)
    omega
  · by_contra h
    have he : degree N C w = 0 :=
      List.getD_eq_default (degrees N C) 0 (by rw [degrees_length]; omega)
    omega

lemma degree_two_gateAt (N : ℕ) (C : Circuit) (w : ℕ) (hd : degree N C w = 2) :
    ∃ g, gateAt N C w = some g := by
  obtain ⟨hlo, hhi⟩ := degree_two_bounds N C w hd
  have hj : w - (N + N) < C.gates.length := by unfold bound Circuit.size at hhi; omega
  refine ⟨C.gates[w - (N + N)], ?_⟩
  have heq : w = N + N + (w - (N + N)) := by omega
  conv_lhs => rw [heq]
  exact gateAt_index N C (w - (N + N)) hj

lemma children_spec (N : ℕ) (C : Circuit) (w r : ℕ) (hr : r ∈ children N C w) :
    ∃ g, gateAt N C w = some g ∧ degree N C w = 2 ∧ r ∈ g.inputs ∧
      r < w ∧ degree N C r = 2 := by
  cases hg : gateAt N C w with
  | none => simp [children, hg] at hr
  | some g =>
    by_cases hd : degree N C w = 2
    · exact ⟨g, rfl, hd, (children_of_gateAt N C w r g hg hd).mp hr⟩
    · simp [children, hg, hd] at hr

lemma edge_bounds (N : ℕ) (C : Circuit) (w r : ℕ) (he : (w, r) ∈ edges N C) :
    r < w ∧ w < bound N C ∧ degree N C w = 2 ∧ degree N C r = 2 := by
  obtain ⟨hw, hr⟩ := (mem_edges N C w r).mp he
  obtain ⟨g, _, hd, _, hlt, hr2⟩ := children_spec N C w r hr
  exact ⟨hlt, hw, hd, hr2⟩

lemma fork_children (N : ℕ) (C : Circuit) (w a b : ℕ) (hf : ForkWith N C w a b) :
    a < w ∧ b < w ∧ w < bound N C ∧ degree N C a = 1 ∧ degree N C b = 1 := by
  have hwa := degree_two_bounds N C w (fork_degree N C w ⟨a, b, hf⟩)
  obtain ⟨g, hg, _, _, ha, hb⟩ := hf
  have hal : a < w := by unfold readDegree at ha; split_ifs at ha; omega
  have hbl : b < w := by unfold readDegree at hb; split_ifs at hb; omega
  exact ⟨hal, hbl, hwa.2, by simpa only [readDegree, ite_eq_left hal] using ha,
    by simpa only [readDegree, ite_eq_left hbl] using hb⟩

lemma weight_gateAt (N : ℕ) (C : Circuit) (w : ℕ) (g : Gate)
    (hg : gateAt N C w = some g) (hd : degree N C w = 2) :
    weight N C w = (gateWeight g ((degrees N C).take w)).map
      (fun r => if r < w then r else bound N C) := by
  have hfun : (fun r => decide (readDegree N C w r = 0)) =
      (fun r => decide (((degrees N C).take w).getD r 0 = 0)) := by
    funext r
    rw [take_degree_read]
  unfold weight
  simp only [hg, hd, ite_true]
  cases hop : g.op <;> simp only [hop, gateWeight, hfun, Option.map_none]

lemma active_weight (N : ℕ) (C : Circuit) (w : ℕ) (g : Gate) (z : List Bool)
    (hz : z.length = bound N C) (hg : gateAt N C w = some g) (hd : degree N C w = 2) :
    active z (weight N C w) = active (z.take w) (gateWeight g ((degrees N C).take w)) := by
  rw [weight_gateAt N C w g hg hd]
  cases hv : gateWeight g ((degrees N C).take w) with
  | none => rfl
  | some r =>
    simp only [Option.map_some, active, Option.elim_some, getD_take_guard]
    by_cases hr : r < w
    · simp only [ite_eq_left hr]
    · simp only [ite_eq_right hr]
      exact List.getD_eq_default z false (by omega)

lemma gateAt_full (N : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) (w : ℕ) (g : Gate)
    (hg : gateAt N C w = some g) :
    (fullValues C x y).getD w false = value g ((fullValues C x y).take w) := by
  obtain ⟨j, hj, rfl, rfl⟩ := gateAt_some N C w g hg
  simpa only [fullValues, List.length_append, hx, hy] using wires_gate_take C (x ++ y) j hj

lemma gateAt_zero (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N)
    (w : ℕ) (g : Gate) (hg : gateAt N C w = some g) :
    (zeroValues N C x).getD w false = value g ((zeroValues N C x).take w) := by
  obtain ⟨j, hj, rfl, rfl⟩ := gateAt_some N C w g hg
  simpa only [zeroValues, List.length_append, List.length_replicate, hx] using
    wires_gate_take C (x ++ List.replicate N false) j hj

lemma gateAt_positive (N : ℕ) (C : Circuit) (x y : List Bool)
    (hx : x.length = N) (hy : y.length = N) (w : ℕ) (g : Gate)
    (hg : gateAt N C w = some g) :
    (positiveValues C x y).getD w false =
      coeff g ((zeroValues N C x).take w) ((positiveValues C x y).take w) := by
  obtain ⟨j, hj, rfl, rfl⟩ := gateAt_some N C w g hg
  exact positive_gate_take N C x y hx hy j hj

lemma edge_up (N : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (w r : ℕ) (he : (w, r) ∈ edges N C)
    (hz : active (zeroValues N C x) (weight N C w) = true)
    (hr : (fullValues C x y).getD r false = true) :
    (fullValues C x y).getD w false = true := by
  obtain ⟨_, hc⟩ := (mem_edges N C w r).mp he
  obtain ⟨g, hg, hd, hri, hlt, hr2⟩ := children_spec N C w r hc
  obtain ⟨hgm, hgl⟩ := gateAt_mono N C hm w g hg
  have hat := take_allAt _ _ _ _ w (actual_allAt N C hm x y hx hy)
  have hgd : g.lineDegree ((degrees N C).take w) = 2 := by rwa [← gateAt_degree N C w g hg]
  have hrd : ((degrees N C).take w).getD r 0 = 2 := by
    rw [take_degree_read, readDegree, ite_eq_left hlt]
    exact hr2
  have hrw : ((fullValues C x y).take w).getD r false = true := by
    rw [getD_take_guard, ite_eq_left hlt]
    exact hr
  rw [active_weight N C w g _ (zeroValues_length N C x hx) hg hd] at hz
  rw [gateAt_full N C x y hx hy w g hg]
  exact gate_up g _ _ _ _ hgm hgl hat hgd r hri hrd hrw hz

lemma fork_full (N : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (w a b : ℕ) (hf : ForkWith N C w a b)
    (ha : (positiveValues C x y).getD a false = true)
    (hb : (positiveValues C x y).getD b false = true) :
    (fullValues C x y).getD w false = true := by
  have hc := fork_children N C w a b hf
  have hi := actual_allAt N C hm x y hx hy
  have hwa := (hi a).2.1 ha
  have hwb := (hi b).2.1 hb
  obtain ⟨g, hg, hop, hins, _, _⟩ := hf
  rw [gateAt_full N C x y hx hy w g hg]
  rcases g with ⟨op, ins⟩
  change op = .and at hop
  change ins = [a, b] at hins
  subst op
  subst ins
  rw [value_and_pair, getD_take_guard, getD_take_guard, ite_eq_left hc.1,
    ite_eq_left hc.2.1, hwa, hwb]
  rfl

def Residual (N : ℕ) (C : Circuit) (x y : List Bool) (w : ℕ) : Prop :=
  degree N C w = 2 ∧ (fullValues C x y).getD w false = true ∧
    (zeroValues N C x).getD w false = false ∧ (positiveValues C x y).getD w false = false

def ActiveEdge (N : ℕ) (C : Circuit) (x : List Bool) (w r : ℕ) : Prop :=
  (w, r) ∈ edges N C ∧ active (zeroValues N C x) (weight N C w) = true

lemma edge_down (N : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (w : ℕ) (hw : Residual N C x y w) :
    (∃ a b, ForkWith N C w a b ∧ (positiveValues C x y).getD a false = true ∧
      (positiveValues C x y).getD b false = true) ∨
    ∃ r, ActiveEdge N C x w r ∧ Residual N C x y r := by
  obtain ⟨hd, hw, hz, hp⟩ := hw
  obtain ⟨g, hg⟩ := degree_two_gateAt N C w hd
  obtain ⟨hgm, hgl⟩ := gateAt_mono N C hm w g hg
  have hat := take_allAt _ _ _ _ w (actual_allAt N C hm x y hx hy)
  have hgd : g.lineDegree ((degrees N C).take w) = 2 := by rwa [← gateAt_degree N C w g hg]
  rw [gateAt_full N C x y hx hy w g hg] at hw
  rw [gateAt_zero N C x hx w g hg] at hz
  rw [gateAt_positive N C x y hx hy w g hg] at hp
  rcases gate_down g _ _ _ _ hgm hgl hat hgd hw hz hp with hf | he
  · obtain ⟨a, b, hop, hins, ha1, hb1, hpa, hpb⟩ := hf
    have hal : a < w := by rw [take_degree_read] at ha1; unfold readDegree at ha1; split_ifs at ha1; omega
    have hbl : b < w := by rw [take_degree_read] at hb1; unfold readDegree at hb1; split_ifs at hb1; omega
    left
    refine ⟨a, b, ⟨g, hg, hop, hins, ?_, ?_⟩, ?_, ?_⟩
    · rwa [take_degree_read] at ha1
    · rwa [take_degree_read] at hb1
    · simpa only [getD_take_guard, ite_eq_left hal] using hpa
    · simpa only [getD_take_guard, ite_eq_left hbl] using hpb
  · obtain ⟨r, hri, hr2, hrw, hrz, hrp, hweight⟩ := he
    have hrl : r < w := by rw [take_degree_read] at hr2; unfold readDegree at hr2; split_ifs at hr2; omega
    have hrd : degree N C r = 2 := by
      simpa only [take_degree_read, readDegree, ite_eq_left hrl] using hr2
    right
    refine ⟨r, ⟨?_, ?_⟩, hrd, ?_, ?_, ?_⟩
    · apply (mem_edges N C w r).mpr
      exact ⟨(degree_two_bounds N C w hd).2,
        (children_of_gateAt N C w r g hg hd).mpr ⟨hri, hrl, hrd⟩⟩
    · rwa [active_weight N C w g _ (zeroValues_length N C x hx) hg hd]
    · simpa only [getD_take_guard, ite_eq_left hrl] using hrw
    · simpa only [getD_take_guard, ite_eq_left hrl] using hrz
    · simpa only [getD_take_guard, ite_eq_left hrl] using hrp

lemma fork_descent (N : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (w : ℕ) (hw : Residual N C x y w) :
    ∃ v a b, Relation.ReflTransGen (ActiveEdge N C x) w v ∧ ForkWith N C v a b ∧
      (positiveValues C x y).getD a false = true ∧ (positiveValues C x y).getD b false = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases edge_down N C hm x y hx hy w hw with hf | he
    · obtain ⟨a, b, hf, ha, hb⟩ := hf
      exact ⟨w, a, b, .refl, hf, ha, hb⟩
    · obtain ⟨r, he, hr⟩ := he
      obtain ⟨v, a, b, hpath, hf, ha, hb⟩ := ih r (edge_bounds N C w r he.1).1 hr
      exact ⟨v, a, b, Relation.ReflTransGen.head he hpath, hf, ha, hb⟩

lemma path_up (N : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (w v : ℕ) (hp : Relation.ReflTransGen (ActiveEdge N C x) w v)
    (hv : (fullValues C x y).getD v false = true) : (fullValues C x y).getD w false = true := by
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head he _ ih => exact edge_up N C hm x y hx hy _ _ he.1 he.2 ih

lemma gateWeight_some_zero (g : Gate) (d : List ℕ) (r : ℕ)
    (hr : gateWeight g d = some r) : d.getD r 0 = 0 := by
  cases hop : g.op with
  | and =>
    simp only [gateWeight, hop] at hr
    exact of_decide_eq_true (List.find?_eq_some_iff_append.mp hr).1
  | or => simp [gateWeight, hop] at hr
  | not => simp [gateWeight, hop] at hr
  | mod m => simp [gateWeight, hop] at hr
  | maj => simp [gateWeight, hop] at hr

lemma weight_some_degree (N : ℕ) (C : Circuit) (w a : ℕ)
    (hw : weight N C w = some a) : degree N C a = 0 := by
  cases hg : gateAt N C w with
  | none => simp [weight, hg] at hw
  | some g =>
    by_cases hd : degree N C w = 2
    · rw [weight_gateAt N C w g hg hd] at hw
      obtain ⟨r, hr, heq⟩ := Option.map_eq_some_iff.mp hw
      have hr0 := gateWeight_some_zero g ((degrees N C).take w) r hr
      by_cases hrl : r < w
      · simp only [ite_eq_left hrl] at heq
        subst a
        simpa only [take_degree_read, readDegree, ite_eq_left hrl] using hr0
      · simp only [ite_eq_right hrl] at heq
        subst a
        exact List.getD_eq_default (degrees N C) 0 (by rw [degrees_length])
    · simp [weight, hg, hd] at hw

end PEqualNP.Outside.L_meta_1020.OriginalGraph

namespace Pilot5bMeta1020OriginalNormalization

open PEqualNP.CircuitLowerBounds Pilot5bMeta1020Linear

abbrev F := Pilot5bMeta1020Forward.normalize
abbrev fnet (N : ℕ) (C : Circuit) := Pilot5bMeta1020Forward.net (F N C)
abbrev fmap (N : ℕ) (C : Circuit) (r : ℕ) :=
  (Pilot5bMeta1020Forward.one (F N C)).getD r N
abbrev OBound := PEqualNP.Outside.L_meta_1020.OriginalGraph.bound
abbrev OEdges := PEqualNP.Outside.L_meta_1020.OriginalGraph.edges
abbrev OWeight := PEqualNP.Outside.L_meta_1020.OriginalGraph.weight
abbrev OFork := PEqualNP.Outside.L_meta_1020.OriginalGraph.Fork
abbrev OForkWith := PEqualNP.Outside.L_meta_1020.OriginalGraph.ForkWith
abbrev ODegree := PEqualNP.Outside.L_meta_1020.OriginalGraph.degree

def seeds {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) : List (ℕ × ℕ) :=
  List.ofFn fun j => (fa j, fmap N C (fb j))

def state {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) :
    Pilot5bMeta1020Reverse.State :=
  Pilot5bMeta1020Reverse.build N (seeds N C fa fb) (OEdges N C) (OWeight N C)
    (OBound N C) (Pilot5bMeta1020Reverse.initial N (fnet N C))

def net {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) : List Instruction :=
  Pilot5bMeta1020Reverse.net (state N C fa fb)

def context {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) (w : ℕ) : ℕ :=
  Pilot5bMeta1020Reverse.context (state N C fa fb) w

noncomputable def forks (N : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range (OBound N C)).filter (OFork N C)

noncomputable def usedForks {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) : Finset ℕ :=
  Pilot5bMeta1020ReverseStructure.usedForks (seeds N C fa fb) (OEdges N C) (forks N C)

def forkInputs (N : ℕ) (C : Circuit) (w : ℕ) : List ℕ :=
  ((PEqualNP.Outside.L_meta_1020.OriginalGraph.gateAt N C w).map Gate.inputs).getD []

def forkLeft (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (forkInputs N C w).getD 0 (OBound N C)

def forkRight (N : ℕ) (C : Circuit) (w : ℕ) : ℕ :=
  (forkInputs N C w).getD 1 (OBound N C)

abbrev Triple := ℕ × ℕ × ℕ

def bulkJob {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) (j : Fin J) : Triple :=
  (fmap N C (fa j), fmap N C (fb j), fmap N C (fb j))

def forkJob {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) (w : ℕ) : Triple :=
  (fmap N C (forkLeft N C w), fmap N C (forkRight N C w), context N C fa fb w)

noncomputable def jobs {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) : List Triple :=
  List.ofFn (bulkJob N C fa fb) ++
    (usedForks N C fa fb).toList.map (forkJob N C fa fb)

lemma seeds_length {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) :
    (seeds N C fa fb).length = J := by simp [seeds]

lemma mem_seeds {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) (e : ℕ × ℕ) :
    e ∈ seeds N C fa fb ↔ ∃ j, e = (fa j, fmap N C (fb j)) := by
  simp [seeds, eq_comm]

lemma seeds_bound {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) :
    ∀ e ∈ seeds N C fa fb, e.2 < N + (fnet N C).length := by
  intro e he
  obtain ⟨j, rfl⟩ := (mem_seeds N C fa fb e).mp he
  exact Pilot5bMeta1020Forward.normalize_one_getD_bound N C (fb j)

lemma forward_head (N : ℕ) (C : Circuit) : (fnet N C).head? = some (Sum.inl []) := by
  obtain ⟨t, ht⟩ := Pilot5bMeta1020Forward.build_net_false_prefix N (N + N + C.size) C.gates
  change (Pilot5bMeta1020Forward.net
    (Pilot5bMeta1020Forward.build N (N + N + C.size) C.gates)).head? = _
  rw [ht]
  rfl

lemma old_read {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = N) (r : ℕ) :
    (run (net N C fa fb) labels y).getD (fmap N C r) false =
      (run (fnet N C) labels y).getD (fmap N C r) false := by
  exact Pilot5bMeta1020ReverseStructure.build_old_read N (seeds N C fa fb)
    (OEdges N C) (OWeight N C) (OBound N C)
    (Pilot5bMeta1020Reverse.initial N (fnet N C)) labels y hy (fmap N C r)
    (Pilot5bMeta1020Forward.normalize_one_getD_bound N C r)

lemma jobs_length {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) :
    (jobs N C fa fb).length = J + (usedForks N C fa fb).card := by
  simp [jobs]

lemma mem_jobs {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) (t : Triple) :
    t ∈ jobs N C fa fb ↔ (∃ j, t = bulkJob N C fa fb j) ∨
      ∃ w ∈ usedForks N C fa fb, t = forkJob N C fa fb w := by
  simp [jobs, eq_comm]

lemma mem_forks (N : ℕ) (C : Circuit) (w : ℕ) :
    w ∈ forks N C ↔ w < OBound N C ∧ OFork N C w := by
  classical
  simp [forks]

lemma mem_usedForks {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ) (w : ℕ) :
    w ∈ usedForks N C fa fb ↔ w < OBound N C ∧ OFork N C w ∧
      0 < Pilot5bMeta1020Reverse.incomingCount (seeds N C fa fb) (OEdges N C) w := by
  classical
  simp [usedForks, Pilot5bMeta1020ReverseStructure.usedForks, mem_forks, and_assoc]

lemma fork_spec (N : ℕ) (C : Circuit) (w : ℕ) (hf : OFork N C w) :
    OForkWith N C w (forkLeft N C w) (forkRight N C w) := by
  obtain ⟨a, b, g, hg, ho, hi, ha, hb⟩ := hf
  have hl : forkLeft N C w = a := by simp [forkLeft, forkInputs, hg, hi]
  have hr : forkRight N C w = b := by simp [forkRight, forkInputs, hg, hi]
  exact hl ▸ hr ▸ ⟨g, hg, ho, hi, ha, hb⟩


lemma edge_bounds (N : ℕ) (C : Circuit) :
    ∀ e ∈ OEdges N C, e.2 < e.1 ∧ e.1 < OBound N C := by
  rintro ⟨w, r⟩ he
  obtain ⟨hw, hr⟩ := (PEqualNP.Outside.L_meta_1020.OriginalGraph.mem_edges N C w r).mp he
  refine ⟨?_, hw⟩
  cases hg : PEqualNP.Outside.L_meta_1020.OriginalGraph.gateAt N C w with
  | none => simp [PEqualNP.Outside.L_meta_1020.OriginalGraph.children, hg] at hr
  | some g =>
    by_cases hd : ODegree N C w = 2
    · exact ((PEqualNP.Outside.L_meta_1020.OriginalGraph.children_of_gateAt N C w r g hg hd).mp hr).2.1
    · simp [PEqualNP.Outside.L_meta_1020.OriginalGraph.children, hg, hd] at hr

lemma context_reachable {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (labels : ℕ → Bool) (y : List Bool) (hy : y.length = N) (w : ℕ)
    (hw : w < OBound N C) :
    (run (net N C fa fb) labels y).getD (context N C fa fb w) false = true ↔
      Pilot5bMeta1020Weighted.seedReachable (OEdges N C)
        (Pilot5bMeta1020Reverse.weightValue labels (OWeight N C)) (seeds N C fa fb)
        (fun r => (run (fnet N C) labels y).getD r false) w := by
  exact Pilot5bMeta1020ReverseWeightedCorrectness.context_true_iff N (OBound N C)
    (fnet N C) (seeds N C fa fb) (OEdges N C) (OWeight N C) labels y hy
    (forward_head N C) (seeds_bound N C fa fb) (edge_bounds N C) w hw

lemma reachable_incoming_positive (edges seeds : List (ℕ × ℕ))
    (weightEval seedEval : ℕ → Bool) (w : ℕ)
    (hr : Pilot5bMeta1020Weighted.seedReachable edges weightEval seeds seedEval w) :
    0 < Pilot5bMeta1020Reverse.incomingCount seeds edges w := by
  have ht := (Pilot5bMeta1020Weighted.target_true edges weightEval seeds seedEval w).mpr hr
  have hd := (Pilot5bMeta1020Weighted.target_recurrence edges weightEval seeds seedEval w).mp ht
  by_contra hp
  have hz : Pilot5bMeta1020Reverse.incomingCount seeds edges w = 0 := by omega
  simp only [Pilot5bMeta1020Reverse.incomingCount, Nat.add_eq_zero,
    List.length_eq_zero_iff] at hz
  rcases hd with ⟨s, hs, hsw, _⟩ | ⟨e, he, hew, _, _⟩
  · have hm : s ∈ seeds.filter (fun e => decide (e.1 = w)) := by simp [hs, hsw]
    rw [hz.1] at hm
    simp at hm
  · have hm : e ∈ edges.filter (fun e => decide (e.2 = w)) := by simp [he, hew]
    rw [hz.2] at hm
    simp at hm

def Fires (read : ℕ → Bool) (t : Triple) : Prop :=
  read t.1 = true ∧ read t.2.1 = true ∧ read t.2.2 = true

lemma bulk_sound {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hda : ∀ j, ODegree N C (fa j) ≤ 2) (hdb : ∀ j, ODegree N C (fb j) ≤ 1)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N) (j : Fin J)
    (hf : Fires (fun r => (run (net N C fa fb)
      (Pilot5bMeta1020Forward.pointLabels N C x) y).getD r false)
      (bulkJob N C fa fb j)) :
    (C.wires (x ++ y)).getD (fa j) false = true ∧
      (C.wires (x ++ y)).getD (fb j) false = true := by
  rcases hf with ⟨ha, hb, _⟩
  change (run (net N C fa fb) _ y).getD (fmap N C (fa j)) false = true at ha
  change (run (net N C fa fb) _ y).getD (fmap N C (fb j)) false = true at hb
  rw [old_read N C fa fb _ y hy] at ha hb
  exact ⟨Pilot5bMeta1020Forward.normalize_sound N C hm x y hx hy (fa j) (hda j) ha,
    Pilot5bMeta1020Forward.normalize_sound N C hm x y hx hy (fb j) (Nat.le_trans (hdb j) (by omega)) hb⟩


lemma mapped_positive (N : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N) (r : ℕ)
    (hr : ODegree N C r ≤ 2) :
    (run (fnet N C) (Pilot5bMeta1020Forward.pointLabels N C x) y).getD
      (fmap N C r) false =
      (PEqualNP.Outside.L_meta_1020.OriginalGraph.positiveValues C x y).getD r false :=
  Pilot5bMeta1020Forward.normalize_correct N C hm x y hx hy r hr

lemma fork_left_eq (N : ℕ) (C : Circuit) (w a b : ℕ) (hf : OForkWith N C w a b) :
    forkLeft N C w = a := by
  obtain ⟨g, hg, _, hi, _, _⟩ := hf
  simp [forkLeft, forkInputs, hg, hi]

lemma fork_right_eq (N : ℕ) (C : Circuit) (w a b : ℕ) (hf : OForkWith N C w a b) :
    forkRight N C w = b := by
  obtain ⟨g, hg, _, hi, _, _⟩ := hf
  simp [forkRight, forkInputs, hg, hi]

lemma fork_sound {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (hdb : ∀ j, ODegree N C (fb j) ≤ 1)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N) (w : ℕ)
    (hw : w ∈ usedForks N C fa fb)
    (hf : Fires (fun r => (run (net N C fa fb)
      (Pilot5bMeta1020Forward.pointLabels N C x) y).getD r false)
      (forkJob N C fa fb w)) :
    ∃ j, (C.wires (x ++ y)).getD (fa j) false = true ∧
      (C.wires (x ++ y)).getD (fb j) false = true := by
  obtain ⟨hwlt, hwfork, _⟩ := (mem_usedForks N C fa fb w).mp hw
  have hspec := fork_spec N C w hwfork
  have hc := PEqualNP.Outside.L_meta_1020.OriginalGraph.fork_children N C w _ _ hspec
  rcases hf with ⟨ha, hb, hk⟩
  change (run (net N C fa fb) _ y).getD (fmap N C (forkLeft N C w)) false = true at ha
  change (run (net N C fa fb) _ y).getD (fmap N C (forkRight N C w)) false = true at hb
  change (run (net N C fa fb) _ y).getD (context N C fa fb w) false = true at hk
  rw [old_read N C fa fb _ y hy, mapped_positive N C hm x y hx hy _ (Nat.le_trans (Nat.le_of_eq hc.2.2.2.1) (by omega))] at ha
  rw [old_read N C fa fb _ y hy, mapped_positive N C hm x y hx hy _ (Nat.le_trans (Nat.le_of_eq hc.2.2.2.2) (by omega))] at hb
  have hwfull := PEqualNP.Outside.L_meta_1020.OriginalGraph.fork_full
    N C hm x y hx hy w _ _ hspec ha hb
  obtain ⟨e, he, hseed, hpath⟩ :=
    (context_reachable N C fa fb _ y hy w hwlt).mp hk
  obtain ⟨j, rfl⟩ := (mem_seeds N C fa fb e).mp he
  have hfull := PEqualNP.Outside.L_meta_1020.OriginalGraph.path_up
    N C hm x y hx hy (fa j) w hpath hwfull
  refine ⟨j, hfull, ?_⟩
  exact Pilot5bMeta1020Forward.normalize_sound N C hm x y hx hy (fb j)
    (Nat.le_trans (hdb j) (by omega)) hseed

lemma jobs_sound {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hda : ∀ j, ODegree N C (fa j) ≤ 2) (hdb : ∀ j, ODegree N C (fb j) ≤ 1)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (t : Triple) (ht : t ∈ jobs N C fa fb)
    (hf : Fires (fun r => (run (net N C fa fb)
      (Pilot5bMeta1020Forward.pointLabels N C x) y).getD r false) t) :
    ∃ j, (C.wires (x ++ y)).getD (fa j) false = true ∧
      (C.wires (x ++ y)).getD (fb j) false = true := by
  rcases (mem_jobs N C fa fb t).mp ht with ⟨j, rfl⟩ | ⟨w, hw, rfl⟩
  · exact ⟨j, bulk_sound N C fa fb hm hda hdb x y hx hy j hf⟩
  · exact fork_sound N C fa fb hm hdb x y hx hy w hw hf

lemma jobs_cover {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hda : ∀ j, ODegree N C (fa j) ≤ 2) (hdb : ∀ j, ODegree N C (fb j) ≤ 1)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N) (j : Fin J)
    (ha : (C.wires (x ++ y)).getD (fa j) false = true)
    (hb : (C.wires (x ++ y)).getD (fb j) false = true)
    (hza : (C.wires (x ++ List.replicate N false)).getD (fa j) false = false)
    (hzb : (C.wires (x ++ List.replicate N false)).getD (fb j) false = false) :
    ∃ t ∈ jobs N C fa fb, Fires (fun r => (run (net N C fa fb)
      (Pilot5bMeta1020Forward.pointLabels N C x) y).getD r false) t := by
  have hpb := Pilot5bMeta1020Forward.normalize_complete_degree_one
    N C hm x y hx hy (fb j) (hdb j) hb hzb
  have hpb' : (run (net N C fa fb) (Pilot5bMeta1020Forward.pointLabels N C x) y).getD
      (fmap N C (fb j)) false = true := by
    rw [old_read N C fa fb _ y hy]
    exact hpb
  by_cases hpa : (run (fnet N C) (Pilot5bMeta1020Forward.pointLabels N C x) y).getD
      (fmap N C (fa j)) false = true
  · refine ⟨bulkJob N C fa fb j, (mem_jobs N C fa fb _).mpr (Or.inl ⟨j, rfl⟩), ?_⟩
    refine ⟨?_, hpb', hpb'⟩
    change (run (net N C fa fb) _ y).getD (fmap N C (fa j)) false = true
    rw [old_read N C fa fb _ y hy]
    exact hpa
  · have hpa0 : (run (fnet N C) (Pilot5bMeta1020Forward.pointLabels N C x) y).getD
        (fmap N C (fa j)) false = false := Bool.eq_false_iff.mpr hpa
    have hda2 : ODegree N C (fa j) = 2 := by
      by_contra hn
      have hle : ODegree N C (fa j) ≤ 1 := by have := hda j; omega
      exact hpa (Pilot5bMeta1020Forward.normalize_complete_degree_one
        N C hm x y hx hy (fa j) hle ha hza)
    have hpzero : (PEqualNP.Outside.L_meta_1020.OriginalGraph.positiveValues C x y).getD
        (fa j) false = false := by
      rw [← mapped_positive N C hm x y hx hy (fa j) (hda j)]
      exact hpa0
    obtain ⟨w, a, b, hpath, hf, hpa, hpb⟩ :=
      PEqualNP.Outside.L_meta_1020.OriginalGraph.fork_descent N C hm x y hx hy (fa j)
        ⟨hda2, ha, hza, hpzero⟩
    have hc := PEqualNP.Outside.L_meta_1020.OriginalGraph.fork_children N C w a b hf
    have hr : Pilot5bMeta1020Weighted.seedReachable (OEdges N C)
        (Pilot5bMeta1020Reverse.weightValue (Pilot5bMeta1020Forward.pointLabels N C x) (OWeight N C))
        (seeds N C fa fb)
        (fun r => (run (fnet N C) (Pilot5bMeta1020Forward.pointLabels N C x) y).getD r false) w :=
      ⟨(fa j, fmap N C (fb j)), (mem_seeds N C fa fb _).mpr ⟨j, rfl⟩,
        Pilot5bMeta1020Forward.normalize_complete_degree_one N C hm x y hx hy (fb j) (hdb j) hb hzb,
        hpath⟩
    have hw : w ∈ usedForks N C fa fb := (mem_usedForks N C fa fb w).mpr
      ⟨hc.2.2.1, ⟨a, b, hf⟩, reachable_incoming_positive _ _ _ _ w hr⟩
    refine ⟨forkJob N C fa fb w,
      (mem_jobs N C fa fb _).mpr (Or.inr ⟨w, hw, rfl⟩), ?_⟩
    refine ⟨?_, ?_, (context_reachable N C fa fb _ y hy w hc.2.2.1).mpr hr⟩
    · change (run (net N C fa fb) _ y).getD (fmap N C (forkLeft N C w)) false = true
      rw [fork_left_eq N C w a b hf, old_read N C fa fb _ y hy,
        mapped_positive N C hm x y hx hy a (Nat.le_trans (Nat.le_of_eq hc.2.2.2.1) (by omega))]
      exact hpa
    · change (run (net N C fa fb) _ y).getD (fmap N C (forkRight N C w)) false = true
      rw [fork_right_eq N C w a b hf, old_read N C fa fb _ y hy,
        mapped_positive N C hm x y hx hy b (Nat.le_trans (Nat.le_of_eq hc.2.2.2.2) (by omega))]
      exact hpb

end Pilot5bMeta1020OriginalNormalization

namespace Pilot5bMeta1020OriginalNormalization

open PEqualNP.CircuitLowerBounds Pilot5bMeta1020Linear

def tripleRoots (t : Triple) : Fin 3 → ℕ := ![t.1, t.2.1, t.2.2]

noncomputable def roots {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (j : Fin (jobs N C fa fb).length) : Fin 3 → ℕ :=
  tripleRoots (jobs N C fa fb)[j]

lemma tripleRoots_fires (t : Triple) (read : ℕ → Bool) :
    (∀ i, read (tripleRoots t i) = true) ↔ Fires read t := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨ha, hb, hc⟩ i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc

lemma roots_fires {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (j : Fin (jobs N C fa fb).length) (read : ℕ → Bool) :
    (∀ i, read (roots N C fa fb j i) = true) ↔ Fires read (jobs N C fa fb)[j] :=
  tripleRoots_fires _ _

lemma exists_roots_iff {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (read : ℕ → Bool) :
    (∃ j, ∀ i, read (roots N C fa fb j i) = true) ↔
      ∃ t ∈ jobs N C fa fb, Fires read t := by
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨(jobs N C fa fb)[j], List.get_mem _ j, (roots_fires N C fa fb j read).mp hj⟩
  · rintro ⟨t, ht, hf⟩
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp ht
    refine ⟨⟨j, hj⟩, (roots_fires N C fa fb ⟨j, hj⟩ read).mpr ?_⟩
    change Fires read (jobs N C fa fb)[j]
    rw [hget]
    exact hf

lemma roots_sound {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hda : ∀ j, ODegree N C (fa j) ≤ 2) (hdb : ∀ j, ODegree N C (fb j) ≤ 1)
    (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (j : Fin (jobs N C fa fb).length)
    (hf : ∀ i, (run (net N C fa fb) (Pilot5bMeta1020Forward.pointLabels N C x) y).getD
      (roots N C fa fb j i) false = true) :
    ∃ k, (C.wires (x ++ y)).getD (fa k) false = true ∧
      (C.wires (x ++ y)).getD (fb k) false = true :=
  jobs_sound N C fa fb hm hda hdb x y hx hy _ (List.get_mem _ j)
    ((roots_fires N C fa fb j _).mp hf)

lemma roots_sound_functions {J : ℕ} (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : Circuit) (fa fb : Fin J → ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hda : ∀ j, ODegree N C (fa j) ≤ 2) (hdb : ∀ j, ODegree N C (fb j) ≤ 1)
    (hsound : ∀ j (z : Fin (N + N) → Bool),
      (C.wires (List.ofFn z)).getD (fa j) false = true →
      (C.wires (List.ofFn z)).getD (fb j) false = true →
      ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (x y : Fin N → Bool) (j : Fin (jobs N C fa fb).length)
    (hf : ∀ i, (run (net N C fa fb)
      (Pilot5bMeta1020Forward.pointLabels N C (List.ofFn x)) (List.ofFn y)).getD
      (roots N C fa fb j i) false = true) :
    ∃ p l, I p l ∧ x p = true ∧ y l = true := by
  obtain ⟨k, ha, hb⟩ := roots_sound N C fa fb hm hda hdb
    (List.ofFn x) (List.ofFn y) (by simp) (by simp) j hf
  rw [← List.ofFn_fin_append] at ha hb
  obtain ⟨p, l, hi, hp, hl⟩ := hsound k (Fin.append x y) ha hb
  exact ⟨p, l, hi, by simpa only [Fin.append_left] using hp,
    by simpa only [Fin.append_right] using hl⟩

lemma roots_cover_pair {J : ℕ} (N : ℕ) (C : Circuit) (fa fb : Fin J → ℕ)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hda : ∀ j, ODegree N C (fa j) ≤ 2) (hdb : ∀ j, ODegree N C (fb j) ≤ 1)
    (p l : Fin N) (j : Fin J)
    (ha : (C.wires (List.ofFn (Pilot5bMeta1020Forward.pairInput p l))).getD (fa j) false = true)
    (hb : (C.wires (List.ofFn (Pilot5bMeta1020Forward.pairInput p l))).getD (fb j) false = true)
    (hza : (C.wires (List.ofFn (Pilot5bMeta1020Forward.pointInput p))).getD (fa j) false = false)
    (hzb : (C.wires (List.ofFn (Pilot5bMeta1020Forward.pointInput p))).getD (fb j) false = false) :
    ∃ k, ∀ i, (run (net N C fa fb)
      (Pilot5bMeta1020Forward.pointLabels N C (List.ofFn (fun q => decide (q = p))))
      (List.ofFn (fun u => decide (u = l)))).getD (roots N C fa fb k i) false = true := by
  apply (exists_roots_iff N C fa fb (fun r =>
    (run (net N C fa fb)
      (Pilot5bMeta1020Forward.pointLabels N C (List.ofFn (fun q => decide (q = p))))
      (List.ofFn (fun u => decide (u = l)))).getD r false)).mpr
  rw [Pilot5bMeta1020Forward.pairInput_list] at ha hb
  rw [Pilot5bMeta1020Forward.pointInput_list] at hza hzb
  exact jobs_cover N C fa fb hm hda hdb _ _ (by simp) (by simp) j ha hb hza hzb

end Pilot5bMeta1020OriginalNormalization
