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
