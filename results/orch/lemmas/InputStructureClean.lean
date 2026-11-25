import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_2592_aux.InputSlots

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

open Classical

-- NOT ignores all but its first input; these are precisely the effective slots.
noncomputable def effective (g : Gate) : List ℕ :=
  if g.op = GateOp.not then g.inputs.take 1 else g.inputs

noncomputable def slots (C : Circuit) : List ℕ := C.gates.flatMap effective

noncomputable def normGate (g : Gate) : Gate := ⟨g.op, effective g⟩

noncomputable def normalize (C : Circuit) : Circuit := ⟨C.gates.map normGate, C.output⟩

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp only [normGate, effective]
  all_goals first | rfl | (cases ins <;> simp [GateOp.eval])

lemma normalize_eval (C : Circuit) (x : List Bool) :
    (normalize C).eval x = C.eval x := by
  have h : ∀ (gs : List Gate) (w : List Bool),
      (gs.map normGate).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w := by
    intro gs
    induction gs with
    | nil => intro w; rfl
    | cons g gs ih =>
      intro w
      simp only [List.map_cons, List.foldl_cons, normGate_eval]
      exact ih _
  exact congrArg (fun w => w.getD C.output false) (h C.gates x)

lemma normalize_size (C : Circuit) : (normalize C).size = C.size := by
  simp [normalize, Circuit.size]

lemma normalize_notCount (C : Circuit) :
    NotBracket.notCount (normalize C) = NotBracket.notCount C := by
  simp only [NotBracket.notCount, normalize, List.filter_map, List.length_map]
  rfl

lemma effective_length (g : Gate) (hlen : g.inputs.length ≤ 2) :
    (effective g).length + (if g.op = GateOp.not then 1 else 0) ≤ 2 := by
  by_cases hn : g.op = GateOp.not
  · simp [effective, hn]
  · simpa [effective, hn] using hlen

lemma slots_bound (C : Circuit) (fan : FanInTwo C) :
    (slots C).length + NotBracket.notCount C ≤ 2 * C.size := by
  letI : DecidableEq GateOp := lineDegreeGateOpDecEq
  have h : ∀ (gs : List Gate), (∀ g ∈ gs, g.inputs.length ≤ 2) →
      (gs.flatMap effective).length + (gs.filter fun g => decide (g.op = GateOp.not)).length ≤
        2 * gs.length := by
    intro gs
    induction gs with
    | nil => intro _; simp
    | cons g gs ih =>
      intro hg
      have hh := effective_length g (hg g (by simp))
      have ht := ih (fun q hq => hg q (List.mem_cons_of_mem _ hq))
      simp only [List.flatMap_cons, List.length_append, List.filter_cons, List.length_cons]
      split_ifs <;> simp_all only [decide_eq_true_eq, ite_true, ite_false, List.length_cons] <;> omega
  exact h C.gates (fun g hg => (fan g hg).2)

lemma count_sum_le (xs : List ℕ) (S : Finset ℕ) :
    ∑ i ∈ S, xs.count i ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.count_cons, beq_iff_eq, Finset.sum_add_distrib, List.length_cons]
    have hi : (∑ i ∈ S, if a = i then 1 else 0) ≤ 1 := by
      simp only [Finset.sum_ite_eq]
      split_ifs <;> omega
    omega

lemma shifted_count_sum_le (xs : List ℕ) (n m : ℕ) :
    ∑ j ∈ Finset.range m, xs.count (n + j) ≤ xs.length := by
  have h := count_sum_le xs ((Finset.range m).image fun j => n + j)
  rw [Finset.sum_image] at h
  · exact h
  · intro a ha b hb hab
    exact Nat.add_left_cancel hab

lemma internal_count (xs : List ℕ) (n m out : ℕ)
    (live : ∀ j, j < m → n + j ≠ out → n + j ∈ xs) :
    m ≤ (∑ j ∈ Finset.range m, xs.count (n + j)) + 1 := by
  have hp : ∀ j ∈ Finset.range m,
      1 ≤ xs.count (n + j) + ([out] : List ℕ).count (n + j) := by
    intro j hj
    by_cases he : n + j = out
    · simp [he]
    · have hh := List.count_pos_iff.mpr (live j (Finset.mem_range.mp hj) he)
      omega
  have hsum := Finset.sum_le_sum hp
  have hout := shifted_count_sum_le [out] n m
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
    Finset.sum_add_distrib, List.length_singleton] at hsum hout
  omega

-- Every essential input is read. If at most one gate output may be unread,
-- a circuit with fewer than 2n - 1 + t gates has an input used exactly once.
lemma input_once (C : Circuit) (n : ℕ) (fan : FanInTwo C)
    (essential : ∀ i, i < n → i ∈ slots C)
    (live : ∀ j, j < C.size → n + j ≠ C.output → n + j ∈ slots C)
    (budget : C.size + 1 < 2 * n + NotBracket.notCount C) :
    ∃ i, i < n ∧ (slots C).count i = 1 := by
  by_contra hn
  push Not at hn
  have hraw : 2 * n ≤ ∑ i ∈ Finset.range n, (slots C).count i := by
    have h := Finset.sum_le_sum (fun i hi => show 2 ≤ (slots C).count i from by
      have hp := List.count_pos_iff.mpr (essential i (Finset.mem_range.mp hi))
      have hne := hn i (Finset.mem_range.mp hi)
      omega)
    simpa [Nat.mul_comm] using h
  have hint := internal_count (slots C) n C.size C.output live
  have htotal := count_sum_le (slots C) (Finset.range (n + C.size))
  rw [Finset.sum_range_add] at htotal
  have hb := slots_bound C fan
  omega

lemma petersen_input_once (C : Circuit) (fan : FanInTwo C)
    (essential : ∀ i, i < 10 → i ∈ slots C)
    (live : ∀ j, j < C.size → 10 + j ≠ C.output → 10 + j ∈ slots C)
    (budget : C.size ≤ 19) (hasNot : 1 ≤ NotBracket.notCount C) :
    ∃ i, i < 10 ∧ (slots C).count i = 1 := by
  apply input_once C 10 fan essential live
  omega

lemma unique_reader (gs : List Gate) (i : ℕ)
    (once : (gs.flatMap effective).count i = 1) :
    ∃ q, q < gs.length ∧ i ∈ effective (gs.getD q ⟨GateOp.or, []⟩) ∧
      ∀ t, t < gs.length → t ≠ q → i ∉ effective (gs.getD t ⟨GateOp.or, []⟩) := by
  induction gs with
  | nil => simp at once
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.count_append] at once
    by_cases hg : i ∈ effective g
    · have hp := List.count_pos_iff.mpr hg
      have hz : (gs.flatMap effective).count i = 0 := by omega
      have hno := List.count_eq_zero.mp hz
      refine ⟨0, by simp, by simpa using hg, ?_⟩
      intro t ht hne hi
      cases t with
      | zero => exact hne rfl
      | succ t =>
        have htl : t < gs.length := by simpa using ht
        apply hno
        apply List.mem_flatMap.mpr
        refine ⟨gs.getD t ⟨GateOp.or, []⟩, ?_, ?_⟩
        · rw [List.getD_eq_getElem _ _ htl]
          exact List.getElem_mem _
        · simpa using hi
    · have hz := List.count_eq_zero_of_not_mem hg
      have ho : (gs.flatMap effective).count i = 1 := by omega
      obtain ⟨q, hq, hr, hu⟩ := ih ho
      refine ⟨q + 1, by simpa using hq, by simpa using hr, ?_⟩
      intro t ht hne
      cases t with
      | zero => simpa using hg
      | succ t =>
        apply hu t (by simpa using ht) (by omega)

lemma petersen_unique_reader (C : Circuit) (fan : FanInTwo C)
    (essential : ∀ i, i < 10 → i ∈ slots C)
    (live : ∀ j, j < C.size → 10 + j ≠ C.output → 10 + j ∈ slots C)
    (budget : C.size ≤ 19) (hasNot : 1 ≤ NotBracket.notCount C) :
    ∃ (i : Fin 10) (q : ℕ), q < C.gates.length ∧
      i.val ∈ effective (C.gates.getD q ⟨GateOp.or, []⟩) ∧
      ∀ t, t < C.gates.length → t ≠ q →
        i.val ∉ effective (C.gates.getD t ⟨GateOp.or, []⟩) := by
  obtain ⟨i, hi, hone⟩ := petersen_input_once C fan essential live budget hasNot
  obtain ⟨q, hq, hr, hu⟩ := unique_reader C.gates i hone
  exact ⟨⟨i, hi⟩, q, hq, hr, hu⟩

end PEqualNP.Outside.L_meta_2592_aux.InputSlots

namespace PEqualNP.Outside.L_meta_2592_aux.Prune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Classical

def shift (k i : ℕ) : ℕ := if i < k then i else i - 1

def shiftGate (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift k)⟩

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [_])).length = w.length + (g :: gs).length
    rw [ih]
    simp
    omega

lemma getD_snoc (l : List Bool) (b : Bool) (k : ℕ) :
    (l ++ [b]).getD k false =
      if k < l.length then l.getD k false else if k = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none]
    · rfl
    · simp
      omega

def Related (k : ℕ) (u v : List Bool) : Prop :=
  u.length + 1 = v.length ∧ k < v.length ∧
    ∀ i, i ≠ k → u.getD (shift k i) false = v.getD i false

lemma related_start (u : List Bool) (b : Bool) : Related u.length u (u ++ [b]) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i hi
  rw [getD_snoc]
  by_cases h : i < u.length
  · simp [shift, h]
  · have he : u.length ≤ shift u.length i := by simp [shift, h]; omega
    rw [List.getD_eq_default _ _ he]
    simp [h, hi]

lemma related_snoc {k : ℕ} {u v : List Bool} (h : Related k u v) (b : Bool) :
    Related k (u ++ [b]) (v ++ [b]) := by
  rcases h with ⟨hl, hk, hr⟩
  refine ⟨by simp; omega, by simp; omega, ?_⟩
  intro i hi
  rw [getD_snoc, getD_snoc]
  have he : shift k i < u.length ↔ i < v.length := by unfold shift; split_ifs <;> omega
  have heq : shift k i = u.length ↔ i = v.length := by unfold shift; split_ifs <;> omega
  simp only [he, heq]
  split_ifs with h1 h2
  · exact hr i hi
  · rfl
  · rfl

lemma run_related (gs : List Gate) (k : ℕ)
    (noRead : ∀ g ∈ gs, k ∉ g.inputs) {u v : List Bool} (hr : Related k u v) :
    Related k (run (gs.map (shiftGate k)) u) (run gs v) := by
  induction gs generalizing u v with
  | nil => exact hr
  | cons g gs ih =>
    have hv : (shiftGate k g).op.eval ((shiftGate k g).inputs.map fun i => u.getD i false) =
        g.op.eval (g.inputs.map fun i => v.getD i false) := by
      congr 1
      simp only [shiftGate, List.map_map]
      apply List.map_congr_left
      intro i hi
      exact hr.2.2 i (fun e => noRead g (by simp) (e ▸ hi))
    change Related k
      (run (gs.map (shiftGate k)) (u ++ [(shiftGate k g).op.eval ((shiftGate k g).inputs.map fun i => u.getD i false)]))
      (run gs (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]))
    rw [hv]
    exact ih (fun q hq => noRead q (List.mem_cons_of_mem _ hq)) (related_snoc hr _)

def drop (n : ℕ) (pre post : List Gate) (out : ℕ) : Circuit :=
  ⟨pre ++ post.map (shiftGate (n + pre.length)), shift (n + pre.length) out⟩

lemma drop_eval (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (out : ℕ)
    (noRead : ∀ q ∈ post, n + pre.length ∉ q.inputs) (notOut : out ≠ n + pre.length)
    (x : List Bool) (hlen : x.length = n) :
    (drop n pre post out).eval x = (⟨pre ++ g :: post, out⟩ : Circuit).eval x := by
  let w := run pre x
  let b := g.op.eval (g.inputs.map fun i => w.getD i false)
  have hw : w.length = n + pre.length := by simpa [w, hlen] using run_length pre x
  have hr := related_start w b
  rw [hw] at hr
  have hf := run_related post (n + pre.length) noRead hr
  simpa only [Circuit.eval, Circuit.wires, drop, run, List.foldl_append, List.foldl_cons, w, b]
    using hf.2.2 out notOut

lemma drop_fan (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (out : ℕ)
    (fan : FanInTwo (⟨pre ++ g :: post, out⟩ : Circuit)) :
    FanInTwo (drop n pre post out) := by
  intro q hq
  rcases List.mem_append.mp hq with hp | hs
  · exact fan q (List.mem_append_left _ hp)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hop, hlen⟩ := fan r (List.mem_append_right _ (List.mem_cons_of_mem _ hr))
    exact ⟨hop, by simpa [shiftGate] using hlen⟩

lemma drop_size (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ) :
    (drop n pre post out).size + 1 = (⟨pre ++ g :: post, out⟩ : Circuit).size := by
  simp [drop, Circuit.size]
  omega

lemma drop_notCount (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ) :
    NotBracket.notCount (drop n pre post out) + (if g.op = GateOp.not then 1 else 0) =
      NotBracket.notCount (⟨pre ++ g :: post, out⟩ : Circuit) := by
  letI : DecidableEq GateOp := lineDegreeGateOpDecEq
  simp only [NotBracket.notCount, drop, List.filter_append, List.filter_map, List.length_append,
    List.length_map]
  have he : (fun q => decide (q.op = GateOp.not)) ∘ shiftGate (n + pre.length) =
      (fun q => decide (q.op = GateOp.not)) := rfl
  rw [he]
  by_cases hg : g.op = GateOp.not <;> simp [hg] <;> omega

def weight (C : Circuit) : ℕ := C.size + if NotBracket.notCount C = 0 then 1 else 0

lemma drop_weight (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ) :
    weight (drop n pre post out) ≤ weight (⟨pre ++ g :: post, out⟩ : Circuit) := by
  have hs := drop_size n pre post g out
  have hn := drop_notCount n pre post g out
  unfold weight
  split_ifs at * <;> omega

end PEqualNP.Outside.L_meta_2592_aux.Prune

namespace PEqualNP.Outside.L_meta_2592_aux.WeightedLive

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open InputSlots Prune
open Classical

def Normal (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1

lemma effective_eq (C : Circuit) (h : Normal C) (g : Gate) (hg : g ∈ C.gates) :
    effective g = g.inputs := by
  by_cases hn : g.op = GateOp.not
  · simpa [effective, hn] using List.take_of_length_le (h g hg hn)
  · simp [effective, hn]

lemma normalize_normal (C : Circuit) : Normal (normalize C) := by
  intro g hg hn
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  change q.op = GateOp.not at hn
  simp [normGate, effective, hn]

lemma normalize_fan (C : Circuit) (h : FanInTwo C) : FanInTwo (normalize C) := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  obtain ⟨hop, hlen⟩ := h q hq
  refine ⟨hop, ?_⟩
  change (effective q).length ≤ 2
  have := effective_length q hlen
  omega

lemma normalize_weight (C : Circuit) : weight (normalize C) = weight C := by
  simp only [weight, normalize_size, normalize_notCount]

lemma drop_normal (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ)
    (hn : Normal (⟨pre ++ g :: post, out⟩ : Circuit)) : Normal (Prune.drop n pre post out) := by
  intro q hq hop
  rcases List.mem_append.mp hq with hpre | hpost
  · exact hn q (List.mem_append_left _ hpre) hop
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hpost
    have := hn r (List.mem_append_right _ (List.mem_cons_of_mem _ hr)) hop
    simpa [shiftGate] using this

lemma split_at (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ pre g post, gs = pre ++ g :: post ∧ pre.length = j := by
  induction gs generalizing j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => exact ⟨[], g, gs, rfl, rfl⟩
    | succ j =>
      obtain ⟨pre, q, post, he, hl⟩ := ih j (by simpa using hj)
      exact ⟨g :: pre, q, post, by simp [he], by simp [hl]⟩

-- Keeping the extra unit for a NOT-free circuit makes deleting the sole NOT safe.
lemma exists_live (n : ℕ) (C : Circuit) (fan : FanInTwo C) :
    ∃ D : Circuit, FanInTwo D ∧ Normal D ∧ weight D ≤ weight C ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      (∀ j, j < D.size → n + j ≠ D.output → n + j ∈ slots D) := by
  classical
  let P := fun s => ∃ D : Circuit, D.size = s ∧ FanInTwo D ∧ Normal D ∧
      weight D ≤ weight C ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)
  have hex : ∃ s, P s := by
    refine ⟨(normalize C).size, normalize C, rfl, normalize_fan C fan, normalize_normal C, ?_, ?_⟩
    · exact le_of_eq (normalize_weight C)
    · exact fun x => normalize_eval C (List.ofFn x)
  obtain ⟨D, hsize, hfan, hnorm, hweight, heval⟩ := Nat.find_spec hex
  refine ⟨D, hfan, hnorm, hweight, heval, ?_⟩
  intro j hj ho
  by_contra hdead
  obtain ⟨pre, g, post, hsplit, hlen⟩ := split_at D.gates j hj
  have hD : D = ⟨pre ++ g :: post, D.output⟩ := by cases D; simp_all
  have hno : ∀ q ∈ post, n + pre.length ∉ q.inputs := by
    intro q hq hm
    have hqD : q ∈ D.gates := by rw [hsplit]; simp [hq]
    apply hdead
    apply List.mem_flatMap.mpr
    refine ⟨q, hqD, ?_⟩
    rw [effective_eq D hnorm q hqD]
    simpa [hlen] using hm
  let E := Prune.drop n pre post D.output
  have hEfan : FanInTwo E := drop_fan n pre g post D.output (hD ▸ hfan)
  have hEnorm : Normal E := drop_normal n pre post g D.output (hD ▸ hnorm)
  have hEweight : weight E ≤ weight C := by
    have h := drop_weight n pre post g D.output
    rw [← hD] at h
    exact h.trans hweight
  have hEeval : ∀ x : Fin n → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro x
    have h := drop_eval n pre g post D.output hno (by omega) (List.ofFn x) (by simp)
    rw [← hD] at h
    exact h.trans (heval x)
  have hmin : Nat.find hex ≤ E.size := Nat.find_min' hex
    ⟨E, rfl, hEfan, hEnorm, hEweight, hEeval⟩
  have hs := drop_size n pre post g D.output
  rw [← hD] at hs
  change E.size + 1 = D.size at hs
  omega

end PEqualNP.Outside.L_meta_2592_aux.WeightedLive

namespace PEqualNP.Outside.L_meta_2592_aux.WeightedPetersen

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open InputSlots Prune WeightedLive

lemma run_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (Prune.run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (Prune.run gs (w ++ [_])).getD i false = w.getD i false
    rw [ih _ (by simp; omega), getD_snoc]
    simp [hi]

lemma run_agree (gs : List Gate) (i : ℕ) (noRead : ∀ g ∈ gs, i ∉ g.inputs)
    (u v : List Bool) (hlen : u.length = v.length) (hi : i < u.length)
    (same : ∀ k, k ≠ i → u.getD k false = v.getD k false) :
    ∀ k, k ≠ i → (Prune.run gs u).getD k false = (Prune.run gs v).getD k false := by
  induction gs generalizing u v with
  | nil => exact same
  | cons g gs ih =>
    have hg : g.op.eval (g.inputs.map fun k => u.getD k false) =
        g.op.eval (g.inputs.map fun k => v.getD k false) := by
      congr 1
      apply List.map_congr_left
      intro k hk
      exact same k (fun he => noRead g (by simp) (he ▸ hk))
    apply ih (fun q hq => noRead q (List.mem_cons_of_mem _ hq))
      (u ++ [_]) (v ++ [_]) (by simp [hlen]) (by simp; omega)
    intro k hk
    rw [getD_snoc, getD_snoc, hlen]
    split_ifs <;> first | exact same k hk | exact hg | rfl

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (k : ℕ) :
    (List.ofFn x).getD k false = if h : k < n then x ⟨k, h⟩ else false := by
  by_cases h : k < n
  · simp [List.getD_eq_getElem (List.ofFn x) false (by simpa using h), h]
  · simp [List.getD_eq_default (List.ofFn x) false (by simpa using Nat.le_of_not_gt h), h]

def petersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def neighbor (i : Fin 10) : Fin 10 :=
  ([1, 0, 1, 2, 0, 0, 1, 2, 3, 4] : List (Fin 10)).getD i.val 0

def low (i : Fin 10) : Fin 10 → Bool := fun j => decide (j = neighbor i)
def high (i : Fin 10) : Fin 10 → Bool := fun j => decide (j = i ∨ j = neighbor i)

lemma witness : ∀ i : Fin 10,
    petersen (low i) = false ∧ petersen (high i) = true ∧
    ∀ j, j ≠ i → low i j = high i j := by decide +kernel

lemma singleton_false : ∀ i : Fin 10,
    petersen (fun j => decide (j = i)) = false := by decide +kernel

lemma output_not_input (C : Circuit)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) (i : Fin 10) :
    C.output ≠ i.val := by
  intro he
  have h := correct (fun j => decide (j = i))
  change (Prune.run C.gates (List.ofFn fun j => decide (j = i))).getD C.output false = _ at h
  rw [he, run_input _ _ i.val (by simp), ofFn_getD, singleton_false] at h
  simp at h

lemma essential (C : Circuit) (hnorm : Normal C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) :
    ∀ i, i < 10 → i ∈ slots C := by
  intro i hi
  by_contra hnot
  have hno : ∀ g ∈ C.gates, i ∉ g.inputs := by
    intro g hg hm
    apply hnot
    apply List.mem_flatMap.mpr
    refine ⟨g, hg, ?_⟩
    rwa [effective_eq C hnorm g hg]
  let a : Fin 10 := ⟨i, hi⟩
  have he := run_agree C.gates i hno (List.ofFn (low a)) (List.ofFn (high a))
    (by simp) (by simp [hi]) (by
      intro k hk
      rw [ofFn_getD, ofFn_getD]
      split_ifs with h
      · exact (witness a).2.2 ⟨k, h⟩ (fun e => hk (congrArg Fin.val e))
      · rfl) C.output (output_not_input C correct a)
  change C.eval (List.ofFn (low a)) = C.eval (List.ofFn (high a)) at he
  rw [correct, correct, (witness a).1, (witness a).2.1] at he
  contradiction

lemma normalized_unique_reader (C : Circuit) (fan : FanInTwo C)
    (budget : C.size ≤ 19) (hasNot : 1 ≤ NotBracket.notCount C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) :
    ∃ (D : Circuit) (i : Fin 10) (q : ℕ), FanInTwo D ∧ Normal D ∧ weight D ≤ 19 ∧
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = petersen x) ∧
      q < D.gates.length ∧ i.val ∈ (D.gates.getD q ⟨GateOp.or, []⟩).inputs ∧
      ∀ t, t < D.gates.length → t ≠ q → i.val ∉ (D.gates.getD t ⟨GateOp.or, []⟩).inputs := by
  obtain ⟨D, hfan, hnorm, hweight, heval, hlive⟩ := exists_live 10 C fan
  have hCweight : weight C ≤ 19 := by unfold weight; simp [show NotBracket.notCount C ≠ 0 by omega]; omega
  have hw : weight D ≤ 19 := hweight.trans hCweight
  have hc : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = petersen x := fun x => (heval x).trans (correct x)
  have hb : D.size + 1 < 2 * 10 + NotBracket.notCount D := by
    unfold weight at hw
    split_ifs at hw <;> omega
  obtain ⟨i, hi, hone⟩ := input_once D 10 hfan (essential D hnorm hc) hlive hb
  obtain ⟨q, hq, hread, hother⟩ := unique_reader D.gates i hone
  have get_mem : ∀ t, t < D.gates.length → D.gates.getD t ⟨GateOp.or, []⟩ ∈ D.gates := by
    intro t ht
    rw [List.getD_eq_getElem _ _ ht]
    exact List.getElem_mem ht
  refine ⟨D, ⟨i, hi⟩, q, hfan, hnorm, hw, hc, hq, ?_, ?_⟩
  · rwa [effective_eq D hnorm _ (get_mem q hq)] at hread
  · intro t ht hne
    have h := hother t ht hne
    rwa [effective_eq D hnorm _ (get_mem t ht)] at h

end PEqualNP.Outside.L_meta_2592_aux.WeightedPetersen
