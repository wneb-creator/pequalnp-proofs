import InputSlots
import Prune

namespace PEqualNP.Outside.L_meta_2592_aux.WeightedLive

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open InputSlots Prune
local instance : DecidableEq GateOp := lineDegreeGateOpDecEq

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
