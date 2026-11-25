import OneNotAnywhere

namespace PEqualNP.Outside.L_meta_2373.Live1024.OneNotForcedPair
open LiftSeventeen OneNotFirstAnd
open PEqualNP.CircuitLowerBounds

def forcesPair (h : Sig) (a b : Fin 10) : Prop :=
  ∀ r : Row, bit r h = true → bit r (input a) = true ∧ bit r (input b) = true

def bank (h : Sig) : Finset Sig := insert h (insert (neg h) inputs.toFinset)

lemma false_of_pair (h : Sig) (a b : Fin 10) (forces : forcesPair h a b) (r : Row)
    (off : bit r (input a) = false ∨ bit r (input b) = false) : bit r h = false := by
  cases he : bit r h
  · rfl
  · have pair := forces r he
    rcases off with ha | hb
    · rw [ha] at pair
      cases pair.1
    · rw [hb] at pair
      cases pair.2

lemma retained_left (h : Sig) (a b : Fin 10) (ab : a ≠ b) (forces : forcesPair h a b)
    {S : Finset Sig} {k : Nat} (sub : S ⊆ bank h) (run : Live false graph k S) : input a ∈ S := by
  by_contra missing
  obtain ⟨r, s, same, rb, sb, different⟩ := conditional_influence_rows a b ab false
  have hr := false_of_pair h a b forces r (Or.inr rb)
  have hs := false_of_pair h a b forces s (Or.inr sb)
  obtain ⟨w, hw, diff⟩ := live_row_difference run different
  have mem := sub hw
  rcases Finset.mem_insert.mp mem with rfl | mem
  · exact diff (hr.trans hs.symm)
  rcases Finset.mem_insert.mp mem with rfl | mem
  · apply diff
    rw [neg_bit, neg_bit, hr, hs]
  · obtain ⟨i, rfl⟩ := input_index w (List.mem_toFinset.mp mem)
    exact diff (same i (by rintro rfl; exact missing hw))

lemma value_zero (h : Sig) (a b : Fin 10) (forces : forcesPair h a b) :
    projected (rowMap a) h = (fun _ => false) := by
  funext r
  exact false_of_pair h a b forces (rowMap a r) (Or.inl (rowMap_missing a r))

lemma neg_value_one (h : Sig) (a b : Fin 10) (forces : forcesPair h a b) :
    projected (rowMap a) (neg h) = (fun _ => true) := by
  funext r
  change bit (rowMap a r) (neg h) = true
  rw [neg_bit, false_of_pair h a b forces (rowMap a r) (Or.inl (rowMap_missing a r))]
  rfl

lemma input_distinct (h : Sig) (a b : Fin 10) (ab : a ≠ b) (forces : forcesPair h a b) :
    input a ≠ h ∧ input a ≠ neg h := by
  constructor
  · intro eq
    have ha : bit (singleRow a) (input a) = true := by
      rw [singleRow_input]
      simp [PEqualNP.Outside.L_meta_2373.singleInput]
    have hb : bit (singleRow a) (input b) = false := by
      rw [singleRow_input]
      simp [PEqualNP.Outside.L_meta_2373.singleInput, Ne.symm ab]
    have hz := false_of_pair h a b forces (singleRow a) (Or.inr hb)
    rw [← eq, ha] at hz
    contradiction
  · intro eq
    have iz : bit (rowMap a 0) (input a) = false := rowMap_missing a 0
    have nt : bit (rowMap a 0) (neg h) = true := congrFun (neg_value_one h a b forces) 0
    have e := congrArg (bit (rowMap a 0)) eq
    have bad : false = true := iz.symm.trans (e.trans nt)
    cases bad

lemma bank_covered (h : Sig) (a b : Fin 10) (forces : forcesPair h a b)
    (w : Sig) (mem : w ∈ bank h) :
    Available false (NineSigned.inputs.map NineSigned.observe) (projected (rowMap a) w) := by
  rcases Finset.mem_insert.mp mem with eq | mem
  · rw [eq, value_zero h a b forces]
    exact Or.inr (Or.inl ⟨false, rfl⟩)
  rcases Finset.mem_insert.mp mem with rfl | mem
  · rw [neg_value_one h a b forces]
    exact Or.inr (Or.inl ⟨true, rfl⟩)
  · obtain ⟨i, rfl⟩ := input_index w (List.mem_toFinset.mp mem)
    exact ZeroProfiles.rows_available a i

lemma positive_tail_lower (h : Sig) (a b : Fin 10) (ab : a ≠ b) (forces : forcesPair h a b)
    {S : Finset Sig} {k : Nat} (sub : S ⊆ bank h) (run : Live false graph k S) : 18 ≤ k := by
  by_cases used : h ∈ S ∨ neg h ∈ S
  · have ha := retained_left h a b ab forces sub run
    have ca : Constant (projected (rowMap a) (input a)) := ⟨false, funext (rowMap_missing a)⟩
    apply projected_mono_lower_two (rowMap a) (funext (rowMap_graph a)) S k run
      (fun w hw => bank_covered h a b forces w (sub hw))
    rcases used with used | used
    · exact ⟨input a, ha, h, used, (input_distinct h a b ab forces).1,
        ca, ⟨false, value_zero h a b forces⟩⟩
    · exact ⟨input a, ha, neg h, used, (input_distinct h a b ab forces).2,
        ca, ⟨true, neg_value_one h a b forces⟩⟩
  have subset : ∀ w ∈ S, w ∈ inputs := by
    intro w hw
    have mem := sub hw
    rcases Finset.mem_insert.mp mem with eq | mem
    · exact False.elim (used (Or.inl (eq ▸ hw)))
    rcases Finset.mem_insert.mp mem with eq | mem
    · exact False.elim (used (Or.inr (eq ▸ hw)))
    · exact List.mem_toFinset.mp mem
  have eq : S = inputs.toFinset := by
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (subset w hw)
    · intro hw
      obtain ⟨i, rfl⟩ := input_index w (List.mem_toFinset.mp hw)
      apply raw_required run inputs (input i) subset (absentRow i) (presentRow i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j, rfl⟩ := input_index v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact monotone_rt_lower (eq ▸ run)

lemma stored_gate_value (pre mid : List Gate) (g : Gate) (h : Sig)
    (value : gv (execute pre inputs) g = h) :
    gv (execute mid (execute pre inputs ++ [gv (execute pre inputs) g]))
      {op := .not, inputs := [10 + pre.length]} = neg h := by
  obtain ⟨extra, he⟩ := execute_prefix mid (execute pre inputs ++ [gv (execute pre inputs) g])
  have len : (execute pre inputs).length = 10 + pre.length := execute_length pre inputs
  change neg ((execute mid (execute pre inputs ++ [gv (execute pre inputs) g])).getD
    (10 + pre.length) zero) = neg h
  rw [he, ← len, getD_append_slot, value]

lemma circuit_lower (h : Sig) (a b : Fin 10) (ab : a ≠ b) (forces : forcesPair h a b)
    (C : Circuit) (pre mid post : List Gate) (g : Gate)
    (gatesEq : C.gates = pre ++ [g] ++ mid ++
      [{op := .not, inputs := [10 + pre.length]}] ++ post)
    (value : gv (execute pre inputs) g = h)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (monoPre : ∀ q ∈ pre, isNot q = false)
    (monoMid : ∀ q ∈ mid, isNot q = false)
    (monoPost : ∀ q ∈ post, isNot q = false)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = edge) : 20 ≤ C.size := by
  let ng : Gate := {op := .not, inputs := [10 + pre.length]}
  let free := [h, neg h]
  let wp := execute pre inputs
  let wa := wp ++ [gv wp g]
  let wm := execute mid wa
  let wn := wm ++ [gv wm ng]
  have nv : gv wm ng = neg h := stored_gate_value pre mid g h value
  have whole : execute C.gates inputs = execute post wn := by
    rw [gatesEq]
    simp only [execute, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rfl
  have output : graph ∈ execute post wn := whole ▸ output_member C legal computes
  obtain ⟨k1, S1, bound1, run1, sub1⟩ := FreeBank.pull_positive_chunk post wn free
    (fun q hq => legal q (by rw [gatesEq]; simp [hq])) monoPost (Live.stop graph_proper)
    (by intro w hw; have he : w = graph := Finset.mem_singleton.mp hw
        subst w; exact List.mem_append_left free output)
  have knownN : gv wm ng ∈ free := by simp [free, nv]
  have subN := FreeBank.skip_free_gate wm free ng knownN sub1
  obtain ⟨k2, S2, bound2, run2, sub2⟩ := FreeBank.pull_positive_chunk mid wa free
    (fun q hq => legal q (by rw [gatesEq]; simp [hq])) monoMid run1 subN
  have knownG : gv wp g ∈ free := by simp [free, wp, value]
  have subG := FreeBank.skip_free_gate wp free g knownG sub2
  obtain ⟨k3, S3, bound3, run3, sub3⟩ := FreeBank.pull_positive_chunk pre inputs free
    (fun q hq => legal q (by rw [gatesEq]; simp [hq])) monoPre run2 subG
  have subset : S3 ⊆ bank h := by
    intro w hw
    have mem := sub3 w hw
    simpa [free, bank, List.mem_append, List.mem_cons, List.mem_singleton,
      or_assoc, or_left_comm, or_comm] using mem
  have lower := positive_tail_lower h a b ab forces subset run3
  have size : C.size = pre.length + mid.length + post.length + 2 := by
    simp [Circuit.size, gatesEq]
    omega
  omega

end PEqualNP.Outside.L_meta_2373.Live1024.OneNotForcedPair
