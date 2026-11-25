import FreeBankExtraction

namespace PEqualNP.Outside.L_meta_2373.Live1024.FreeSegments
open PEqualNP.CircuitLowerBounds

def weave : List (List Gate × Gate) → List Gate
  | [] => []
  | (gs, g) :: rest => gs ++ g :: weave rest

def charge : List (List Gate × Gate) → Nat
  | [] => 0
  | (gs, _) :: rest => gs.length + charge rest

def freeTrace (free : List Sig) : List (List Gate × Gate) → List Sig → Prop
  | [], _ => True
  | (gs, g) :: rest, w =>
      gv (execute gs w) g ∈ free ∧ freeTrace free rest (execute gs w ++ [gv (execute gs w) g])

lemma weave_length (segments : List (List Gate × Gate)) :
    (weave segments).length = charge segments + segments.length := by
  induction segments with
  | nil => rfl
  | cons seg rest ih =>
    rcases seg with ⟨gs, g⟩
    simp only [weave, charge, List.length_append, List.length_cons, ih]
    omega

lemma weave_execute (gs : List Gate) (g : Gate) (rest : List (List Gate × Gate)) (w : List Sig) :
    execute (weave ((gs, g) :: rest)) w =
      execute (weave rest) (execute gs w ++ [gv (execute gs w) g]) := by
  simp only [weave, execute, List.foldl_append, List.foldl_cons]

lemma pull_segments (segments : List (List Gate × Gate)) (w free : List Sig)
    {target : Sig} {k : Nat} {S : Finset Sig}
    (legal : ∀ seg ∈ segments, ∀ g ∈ seg.1,
      g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (mono : ∀ seg ∈ segments, ∀ g ∈ seg.1, isNot g = false)
    (known : freeTrace free segments w)
    (run : Live false target k S) (sub : ∀ a ∈ S, a ∈ execute (weave segments) w ++ free) :
    ∃ k' S', k' ≤ k + charge segments ∧ Live false target k' S' ∧ ∀ a ∈ S', a ∈ w ++ free := by
  induction segments generalizing w with
  | nil => exact ⟨k, S, by simp [charge], run, sub⟩
  | cons seg rest ih =>
    rcases seg with ⟨gs, g⟩
    rw [weave_execute] at sub
    obtain ⟨l, U, bound, trace, subset⟩ := ih _
      (fun q hq => legal q (List.mem_cons_of_mem _ hq))
      (fun q hq => mono q (List.mem_cons_of_mem _ hq)) known.2 sub
    have before := FreeBank.skip_free_gate (execute gs w) free g known.1 subset
    obtain ⟨m, V, count, tail, mem⟩ := FreeBank.pull_positive_chunk gs w free
      (legal (gs, g) List.mem_cons_self) (mono (gs, g) List.mem_cons_self) trace before
    exact ⟨m, V, by simp only [charge]; omega, tail, mem⟩

lemma member_weave {segments : List (List Gate × Gate)} {seg : List Gate × Gate}
    (mem : seg ∈ segments) {g : Gate} (hg : g ∈ seg.1) : g ∈ weave segments := by
  induction segments with
  | nil => simp at mem
  | cons top rest ih =>
    rcases List.mem_cons.mp mem with rfl | hm
    · exact List.mem_append_left _ hg
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (ih hm))

end PEqualNP.Outside.L_meta_2373.Live1024.FreeSegments
