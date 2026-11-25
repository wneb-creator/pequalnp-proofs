import OneForcedBank

namespace PEqualNP.Outside.L_meta_2373.Live1024.OneForcedBank
open PEqualNP.CircuitLowerBounds

lemma live_entries_proper {u T k S} (run : Live u T k S) : ∀ a ∈ S, proper a := by
  induction run using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩

lemma pull_gate_keep {u T} {w : List Sig} {z keep : Sig} {k S c}
    (run : Live u T k S)
    (rep : represented w z ∨ (c = 1 ∧ witness u w z))
    (sub : ∀ a ∈ S, a ∈ w ++ [z]) (kept : keep ∈ S) (different : z ≠ keep) :
    ∃ k' S', k' ≤ k + c ∧ Live u T k' S' ∧ (∀ a ∈ S', a ∈ w) ∧ keep ∈ S' := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, S, by omega, run, ?_, kept⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_entries_proper run z hm
      rcases rep with hr | ⟨rfl, d, a, b, hd, ha, hb, pa, pb, hab, eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u T k (insert (bin d a b) U) := by
          simpa [U, Finset.insert_erase hm] using run
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hmem
        have fresh : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | hh
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp hh with eq | hh
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ hh)
        refine ⟨_, _, Nat.le_refl _, Live.binary hd pa pb hab fresh ht, ?_, ?_⟩
        · simpa using And.intro ha (And.intro hb hu)
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨Ne.symm different, kept⟩))
  · refine ⟨k, S, by omega, run, ?_, kept⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

lemma pull_positive_chunk_keep (gs : List Gate) (w free : List Sig) {keep target : Sig}
    {k : Nat} {S : Finset Sig}
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (mono : ∀ g ∈ gs, isNot g = false)
    (safe : ∀ pre post g, gs = pre ++ g :: post → gv (execute pre w) g ≠ keep)
    (run : Live false target k S) (sub : ∀ a ∈ S, a ∈ execute gs w ++ free)
    (kept : keep ∈ S) :
    ∃ k' S', k' ≤ k + gs.length ∧ Live false target k' S' ∧
      (∀ a ∈ S', a ∈ w ++ free) ∧ keep ∈ S' := by
  induction gs generalizing w with
  | nil => exact ⟨k, S, by simp, run, sub, kept⟩
  | cons g gs ih =>
    have safeTail : ∀ pre post q, gs = pre ++ q :: post →
        gv (execute pre (w ++ [gv w g])) q ≠ keep := by
      intro pre post q eq
      exact safe (g :: pre) post q (by simp only [List.cons_append, eq])
    obtain ⟨l, U, bound, trace, subset, hk⟩ := ih (w ++ [gv w g])
      (fun q hq => legal q (by simp [hq])) (fun q hq => mono q (by simp [hq]))
      safeTail sub
    have sub' : ∀ a ∈ U, a ∈ (w ++ free) ++ [gv w g] := by
      intro a ha
      have h := subset a ha
      simpa only [List.mem_append, List.mem_singleton, or_assoc, or_left_comm, or_comm] using h
    obtain ⟨l', U', hb, hr, hs, kept'⟩ := pull_gate_keep trace
      (FreeBank.gate_rep_free w free g (legal g (by simp)) (mono g (by simp))) sub' hk
      (safe [] gs g rfl)
    exact ⟨l', U', by simp only [List.length_cons]; omega, hr, hs, kept'⟩

end PEqualNP.Outside.L_meta_2373.Live1024.OneForcedBank
