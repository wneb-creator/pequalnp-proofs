import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux.Compression

variable {α : Type}

def meet (a b : α → Bool) : α → Bool := fun x => a x && b x

def join (a b : α → Bool) : α → Bool := fun x => a x || b x

def Step (p : List (α → Bool)) (w : α → Bool) : Prop :=
  ∃ a ∈ p, ∃ b ∈ p, w = meet a b ∨ w = join a b

def Trace (p gs : List (α → Bool)) : Prop :=
  List.rec (motive := fun _ => List (α → Bool) → Prop) (fun _ => True)
    (fun w _ rec q => Step q w ∧ rec (q ++ [w])) gs p

lemma step_mono {p q : List (α → Bool)} {w : α → Bool}
    (hpq : p ⊆ q) (hw : Step p w) : Step q w := by
  obtain ⟨a, ha, b, hb, hab⟩ := hw
  exact ⟨a, hpq ha, b, hpq hb, hab⟩

lemma compress_indexed {p q gs : List (α → Bool)}
    (ht : Trace p gs) (hpq : p ⊆ q) (mark : Fin gs.length → Bool)
    (hd : ∀ j : Fin gs.length, mark j = true → gs.get j ∈ q ++ gs.take j.val) :
    ∃ hs, Trace q hs ∧ p ++ gs ⊆ q ++ hs ∧
      hs.length + (∑ j : Fin gs.length, if mark j then 1 else 0) = gs.length := by
  induction gs generalizing p q with
  | nil =>
      refine ⟨[], trivial, ?_, ?_⟩
      · simpa using hpq
      · simp
  | cons w gs ih =>
      let tailMark : Fin gs.length → Bool := fun j => mark j.succ
      have hsum : (∑ j : Fin (w :: gs).length, if mark j then 1 else 0) =
          (if mark 0 then 1 else 0) + ∑ j : Fin gs.length, if tailMark j then 1 else 0 := by
        exact Fin.sum_univ_succ _
      by_cases hm : mark 0 = true
      · have hwq : w ∈ q := by simpa using hd 0 hm
        have hbase : p ++ [w] ⊆ q := by
          intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact hpq ha
          · simpa only [List.mem_singleton.mp ha] using hwq
        have hdelete : ∀ j : Fin gs.length, tailMark j = true →
            gs.get j ∈ q ++ gs.take j.val := by
          intro j hj
          have hjmem : gs.get j ∈ q ++ w :: gs.take j.val := by
            simpa using hd j.succ hj
          rcases List.mem_append.mp hjmem with hq | hg
          · exact List.mem_append_left _ hq
          · rcases List.mem_cons.mp hg with heq | htail
            · exact List.mem_append_left _ (heq ▸ hwq)
            · exact List.mem_append_right _ htail
        obtain ⟨hs, htrace, hcover, hlen⟩ := ih ht.2 hbase tailMark hdelete
        refine ⟨hs, htrace, ?_, ?_⟩
        · simpa [List.append_assoc] using hcover
        · rw [hsum, hm]
          simp only [↓reduceIte, List.length_cons]
          omega
      · have hmfalse : mark 0 = false := Bool.eq_false_iff.mpr hm
        have hbase : p ++ [w] ⊆ q ++ [w] := by
          intro a ha
          rcases List.mem_append.mp ha with ha | ha
          · exact List.mem_append_left _ (hpq ha)
          · exact List.mem_append_right _ ha
        have hdelete : ∀ j : Fin gs.length, tailMark j = true →
            gs.get j ∈ (q ++ [w]) ++ gs.take j.val := by
          intro j hj
          simpa [List.append_assoc] using hd j.succ hj
        obtain ⟨hs, htrace, hcover, hlen⟩ := ih ht.2 hbase tailMark hdelete
        refine ⟨w :: hs, ⟨step_mono hpq ht.1, htrace⟩, ?_, ?_⟩
        · simpa [List.append_assoc] using hcover
        · rw [hsum, hmfalse]
          simp only [Bool.false_eq_true, ↓reduceIte, zero_add, List.length_cons]
          omega

lemma compress_marked {p q gs : List (α → Bool)}
    (ht : Trace p gs) (hpq : p ⊆ q) (marked : Finset (Fin gs.length))
    (hd : ∀ j ∈ marked, gs.get j ∈ q ++ gs.take j.val) :
    ∃ hs, Trace q hs ∧ p ++ gs ⊆ q ++ hs ∧
      hs.length + marked.card = gs.length := by
  classical
  obtain ⟨hs, htrace, hcover, hlen⟩ :=
    compress_indexed ht hpq (fun j => decide (j ∈ marked))
      (fun j hj => hd j (of_decide_eq_true hj))
  refine ⟨hs, htrace, hcover, ?_⟩
  simpa using hlen

lemma compress_free {p freeBase gs : List (α → Bool)}
    (ht : Trace p gs) (marked : Finset (Fin gs.length))
    (hd : ∀ j ∈ marked, gs.get j ∈ (p ++ freeBase) ++ gs.take j.val) :
    ∃ hs, Trace (p ++ freeBase) hs ∧ p ++ gs ⊆ (p ++ freeBase) ++ hs ∧
      hs.length + marked.card = gs.length := by
  exact compress_marked ht (fun _ h => List.mem_append_left _ h) marked hd

lemma compress_free_output {p freeBase gs : List (α → Bool)}
    (ht : Trace p gs) (marked : Finset (Fin gs.length))
    (hd : ∀ j ∈ marked, gs.get j ∈ (p ++ freeBase) ++ gs.take j.val)
    (f : α → Bool) (hf : f ∈ p ++ gs) :
    ∃ hs, Trace (p ++ freeBase) hs ∧ f ∈ (p ++ freeBase) ++ hs ∧
      hs.length + marked.card = gs.length := by
  obtain ⟨hs, htrace, hcover, hlen⟩ := compress_free ht marked hd
  exact ⟨hs, htrace, hcover hf, hlen⟩

lemma compress_two_families {p freeBase gs : List (α → Bool)}
    (ht : Trace p gs) (freeMarks bypassMarks : Finset (Fin gs.length))
    (hdisjoint : Disjoint freeMarks bypassMarks)
    (hfree : ∀ j ∈ freeMarks, gs.get j ∈ p ++ freeBase)
    (hbypass : ∀ j ∈ bypassMarks, gs.get j ∈ p ++ gs.take j.val) :
    ∃ hs, Trace (p ++ freeBase) hs ∧ p ++ gs ⊆ (p ++ freeBase) ++ hs ∧
      hs.length + freeMarks.card + bypassMarks.card = gs.length := by
  classical
  have hd : ∀ j ∈ freeMarks ∪ bypassMarks,
      gs.get j ∈ (p ++ freeBase) ++ gs.take j.val := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact List.mem_append_left _ (hfree j hj)
    · rcases List.mem_append.mp (hbypass j hj) with hp | hg
      · exact List.mem_append_left _ (List.mem_append_left _ hp)
      · exact List.mem_append_right _ hg
  obtain ⟨hs, htrace, hcover, hlen⟩ := compress_free ht (freeMarks ∪ bypassMarks) hd
  refine ⟨hs, htrace, hcover, ?_⟩
  simpa [Finset.card_union_of_disjoint hdisjoint, Nat.add_assoc] using hlen

lemma lower_bound_after_compression {p freeBase gs : List (α → Bool)}
    (ht : Trace p gs) (marked : Finset (Fin gs.length))
    (hd : ∀ j ∈ marked, gs.get j ∈ (p ++ freeBase) ++ gs.take j.val)
    (f : α → Bool) (hf : f ∈ p ++ gs) (lower : ℕ)
    (hlower : ∀ hs, Trace (p ++ freeBase) hs → f ∈ (p ++ freeBase) ++ hs →
      lower ≤ hs.length) :
    lower + marked.card ≤ gs.length := by
  obtain ⟨hs, htrace, hout, hlen⟩ := compress_free_output ht marked hd f hf
  have := hlower hs htrace hout
  omega

end PEqualNP.Outside.L_meta_2590_aux.Compression
