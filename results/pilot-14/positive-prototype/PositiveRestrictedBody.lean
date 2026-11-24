namespace PEqualNP.Outside.L_meta_670_aux.PositiveBase
open Base1007
lemma good_neg {a : Sig} (h : good a) : good (neg a) := by
  rcases h with ⟨hp, hn⟩
  constructor <;> simp only [neg, BitVec.getLsbD_not, hp, hn]
lemma good_bin {a b : Sig} (ha : good a) (hb : good b) (d : Bool) : good (bin d a b) := by
  rcases ha with ⟨hp, hn⟩
  rcases hb with ⟨hq, hm⟩
  cases d <;> constructor <;> simp only [bin, Bool.false_eq_true, ↓reduceIte,
    BitVec.getLsbD_and, BitVec.getLsbD_or, hp, hn, hq, hm]
lemma no_special {a : Sig} (h : good a) : a ∉ special := by
  have hc : special.all (fun a => decide (¬ good a)) = true := by decide +kernel
  intro ha
  exact (of_decide_eq_true (List.all_eq_true.mp hc a ha)) h
lemma inputs_good : ∀ a ∈ inputs, good a := by decide +kernel
lemma restrict {m t S} (h : Live m t S) :
    (∀ a ∈ S, good a) → Restricted m t S := by
  induction h with
  | stop => intro hs; exact Restricted.stop
  | @unary k t U a ha hf tail ih =>
    intro hs
    have hga := hs a (Finset.mem_insert_self _ _)
    refine Restricted.unary ha hf (no_special hga) (ih ?_)
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact good_neg hga
    · exact hs z (Finset.mem_insert_of_mem hz)
  | @binary k t U a b d ha hb hab hf tail ih =>
    intro hs
    have hga := hs a (Finset.mem_insert_self _ _)
    have hgb := hs b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    refine Restricted.binary ha hb hab hf (fun h => False.elim (no_special hga h))
      (fun h => False.elim (no_special hgb h)) (ih ?_)
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact good_bin hga hgb d
    · exact hs z (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hz))
end PEqualNP.Outside.L_meta_670_aux.PositiveBase
