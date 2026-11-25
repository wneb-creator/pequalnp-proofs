import NorReaders

namespace PEqualNP.Outside.L_meta_2592.AndConsumer
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open CleanReader NorCompression ReaderDeletion

lemma wf_length (gs : List Gate) (w : List Bool) :
    (wf gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (wf gs (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])).length = _
    rw [ih]
    simp
    omega

lemma wf_append (a b : List Gate) (w : List Bool) :
    wf (a ++ b) w = wf b (wf a w) := by
  exact List.foldl_append

lemma snoc_except (u : List Bool) (a b : Bool) :
    ∀ k, k ≠ u.length → (u ++ [a]).getD k false = (u ++ [b]).getD k false := by
  intro k hk
  rcases lt_trichotomy k u.length with h | h | h
  · rw [snoc_lt _ _ _ h,snoc_lt _ _ _ h]
  · exact False.elim (hk h)
  · rw [snoc_gt _ _ _ h,snoc_gt _ _ _ h]

lemma wf_agree_except (gs : List Gate) (n : Nat)
    (unused : ∀ g ∈ gs, n ∉ g.inputs)
    (u v : List Bool) (hlen : u.length = v.length)
    (rel : ∀ k, k ≠ n → u.getD k false = v.getD k false) :
    ∀ k, k ≠ n → (wf gs u).getD k false = (wf gs v).getD k false := by
  induction gs generalizing u v with
  | nil => exact rel
  | cons g gs ih =>
    have hv : g.op.eval (g.inputs.map fun k => u.getD k false) =
        g.op.eval (g.inputs.map fun k => v.getD k false) := by
      congr 1
      apply List.map_congr_left
      intro k hk
      exact rel k (by rintro rfl; exact unused g (by simp) hk)
    change ∀ k, k ≠ n →
      (wf gs (u ++ [g.op.eval (g.inputs.map fun k => u.getD k false)])).getD k false =
      (wf gs (v ++ [g.op.eval (g.inputs.map fun k => v.getD k false)])).getD k false
    apply ih (fun g hg => unused g (List.mem_cons_of_mem _ hg)) _ _ (by simp [hlen])
    intro k hk
    rcases lt_trichotomy k u.length with h | rfl | h
    · rw [snoc_lt _ _ _ h,snoc_lt _ _ _ (by omega)]
      exact rel k hk
    · rw [snoc_eq,hlen,snoc_eq]
      exact hv
    · rw [snoc_gt _ _ _ h,snoc_gt _ _ _ (by omega)]

def off (i : Fin 10) : Fin 10 → Bool := fun k =>
  if i.val < 2 then decide (k.val = 2 ∨ k.val = 3)
  else decide (k.val = 0 ∨ k.val = 1)

lemma off_facts : ∀ i : Fin 10, off i i = false ∧ pet (off i) = true := by decide

lemma and_false (g : Gate) (hop : g.op = .and) (i : Nat)
    (hi : i ∈ g.inputs) (u : List Bool) (hui : u.getD i false = false) :
    g.op.eval (g.inputs.map fun k => u.getD k false) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  rw [hop] at h
  simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_def,id_eq] at h
  have hbad := h i hi
  rw [hui] at hbad
  cases hbad

lemma output_not_reader (i j : Fin 10) (pre post : List Gate) (g : Gate) (out : Nat)
    (hc : ∀ x : Fin 10 → Bool,
      (old i j (pre ++ g :: post) out).eval (List.ofFn x) = p10 x)
    (hop : g.op = .and) (hi : i.val ∈ g.inputs) :
    out ≠ 13 + pre.length := by
  intro heq
  let x := off i
  let u := wf pre (seed i j x)
  have hlen : u.length = 13 + pre.length := by simp [u,wf_length,seed_length]
  have hui : u.getD i.val false = false := by
    rw [wf_initial pre (seed i j x) i.val (by rw [seed_length]; have := i.isLt;omega)]
    change (List.ofFn x ++ [!x i,!x j,!x i && !x j]).getD i.val false = false
    rw [read_low]
    exact (off_facts i).1
  have hg := and_false g hop i.val hi u hui
  have h := hc x
  rw [NorReaders.old_eval_seed,wf_append] at h
  change (wf post (u ++ [g.op.eval (g.inputs.map fun k => u.getD k false)])).getD out false = pet x at h
  rw [heq,← hlen,wf_initial post _ _ (by simp),snoc_eq,hg] at h
  have ht : pet x = true := (off_facts i).2
  rw [ht] at h
  cases h

lemma reader_has_consumer (i j : Fin 10) (hij : i ≠ j)
    (pre post : List Gate) (g : Gate) (out : Nat)
    (hf : FanInTwo (old i j (pre ++ g :: post) out))
    (hc : ∀ x : Fin 10 → Bool,
      (old i j (pre ++ g :: post) out).eval (List.ofFn x) = p10 x)
    (mono : ∀ h ∈ pre ++ g :: post, h.op = .and ∨ h.op = .or)
    (hop : g.op = .and) (hi : i.val ∈ g.inputs)
    (noIpre : ∀ h ∈ pre, i.val ∉ h.inputs)
    (noIpost : ∀ h ∈ post, i.val ∉ h.inputs) :
    out ≠ 13 + pre.length ∧ ∃ h ∈ post, 13 + pre.length ∈ h.inputs := by
  have hout := output_not_reader i j pre post g out hc hop hi
  refine ⟨hout,?_⟩
  by_contra hnone
  have unused : ∀ h ∈ post, 13 + pre.length ∉ h.inputs := by
    intro h hh hr
    exact hnone ⟨h,hh,hr⟩
  let z : Gate := ⟨.or,[]⟩
  have comp : ∀ x : Fin 10 → Bool,
      (wf (pre ++ z :: post) (seed i j x)).getD out false = pet x := by
    intro x
    have h := hc x
    rw [NorReaders.old_eval_seed,wf_append] at h
    rw [wf_append]
    let u := wf pre (seed i j x)
    change (wf post (u ++ [false])).getD out false = pet x
    change (wf post (u ++ [g.op.eval (g.inputs.map fun k => u.getD k false)])).getD out false = pet x at h
    rw [← h]
    apply wf_agree_except post (13 + pre.length) unused _ _ (by simp)
    · have hlen : u.length = 13 + pre.length := by simp [u,wf_length,seed_length]
      intro k hk
      exact snoc_except u false _ k (by simpa [hlen] using hk)
    · exact hout
  have hm : ∀ h ∈ pre ++ z :: post, h.op = .and ∨ h.op = .or := by
    intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact mono h (List.mem_append_left _ hh)
    · rcases List.mem_cons.mp hh with rfl | hh
      · exact Or.inr rfl
      · exact mono h (List.mem_append_right _ (List.mem_cons_of_mem _ hh))
  have hl : ∀ h ∈ pre ++ z :: post, h.inputs.length ≤ 2 := by
    intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact (hf h (by simp [old,hh])).2
    · rcases List.mem_cons.mp hh with rfl | hh
      · decide
      · exact (hf h (by simp [old,hh])).2
  obtain ⟨h,hh,hread,_⟩ := clean_reader i j hij false (pre ++ z :: post) out hm hl comp
  change i.val ∈ h.inputs at hread
  rcases List.mem_append.mp hh with hh | hh
  · exact noIpre h hh hread
  · rcases List.mem_cons.mp hh with rfl | hh
    · simp [z] at hread
    · exact noIpost h hh hread

end PEqualNP.Outside.L_meta_2592.AndConsumer
