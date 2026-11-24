import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2870_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def prodF {n : ℕ} (A B : Finset (Finset (Fin n))) : Finset (Finset (Fin n)) :=
  A.biUnion (fun u => B.image (u ∪ ·))

private def holdsF {n : ℕ} (xs : List Bool) (A : Finset (Finset (Fin n))) : Prop :=
  ∃ t ∈ A, ∀ i ∈ t, xs.getD i.val false = true

private lemma holds_union {n : ℕ} (xs : List Bool) (A B : Finset (Finset (Fin n))) :
    holdsF xs (A ∪ B) ↔ holdsF xs A ∨ holdsF xs B := by
  simp only [holdsF, Finset.mem_union]
  aesop

private lemma holds_prod {n : ℕ} (xs : List Bool) (A B : Finset (Finset (Fin n))) :
    holdsF xs (prodF A B) ↔ holdsF xs A ∧ holdsF xs B := by
  constructor
  · rintro ⟨t, ht, hx⟩
    obtain ⟨u, hu, ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨⟨u, hu, fun i hi => hx i (Finset.mem_union_left _ hi)⟩,
      ⟨v, hv, fun i hi => hx i (Finset.mem_union_right _ hi)⟩⟩
  · rintro ⟨⟨u, hu, hx⟩, ⟨v, hv, hy⟩⟩
    refine ⟨u ∪ v, Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩, ?_⟩
    intro i hi
    exact (Finset.mem_union.mp hi).elim (hx i) (hy i)

private def stepF {n : ℕ} (F : List (Finset (Finset (Fin n)))) (g : Gate) :=
  F ++ [if g.op.eval [false,true] then
    F.getD (g.inputs.getD 0 0) ∅ ∪ F.getD (g.inputs.getD 1 0) ∅ else
    prodF (F.getD (g.inputs.getD 0 0) ∅) (F.getD (g.inputs.getD 1 0) ∅)]

private def stepB (xs : List Bool) (g : Gate) :=
  xs ++ [g.op.eval (g.inputs.map (xs.getD · false))]

private lemma foldF_length {n : ℕ} (gs : List Gate) (F : List (Finset (Finset (Fin n)))) :
    (gs.foldl stepF F).length = F.length + gs.length := by
  induction gs generalizing F with
  | nil => simp
  | cons g gs ih => simp [List.foldl, ih, stepF, Nat.add_assoc]; omega

private lemma foldF_prefix {n : ℕ} (gs : List Gate) (F : List (Finset (Finset (Fin n))))
    (w : ℕ) (hw : w < F.length) :
    (gs.foldl stepF F).getD w ∅ = F.getD w ∅ := by
  induction gs generalizing F with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [stepF]; omega)]
    simp [stepF, List.getD, List.getElem?_append_left hw]

private lemma step_semantics {n : ℕ} (xs : List Bool) (F : List (Finset (Finset (Fin n))))
    (bs : List Bool) (g : Gate) (hlen : bs.length = F.length)
    (hs : ∀ w, bs.getD w false = true ↔ holdsF xs (F.getD w ∅))
    (hop : g.op = .and ∨ g.op = .or) (hbin : ∃ a b, g.inputs = [a,b]) :
    ∀ w, (stepB bs g).getD w false = true ↔ holdsF xs ((stepF F g).getD w ∅) := by
  obtain ⟨a,b,hin⟩ := hbin
  intro w
  by_cases hw : w < F.length
  · have hb : w < bs.length := by omega
    simp only [stepB, stepF, List.getD, List.getElem?_append_left hw,
      List.getElem?_append_left hb]
    exact hs w
  by_cases he : w = F.length
  · subst w
    have hB : (stepB bs g).getD F.length false =
        g.op.eval (g.inputs.map (bs.getD · false)) := by
      rw [← hlen]
      simp [stepB, List.getD]
    have hF : (stepF F g).getD F.length ∅ =
        if g.op.eval [false,true] then
          F.getD (g.inputs.getD 0 0) ∅ ∪ F.getD (g.inputs.getD 1 0) ∅ else
          prodF (F.getD (g.inputs.getD 0 0) ∅) (F.getD (g.inputs.getD 1 0) ∅) := by
      simp [stepF, List.getD]
    rw [hB, hF]
    rcases hop with hop | hop
    · simpa [hin, hop, GateOp.eval, holds_prod] using and_congr (hs a) (hs b)
    · simpa [hin, hop, GateOp.eval, holds_union] using or_congr (hs a) (hs b)
  · have hb : (stepB bs g).length ≤ w := by simp [stepB]; omega
    have hf : (stepF F g).length ≤ w := by simp [stepF]; omega
    simp [List.getD, List.getElem?_eq_none hb, List.getElem?_eq_none hf, holdsF]

private lemma fold_semantics {n : ℕ} (xs : List Bool) (gs : List Gate)
    (F : List (Finset (Finset (Fin n)))) (bs : List Bool) (hlen : bs.length = F.length)
    (hs : ∀ w, bs.getD w false = true ↔ holdsF xs (F.getD w ∅))
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b]) :
    ∀ w, (gs.foldl stepB bs).getD w false = true ↔ holdsF xs ((gs.foldl stepF F).getD w ∅) := by
  induction gs generalizing F bs with
  | nil => exact hs
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    · simp [stepB, stepF, hlen]
    · exact step_semantics xs F bs g hlen hs (legal g (by simp)).1 (legal g (by simp)).2
    · intro k hk
      exact legal k (by simp [hk])

private lemma foldF_gate {n : ℕ} (gs : List Gate) (F : List (Finset (Finset (Fin n))))
    (j : ℕ) (hj : j < gs.length) (a b : ℕ) (hin : gs[j].inputs = [a,b])
    (ha : a < F.length+j) (hb : b < F.length+j) :
    (gs.foldl stepF F).getD (F.length+j) ∅ =
      if gs[j].op.eval [false,true] then
        (gs.foldl stepF F).getD a ∅ ∪ (gs.foldl stepF F).getD b ∅ else
        prodF ((gs.foldl stepF F).getD a ∅) ((gs.foldl stepF F).getD b ∅) := by
  let earlier := (gs.take j).foldl stepF F
  have plen : earlier.length = F.length+j := by
    simp [earlier, foldF_length, Nat.min_eq_left hj.le]
  have split : gs.foldl stepF F = (gs[j] :: gs.drop (j+1)).foldl stepF earlier := by
    conv_lhs => rw [← List.take_append_drop j gs]
    rw [List.foldl_append, List.drop_eq_getElem_cons hj]
  have read (w : ℕ) (hw : w < F.length+j) :
      earlier.getD w ∅ = (gs.foldl stepF F).getD w ∅ := by
    rw [split]
    exact (foldF_prefix _ earlier w (by simpa only [plen] using hw)).symm
  rw (occs := [1]) [split]
  rw (occs := [1]) [List.foldl_cons]
  rw [foldF_prefix _ _ _ (by simp [stepF, plen])]
  have self : (stepF earlier gs[j]).getD (F.length+j) ∅ =
      if gs[j].op.eval [false,true] then earlier.getD a ∅ ∪ earlier.getD b ∅ else
      prodF (earlier.getD a ∅) (earlier.getD b ∅) := by
    rw [← plen]
    simp [stepF, hin, List.getD]
  rw [self, read a ha, read b hb]

lemma dnf_compiler (n : ℕ) (C : Circuit) (mono : Monotone2 C)
    (order : ∀ j g, C.gates[j]? = some g → ∃ a b, g.inputs=[a,b] ∧ a<b ∧ b<n+j) :
    ∃ F : ℕ → Finset (Finset (Fin n)),
      (∀ i : Fin n, F i={{i}}) ∧
      (∀ j (hj:j<C.size), ∃ a b, C.gates[j].inputs=[a,b] ∧ a<b ∧ b<n+j ∧
        F (n+j) = (if C.gates[j].op.eval [false,true] then F a ∪ F b else
          (F a).biUnion (fun u => (F b).image (u ∪ ·)))) ∧
      (∀ xs : List Bool, xs.length=n → ∀ w,
        (C.wires xs).getD w false=true ↔ ∃ t∈F w, ∀ i∈t, xs.getD i.val false=true) := by
  let init : List (Finset (Finset (Fin n))) := List.ofFn fun i : Fin n => {{i}}
  let F (w : ℕ) := (C.gates.foldl stepF init).getD w ∅
  have ilen : init.length = n := by simp [init]
  refine ⟨F, ?_, ?_, ?_⟩
  · intro i
    change (C.gates.foldl stepF init).getD i.val ∅ = {{i}}
    rw [foldF_prefix _ _ _ (by simpa only [ilen] using i.isLt)]
    simp [init, List.getD]
  · intro j hj
    have hj' : j < C.gates.length := hj
    obtain ⟨a,b,hin,hab,hb⟩ := order j C.gates[j] (List.getElem?_eq_getElem hj')
    refine ⟨a,b,hin,hab,hb,?_⟩
    have h := foldF_gate C.gates init j hj' a b hin (by rw [ilen]; omega)
      (by simpa only [ilen] using hb)
    change F (init.length+j) = (if C.gates[j].op.eval [false,true] then
      F a ∪ F b else prodF (F a) (F b)) at h
    rw [ilen] at h
    exact h
  · intro xs hx w
    have base : ∀ w, xs.getD w false = true ↔ holdsF xs (init.getD w ∅) := by
      intro w
      by_cases hw : w < n
      · simp [init, List.getD, hw, holdsF]
      · have hxs : xs.length ≤ w := by omega
        have hi : init.length ≤ w := by omega
        rw [List.getD_eq_default _ _ hxs, List.getD_eq_default _ _ hi]
        simp [holdsF]
    have legal : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ ∃ a b, g.inputs = [a,b] := by
      intro g hg
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
      obtain ⟨a,b,hin,_,_⟩ := order j C.gates[j] (List.getElem?_eq_getElem hj)
      exact ⟨(mono _ (List.getElem_mem hj)).1, a, b, hin⟩
    exact fold_semantics xs C.gates init xs (hx.trans ilen.symm) base legal w

end PEqualNP.Outside.L_meta_2870_aux
