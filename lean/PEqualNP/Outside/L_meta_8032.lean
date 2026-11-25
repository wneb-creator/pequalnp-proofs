import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8032
open CircuitLowerBounds MetaComplexity EdgeOwnership

abbrev edges : List (Fin 11 × Fin 11) :=
  [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
   (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

abbrev negatives : List ℕ :=
  [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]

lemma wire_mono (C : Circuit) (hm : Monotone2 C) (x y : List Bool)
    (hl : x.length = y.length) (hxy : ∀ k, x.getD k false = true → y.getD k false = true) :
    ∀ k, (C.wires x).getD k false = true → (C.wires y).getD k false = true := by
  have snoc (w : List Bool) (v : Bool) (k : ℕ) : (w ++ [v]).getD k false =
      if k = w.length then v else w.getD k false := by
    rcases lt_trichotomy k w.length with h | h | h
    · rw [ite_eq_right (by omega),List.getD_append _ _ _ _ h]
    · subst k; simp [List.getD_eq_getElem?_getD]
    · rw [ite_eq_right (by omega)]
      rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simp; omega),
        List.getElem?_eq_none (by omega)]
  obtain ⟨gs,out⟩ := C
  unfold Circuit.wires
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    · simp [hl]
    · intro k hk
      simp only [snoc,hl] at hk ⊢
      split_ifs at hk ⊢ with h
      · have hgate : g.op = .and ∨ g.op = .or := (hm g (List.mem_cons_self ..)).1
        rcases hgate with h | h
        · simp only [h,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at hk ⊢
          exact fun i hi => hxy i (hk i hi)
        · simp only [h,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] at hk ⊢
          obtain ⟨i,hi,hv⟩ := hk; exact ⟨i,hi,hxy i hv⟩
      · exact hxy k hk
    · exact fun g' hg' => hm g' (List.mem_cons_of_mem _ hg')


lemma up (C : Circuit) (hm : Monotone2 C) {x y : Fin 11 → Bool}
    (h : ∀ i, x i = true → y i = true) : circuitFun 11 C x = true → circuitFun 11 C y = true := by
  apply wire_mono C hm (List.ofFn x) (List.ofFn y) (by simp) _ C.output
  intro k hk
  by_cases hlt : k < 11
  · rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at hk ⊢
    simp only [List.getElem_ofFn] at hk ⊢
    exact h ⟨k,hlt⟩ hk
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hlt)] at hk; cases hk

-- Every independent support is contained in one of the listed negative masks.
set_option maxHeartbeats 4000000 in
lemma covered : ∀ x : Fin 11 → Bool,
    edges.any (fun e => x e.1 && x e.2) = false →
    ∃ m ∈ negatives, ∀ i, x i = true → m.testBit i.val = true := by decide +kernel

lemma exactTests_compute : ∀ C : Circuit, Monotone2 C →
    (∀ e ∈ edges, C.eval (List.ofFn (pairInput e.1 e.2)) = true) →
    (∀ m ∈ negatives, C.eval (List.ofFn fun i : Fin 11 => m.testBit i.val) = false) →
    circuitFun 11 C = fun x => edges.any fun e => x e.1 && x e.2 := by
  intro C hm positive negative; funext x
  cases hv : edges.any (fun e => x e.1 && x e.2) with
  | false =>
    obtain ⟨m,hm',hsub⟩ := covered x hv
    apply Bool.eq_false_iff.mpr; intro hx
    have ht := up C hm hsub hx
    exact Bool.noConfusion ((negative m hm').symm.trans ht)
  | true =>
    obtain ⟨e,he,hbit⟩ := List.any_eq_true.mp hv
    simp only [Bool.and_eq_true] at hbit
    apply up C hm _ (positive e he)
    intro i hi; rw [pairInput,decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact hbit.1
    · exact hbit.2

end PEqualNP.Outside.L_meta_8032
