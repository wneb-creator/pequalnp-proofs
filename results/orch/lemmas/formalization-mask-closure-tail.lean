namespace PEqualNP.Outside.L_meta_6659_aux

lemma support_mask_closed {n : ℕ} {D : Dag} (hS : Strict n D)
    (P : Finset (Fin n)) (Allowed Closed : Finset (Fin n) → Prop)
    (allowed : ∀ w, Allowed (supp n D w ∩ P))
    (empty : Closed ∅) (singletons : ∀ i : Fin n, i ∈ P → Closed {i})
    (unions : ∀ A B, Closed A → Closed B → Allowed (A ∪ B) → Closed (A ∪ B))
    (intersections : ∀ A B, Closed A → Closed B → Allowed (A ∩ B) → Closed (A ∩ B)) :
    ∀ w, Closed (supp n D w ∩ P) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases input : w < n
    · rw [supp_input D ⟨w,input⟩]
      by_cases member : (⟨w,input⟩ : Fin n) ∈ P
      · simpa [member] using singletons ⟨w,input⟩ member
      · simpa [member] using empty
    · by_cases valid : w < n+D.length
      · obtain ⟨j,rfl⟩ : ∃ j, w=n+j := ⟨w-n,by omega⟩
        have hj : j<D.length := by omega
        obtain ⟨ha,hb,_⟩ := hS j hj
        cases ht : tag D j with
        | false =>
          have mask : supp n D (n+j) ∩ P =
              (supp n D (opA D j) ∩ P) ∪ (supp n D (opB D j) ∩ P) := by
            rw [supp_gate hS j hj,ht]
            ext v
            simp only [Bool.false_eq_true,ite_false,Finset.mem_inter,Finset.mem_union]
            tauto
          rw [mask]
          exact unions _ _ (ih _ ha) (ih _ hb) (by rw [← mask]; exact allowed _)
        | true =>
          have mask : supp n D (n+j) ∩ P =
              (supp n D (opA D j) ∩ P) ∩ (supp n D (opB D j) ∩ P) := by
            rw [supp_gate hS j hj,ht]
            ext v
            simp only [ite_true,Finset.mem_inter]
            tauto
          rw [mask]
          exact intersections _ _ (ih _ ha) (ih _ hb) (by rw [← mask]; exact allowed _)
      · simpa only [supp_ge (n := n) D w (by omega),Finset.empty_inter] using empty

end PEqualNP.Outside.L_meta_6659_aux
