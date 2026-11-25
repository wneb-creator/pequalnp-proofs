import PetersenSeventeenFull

namespace PEqualNP.Outside.L_meta_2373.Live1024

def copyIndex {n : Nat} : Sum (Fin n) Bool → Fin (n + 2)
  | Sum.inl i => ⟨i.val, by omega⟩
  | Sum.inr false => ⟨n, by omega⟩
  | Sum.inr true => ⟨n + 1, by omega⟩

theorem copyIndex_injective {n : Nat} :
    Function.Injective (@copyIndex n) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have he := congrArg (fun q : Fin (n + 2) => q.val) h
      change a.val = b.val at he
      exact congrArg Sum.inl (Fin.ext he)
    | inr b =>
      have ha := a.isLt
      have he := congrArg Fin.val h
      cases b <;> simp only [copyIndex] at he <;> omega
  | inr a =>
    cases b with
    | inl b =>
      have hb := b.isLt
      have he := congrArg Fin.val h
      cases a <;> simp only [copyIndex] at he <;> omega
    | inr b =>
      cases a <;> cases b
      · rfl
      · have he := congrArg Fin.val h
        simp only [copyIndex] at he
        omega
      · have he := congrArg Fin.val h
        simp only [copyIndex] at he
        omega
      · rfl

theorem runCut_of_image {α β : Type} [DecidableEq α] [DecidableEq β]
    (roots : Finset α) (nextRoots : Finset β) (raw : α → Sig) (nextRaw : β → Sig)
    (f : α → β) (injective : Function.Injective f)
    (same : ∀ r, nextRaw (f r) = raw r) (image : roots.image f = nextRoots)
    (u : Bool) (T : Sig) (depth : Nat)
    (blocked : ∀ k, k + 1 ≤ nextRoots.card + depth →
      ¬ Run u (observe T) k (nextRoots.toList.map (fun r => observe (nextRaw r)))) :
    ∀ k, k + 1 ≤ roots.card + depth →
      ¬ Run u (observe T) k (roots.toList.map (fun r => observe (raw r))) := by
  have perm : (roots.toList.map f).Perm nextRoots.toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq
      ((Finset.nodup_toList roots).map injective) (Finset.nodup_toList nextRoots)
    rw [← image]
    ext r
    simp
  have count : roots.card = nextRoots.card := by
    simpa only [List.length_map, Finset.length_toList] using perm.length_eq
  intro k bound run
  have mapped : Run u (observe T) k
      ((roots.toList.map f).map (fun r => observe (nextRaw r))) := by
    simpa only [List.map_map, Function.comp_def, same] using run
  exact blocked k (by omega) (Run.perm (perm.map (fun r => observe (nextRaw r))) mapped)

end PEqualNP.Outside.L_meta_2373.Live1024
