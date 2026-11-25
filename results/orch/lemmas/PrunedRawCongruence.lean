import PrunedInterface

namespace PEqualNP.Outside.L_meta_2373.Live1024

lemma budgetRunCut_raw_congr {α : Type} [DecidableEq α]
    (roots : Finset α) (f g : α → Sig) (u : Bool) (T : Sig) (depth : Nat)
    (same : ∀ r ∈ roots, f r = g r) (cut : BudgetRunCut roots f u T depth) :
    BudgetRunCut roots g u T depth := by
  have values : roots.toList.map (fun r => observe (f r)) =
      roots.toList.map (fun r => observe (g r)) := by
    apply List.map_congr_left
    intro r hr
    rw [same r (by simpa using hr)]
  intro n cap run
  rw [← values] at run
  exact cut n cap run

lemma duplicateRaw_agree {α : Type} [DecidableEq α]
    (roots A : Finset α) (f g : α → Sig) (v : Sig)
    (same : ∀ r ∈ roots, f r = g r) :
    ∀ r ∈ duplicateRoots roots A, duplicateRaw f v r = duplicateRaw g v r := by
  intro r hr
  cases r with
  | inl a =>
    have mem : a ∈ roots := by
      simp [duplicateRoots, liftLabels] at hr
      exact hr.1
    exact same a mem
  | inr b => rfl

lemma compressedRaw_agree {α : Type} [DecidableEq α]
    (roots A : Finset α) (f g : α → Sig) (v : Sig)
    (same : ∀ r ∈ roots, f r = g r) :
    ∀ r ∈ compressRoots roots A, duplicateRaw f v r = duplicateRaw g v r := by
  intro r hr
  cases r with
  | inl a =>
    have mem : a ∈ roots := by
      simp [compressRoots, liftLabels] at hr
      exact hr.1
    exact same a mem
  | inr b => rfl

lemma columnAdmissible_raw_congr {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (f g : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (A : Finset α) (v : Sig) (same : ∀ r ∈ roots, f r = g r)
    (adm : ColumnAdmissible roots f col need A v) :
    ColumnAdmissible roots g col need A v := by
  intro o ho outside
  apply adm o ho
  intro r hr hn
  rw [same r hr]
  exact outside r hr hn

lemma prunedGateClosed_raw_congr {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (f g : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig) (depth : Nat)
    (same : ∀ r ∈ roots, f r = g r)
    (closed : PrunedGateClosed roots f col need Cert u T depth) :
    PrunedGateClosed roots g col need Cert u T depth := by
  intro A B a b d dis legal distinct freshA freshB proper ca cb adm
  have old := columnAdmissible_raw_congr roots g f col need (A ∪ B) (bin d a b)
    (fun r hr => (same r hr).symm) adm
  rcases closed A B a b d dis legal distinct freshA freshB proper ca cb old with kept | cut
  · exact Or.inl kept
  · exact Or.inr (budgetRunCut_raw_congr _ _ _ u T depth
      (compressedRaw_agree roots (A ∪ B) f g _ same) cut)

lemma prunedBridge_raw_congr {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (f g : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (Cert2 : Finset (Sum α Bool) → Sig → Prop)
    (u : Bool) (T : Sig) (depth : Nat) (A : Finset α) (v : Sig)
    (same : ∀ r ∈ roots, f r = g r)
    (bridge : PrunedBridge roots f col need Cert Cert2 u T depth A v) :
    PrunedBridge roots g col need Cert Cert2 u T depth A v := by
  intro B w member dis adm
  have copied := duplicateRaw_agree roots A f g v same
  have old := columnAdmissible_raw_congr _ _ _ col need (liftLabels B) w
    (fun r hr => (copied r hr).symm) adm
  rcases bridge B w member dis old with kept | cut
  · exact Or.inl kept
  · exact Or.inr (budgetRunCut_raw_congr _ _ _ u T depth
      (compressedRaw_agree _ (liftLabels B) _ _ w copied) cut)

theorem prunedNode_raw_congr {Ω : Type} (col : Sig → Set Ω) (need : Set Ω)
    (u : Bool) (T : Sig) (depth : Nat) :
    ∀ {α : Type} [DecidableEq α] (roots : Finset α) (f g : α → Sig)
      (Cert : Finset α → Sig → Prop),
      (∀ r ∈ roots, f r = g r) →
      PrunedNode col need u T depth α roots f Cert →
      PrunedNode col need u T depth α roots g Cert := by
  induction depth with
  | zero =>
    intro α inst roots f g Cert same node
    refine ⟨?_, prunedGateClosed_raw_congr roots f g col need Cert u T 0 same node.2.1,
      node.2.2.1, trivial⟩
    intro r hr
    rw [← same r hr]
    exact node.1 r hr
  | succ depth ih =>
    intro α inst roots f g Cert same node
    refine ⟨?_, prunedGateClosed_raw_congr roots f g col need Cert u T (depth + 1)
      same node.2.1, node.2.2.1, ?_⟩
    · intro r hr
      rw [← same r hr]
      exact node.1 r hr
    · intro A v sub proper member
      have copied := duplicateRaw_agree roots A f g v same
      rcases node.2.2.2 A v sub proper member with cut | child
      · exact Or.inl (budgetRunCut_raw_congr _ _ _ u T depth copied cut)
      · obtain ⟨Cert2, bridge, child⟩ := child
        exact Or.inr ⟨Cert2, prunedBridge_raw_congr roots f g col need Cert Cert2
          u T depth A v same bridge, ih _ _ _ Cert2 copied child⟩

end PEqualNP.Outside.L_meta_2373.Live1024
