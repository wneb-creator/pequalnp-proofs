
namespace PEqualNP.Outside.L_meta_1890.FiniteBridge
open FiniteEngine

theorem available_up {R : Type} {u : Bool} {bank : List (R → Bool)} {a}
    (h : B.Available false bank a) : B.Available u bank a := by
  rcases h with hm | hc | ⟨hu,hm⟩
  · exact Or.inl hm
  · exact Or.inr (Or.inl hc)
  · cases hu

theorem available_inv {R : Type} {bank : List (R → Bool)} {a}
    (h : B.Available true bank a) : B.Available true bank (FiniteEngine.inv a) := by
  rcases h with hm | hc | ⟨hu,hm⟩
  · exact Or.inr (Or.inr ⟨rfl,by simpa [B.inv,FiniteEngine.inv] using hm⟩)
  · rcases hc with ⟨b,rfl⟩
    exact Or.inr (Or.inl ⟨!b,rfl⟩)
  · exact Or.inl hm

theorem available_transfer {R : Type} {u : Bool} {bank bs : List (R → Bool)}
    (hs : ∀ v ∈ bank, B.Available u bs v) {a}
    (ha : FiniteEngine.Available bank a) : B.Available u bs a := by
  rcases ha with hm | hc
  · exact hs a hm
  · exact Or.inr (Or.inl hc)

theorem translate {R : Type} {roots bank : List (R → Bool)} {p}
    (h : FiniteEngine.Reach roots p bank) :
    (∃ q bs, B.Reach false roots q bs ∧ q ≤ p ∧
      ∀ v ∈ bank, B.Available false bs v) ∨
    (∃ q bs, B.Reach true roots q bs ∧ q < p ∧
      ∀ v ∈ bank, B.Available true bs v) := by
  induction h with
  | start => exact Or.inl ⟨0,roots,B.Reach.start,by omega,fun v hv => Or.inl hv⟩
  | @one p bank a h ha ih =>
    rcases ih with ⟨q,bs,hq,hn,hs⟩ | ⟨q,bs,hq,hn,hs⟩
    · refine Or.inr ⟨q,bs,B.reach_up hq,by omega,?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact available_inv (available_up (available_transfer hs ha))
      · exact available_up (hs v hv)
    · refine Or.inr ⟨q,bs,hq,by omega,?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact available_inv (available_transfer hs ha)
      · exact hs v hv
  | @two p bank a b op h ha hb ih =>
    rcases ih with ⟨q,bs,hq,hn,hs⟩ | ⟨q,bs,hq,hn,hs⟩
    · refine Or.inl ⟨q+1,B.combine op a b :: bs,
        B.Reach.two op hq (available_transfer hs ha) (available_transfer hs hb),by omega,?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Or.inl (List.mem_cons_self _ _)
      · exact B.available_cons _ (hs v hv)
    · refine Or.inr ⟨q+1,B.combine op a b :: bs,
        B.Reach.two op hq (available_transfer hs ha) (available_transfer hs hb),by omega,?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact Or.inl (List.mem_cons_self _ _)
      · exact B.available_cons _ (hs v hv)

theorem total_lower {R : Type} {roots : List (R → Bool)} {goal : R → Bool} {L : Nat}
    (mono : ∀ q bs, B.Reach false roots q bs → B.Available false bs goal → L+1 ≤ q)
    (signed : ∀ q bs, B.Reach true roots q bs → B.Available true bs goal → L ≤ q)
    {p bank} (hp : FiniteEngine.Reach roots p bank) (ha : FiniteEngine.Available bank goal) :
    L+1 ≤ p := by
  rcases translate hp with ⟨q,bs,hq,hn,hs⟩ | ⟨q,bs,hq,hn,hs⟩
  · have hl := mono q bs hq (available_transfer hs ha)
    omega
  · have hl := signed q bs hq (available_transfer hs ha)
    omega

theorem signed_lower {R : Type} {roots : List (R → Bool)} {goal : R → Bool} {L : Nat}
    (signed : ∀ q bs, B.Reach true roots q bs → B.Available true bs goal → L ≤ q)
    {p bank} (hp : FiniteEngine.Reach roots p bank) (ha : FiniteEngine.Available bank goal) :
    L ≤ p := by
  rcases translate hp with ⟨q,bs,hq,hn,hs⟩ | ⟨q,bs,hq,hn,hs⟩
  · have hl := signed q bs (B.reach_up hq) (available_up (available_transfer hs ha))
    omega
  · have hl := signed q bs hq (available_transfer hs ha)
    omega

end PEqualNP.Outside.L_meta_1890.FiniteBridge
