import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3754.CycleExamples
open PEqualNP.EdgeOwnership

def cycleEdges (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).map fun i => (i,(i+1)%n)

def cycle (n : ℕ) : SimpleGraph (Fin n) := edgeGraph n (cycleEdges n)

instance (n : ℕ) : DecidableRel (cycle n).Adj := by
  unfold cycle
  infer_instance

def finiteSparse {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  ∀ S : Finset (Fin n),(G.edgeFinset.filter fun e=>∀v∈e,v∈S).card≤S.card

def next {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val+1)%n,Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

lemma cycle_adj {n : ℕ} (u v : Fin n) :
    (cycle n).Adj u v → next u=v ∨ next v=u := by
  rintro ⟨_,h | h⟩
  · obtain ⟨i,_,he⟩ := List.mem_map.mp h
    have hu : i=u.val := congrArg Prod.fst he
    have hv : (i+1)%n=v.val := congrArg Prod.snd he
    exact Or.inl (Fin.ext (by simpa only [next,hu] using hv))
  · obtain ⟨i,_,he⟩ := List.mem_map.mp h
    have hv : i=v.val := congrArg Prod.fst he
    have hu : (i+1)%n=u.val := congrArg Prod.snd he
    exact Or.inr (Fin.ext (by simpa only [next,hv] using hu))

lemma functional_sparse {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : Fin n → Fin n) (hf : ∀u v,G.Adj u v → f u=v ∨ f v=u) : finiteSparse G := by
  intro S
  have hsub : (G.edgeFinset.filter fun e=>∀v∈e,v∈S) ⊆
      S.image (fun i=>s(i,f i)) := by
    intro e he
    obtain ⟨he,hS⟩ := Finset.mem_filter.mp he
    induction e using Sym2.inductionOn with
    | _ u v =>
      have huv : G.Adj u v := by simpa using he
      rcases hf u v huv with h | h
      · exact Finset.mem_image.mpr ⟨u,hS u (by simp),by rw [h]⟩
      · exact Finset.mem_image.mpr ⟨v,hS v (by simp),by simp [h,Sym2.eq_swap]⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

lemma cycle_sparse (n : ℕ) : finiteSparse (cycle n) :=
  functional_sparse (cycle n) next cycle_adj

lemma cycle8_sparse : finiteSparse (cycle 8) := cycle_sparse 8
lemma cycle10_sparse : finiteSparse (cycle 10) := cycle_sparse 10

def leafNext (i : Fin 7) : Fin 7 :=
  if i=6 then 0 else ⟨(i.val+1)%6,by have := Nat.mod_lt (i.val+1) (by decide : 0<6);omega⟩

lemma cycleLeaf7_sparse : finiteSparse (edgeGraph 7
    [(0,1),(1,2),(2,3),(3,4),(4,5),(5,0),(0,6)]) := by
  apply functional_sparse _ leafNext
  decide +kernel

lemma cycle8_edges : (cycle 8).edgeFinset.card=8 := by decide +kernel
lemma cycle10_edges : (cycle 10).edgeFinset.card=10 := by decide +kernel

lemma finiteSparse_set {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h : finiteSparse G) (S : Finset (Fin n)) :
    {e : Sym2 (Fin n) | e∈G.edgeSet ∧ ∀v∈e,v∈S}.ncard≤S.card := by
  have he : {e : Sym2 (Fin n) | e∈G.edgeSet ∧ ∀v∈e,v∈S}=
      (↑(G.edgeFinset.filter fun e=>∀v∈e,v∈S) : Set (Sym2 (Fin n))) := by
    ext e
    simp
  rw [he,Set.ncard_coe_finset]
  exact h S

end PEqualNP.Outside.L_meta_3754.CycleExamples
