import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.CommonFilter

variable {α β : Type} [DecidableEq α] [DecidableEq β]

def Rect (P A : Finset α) (L B : Finset β) : Finset (α × β) :=
  (P ×ˢ L).filter fun e => e.1 ∈ A ∨ e.2 ∈ B

def NoFour (E : Finset (α × β)) : Prop :=
  ∀ p p' l l', p ≠ p' → l ≠ l' →
    ¬ ((p,l) ∈ E ∧ (p,l') ∈ E ∧ (p',l) ∈ E ∧ (p',l') ∈ E)

lemma rectangle_small_side (E : Finset (α × β)) (hE : NoFour E)
    (P : Finset α) (L : Finset β) (hPL : P ×ˢ L ⊆ E) : P.card ≤ 1 ∨ L.card ≤ 1 := by
  by_contra h
  simp only [not_or, not_le] at h
  obtain ⟨p,hp,p',hp',hpp⟩ := Finset.one_lt_card.mp h.1
  obtain ⟨l,hl,l',hl',hll⟩ := Finset.one_lt_card.mp h.2
  exact hE p p' l l' hpp hll
    ⟨hPL (Finset.mem_product.mpr ⟨hp,hl⟩), hPL (Finset.mem_product.mpr ⟨hp,hl'⟩),
      hPL (Finset.mem_product.mpr ⟨hp',hl⟩), hPL (Finset.mem_product.mpr ⟨hp',hl'⟩)⟩

lemma rect_union (P A : Finset α) (L B : Finset β) :
    Rect P A L B = ((P ∩ A) ×ˢ L) ∪ (P ×ˢ (L ∩ B)) := by
  ext e
  simp only [Rect,Finset.mem_filter,Finset.mem_product,Finset.mem_inter,Finset.mem_union]
  tauto

lemma rect_count (P A : Finset α) (L B : Finset β) :
    (Rect P A L B).card + (P ∩ A).card * (L ∩ B).card =
      (P ∩ A).card * L.card + P.card * (L ∩ B).card := by
  have hinter : (((P ∩ A) ×ˢ L) ∩ (P ×ˢ (L ∩ B))) = (P ∩ A) ×ˢ (L ∩ B) := by
    ext e
    simp only [Finset.mem_product,Finset.mem_inter]
    tauto
  have h := Finset.card_union_add_card_inter ((P ∩ A) ×ˢ L) (P ×ˢ (L ∩ B))
  rw [← rect_union,hinter] at h
  simpa only [Finset.card_product] using h

lemma rect_edges (P A : Finset α) (L B : Finset β)
    (hp : P.Nonempty) (hl : L.Nonempty) (hfour : NoFour (Rect P A L B)) :
    (Rect P A L B).card + 1 ≤ P.card + L.card := by
  have hp0 : 0 < P.card := Finset.card_pos.mpr hp
  have hl0 : 0 < L.card := Finset.card_pos.mpr hl
  have hsub : Rect P A L B ⊆ P ×ˢ L := Finset.filter_subset _ _
  have hcnt := Finset.card_le_card hsub
  rw [Finset.card_product] at hcnt
  by_cases hp1 : P.card ≤ 1
  · have he : P.card = 1 := by omega
    rw [he] at hcnt ⊢
    simp only [one_mul] at hcnt
    omega
  by_cases hl1 : L.card ≤ 1
  · have he : L.card = 1 := by omega
    rw [he] at hcnt ⊢
    simp only [mul_one] at hcnt
    omega
  have hpa : (P ∩ A).card ≤ 1 := by
    have hs : (P ∩ A) ×ˢ L ⊆ Rect P A L B := by rw [rect_union]; exact Finset.subset_union_left
    exact (rectangle_small_side _ hfour _ _ hs).resolve_right hl1
  have hlb : (L ∩ B).card ≤ 1 := by
    have hs : P ×ˢ (L ∩ B) ⊆ Rect P A L B := by rw [rect_union]; exact Finset.subset_union_right
    exact (rectangle_small_side _ hfour _ _ hs).resolve_left hp1
  have he := rect_count P A L B
  interval_cases h : (P ∩ A).card <;> interval_cases k : (L ∩ B).card <;>
    simp only [h,k,zero_mul,mul_zero,one_mul,mul_one,Nat.add_zero,Nat.zero_add] at he <;> omega

lemma noFour_subset {E F : Finset (α × β)} (h : E ⊆ F) (hf : NoFour F) : NoFour E := by
  intro p p' l l' hp hl he
  exact hf p p' l l' hp hl ⟨h he.1,h he.2.1,h he.2.2.1,h he.2.2.2⟩

lemma common_filter_cover (P1 P2 A : Finset α) (L1 L2 B : Finset β)
    (hp1 : P1.Nonempty) (hp2 : P2.Nonempty) (hl1 : L1.Nonempty) (hl2 : L2.Nonempty)
    (hfour : NoFour (Rect P1 A L1 B ∪ Rect P2 A L2 B)) :
    (∀ p l, (p,l) ∈ Rect P1 A L1 B ∪ Rect P2 A L2 B → p ∈ A ∨ l ∈ B) ∧
    (Rect P1 A L1 B ∪ Rect P2 A L2 B).card + A.card + B.card + 2 ≤
      P1.card + L1.card + P2.card + L2.card + A.card + B.card := by
  have h1 := rect_edges P1 A L1 B hp1 hl1 (noFour_subset Finset.subset_union_left hfour)
  have h2 := rect_edges P2 A L2 B hp2 hl2 (noFour_subset Finset.subset_union_right hfour)
  have hsum := Finset.card_union_le (Rect P1 A L1 B) (Rect P2 A L2 B)
  constructor
  · intro p l h
    rcases Finset.mem_union.mp h with h | h
    · exact (Finset.mem_filter.mp h).2
    · exact (Finset.mem_filter.mp h).2
  · omega

end PEqualNP.Outside.L_meta_2583.CommonFilter

namespace PEqualNP.Outside.L_meta_2583.CommonFilter

variable {α β : Type} [DecidableEq α] [DecidableEq β]

def Core (R : Finset (α × β)) (A : Finset α) (B : Finset β) : Finset (α × β) :=
  R.filter fun e => e.1 ∈ A ∨ e.2 ∈ B

def Graph (E : Finset (α × β)) (x : α → Bool) (y : β → Bool) : Prop :=
  ∃ p l, (p,l) ∈ E ∧ x p = true ∧ y l = true

def Block (R : Finset (α × β)) (A : Finset α) (B : Finset β)
    (x : α → Bool) (y : β → Bool) : Prop :=
  Graph R x y ∧ ((∃ w ∈ A, x w = true) ∨ ∃ w ∈ B, y w = true)

def Safe (R : Finset (α × β)) (A : Finset α) (B : Finset β) : Prop :=
  ∀ p l, (p,l) ∈ R →
    (∀ w ∈ A, (p,l) ∈ Core R A B ∨ (w,l) ∈ Core R A B) ∧
    (∀ w ∈ B, (p,l) ∈ Core R A B ∨ (p,w) ∈ Core R A B)

lemma graph_implies_block (R : Finset (α × β)) (A : Finset α) (B : Finset β)
    (x : α → Bool) (y : β → Bool) : Graph (Core R A B) x y → Block R A B x y := by
  rintro ⟨p,l,he,hp,hl⟩
  obtain ⟨hr,hw⟩ := Finset.mem_filter.mp he
  refine ⟨⟨p,l,hr,hp,hl⟩,?_⟩
  rcases hw with hw | hw
  · exact Or.inl ⟨p,hw,hp⟩
  · exact Or.inr ⟨l,hw,hl⟩

lemma block_below_iff_safe (R : Finset (α × β)) (A : Finset α) (B : Finset β) :
    (∀ x y, Block R A B x y → Graph (Core R A B) x y) ↔ Safe R A B := by
  constructor
  · intro h p l hpl
    constructor
    · intro w hw
      have hb : Block R A B (fun a => decide (a = p ∨ a = w)) (fun b => decide (b = l)) :=
        ⟨⟨p,l,hpl,by simp,by simp⟩,Or.inl ⟨w,hw,by simp⟩⟩
      obtain ⟨a,b,he,ha,hb⟩ := h _ _ hb
      have hb' : b = l := by simpa using hb
      subst b
      have ha' : a = p ∨ a = w := by simpa using ha
      rcases ha' with rfl | rfl
      · exact Or.inl he
      · exact Or.inr he
    · intro w hw
      have hb : Block R A B (fun a => decide (a = p)) (fun b => decide (b = l ∨ b = w)) :=
        ⟨⟨p,l,hpl,by simp,by simp⟩,Or.inr ⟨w,hw,by simp⟩⟩
      obtain ⟨a,b,he,ha,hb⟩ := h _ _ hb
      have ha' : a = p := by simpa using ha
      subst a
      have hb' : b = l ∨ b = w := by simpa using hb
      rcases hb' with rfl | rfl
      · exact Or.inl he
      · exact Or.inr he
  · intro h x y hb
    obtain ⟨⟨p,l,hpl,hp,hl⟩,hw⟩ := hb
    rcases hw with ⟨w,hw,hx⟩ | ⟨w,hw,hy⟩
    · rcases (h p l hpl).1 w hw with he | he
      · exact ⟨p,l,he,hp,hl⟩
      · exact ⟨w,l,he,hx,hl⟩
    · rcases (h p l hpl).2 w hw with he | he
      · exact ⟨p,l,he,hp,hl⟩
      · exact ⟨p,w,he,hp,hy⟩

lemma block_eq_graph_iff_safe (R : Finset (α × β)) (A : Finset α) (B : Finset β) :
    (∀ x y, Block R A B x y ↔ Graph (Core R A B) x y) ↔ Safe R A B := by
  constructor
  · intro h
    exact (block_below_iff_safe R A B).mp (fun x y => (h x y).mp)
  · intro h x y
    exact ⟨(block_below_iff_safe R A B).mpr h x y,graph_implies_block R A B x y⟩

lemma core_two_rectangles (P1 P2 A : Finset α) (L1 L2 B : Finset β) :
    Core ((P1 ×ˢ L1) ∪ (P2 ×ˢ L2)) A B = Rect P1 A L1 B ∪ Rect P2 A L2 B := by
  ext e
  simp only [Core,Rect,Finset.mem_filter,Finset.mem_union]
  tauto

lemma block_two_rectangles (P1 P2 A : Finset α) (L1 L2 B : Finset β)
    (x : α → Bool) (y : β → Bool) :
    Block ((P1 ×ˢ L1) ∪ (P2 ×ˢ L2)) A B x y ↔
      (((∃ p ∈ P1, x p = true) ∧ (∃ l ∈ L1, y l = true)) ∨
        ((∃ p ∈ P2, x p = true) ∧ (∃ l ∈ L2, y l = true))) ∧
      ((∃ w ∈ A, x w = true) ∨ ∃ w ∈ B, y w = true) := by
  simp only [Block,Graph,Finset.mem_union,Finset.mem_product]
  aesop

end PEqualNP.Outside.L_meta_2583.CommonFilter

namespace PEqualNP.Outside.L_meta_2583.CommonFilter

variable {ι α β : Type} [DecidableEq ι] [DecidableEq α] [DecidableEq β]

lemma family_edges (T : Finset ι) (P : ι → Finset α) (L : ι → Finset β)
    (A : Finset α) (B : Finset β)
    (hp : ∀ i ∈ T, (P i).Nonempty) (hl : ∀ i ∈ T, (L i).Nonempty)
    (hfour : NoFour (T.biUnion fun i => Rect (P i) A (L i) B)) :
    (T.biUnion fun i => Rect (P i) A (L i) B).card + T.card ≤
      ∑ i ∈ T, ((P i).card + (L i).card) := by
  revert hp hl hfour
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    intro hp hl hfour
    have hi4 : NoFour (Rect (P i) A (L i) B) := noFour_subset (by
      intro e he
      exact Finset.mem_biUnion.mpr ⟨i,by simp,he⟩) hfour
    have ht4 : NoFour (T.biUnion fun i => Rect (P i) A (L i) B) := noFour_subset (by
      intro e he
      obtain ⟨j,hj,he⟩ := Finset.mem_biUnion.mp he
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_insert_of_mem hj,he⟩) hfour
    have hnew := rect_edges (P i) A (L i) B (hp i (by simp)) (hl i (by simp)) hi4
    have hold := ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))
      (fun j hj => hl j (Finset.mem_insert_of_mem hj)) ht4
    have hu := Finset.card_union_le (Rect (P i) A (L i) B)
      (T.biUnion fun i => Rect (P i) A (L i) B)
    rw [Finset.biUnion_insert,Finset.card_insert_of_notMem hi,Finset.sum_insert hi]
    omega

lemma family_cover (T : Finset ι) (P : ι → Finset α) (L : ι → Finset β)
    (A : Finset α) (B : Finset β)
    (hp : ∀ i ∈ T, (P i).Nonempty) (hl : ∀ i ∈ T, (L i).Nonempty)
    (hfour : NoFour (T.biUnion fun i => Rect (P i) A (L i) B)) :
    (∀ p l, (p,l) ∈ (T.biUnion fun i => Rect (P i) A (L i) B) → p ∈ A ∨ l ∈ B) ∧
    (T.biUnion fun i => Rect (P i) A (L i) B).card + A.card + B.card + T.card ≤
      (∑ i ∈ T, ((P i).card + (L i).card)) + A.card + B.card := by
  constructor
  · intro p l h
    obtain ⟨i,_,he⟩ := Finset.mem_biUnion.mp h
    exact (Finset.mem_filter.mp he).2
  · have := family_edges T P L A B hp hl hfour
    omega

lemma core_family (T : Finset ι) (P : ι → Finset α) (L : ι → Finset β)
    (A : Finset α) (B : Finset β) :
    Core (T.biUnion fun i => P i ×ˢ L i) A B =
      T.biUnion fun i => Rect (P i) A (L i) B := by
  ext e
  simp only [Core,Rect,Finset.mem_filter,Finset.mem_biUnion]
  aesop

end PEqualNP.Outside.L_meta_2583.CommonFilter
