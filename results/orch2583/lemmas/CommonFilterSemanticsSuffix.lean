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
