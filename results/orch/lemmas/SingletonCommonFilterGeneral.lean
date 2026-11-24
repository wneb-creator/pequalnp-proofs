import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.StructuralMasks

def orValue {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

def productValue {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  orValue A x && orValue B x

def CleanMask {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (c : Fin n) : Prop :=
  ∀ x : Fin n → Bool, productValue A B x = true → x c = true →
    ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true

def EffectiveMask {n : ℕ} (G : SimpleGraph (Fin n)) (A B : Finset (Fin n))
    (c : Fin n) : Prop :=
  ∃ u v : Fin n, G.Adj u v ∧
    productValue A B (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
    PEqualNP.EdgeOwnership.pairInput u v c = true

lemma graph_pair_iff {n : ℕ} (G : SimpleGraph (Fin n)) (c d : Fin n) :
    (∃ u v : Fin n, G.Adj u v ∧ PEqualNP.EdgeOwnership.pairInput c d u = true ∧
      PEqualNP.EdgeOwnership.pairInput c d v = true) ↔ G.Adj c d := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact (G.loopless.irrefl _ huv).elim
    · exact huv
    · exact huv.symm
    · exact (G.loopless.irrefl _ huv).elim
  · intro h
    exact ⟨c, d, h, by simp [PEqualNP.EdgeOwnership.pairInput],
      by simp [PEqualNP.EdgeOwnership.pairInput]⟩

lemma cleanMask_of_mem_left_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ A) :
    CleanMask G A B c ↔ ∀ b ∈ B, G.Adj c b := by
  constructor
  · intro h b hb
    apply (graph_pair_iff G c b).mp
    apply h (PEqualNP.EdgeOwnership.pairInput c b)
    · simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq]
      exact ⟨⟨c, hc, by simp [PEqualNP.EdgeOwnership.pairInput]⟩,
        ⟨b, hb, by simp [PEqualNP.EdgeOwnership.pairInput]⟩⟩
    · simp [PEqualNP.EdgeOwnership.pairInput]
  · intro h x hx hxc
    simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq] at hx
    obtain ⟨b, hb, hxb⟩ := hx.2
    exact ⟨c, b, h b hb, hxc, hxb⟩

lemma cleanMask_of_mem_right_iff {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (c : Fin n) (hc : c ∈ B) :
    CleanMask G A B c ↔ ∀ a ∈ A, G.Adj a c := by
  have hs : CleanMask G A B c ↔ CleanMask G B A c := by
    simp only [CleanMask, productValue, Bool.and_comm]
  rw [hs, cleanMask_of_mem_left_iff G B A c hc]
  exact forall₂_congr fun a _ => G.adj_comm c a

lemma cleanMask_adj_overlap {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (c : Fin n) (hc : CleanMask G A B c)
    (z : Fin n) (hz : z ∈ A ∩ B) : G.Adj c z := by
  apply (graph_pair_iff G c z).mp
  apply hc (PEqualNP.EdgeOwnership.pairInput c z)
  · simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq]
    exact ⟨⟨z, (Finset.mem_inter.mp hz).1, by simp [PEqualNP.EdgeOwnership.pairInput]⟩,
      ⟨z, (Finset.mem_inter.mp hz).2, by simp [PEqualNP.EdgeOwnership.pairInput]⟩⟩
  · simp [PEqualNP.EdgeOwnership.pairInput]

lemma effectiveMask_mem_union {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (hdis : Disjoint A B) (c : Fin n)
    (hc : EffectiveMask G A B c) : c ∈ A ∪ B := by
  obtain ⟨u, v, _, hprod, hmask⟩ := hc
  simp only [productValue, Bool.and_eq_true, orValue, decide_eq_true_eq] at hprod
  obtain ⟨a, ha, hpa⟩ := hprod.1
  obtain ⟨b, hb, hpb⟩ := hprod.2
  simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at hpa hpb hmask
  by_contra hnot
  have hca : c ∉ A := fun h => hnot (Finset.mem_union_left _ h)
  have hcb : c ∉ B := fun h => hnot (Finset.mem_union_right _ h)
  have hab : a ≠ b := fun h => (Finset.disjoint_left.mp hdis ha) (h ▸ hb)
  rcases hmask with rfl | rfl <;>
    rcases hpa with rfl | rfl <;> rcases hpb with rfl | rfl <;> contradiction

end PEqualNP.Outside.L_meta_1477.StructuralMasks

namespace PEqualNP.Outside.L_meta_1477.SingletonCommonFilterGeneral
open StructuralMasks PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma two_colors_eq {n : ℕ} (color : Fin n → Fin 2) (a d c : Fin n)
    (hd : color d ≠ color a) (hc : color c ≠ color a) : color d = color c := by
  apply Fin.ext
  have hda : (color d).val ≠ (color a).val := fun he => hd (Fin.ext he)
  have hca : (color c).val ≠ (color a).val := fun he => hc (Fin.ext he)
  have ha := (color a).isLt
  have hdv := (color d).isLt
  have hcv := (color c).isLt
  omega

lemma opposite_clean_mask_adj {n : ℕ} (G : SimpleGraph (Fin n))
    (color : Fin n → Fin 2) (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (a : Fin n) (B : Finset (Fin n)) (d : Fin n) (hd : d ∈ B)
    (hbad : ¬ G.Adj a d) (hda : color d ≠ color a)
    (c : Fin n) (hc : CleanMask G {a} B c) (hca : color c ≠ color a) : G.Adj a c := by
  have hdc : color d = color c := two_colors_eq color a d c hda hca
  have hnotdc : ¬ G.Adj d c := fun h => hcolor d c h hdc
  let x : Fin n → Bool := fun v => decide (v=a ∨ v=d ∨ v=c)
  have hp : productValue {a} B x = true := by
    simp only [productValue,Bool.and_eq_true,orValue,decide_eq_true_eq]
    exact ⟨⟨a,by simp,by simp [x]⟩,⟨d,hd,by simp [x]⟩⟩
  obtain ⟨u,v,huv,hu,hv⟩ := hc x hp (by simp [x])
  simp only [x,decide_eq_true_eq] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact (G.loopless.irrefl _ huv).elim
  · exact (hbad huv).elim
  · exact huv
  · exact (hbad huv.symm).elim
  · exact (G.loopless.irrefl _ huv).elim
  · exact (hnotdc huv).elim
  · exact huv.symm
  · exact (hnotdc huv.symm).elim
  · exact (G.loopless.irrefl _ huv).elim

lemma effective_dirty_singleton_adj {n : ℕ} (G : SimpleGraph (Fin n))
    (a : Fin n) (B : Finset (Fin n)) (d : Fin n) (hd : d∈B) (hbad : ¬G.Adj a d)
    (c : Fin n) (hc : CleanMask G {a} B c) (heff : EffectiveMask G {a} B c) : G.Adj a c := by
  have hca : c≠a := by
    intro he
    subst c
    exact hbad ((cleanMask_of_mem_left_iff G {a} B a (by simp)).mp hc d hd)
  obtain ⟨u,v,huv,hprod,hpc⟩ := heff
  simp only [productValue,Bool.and_eq_true,orValue,decide_eq_true_eq] at hprod
  have hpa : pairInput u v a = true := by
    simpa only [Finset.mem_singleton,exists_eq_left] using hprod.1
  simp only [pairInput,decide_eq_true_eq] at hpa hpc
  rcases hpa with rfl | rfl <;> rcases hpc with rfl | rfl
  · exact (hca rfl).elim
  · exact huv
  · exact huv.symm
  · exact (hca rfl).elim

lemma same_color_common_effective_adj {n : ℕ} (G : SimpleGraph (Fin n))
    (color : Fin n → Fin 2) (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (a b : Fin n) (hab : color a = color b) (B D : Finset (Fin n))
    (d e : Fin n) (hd : d∈B) (he : e∈D) (had : ¬G.Adj a d) (hbe : ¬G.Adj b e)
    (hda : color d ≠ color a) (heb : color e ≠ color b)
    (c : Fin n) (hcA : CleanMask G {a} B c) (hcB : CleanMask G {b} D c)
    (heff : EffectiveMask G {a} B c ∨ EffectiveMask G {b} D c) :
    G.Adj a c ∧ G.Adj b c := by
  rcases heff with hg | hh
  · have hac := effective_dirty_singleton_adj G a B d hd had c hcA hg
    have hcb : color c ≠ color b := by simpa only [←hab] using (hcolor a c hac).symm
    exact ⟨hac,opposite_clean_mask_adj G color hcolor b D e he hbe heb c hcB hcb⟩
  · have hbc := effective_dirty_singleton_adj G b D e he hbe c hcB hh
    have hca : color c ≠ color a := by simpa only [hab] using (hcolor b c hbc).symm
    exact ⟨opposite_clean_mask_adj G color hcolor a B d hd had hda c hcA hca,hbc⟩

lemma same_color_common_effective_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (a b : Fin n) (hne : a≠b) (hab : color a = color b) (B D : Finset (Fin n))
    (d e : Fin n) (hd : d∈B) (he : e∈D) (had : ¬G.Adj a d) (hbe : ¬G.Adj b e)
    (hda : color d ≠ color a) (heb : color e ≠ color b)
    (S : Finset (Fin n))
    (hclean : ∀ c∈S, CleanMask G {a} B c ∧ CleanMask G {b} D c)
    (heff : ∀ c∈S, EffectiveMask G {a} B c ∨ EffectiveMask G {b} D c) : S.card≤1 := by
  have hs : S ⊆ Finset.univ.filter (fun c => G.Adj a c ∧ G.Adj b c) := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,same_color_common_effective_adj G color hcolor
      a b hab B D d e hd he had hbe hda heb c (hclean c hc).1 (hclean c hc).2 (heff c hc)⟩
  exact (Finset.card_le_card hs).trans (h4 a b hne)

lemma common_reader_pair_cover_one {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (a b : Fin n) (hne : a≠b) (hab : color a = color b) (B D : Finset (Fin n))
    (d e : Fin n) (hd : d∈B) (he : e∈D) (had : ¬G.Adj a d) (hbe : ¬G.Adj b e)
    (hda : color d ≠ color a) (heb : color e ≠ color b)
    (R : Finset (Fin n))
    (hclean : ∀ c∈R, CleanMask G {a} B c ∧ CleanMask G {b} D c) :
    ∃ T : Finset (Fin n), T.card≤1 ∧ T⊆R ∧ ∀ u v : Fin n, G.Adj u v →
      (productValue {a} B (pairInput u v)=true ∨ productValue {b} D (pairInput u v)=true) →
      orValue R (pairInput u v)=true → ∃ c∈T, c=u ∨ c=v := by
  classical
  let T := R.filter fun c => EffectiveMask G {a} B c ∨ EffectiveMask G {b} D c
  refine ⟨T,?_,Finset.filter_subset _ _,?_⟩
  · apply same_color_common_effective_card G h4 color hcolor a b hne hab B D d e hd he had hbe hda heb T
    · intro c hc
      exact hclean c (Finset.mem_filter.mp hc).1
    · intro c hc
      exact (Finset.mem_filter.mp hc).2
  · intro u v huv hprod hfilter
    obtain ⟨c,hc,hpc⟩ := of_decide_eq_true hfilter
    refine ⟨c,Finset.mem_filter.mpr ⟨hc,?_⟩,by simpa only [pairInput,decide_eq_true_eq] using hpc⟩
    rcases hprod with hg | hh
    · exact Or.inl ⟨u,v,huv,hg,hpc⟩
    · exact Or.inr ⟨u,v,huv,hh,hpc⟩

end PEqualNP.Outside.L_meta_1477.SingletonCommonFilterGeneral
