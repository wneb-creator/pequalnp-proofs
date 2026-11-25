import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux.PointGadget

abbrev Lit := Fin 12 × Bool

def word (p : Fin 13) : Finset Lit :=
  match p.val with
  | 0 => {(0,true), (1,true), (2,true), (3,true)}
  | 1 => {(2,false), (3,true)}
  | 2 => {(0,false), (2,true)}
  | 3 => {(4,true)}
  | 4 => {(0,true), (1,false)}
  | 5 => {(5,true)}
  | 6 => {(1,true), (3,false)}
  | 7 => {(6,true)}
  | 8 => {(7,true)}
  | 9 => {(8,true)}
  | 10 => {(9,true)}
  | 11 => {(10,true)}
  | _ => {(11,true)}

def Hit (f : Fin 12 → Option Bool) (W : Finset Lit) : Prop :=
  ∃ l ∈ W, f l.1 = some l.2

def Avoid (f : Fin 12 → Option Bool) (W : Finset Lit) : Prop :=
  ∀ l ∈ W, f l.1 ≠ some l.2

def PointSep (f : Fin 12 → Option Bool) (S : Finset (Fin 13)) : Prop :=
  (∀ p ∈ S, Avoid f (word p)) ∧ ∀ p, p ∉ S → Hit f (word p)

lemma cycle_pos (a b c d : Option Bool)
    (h0 : a = some true ∨ b = some true ∨ c = some true ∨ d = some true)
    (h1 : c = some false ∨ d = some true)
    (h4 : a = some true ∨ b = some false)
    (h6 : b = some true ∨ d = some false)
    (h2 : a = some false ∨ c = some true) :
    a = some true ∧ b = some true ∧ c = some true ∧ d = some true := by
  rcases h0 with ha | hb | hc | hd <;> simp_all

lemma pos_except (f : Fin 12 → Option Bool)
    (h : ∀ p : Fin 13, p ≠ 11 → Hit f (word p)) :
    ∀ i : Fin 12, i ≠ 10 → f i = some true := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h4 := h 4 (by decide)
  have h6 := h 6 (by decide)
  simp [Hit, word] at h0 h1 h2 h4 h6
  have hg := cycle_pos (f 0) (f 1) (f 2) (f 3) h0 h1 h4 h6 h2
  have h3 := h 3 (by decide)
  have h5 := h 5 (by decide)
  have h7 := h 7 (by decide)
  have h8 := h 8 (by decide)
  have h9 := h 9 (by decide)
  have h10 := h 10 (by decide)
  have h12 := h 12 (by decide)
  simp [Hit, word] at h3 h5 h7 h8 h9 h10 h12
  intro i hi
  fin_cases i <;> simp_all

lemma all_pos (f : Fin 12 → Option Bool) (h : ∀ p : Fin 13, Hit f (word p)) :
    ∀ i : Fin 12, f i = some true := by
  have hp := pos_except f (fun p _ => h p)
  have h11 := h 11
  simp [Hit, word] at h11
  intro i
  by_cases hi : i = 10
  · simpa [hi] using h11
  · exact hp i hi

lemma selected_gadget_negative (f : Fin 12 → Option Bool)
    (h : PointSep f {0,1,2,4,6,11}) :
    ∀ i : Fin 12, f i = some false → i = 10 := by
  have h1 := h.1 1 (by decide)
  have h2 := h.1 2 (by decide)
  have h4 := h.1 4 (by decide)
  have h6 := h.1 6 (by decide)
  simp [Avoid, word] at h1 h2 h4 h6
  have h3 := h.2 3 (by decide)
  have h5 := h.2 5 (by decide)
  have h7 := h.2 7 (by decide)
  have h8 := h.2 8 (by decide)
  have h9 := h.2 9 (by decide)
  have h10 := h.2 10 (by decide)
  have h12 := h.2 12 (by decide)
  simp [Hit, word] at h3 h5 h7 h8 h9 h10 h12
  intro i hi
  fin_cases i <;> simp_all

theorem no_extension (L : Fin 13 → Finset Lit)
    (hA : ∃ f : Fin 12 → Option Bool,
      (∀ p : Fin 13, Hit f (word p)) ∧ ∀ l, Avoid f (L l))
    (hB : ∃ f : Fin 12 → Option Bool,
      PointSep f {11} ∧ Avoid f (L 0) ∧ Hit f (L 11))
    (hC : ∃ f : Fin 12 → Option Bool,
      PointSep f {0,1,2,4,6,11} ∧ Hit f (L 0)) : False := by
  obtain ⟨a, ha, haL⟩ := hA
  obtain ⟨b, hb, hbL, hbHit⟩ := hB
  obtain ⟨c, hc, hcHit⟩ := hC
  have haPos := all_pos a ha
  have noPos : ∀ l : Fin 13, ∀ i : Fin 12, (i,true) ∉ L l := by
    intro l i hm
    exact haL l (i,true) hm (haPos i)
  have hbPos := pos_except b (fun p hp => hb.2 p (by simpa using hp))
  have hbTen : b 10 = some false := by
    obtain ⟨⟨i,s⟩, hm, hv⟩ := hbHit
    cases s
    · have hi : i = 10 := by
        by_contra hi
        have ht := hbPos i hi
        simp_all
      simpa [hi] using hv
    · exact (noPos 11 i hm).elim
  have noTen : (10,false) ∉ L 0 := by
    intro hm
    exact hbL (10,false) hm hbTen
  obtain ⟨⟨i,s⟩, hm, hv⟩ := hcHit
  cases s
  · have hi := selected_gadget_negative c hc i hv
    subst i
    exact noTen hm
  · exact noPos 0 i hm

end PEqualNP.Outside.L_meta_2602_aux.PointGadget
