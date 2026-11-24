import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_1415

open PEqualNP.CircuitLowerBounds

-- a step: operation code (0 and, 1 or, otherwise not) and two operand tables
abbrev Stp := ℕ × ℕ × ℕ

def nt (s : Stp) : Bool := s.1 != 0 && s.1 != 1

def out (F : ℕ) (s : Stp) : ℕ :=
  if s.1 = 0 then s.2.1 &&& s.2.2 else if s.1 = 1 then s.2.1 ||| s.2.2 else F ^^^ s.2.1

def Ok (S : Finset ℕ) (s : Stp) : Prop :=
  s.2.1 ∈ S ∧ s.2.2 ∈ S ∧ (nt s = true → s.2.1 = s.2.2)

def Val (F : ℕ) : Finset ℕ → List Stp → Prop
  | _, [] => True
  | S, s :: l => Ok S s ∧ Val F (insert (out F s) S) l

def outs (F : ℕ) (l : List Stp) : Finset ℕ := (l.map (out F)).toFinset

def ops (l : List Stp) : Finset ℕ := (l.map (fun s => s.2.1)).toFinset ∪ (l.map (fun s => s.2.2)).toFinset

lemma mem_outs {F : ℕ} {l : List Stp} {t : ℕ} : t ∈ outs F l ↔ ∃ s ∈ l, out F s = t := by
  simp [outs]

lemma mem_ops {l : List Stp} {t : ℕ} : t ∈ ops l ↔ ∃ s ∈ l, s.2.1 = t ∨ s.2.2 = t := by
  simp only [ops, Finset.mem_union, List.mem_toFinset, List.mem_map]
  constructor
  · rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩)
    · exact ⟨s, hs, Or.inl h⟩
    · exact ⟨s, hs, Or.inr h⟩
  · rintro ⟨s, hs, h | h⟩
    · exact Or.inl ⟨s, hs, h⟩
    · exact Or.inr ⟨s, hs, h⟩

lemma ops_card (l : List Stp) : (ops l).card ≤ 2 * l.length := by
  have h1 := List.toFinset_card_le (l.map (fun s : Stp => s.2.1))
  have h2 := List.toFinset_card_le (l.map (fun s : Stp => s.2.2))
  have h3 := Finset.card_union_le (l.map (fun s : Stp => s.2.1)).toFinset
    (l.map (fun s : Stp => s.2.2)).toFinset
  simp only [List.length_map] at h1 h2
  unfold ops
  omega

@[simp] lemma outs_nil (F : ℕ) : outs F [] = ∅ := by simp [outs]

@[simp] lemma outs_cons (F : ℕ) (s : Stp) (l : List Stp) :
    outs F (s :: l) = insert (out F s) (outs F l) := by simp [outs]

@[simp] lemma outs_append (F : ℕ) (p q : List Stp) : outs F (p ++ q) = outs F p ∪ outs F q := by
  simp [outs]

lemma Ok.mono {S S' : Finset ℕ} (h : S ⊆ S') {s : Stp} (hs : Ok S s) : Ok S' s :=
  ⟨h hs.1, h hs.2.1, hs.2.2⟩

lemma Val.mono {F : ℕ} {l : List Stp} : ∀ {S S' : Finset ℕ}, S ⊆ S' → Val F S l → Val F S' l := by
  induction l with
  | nil => intros; trivial
  | cons s l ih =>
    intro S S' h hv
    exact ⟨hv.1.mono h, ih (Finset.insert_subset_insert _ h) hv.2⟩

lemma val_append {F : ℕ} {p q : List Stp} : ∀ {S : Finset ℕ},
    Val F S (p ++ q) ↔ Val F S p ∧ Val F (S ∪ outs F p) q := by
  induction p with
  | nil => intro S; simp [Val]
  | cons s p ih =>
    intro S
    simp only [List.cons_append, Val, ih, outs_cons]
    rw [Finset.union_insert, Finset.insert_union]
    tauto

-- an element never read can be dropped from the available set
lemma val_drop {F : ℕ} {l : List Stp} : ∀ {S : Finset ℕ} {x : ℕ},
    Val F (insert x S) l → x ∉ ops l → Val F S l := by
  induction l with
  | nil => intros; trivial
  | cons s l ih =>
    intro S x hv hx
    have hx1 : s.2.1 ≠ x ∧ s.2.2 ≠ x := by
      constructor
      · intro h; exact hx (mem_ops.2 ⟨s, by simp, Or.inl h⟩)
      · intro h; exact hx (mem_ops.2 ⟨s, by simp, Or.inr h⟩)
    have hx2 : x ∉ ops l := by
      intro h
      obtain ⟨s', hs', h'⟩ := mem_ops.1 h
      exact hx (mem_ops.2 ⟨s', by simp [hs'], h'⟩)
    obtain ⟨⟨h1, h2, h3⟩, hv2⟩ := hv
    refine ⟨⟨Finset.mem_of_mem_insert_of_ne h1 hx1.1, Finset.mem_of_mem_insert_of_ne h2 hx1.2, h3⟩, ?_⟩
    exact ih (by rwa [Finset.insert_comm] at hv2) hx2

lemma ops_sub {F : ℕ} {l : List Stp} : ∀ {S : Finset ℕ}, Val F S l → ops l ⊆ S ∪ outs F l := by
  induction l with
  | nil => intro S _; simp [ops]
  | cons s l ih =>
    intro S hv t ht
    obtain ⟨s', hs', h'⟩ := mem_ops.1 ht
    rcases List.mem_cons.1 hs' with rfl | hs'
    · rcases h' with rfl | rfl
      · exact Finset.mem_union_left _ hv.1.1
      · exact Finset.mem_union_left _ hv.1.2.1
    · have := ih hv.2 (mem_ops.2 ⟨s', hs', h'⟩)
      rw [outs_cons, Finset.union_insert, ← Finset.insert_union]
      exact this

-- chains
def Ch (F : ℕ) (S0 : Finset ℕ) (T : ℕ) (l : List Stp) : Prop :=
  Val F S0 l ∧ l.countP nt ≤ 1 ∧ T ∈ outs F l

def Mn (F : ℕ) (S0 : Finset ℕ) (T : ℕ) (l : List Stp) : Prop :=
  Ch F S0 T l ∧ ∀ l', Ch F S0 T l' → l.length ≤ l'.length

lemma exists_mn {F : ℕ} {S0 : Finset ℕ} {T : ℕ} {l : List Stp} (h : Ch F S0 T l) :
    ∃ m, Mn F S0 T m ∧ m.length ≤ l.length := by
  classical
  have hex : ∃ n, ∃ m, Ch F S0 T m ∧ m.length = n := ⟨l.length, l, h, rfl⟩
  obtain ⟨m, hm, hlen⟩ := Nat.find_spec hex
  refine ⟨m, ⟨hm, ?_⟩, ?_⟩
  · intro l' hl'
    rw [hlen]
    exact Nat.find_min' hex ⟨l', hl', rfl⟩
  · rw [hlen]
    exact Nat.find_min' hex ⟨l, h, rfl⟩

lemma mn_new {F : ℕ} {S0 : Finset ℕ} {T : ℕ} (hT : T ∉ S0) {p q : List Stp} {s : Stp}
    (h : Mn F S0 T (p ++ s :: q)) : out F s ∉ S0 ∪ outs F p := by
  intro hin
  obtain ⟨⟨hv, hn, ht⟩, hmin⟩ := h
  have hc : Ch F S0 T (p ++ q) := by
    obtain ⟨h1, h2⟩ := val_append.1 hv
    refine ⟨val_append.2 ⟨h1, ?_⟩, ?_, ?_⟩
    · have := h2.2
      rwa [Finset.insert_eq_of_mem hin] at this
    · simp only [List.countP_append, List.countP_cons] at hn ⊢; omega
    · simp only [outs_append, outs_cons, Finset.mem_union, Finset.mem_insert] at ht hin ⊢
      rcases ht with ht | rfl | ht
      · exact Or.inl ht
      · rcases hin with h | h
        · exact absurd h hT
        · exact Or.inl h
      · exact Or.inr ht
  have := hmin _ hc
  simp at this

lemma mn_read {F : ℕ} {S0 : Finset ℕ} {T : ℕ} {p q : List Stp} {s : Stp}
    (h : Mn F S0 T (p ++ s :: q)) (hs : out F s ≠ T) : out F s ∈ ops q := by
  by_contra hin
  obtain ⟨⟨hv, hn, ht⟩, hmin⟩ := h
  have hc : Ch F S0 T (p ++ q) := by
    obtain ⟨h1, h2⟩ := val_append.1 hv
    refine ⟨val_append.2 ⟨h1, val_drop h2.2 hin⟩, ?_, ?_⟩
    · simp only [List.countP_append, List.countP_cons] at hn ⊢; omega
    · simp only [outs_append, outs_cons, Finset.mem_union, Finset.mem_insert] at ht ⊢
      rcases ht with ht | rfl | ht
      · exact Or.inl ht
      · exact absurd rfl hs
      · exact Or.inr ht
  have := hmin _ hc
  simp at this

-- the new outputs of the remaining steps are fresh and distinct
lemma mn_fresh {F : ℕ} {S0 : Finset ℕ} {T : ℕ} (hT : T ∉ S0) {p l : List Stp}
    (h : Mn F S0 T (p ++ l)) : Disjoint (S0 ∪ outs F p) (outs F l) ∧ (outs F l).card = l.length := by
  induction l generalizing p with
  | nil => simp
  | cons s l ih =>
    have h1 := mn_new hT h
    have h2 := ih (p := p ++ [s]) (by simpa using h)
    simp only [outs_append, outs_cons, outs_nil] at h2
    have h3 : out F s ∉ outs F l := by
      intro hh
      exact Finset.disjoint_left.1 h2.1 (by simp) hh
    constructor
    · rw [outs_cons, Finset.disjoint_insert_right]
      refine ⟨h1, ?_⟩
      refine Finset.disjoint_of_subset_left ?_ h2.1
      intro x hx
      simp only [Finset.mem_union] at hx ⊢
      tauto
    · rw [outs_cons, Finset.card_insert_of_notMem h3, h2.2]; simp

lemma mn_rd {F : ℕ} {S0 : Finset ℕ} {T : ℕ} (hT : T ∉ S0) {p l : List Stp}
    (h : Mn F S0 T (p ++ l)) : (ops l ∩ (S0 ∪ outs F p)).card ≤ l.length + 1 := by
  obtain ⟨hd, hc⟩ := mn_fresh hT h
  have hsub : (ops l ∩ (S0 ∪ outs F p)) ∪ (outs F l).erase T ⊆ ops l := by
    intro x hx
    rcases Finset.mem_union.1 hx with hx | hx
    · exact (Finset.mem_inter.1 hx).1
    · obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
      obtain ⟨s, hs, rfl⟩ := mem_outs.1 hx
      obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hs
      have := mn_read (p := p ++ l1) (q := l2) (s := s) (by simpa using h) hne
      obtain ⟨s', hs', h'⟩ := mem_ops.1 this
      exact mem_ops.2 ⟨s', by simp [hs'], h'⟩
  have hdis : Disjoint (ops l ∩ (S0 ∪ outs F p)) ((outs F l).erase T) := by
    refine Finset.disjoint_of_subset_left Finset.inter_subset_right ?_
    exact Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hd
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis] at h1
  have h2 := ops_card l
  have h3 := Finset.pred_card_le_card_erase (s := outs F l) (a := T)
  omega

-- moving a step to the front, possibly with other operands
lemma mn_move {F : ℕ} {S0 : Finset ℕ} {T : ℕ} {p l1 l2 : List Stp} {s s' : Stp}
    (h : Mn F S0 T (p ++ (l1 ++ s :: l2))) (ho : out F s' = out F s) (hok : Ok (S0 ∪ outs F p) s')
    (hnt : nt s' = true → nt s = true) : Mn F S0 T ((p ++ [s']) ++ (l1 ++ l2)) := by
  obtain ⟨⟨hv, hn, ht⟩, hmin⟩ := h
  obtain ⟨hv1, hv2⟩ := val_append.1 hv
  obtain ⟨hv3, hv4⟩ := val_append.1 hv2
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [List.append_assoc, val_append]
    refine ⟨hv1, ?_⟩
    simp only [List.singleton_append]
    refine ⟨hok, ?_⟩
    rw [val_append]
    refine ⟨hv3.mono (Finset.subset_insert _ _), ?_⟩
    have := hv4.2
    rwa [← ho, ← Finset.insert_union] at this
  · simp only [List.countP_append, List.countP_cons, List.countP_nil] at hn ⊢
    by_cases h1 : nt s' = true
    · have := hnt h1
      simp only [h1, this] at hn ⊢; simp at hn ⊢; omega
    · simp only [h1] at hn ⊢; simp at hn ⊢; omega
  · simp only [outs_append, outs_cons, outs_nil, Finset.mem_union, Finset.mem_insert, ho] at ht ⊢
    tauto
  · intro l' hl'
    have := hmin l' hl'
    simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢
    omega

-- two bit positions on which every read element of the available set agrees
lemma agree {F : ℕ} {l : List Stp} {p q : ℕ} (hF : F.testBit p = F.testBit q) :
    ∀ {S : Finset ℕ}, Val F S l → (∀ c ∈ S, c ∈ ops l → c.testBit p = c.testBit q) →
      ∀ t ∈ outs F l, t.testBit p = t.testBit q := by
  induction l with
  | nil => intro S _ _ t ht; simp at ht
  | cons s l ih =>
    intro S hv hS t ht
    have ha := hS _ hv.1.1 (mem_ops.2 ⟨s, by simp, Or.inl rfl⟩)
    have hb := hS _ hv.1.2.1 (mem_ops.2 ⟨s, by simp, Or.inr rfl⟩)
    have ho : (out F s).testBit p = (out F s).testBit q := by
      unfold out
      split_ifs
      · rw [Nat.testBit_land, Nat.testBit_land, ha, hb]
      · rw [Nat.testBit_lor, Nat.testBit_lor, ha, hb]
      · rw [Nat.testBit_xor, Nat.testBit_xor, ha, hF]
    rw [outs_cons, Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · exact ho
    · refine ih hv.2 ?_ t ht
      intro c hc hcr
      rcases Finset.mem_insert.1 hc with rfl | hc
      · exact ho
      · obtain ⟨s', hs', h'⟩ := mem_ops.1 hcr
        exact hS c hc (mem_ops.2 ⟨s', by simp [hs'], h'⟩)

-- masked images
def img (M : ℕ) (S : Finset ℕ) : Finset ℕ := S.image (fun t => t &&& M)

lemma img_card_le {F M : ℕ} (l : List Stp) (S : Finset ℕ) :
    (img M (S ∪ outs F l)).card ≤ (img M S).card + l.length := by
  unfold img
  rw [Finset.image_union]
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : ((outs F l).image (fun t => t &&& M)).card ≤ l.length :=
    Finset.card_image_le.trans ((List.toFinset_card_le _).trans (by simp))
  omega

-- a collapsing step among the remaining ones costs one
lemma img_card_lt {F M : ℕ} {l1 l2 : List Stp} {s : Stp} {S : Finset ℕ}
    (h : (out F s) &&& M ∈ img M (S ∪ outs F (l1 ++ l2))) :
    (img M (S ∪ outs F (l1 ++ s :: l2))).card + 1 ≤ (img M S).card + (l1 ++ s :: l2).length := by
  have he : img M (S ∪ outs F (l1 ++ s :: l2)) = img M (S ∪ outs F (l1 ++ l2)) := by
    have : S ∪ outs F (l1 ++ s :: l2) = insert (out F s) (S ∪ outs F (l1 ++ l2)) := by
      simp only [outs_append, outs_cons, Finset.union_insert]
    rw [this]
    unfold img at h ⊢
    rw [Finset.image_insert, Finset.insert_eq_of_mem h]
  rw [he]
  have := img_card_le (F := F) (M := M) (l1 ++ l2) S
  simp only [List.length_append, List.length_cons] at this ⊢
  omega

-- a step reading an element that is constant under the mask collapses
lemma img_const {F M : ℕ} {l : List Stp} {S : Finset ℕ} {c : ℕ} (hv : Val F S l)
    (h0 : 0 ∈ S) (hFS : F ∈ S) (hFM : F &&& M = M) (hc : c ∈ ops l)
    (hcc : c &&& M = 0 ∨ c &&& M = M) :
    (img M (S ∪ outs F l)).card + 1 ≤ (img M S).card + l.length := by
  obtain ⟨s, hs, hr⟩ := mem_ops.1 hc
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hs
  apply img_card_lt
  obtain ⟨hv1, hv2⟩ := val_append.1 hv
  have hsub : S ∪ outs F l1 ⊆ S ∪ outs F (l1 ++ l2) := by
    rw [outs_append, ← Finset.union_assoc]; exact Finset.subset_union_left
  have ha : s.2.1 &&& M ∈ img M (S ∪ outs F (l1 ++ l2)) :=
    Finset.mem_image_of_mem _ (hsub hv2.1.1)
  have hb : s.2.2 &&& M ∈ img M (S ∪ outs F (l1 ++ l2)) :=
    Finset.mem_image_of_mem _ (hsub hv2.1.2.1)
  have hz : 0 ∈ img M (S ∪ outs F (l1 ++ l2)) := by
    exact Finset.mem_image.2 ⟨0, Finset.mem_union_left _ h0, Nat.zero_and M⟩
  have hM : M ∈ img M (S ∪ outs F (l1 ++ l2)) := by
    exact Finset.mem_image.2 ⟨F, Finset.mem_union_left _ hFS, hFM⟩
  have hand : (s.2.1 &&& s.2.2) &&& M = (s.2.1 &&& M) &&& (s.2.2 &&& M) := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_land]
    cases s.2.1.testBit i <;> cases s.2.2.testBit i <;> cases M.testBit i <;> rfl
  have hor : (s.2.1 ||| s.2.2) &&& M = (s.2.1 &&& M) ||| (s.2.2 &&& M) := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_land, Nat.testBit_lor]
    cases s.2.1.testBit i <;> cases s.2.2.testBit i <;> cases M.testBit i <;> rfl
  have hxor : (F ^^^ s.2.1) &&& M = M ^^^ (s.2.1 &&& M) := by
    rw [← hFM]
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_land, Nat.testBit_xor]
    cases s.2.1.testBit i <;> cases F.testBit i <;> cases M.testBit i <;> rfl
  have hMl : ∀ x : ℕ, M &&& (x &&& M) = x &&& M := by
    intro x
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_land]
    cases x.testBit i <;> cases M.testBit i <;> rfl
  have hMr : ∀ x : ℕ, (x &&& M) &&& M = x &&& M := by
    intro x
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_land]
    cases x.testBit i <;> cases M.testBit i <;> rfl
  have hMo : ∀ x : ℕ, M ||| (x &&& M) = M := by
    intro x
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_land, Nat.testBit_lor]
    cases x.testBit i <;> cases M.testBit i <;> rfl
  have hMo' : ∀ x : ℕ, (x &&& M) ||| M = M := by
    intro x
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_land, Nat.testBit_lor]
    cases x.testBit i <;> cases M.testBit i <;> rfl
  by_cases h0 : s.1 = 0
  · simp only [out, h0, ite_true, hand]
    rcases hr with rfl | rfl
    · rcases hcc with h | h
      · rw [h, Nat.zero_and]; exact hz
      · rw [h, hMl]; exact hb
    · rcases hcc with h | h
      · rw [h, Nat.and_zero]; exact hz
      · rw [h, hMr]; exact ha
  · by_cases h1 : s.1 = 1
    · simp only [out, h1, ite_true, ite_eq_right one_ne_zero, hor]
      rcases hr with rfl | rfl
      · rcases hcc with h | h
        · rw [h, Nat.zero_or]; exact hb
        · rw [h, hMo]; exact hM
      · rcases hcc with h | h
        · rw [h, Nat.or_zero]; exact ha
        · rw [h, hMo']; exact hM
    · have hn : nt s = true := by simp [nt, h0, h1]
      have hab := hv2.1.2.2 hn
      have hc1 : s.2.1 = c := by rcases hr with h | h; exact h; rw [hab]; exact h
      simp only [out, ite_eq_right h0, ite_eq_right h1, hxor]
      rw [hc1]
      rcases hcc with h | h
      · rw [h, Nat.xor_zero]; exact hM
      · rw [h, Nat.xor_self]; exact hz

-- the search, written with direct recursors so that the kernel evaluates it quickly
noncomputable def mem (t : ℕ) (L : List ℕ) : Bool :=
  List.rec false (fun h _ ih => cond (Nat.beq t h) true ih) L

noncomputable def prs (A B : List ℕ) : List (ℕ × ℕ) :=
  List.rec [] (fun a _ ih => List.rec ih (fun b _ ih2 => (a, b) :: ih2) B) A

noncomputable def ups (A : List ℕ) : List (ℕ × ℕ) :=
  List.rec [] (fun a L ih => List.rec ih (fun b _ ih2 => (a, b) :: ih2) L) A

def tb (X t : ℕ) : Bool := Nat.beq (Nat.land (Nat.shiftRight X t) 1) 1

-- record: mask, slack, images
abbrev RS := ℕ × ℕ × List ℕ

noncomputable def upd (t : ℕ) (R : List RS) : (List RS → Bool) → Bool :=
  List.rec (fun k => k [])
    (fun h _ ih => fun k =>
      cond (mem (Nat.land t h.1) h.2.2)
        (Nat.rec true (fun s _ => ih (fun R2 => k ((h.1, s, h.2.2) :: R2))) h.2.1)
        (ih (fun R2 => k ((h.1, h.2.1, Nat.land t h.1 :: h.2.2) :: R2)))) R

noncomputable def ksub (a b : ℕ) (K : List ℕ) : List ℕ :=
  List.rec [] (fun h _ ih => cond (Nat.beq h a) ih (cond (Nat.beq h b) ih (h :: ih))) K

-- forced elements: (element, the edges only it separates)
abbrev UL := List (ℕ × ℕ)

noncomputable def frc (v : ℕ) (U : UL) : List ℕ → UL → (List ℕ → UL → Bool) → Bool :=
  List.rec (fun KF U2 k => k KF U2)
    (fun h _ ih => fun KF U2 k =>
      cond (Nat.beq (Nat.land h.2 v) h.2) (ih KF U2 k)
        (cond (mem h.1 KF) (ih KF ((h.1, Nat.xor h.2 (Nat.land h.2 v)) :: U2) k)
          (ih (h.1 :: KF) ((h.1, Nat.xor h.2 (Nat.land h.2 v)) :: U2) k))) U

-- at most n elements, the remaining slack passed on
noncomputable def slk (K : List ℕ) : ℕ → (ℕ → Bool) → Bool :=
  List.rec (fun n k => k n) (fun _ _ ih => fun n k => Nat.rec true (fun m _ => ih m k) n) K

noncomputable def orv (sn : ℕ → ℕ) (K : List ℕ) : ℕ :=
  List.rec 0 (fun h _ ih => Nat.lor (sn h) ih) K

noncomputable def cst (M : ℕ) (K : List ℕ) : Bool :=
  List.rec false (fun c _ ih => cond (Nat.beq (Nat.land c M) 0) true
    (cond (Nat.beq (Nat.land c M) M) true ih)) K

noncomputable def pend (K : List ℕ) (R : List RS) : Bool :=
  List.rec false (fun h _ ih => cond (Nat.beq h.2.1 0) (cond (cst h.1 K) true ih) ih) R

def one (child : ℕ → ℕ → ℕ → ℕ → Bool) (t a b X : ℕ) (k : ℕ → Bool) : Bool :=
  cond (tb X t) (k X) (cond (child X t a b) (k (Nat.lor X (Nat.shiftLeft 1 t))) false)

noncomputable def lp2 (child : ℕ → ℕ → ℕ → ℕ → Bool) (Ps : List (ℕ × ℕ)) : ℕ → Bool :=
  List.rec (fun _ => true) (fun p _ ih => fun X =>
    one child (Nat.land p.1 p.2) p.1 p.2 X (fun Y => one child (Nat.lor p.1 p.2) p.1 p.2 Y ih)) Ps

noncomputable def lpn (child : ℕ → ℕ → Bool) (F X : ℕ) (N : List ℕ) : Bool :=
  List.rec true (fun a _ ih =>
    cond (tb X (Nat.xor F a)) ih (cond (child (Nat.xor F a) a) ih false)) N

abbrev ST := Bool → List ℕ → List ℕ → List ℕ → UL → List ℕ → ℕ → ℕ → List RS → Bool

-- r steps remain after adding t
noncomputable def chd (sn : ℕ → ℕ) (T EM : ℕ) (r : ℕ) (st : ST) (k : Bool) (t a b : ℕ)
    (S : List ℕ) (K : List ℕ) (U : UL) (X : ℕ) (R : List RS) : Bool :=
  cond (Nat.beq t T) false (Nat.rec true (fun _ _ =>
    upd t R (fun R2 =>
      (fun K2 => frc (sn t) U K2 [] (fun KF U2 =>
          slk KF (Nat.add r 1) (fun e =>
            cond (cond (Nat.beq e 0) (Nat.beq (Nat.land (orv sn KF) EM) EM) true)
              (cond (pend KF R2) true
                (st k [t] (t :: S) K2 U2 KF e (Nat.lor X (Nat.shiftLeft 1 t)) R2)) true)))
        (t :: ksub a b K))) r)

noncomputable def prl (S KF : List ℕ) (e : ℕ) : List (ℕ × ℕ) :=
  Nat.rec (ups KF) (fun e1 _ => Nat.rec (prs KF S) (fun _ _ => ups S) e1) e

noncomputable def srch (sn : ℕ → ℕ) (F T EM : ℕ) (r : ℕ) : ST :=
  Nat.rec (fun _ _ _ _ _ _ _ _ _ => true)
    (fun r st => fun k N S K U KF e X R =>
      cond (cond k (lpn (fun t a => chd sn T EM r st false t a a S K U X R) F X N) true)
        (lp2 (fun Y t a b => chd sn T EM r st k t a b S K U Y R) (prl S KF e) X)
        false) r

-- facts about the pieces
lemma mem_cons (t h : ℕ) (L : List ℕ) : mem t (h :: L) = cond (Nat.beq t h) true (mem t L) := rfl

lemma mem_iff (t : ℕ) (L : List ℕ) : mem t L = true ↔ t ∈ L := by
  induction L with
  | nil => simp [mem]
  | cons h L ih =>
    rw [mem_cons]
    cases hb : Nat.beq t h with
    | true => simp [Nat.eq_of_beq_eq_true hb]
    | false =>
      have hne := Nat.ne_of_beq_eq_false hb
      simp [ih, hne]

lemma mem_false (t : ℕ) (L : List ℕ) : mem t L = false ↔ t ∉ L := by
  rw [← mem_iff]; simp

lemma prs_nil (B : List ℕ) : prs [] B = [] := rfl

lemma prs_aux (a : ℕ) (B : List ℕ) (I : List (ℕ × ℕ)) :
    (List.rec I (fun b _ ih2 => (a, b) :: ih2) B : List (ℕ × ℕ)) = B.map (fun b => (a, b)) ++ I := by
  induction B with
  | nil => rfl
  | cons b B ih => simp only [List.map_cons, List.cons_append, ih]

lemma prs_cons (a : ℕ) (A B : List ℕ) : prs (a :: A) B = B.map (fun b => (a, b)) ++ prs A B :=
  prs_aux a B (prs A B)

lemma ups_cons (a : ℕ) (A : List ℕ) : ups (a :: A) = A.map (fun b => (a, b)) ++ ups A :=
  prs_aux a A (ups A)

lemma mem_prs {A B : List ℕ} {p : ℕ × ℕ} : p ∈ prs A B ↔ p.1 ∈ A ∧ p.2 ∈ B := by
  induction A with
  | nil => simp [prs_nil]
  | cons a A ih =>
    rw [prs_cons, List.mem_append, ih, List.mem_map, List.mem_cons]
    constructor
    · rintro (⟨b, hb, rfl⟩ | h)
      · exact ⟨Or.inl rfl, hb⟩
      · exact ⟨Or.inr h.1, h.2⟩
    · rintro ⟨rfl | h1, h2⟩
      · exact Or.inl ⟨p.2, h2, rfl⟩
      · exact Or.inr ⟨h1, h2⟩

lemma ups_sub {A : List ℕ} {p : ℕ × ℕ} (h : p ∈ ups A) : p.1 ∈ A ∧ p.2 ∈ A := by
  induction A with
  | nil => simp [ups] at h
  | cons a A ih =>
    rw [ups_cons, List.mem_append, List.mem_map] at h
    rcases h with ⟨b, hb, rfl⟩ | h
    · exact ⟨by simp, by simp [hb]⟩
    · exact ⟨List.mem_cons_of_mem _ (ih h).1, List.mem_cons_of_mem _ (ih h).2⟩

lemma mem_ups {A : List ℕ} {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    (a, b) ∈ ups A ∨ (b, a) ∈ ups A := by
  induction A with
  | nil => simp at ha
  | cons c A ih =>
    rw [ups_cons, List.mem_append, List.mem_append]
    rcases List.mem_cons.1 ha with rfl | ha'
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact absurd rfl hab
      · exact Or.inl (Or.inl (List.mem_map.2 ⟨b, hb', rfl⟩))
    · rcases List.mem_cons.1 hb with rfl | hb'
      · exact Or.inr (Or.inl (List.mem_map.2 ⟨a, ha', rfl⟩))
      · rcases ih ha' hb' with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr (Or.inr h)

lemma tb_eq (X t : ℕ) : tb X t = X.testBit t := by
  have h : Nat.land (Nat.shiftRight X t) 1 = X / 2 ^ t % 2 := by
    change (X >>> t) &&& 1 = _
    rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  unfold tb
  rw [h, Nat.testBit_eq_decide_div_mod_eq]
  by_cases hh : X / 2 ^ t % 2 = 1
  · rw [hh]; rfl
  · have : Nat.beq (X / 2 ^ t % 2) 1 = false := by
      cases hb : Nat.beq (X / 2 ^ t % 2) 1
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true hb) hh
    rw [this]; simp [hh]

lemma tb_ins (X t u : ℕ) : tb (Nat.lor X (Nat.shiftLeft 1 t)) u = (tb X u || decide (u = t)) := by
  rw [tb_eq, tb_eq]
  change (X ||| (1 <<< t)).testBit u = _
  rw [Nat.testBit_lor, Nat.one_shiftLeft, Nat.testBit_two_pow]
  congr 1
  simp [eq_comm]

-- records
def RecOk (F : ℕ) (h : RS) (S W : Finset ℕ) (r : ℕ) : Prop :=
  F &&& h.1 = h.1 ∧ h.2.2.toFinset = img h.1 S ∧ (img h.1 S).card + r ≤ (img h.1 W).card + h.2.1

lemma upd_cons (t : ℕ) (h : RS) (R : List RS) (k : List RS → Bool) : upd t (h :: R) k =
      cond (mem (Nat.land t h.1) h.2.2)
        (Nat.rec true (fun s _ => upd t R (fun R2 => k ((h.1, s, h.2.2) :: R2))) h.2.1)
        (upd t R (fun R2 => k ((h.1, h.2.1, Nat.land t h.1 :: h.2.2) :: R2))) := rfl

lemma upd_sound {F t r : ℕ} {S W : Finset ℕ}
    (hW : ∀ M, (img M W).card ≤ (img M (insert t S)).card + r) {R : List RS} :
    ∀ {k : List RS → Bool}, upd t R k = true → (∀ h ∈ R, RecOk F h S W (r + 1)) →
      ∃ R2, k R2 = true ∧ ∀ h ∈ R2, RecOk F h (insert t S) W r := by
  induction R with
  | nil => intro k hk _; exact ⟨[], hk, by simp⟩
  | cons h R ih =>
    obtain ⟨M, sl, I⟩ := h
    intro k hk hR
    obtain ⟨h1, h2, h3⟩ := hR _ (List.mem_cons_self ..)
    have hR' : ∀ h ∈ R, RecOk F h S W (r + 1) := fun h hh => hR h (List.mem_cons_of_mem _ hh)
    simp only at h1 h2 h3
    rw [upd_cons] at hk
    simp only at hk
    have hI : mem (Nat.land t M) I = true ↔ t &&& M ∈ img M S := by
      rw [mem_iff, ← h2, List.mem_toFinset]; rfl
    have hins : img M (insert t S) = insert (t &&& M) (img M S) := by
      unfold img; rw [Finset.image_insert]
    cases hm : mem (Nat.land t M) I with
    | true =>
      rw [hm] at hk
      have hin := hI.1 hm
      have he : img M (insert t S) = img M S := by rw [hins, Finset.insert_eq_of_mem hin]
      cases sl with
      | zero =>
        have := hW M
        rw [he] at this
        omega
      | succ s =>
        obtain ⟨R2, hk2, hR2⟩ := ih hk hR'
        refine ⟨_, hk2, ?_⟩
        intro h hh
        rcases List.mem_cons.1 hh with rfl | hh
        · refine ⟨h1, ?_, ?_⟩
          · simp only [he]; exact h2
          · simp only [he]; omega
        · exact hR2 h hh
    | false =>
      rw [hm] at hk
      have hin : t &&& M ∉ img M S := fun hh => by rw [hI.2 hh] at hm; cases hm
      obtain ⟨R2, hk2, hR2⟩ := ih hk hR'
      refine ⟨_, hk2, ?_⟩
      intro h hh
      rcases List.mem_cons.1 hh with rfl | hh
      · refine ⟨h1, ?_, ?_⟩
        · simp only [hins, List.toFinset_cons, h2]; rfl
        · simp only [hins]
          rw [Finset.card_insert_of_notMem hin]; omega
      · exact hR2 h hh

lemma ksub_cons (a b h : ℕ) (K : List ℕ) : ksub a b (h :: K) =
    cond (Nat.beq h a) (ksub a b K) (cond (Nat.beq h b) (ksub a b K) (h :: ksub a b K)) := rfl

lemma ksub_eq (a b : ℕ) (K : List ℕ) : ksub a b K = K.filter (fun h => h ≠ a ∧ h ≠ b) := by
  induction K with
  | nil => rfl
  | cons h K ih =>
    rw [ksub_cons, List.filter_cons, ih]
    cases ha : Nat.beq h a with
    | true => simp [Nat.eq_of_beq_eq_true ha]
    | false =>
      have hna := Nat.ne_of_beq_eq_false ha
      cases hb : Nat.beq h b with
      | true => simp [Nat.eq_of_beq_eq_true hb]
      | false =>
        have hnb := Nat.ne_of_beq_eq_false hb
        simp [hna, hnb]

lemma frc_cons (v : ℕ) (h : ℕ × ℕ) (U : UL) (KF : List ℕ) (U2 : UL) (k : List ℕ → UL → Bool) :
    frc v (h :: U) KF U2 k =
      cond (Nat.beq (Nat.land h.2 v) h.2) (frc v U KF U2 k)
        (cond (mem h.1 KF) (frc v U KF ((h.1, Nat.xor h.2 (Nat.land h.2 v)) :: U2) k)
          (frc v U (h.1 :: KF) ((h.1, Nat.xor h.2 (Nat.land h.2 v)) :: U2) k)) := rfl

lemma frc_sound {v : ℕ} {U : UL} : ∀ {KF : List ℕ} {U2 : UL} {k : List ℕ → UL → Bool},
    frc v U KF U2 k = true → KF.Nodup → ∃ KF' U2', k KF' U2' = true ∧ KF'.Nodup ∧
      (∀ c ∈ KF', c ∈ KF ∨ ∃ w, (c, w) ∈ U2') ∧ (∀ h ∈ U2, h ∈ U2') ∧
      (∀ h ∈ U2', h ∈ U2 ∨ ∃ h0 ∈ U, h.1 = h0.1 ∧ h.2 = h0.2 ^^^ (h0.2 &&& v) ∧ h0.2 &&& v ≠ h0.2) := by
  induction U with
  | nil =>
    intro KF U2 k hk hn
    exact ⟨KF, U2, hk, hn, fun c hc => Or.inl hc, fun h hh => hh, fun h hh => Or.inl hh⟩
  | cons h U ih =>
    intro KF U2 k hk hn
    rw [frc_cons] at hk
    cases hb : Nat.beq (Nat.land h.2 v) h.2 with
    | true =>
      rw [hb] at hk
      obtain ⟨KF', U2', g1, g2, g3, g4, g5⟩ := ih hk hn
      refine ⟨KF', U2', g1, g2, g3, g4, ?_⟩
      intro x hx
      rcases g5 x hx with hx | ⟨h0, h01, h02⟩
      · exact Or.inl hx
      · exact Or.inr ⟨h0, List.mem_cons_of_mem _ h01, h02⟩
    | false =>
      have hne : h.2 &&& v ≠ h.2 := Nat.ne_of_beq_eq_false hb
      rw [hb] at hk
      cases hm : mem h.1 KF with
      | true =>
        rw [hm] at hk
        obtain ⟨KF', U2', g1, g2, g3, g4, g5⟩ := ih hk hn
        refine ⟨KF', U2', g1, g2, g3, fun x hx => g4 x (List.mem_cons_of_mem _ hx), ?_⟩
        intro x hx
        rcases g5 x hx with hx | ⟨h0, h01, h02⟩
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact Or.inr ⟨h, List.mem_cons_self .., rfl, rfl, hne⟩
          · exact Or.inl hx
        · exact Or.inr ⟨h0, List.mem_cons_of_mem _ h01, h02⟩
      | false =>
        rw [hm] at hk
        obtain ⟨KF', U2', g1, g2, g3, g4, g5⟩ :=
          ih hk (List.nodup_cons.2 ⟨(mem_false _ _).1 hm, hn⟩)
        refine ⟨KF', U2', g1, g2, ?_, fun x hx => g4 x (List.mem_cons_of_mem _ hx), ?_⟩
        · intro c hc
          rcases g3 c hc with hc | hc
          · rcases List.mem_cons.1 hc with rfl | hc
            · exact Or.inr ⟨_, g4 _ (List.mem_cons_self ..)⟩
            · exact Or.inl hc
          · exact Or.inr hc
        · intro x hx
          rcases g5 x hx with hx | ⟨h0, h01, h02⟩
          · rcases List.mem_cons.1 hx with rfl | hx
            · exact Or.inr ⟨h, List.mem_cons_self .., rfl, rfl, hne⟩
            · exact Or.inl hx
          · exact Or.inr ⟨h0, List.mem_cons_of_mem _ h01, h02⟩

lemma slk_eq {K : List ℕ} : ∀ {n : ℕ} {k : ℕ → Bool}, K.length ≤ n →
    slk K n k = k (n - K.length) := by
  induction K with
  | nil => intro n k _; rfl
  | cons h K ih =>
    intro n k hn
    cases n with
    | zero => simp at hn
    | succ m =>
      have h1 : slk (h :: K) (m + 1) k = slk K m k := rfl
      rw [h1, ih (by simpa using hn)]
      simp

lemma orv_cons (sn : ℕ → ℕ) (h : ℕ) (K : List ℕ) : orv sn (h :: K) = sn h ||| orv sn K := rfl

lemma orv_bit {sn : ℕ → ℕ} {K : List ℕ} {i : ℕ} (h : ∀ c ∈ K, (sn c).testBit i = false) :
    (orv sn K).testBit i = false := by
  induction K with
  | nil => simp [orv]
  | cons c K ih =>
    rw [orv_cons, Nat.testBit_lor, h c (by simp), ih (fun c hc => h c (by simp [hc]))]; rfl

lemma cst_cons (M c : ℕ) (K : List ℕ) : cst M (c :: K) = cond (Nat.beq (Nat.land c M) 0) true
    (cond (Nat.beq (Nat.land c M) M) true (cst M K)) := rfl

lemma cst_sound {M : ℕ} {K : List ℕ} (h : cst M K = true) :
    ∃ c ∈ K, c &&& M = 0 ∨ c &&& M = M := by
  induction K with
  | nil => simp [cst] at h
  | cons c K ih =>
    rw [cst_cons] at h
    cases h0 : Nat.beq (Nat.land c M) 0 with
    | true => exact ⟨c, by simp, Or.inl (Nat.eq_of_beq_eq_true h0)⟩
    | false =>
      rw [h0] at h
      cases h1 : Nat.beq (Nat.land c M) M with
      | true => exact ⟨c, by simp, Or.inr (Nat.eq_of_beq_eq_true h1)⟩
      | false =>
        rw [h1] at h
        obtain ⟨c', hc', h'⟩ := ih h
        exact ⟨c', by simp [hc'], h'⟩

lemma pend_cons (K : List ℕ) (h : RS) (R : List RS) : pend K (h :: R) =
    cond (Nat.beq h.2.1 0) (cond (cst h.1 K) true (pend K R)) (pend K R) := rfl

lemma pend_sound {K : List ℕ} {R : List RS} (hp : pend K R = true) :
    ∃ h ∈ R, h.2.1 = 0 ∧ ∃ c ∈ K, c &&& h.1 = 0 ∨ c &&& h.1 = h.1 := by
  induction R with
  | nil => simp [pend] at hp
  | cons h R ih =>
    rw [pend_cons] at hp
    cases h0 : Nat.beq h.2.1 0 with
    | true =>
      rw [h0] at hp
      cases hc : cst h.1 K with
      | true => exact ⟨h, by simp, Nat.eq_of_beq_eq_true h0, cst_sound hc⟩
      | false =>
        rw [hc] at hp
        obtain ⟨h', hh', h''⟩ := ih hp
        exact ⟨h', by simp [hh'], h''⟩
    | false =>
      rw [h0] at hp
      obtain ⟨h', hh', h''⟩ := ih hp
      exact ⟨h', by simp [hh'], h''⟩

lemma one_sound {child : ℕ → ℕ → ℕ → ℕ → Bool} {O : Finset ℕ} {t a b X : ℕ} {k : ℕ → Bool}
    (hch : ∀ X, (∀ u ∈ O, tb X u = false) → child X t a b = true → t ∉ O)
    (h : one child t a b X k = true) (hX : ∀ u ∈ O, tb X u = false) :
    t ∉ O ∧ ∃ Y, k Y = true ∧ ∀ u ∈ O, tb Y u = false := by
  unfold one at h
  cases ht : tb X t with
  | true =>
    rw [ht] at h
    refine ⟨fun hh => ?_, X, h, hX⟩
    rw [hX t hh] at ht; cases ht
  | false =>
    rw [ht] at h
    cases hc : child X t a b with
    | true =>
      rw [hc] at h
      have hn := hch X hX hc
      refine ⟨hn, _, h, ?_⟩
      intro u hu
      rw [tb_ins, hX u hu]
      have : u ≠ t := fun hh => hn (hh ▸ hu)
      simp [this]
    | false => rw [hc] at h; cases h

lemma lp2_sound {child : ℕ → ℕ → ℕ → ℕ → Bool} {O : Finset ℕ} {Ps : List (ℕ × ℕ)}
    (hch : ∀ X, (∀ u ∈ O, tb X u = false) → ∀ p ∈ Ps,
      (child X (Nat.land p.1 p.2) p.1 p.2 = true → p.1 &&& p.2 ∉ O) ∧
      (child X (Nat.lor p.1 p.2) p.1 p.2 = true → p.1 ||| p.2 ∉ O)) :
    ∀ {X : ℕ}, lp2 child Ps X = true → (∀ u ∈ O, tb X u = false) →
      ∀ p ∈ Ps, p.1 &&& p.2 ∉ O ∧ p.1 ||| p.2 ∉ O := by
  induction Ps with
  | nil => intro X _ _ p hp; simp at hp
  | cons p0 Ps ih =>
    intro X h hX p hp
    have h' : one child (Nat.land p0.1 p0.2) p0.1 p0.2 X
      (fun Y => one child (Nat.lor p0.1 p0.2) p0.1 p0.2 Y (lp2 child Ps)) = true := h
    obtain ⟨g1, Y, hY, hY2⟩ := one_sound
      (fun X hX => (hch X hX p0 (List.mem_cons_self ..)).1) h' hX
    obtain ⟨g2, Z, hZ, hZ2⟩ := one_sound
      (fun X hX => (hch X hX p0 (List.mem_cons_self ..)).2) hY hY2
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨g1, g2⟩
    · exact ih (fun X hX p hp => hch X hX p (List.mem_cons_of_mem _ hp)) hZ hZ2 p hp

lemma lpn_sound {child : ℕ → ℕ → Bool} {F X : ℕ} {N : List ℕ} (h : lpn child F X N = true) :
    ∀ a ∈ N, tb X (F ^^^ a) = true ∨ child (F ^^^ a) a = true := by
  induction N with
  | nil => intro a ha; simp at ha
  | cons b N ih =>
    have h' : cond (tb X (F ^^^ b)) (lpn child F X N)
      (cond (child (F ^^^ b) b) (lpn child F X N) false) = true := h
    intro a ha
    cases ht : tb X (F ^^^ b) with
    | true =>
      rw [ht] at h'
      rcases List.mem_cons.1 ha with rfl | ha
      · exact Or.inl ht
      · exact ih h' a ha
    | false =>
      rw [ht] at h'
      cases hc : child (F ^^^ b) b with
      | true =>
        rw [hc] at h'
        rcases List.mem_cons.1 ha with rfl | ha
        · exact Or.inr hc
        · exact ih h' a ha
      | false => rw [hc] at h'; cases h'

-- the separation function: a zero bit means agreement on a pair of positions that T separates
def SnOk (sn : ℕ → ℕ) (F T EM : ℕ) : Prop :=
  ∀ i, EM.testBit i = true → ∃ p q, F.testBit p = F.testBit q ∧ T.testBit p ≠ T.testBit q ∧
    ∀ t, (sn t).testBit i = false → t.testBit p = t.testBit q

def UOk (sn : ℕ → ℕ) (EM : ℕ) (S : Finset ℕ) (U : UL) : Prop :=
  ∀ h ∈ U, h.1 ∈ S ∧ h.2 ≠ 0 ∧ ∀ i, h.2.testBit i = true →
    EM.testBit i = true ∧ ∀ c ∈ S, c ≠ h.1 → (sn c).testBit i = false

lemma uok_ops {sn : ℕ → ℕ} {F T EM : ℕ} (hsn : SnOk sn F T EM) {S : Finset ℕ} {U : UL}
    (hU : UOk sn EM S U) {l : List Stp} (hv : Val F S l) (hT : T ∈ outs F l) :
    ∀ h ∈ U, h.1 ∈ ops l := by
  intro h hh
  obtain ⟨_, h2, h3⟩ := hU h hh
  by_contra hn
  obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h2
  obtain ⟨hE, hc⟩ := h3 i hi
  obtain ⟨p, q, hF, hTT, ht⟩ := hsn i hE
  refine hTT (agree hF hv ?_ T hT)
  intro c hcS hco
  exact ht c (hc c hcS (fun he => hn (he ▸ hco)))

lemma uok_child {sn : ℕ → ℕ} {EM : ℕ} {S : Finset ℕ} {U U2 : UL} {t : ℕ}
    (hU : UOk sn EM S U)
    (h : ∀ h ∈ U2, ∃ h0 ∈ U, h.1 = h0.1 ∧ h.2 = h0.2 ^^^ (h0.2 &&& sn t) ∧ h0.2 &&& sn t ≠ h0.2) :
    UOk sn EM (insert t S) U2 := by
  intro x hx
  obtain ⟨h0, h01, h02, h03, h04⟩ := h x hx
  obtain ⟨g1, g2, g3⟩ := hU h0 h01
  refine ⟨?_, ?_, ?_⟩
  · rw [h02]; exact Finset.mem_insert_of_mem g1
  · rw [h03]; intro hz
    exact h04 (Nat.xor_eq_zero_iff.1 hz).symm
  · intro i hi
    rw [h03, Nat.testBit_xor, Nat.testBit_land] at hi
    have hi1 : h0.2.testBit i = true := by
      cases hh : h0.2.testBit i with
      | true => rfl
      | false => rw [hh] at hi; simp at hi
    have hi2 : (sn t).testBit i = false := by
      cases hh : (sn t).testBit i with
      | false => rfl
      | true => rw [hi1, hh] at hi; simp at hi
    obtain ⟨g4, g5⟩ := g3 i hi1
    refine ⟨g4, ?_⟩
    intro c hc hne
    rcases Finset.mem_insert.1 hc with rfl | hc
    · exact hi2
    · exact g5 c hc (by rw [← h02]; exact hne)

def Sound (sn : ℕ → ℕ) (F T EM : ℕ) (S0 : Finset ℕ) (r : ℕ) (st : ST) : Prop :=
  ∀ k N S K U KF e X R, st k N S K U KF e X R = true → ∀ pre l, Mn F S0 T (pre ++ l) →
    S.toFinset = S0 ∪ outs F pre → l.length ≤ r → T ∉ S →
    (∀ t ∈ outs F l, tb X t = false) → (k = false → ∀ s ∈ l, nt s = false) →
    (∀ s ∈ l, nt s = true → s.2.1 ∈ S → s.2.1 ∈ N) →
    (K.Nodup ∧ ∀ c ∈ K, c ∈ outs F pre ∧ c ∉ ops pre) →
    UOk sn EM S.toFinset U →
    (KF.Nodup ∧ (∀ c ∈ KF, c ∈ S ∧ c ∈ ops l) ∧ KF.length + e = r + 1) →
    (∀ h ∈ R, RecOk F h S.toFinset (S0 ∪ outs F (pre ++ l)) r) → False

lemma ops_append (p q : List Stp) : ops (p ++ q) = ops p ∪ ops q := by
  ext x
  simp only [Finset.mem_union, mem_ops, List.mem_append]
  constructor
  · rintro ⟨s, hs | hs, h⟩
    · exact Or.inl ⟨s, hs, h⟩
    · exact Or.inr ⟨s, hs, h⟩
  · rintro (⟨s, hs, h⟩ | ⟨s, hs, h⟩)
    · exact ⟨s, Or.inl hs, h⟩
    · exact ⟨s, Or.inr hs, h⟩

-- an output of the past that the past did not read is read later
lemma unread_ops {F : ℕ} {S0 : Finset ℕ} {T : ℕ} {pre l : List Stp} (hm : Mn F S0 T (pre ++ l))
    {c : ℕ} (hc : c ∈ outs F pre) (hcT : c ≠ T) (hr : c ∉ ops pre) : c ∈ ops l := by
  obtain ⟨s, hs, rfl⟩ := mem_outs.1 hc
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hs
  have := mn_read (p := l1) (q := l2 ++ l) (s := s) (by simpa using hm) hcT
  rw [ops_append] at this
  rcases Finset.mem_union.1 this with h | h
  · refine absurd ?_ hr
    rw [ops_append]
    obtain ⟨s', hs', h'⟩ := mem_ops.1 h
    exact Finset.mem_union_right _ (mem_ops.2 ⟨s', by simp [hs'], h'⟩)
  · exact h

set_option maxHeartbeats 2000000 in
lemma chd_sound {sn : ℕ → ℕ} {F T EM : ℕ} {S0 : Finset ℕ} {r : ℕ} {st : ST}
    (hsn : SnOk sn F T EM) (h0 : 0 ∈ S0) (hF : F ∈ S0) (hT0 : T ∉ S0)
    (hst : Sound sn F T EM S0 r st)
    {k : Bool} {t a b : ℕ} {S K : List ℕ} {U : UL} {X : ℕ} {R : List RS}
    (hc : chd sn T EM r st k t a b S K U X R = true)
    {pre l1 l2 : List Stp} {s s' : Stp}
    (hm : Mn F S0 T (pre ++ (l1 ++ s :: l2)))
    (hS : S.toFinset = S0 ∪ outs F pre) (hl : (l1 ++ s :: l2).length ≤ r + 1) (hTS : T ∉ S)
    (hX : ∀ t ∈ outs F (l1 ++ s :: l2), tb X t = false)
    (hk : k = false → ∀ s2 ∈ l1 ++ l2, nt s2 = false)
    (hN : ∀ s2 ∈ l1 ++ l2, nt s2 = true → s2.2.1 ∉ S)
    (hK : K.Nodup ∧ ∀ c ∈ K, c ∈ outs F pre ∧ c ∉ ops pre)
    (hU : UOk sn EM S.toFinset U)
    (hR : ∀ h ∈ R, RecOk F h S.toFinset (S0 ∪ outs F (pre ++ (l1 ++ s :: l2))) (r + 1))
    (hs' : s'.2 = (a, b)) (ho' : out F s' = out F s) (hot : out F s = t)
    (hok : Ok S.toFinset s') (hnt : nt s' = true → nt s = true) : False := by
  have hok' : Ok (S0 ∪ outs F pre) s' := hS ▸ hok
  have hm2 := mn_move hm ho' hok' hnt
  have hfr := mn_fresh hT0 hm
  have htn : t ∉ S0 ∪ outs F pre := by
    intro hh
    exact Finset.disjoint_left.1 hfr.1 hh (mem_outs.2 ⟨s, by simp, hot⟩)
  have hTo : T ∈ outs F (l1 ++ s :: l2) := by
    have := hm.1.2.2
    rw [outs_append, Finset.mem_union] at this
    rcases this with h | h
    · exact absurd (List.mem_toFinset.1 (hS ▸ Finset.mem_union_right _ h)) hTS
    · exact h
  unfold chd at hc
  cases hb : Nat.beq t T with
  | true => rw [hb] at hc; cases hc
  | false =>
  have htT : t ≠ T := Nat.ne_of_beq_eq_false hb
  rw [hb] at hc
  have hTo2 : T ∈ outs F (l1 ++ l2) := by
    rw [outs_append, outs_cons] at hTo
    rw [outs_append]
    simp only [Finset.mem_union, Finset.mem_insert] at hTo ⊢
    rcases hTo with h | rfl | h
    · exact Or.inl h
    · exact absurd hot.symm htT
    · exact Or.inr h
  have hlen2 : (l1 ++ l2).length ≤ r := by
    simp only [List.length_append, List.length_cons] at hl ⊢; omega
  cases r with
  | zero =>
    have : l1 ++ l2 = [] := List.length_eq_zero_iff.1 (by omega)
    rw [this] at hTo2; simp at hTo2
  | succ r =>
  change upd t R _ = true at hc
  have hout1 : outs F [s'] = {t} := by simp [outs, ho', hot]
  have hS2 : (t :: S).toFinset = S0 ∪ outs F (pre ++ [s']) := by
    rw [List.toFinset_cons, hS, outs_append, hout1, ← Finset.union_assoc, Finset.union_comm _ {t},
      Finset.insert_eq]
  have hWeq : S0 ∪ outs F (pre ++ (l1 ++ s :: l2)) = insert t S.toFinset ∪ outs F (l1 ++ l2) := by
    rw [hS]
    ext x
    simp only [outs_append, outs_cons, Finset.mem_union, Finset.mem_insert, hot]
    tauto
  have hWeq2 : S0 ∪ outs F (pre ++ (l1 ++ s :: l2)) =
      S0 ∪ outs F ((pre ++ [s']) ++ (l1 ++ l2)) := by
    ext x
    simp only [outs_append, outs_cons, outs_nil, Finset.mem_union, Finset.mem_insert, ho']
    tauto
  obtain ⟨R2, hc2, hR2⟩ := upd_sound (F := F) (S := S.toFinset)
    (W := S0 ∪ outs F (pre ++ (l1 ++ s :: l2))) (r := r + 1)
    (fun M => by rw [hWeq]; exact (img_card_le _ _).trans (by omega)) hc hR
  have hval2 : Val F (S0 ∪ outs F (pre ++ [s'])) (l1 ++ l2) := (val_append.1 hm2.1.1).2
  have hval1 : Val F S0 (pre ++ [s']) := (val_append.1 hm2.1.1).1
  have hprev : Val F S0 pre := (val_append.1 hval1).1
  have htpre : t ∉ ops pre := fun hh => htn (ops_sub hprev hh)
  have hab : a ∈ S ∧ b ∈ S := by
    have h1 := hok.1; have h2 := hok.2.1
    rw [hs'] at h1 h2
    exact ⟨List.mem_toFinset.1 h1, List.mem_toFinset.1 h2⟩
  have htS : t ∉ S := fun hh => htn (hS ▸ List.mem_toFinset.2 hh)
  have hops1 : ∀ c, c ∈ ops (pre ++ [s']) ↔ c ∈ ops pre ∨ c = a ∨ c = b := by
    intro c
    rw [ops_append, Finset.mem_union]
    refine or_congr Iff.rfl ?_
    rw [mem_ops]
    simp only [List.mem_singleton, exists_eq_left, hs']
    constructor
    · rintro (h | h) <;> simp [h]
    · rintro (h | h) <;> simp [h]
  have hK2 : (t :: ksub a b K).Nodup ∧
      ∀ c ∈ t :: ksub a b K, c ∈ outs F (pre ++ [s']) ∧ c ∉ ops (pre ++ [s']) := by
    rw [ksub_eq]
    refine ⟨List.nodup_cons.2 ⟨?_, hK.1.filter _⟩, ?_⟩
    · intro hh
      exact htn (Finset.mem_union_right _ (hK.2 t (List.mem_filter.1 hh).1).1)
    · intro c hcc
      rw [hops1, outs_append, hout1, Finset.mem_union, Finset.mem_singleton]
      rcases List.mem_cons.1 hcc with rfl | hcc
      · refine ⟨Or.inr rfl, ?_⟩
        rintro (h | rfl | rfl)
        · exact htpre h
        · exact htS hab.1
        · exact htS hab.2
      · obtain ⟨h1, h2⟩ := List.mem_filter.1 hcc
        simp only [ne_eq, decide_eq_true_eq] at h2
        refine ⟨Or.inl (hK.2 c h1).1, ?_⟩
        rintro (h | h | h)
        · exact (hK.2 c h1).2 h
        · exact h2.1 h
        · exact h2.2 h
  have hTS2 : T ∉ t :: S := by
    intro hh
    rcases List.mem_cons.1 hh with h | h
    · exact htT h.symm
    · exact hTS h
  obtain ⟨KF, U2, hc3, hn3, hKF3, _, hU3⟩ := frc_sound hc2 hK2.1
  have hU2 : UOk sn EM (t :: S).toFinset U2 := by
    rw [List.toFinset_cons]
    refine uok_child hU ?_
    intro h hh
    rcases hU3 h hh with h' | h'
    · simp at h'
    · exact h'
  have hval2' : Val F (t :: S).toFinset (l1 ++ l2) := hS2 ▸ hval2
  have hUops := uok_ops hsn hU2 hval2' hTo2
  have hKF : ∀ c ∈ KF, c ∈ t :: S ∧ c ∈ ops (l1 ++ l2) := by
    intro c hcc
    rcases hKF3 c hcc with h | ⟨w, h⟩
    · obtain ⟨g1, g2⟩ := hK2.2 c h
      have hcS : c ∈ t :: S := by
        rw [← List.mem_toFinset, hS2]; exact Finset.mem_union_right _ g1
      exact ⟨hcS, unread_ops hm2 g1 (fun he => hTS2 (he ▸ hcS)) g2⟩
    · exact ⟨List.mem_toFinset.1 (hU2 _ h).1, hUops _ h⟩
  have hrd := mn_rd hT0 hm2
  rw [← hS2] at hrd
  have hKFsub : KF.toFinset ⊆ ops (l1 ++ l2) ∩ (t :: S).toFinset := by
    intro c hcc
    have := hKF c (List.mem_toFinset.1 hcc)
    exact Finset.mem_inter.2 ⟨this.2, List.mem_toFinset.2 this.1⟩
  have hKFcard : KF.toFinset.card = KF.length := List.toFinset_card_of_nodup hn3
  have hKFlen : KF.length ≤ r + 1 + 1 := by
    have := Finset.card_le_card hKFsub
    omega
  change slk KF (r + 1 + 1) _ = true at hc3
  rw [slk_eq hKFlen] at hc3
  -- the hitting test
  have hhit : cond (Nat.beq (r + 1 + 1 - KF.length) 0) (Nat.beq (Nat.land (orv sn KF) EM) EM) true
      = true := by
    cases he : Nat.beq (r + 1 + 1 - KF.length) 0 with
    | false => rfl
    | true =>
      have he' := Nat.eq_of_beq_eq_true he
      have heq : KF.toFinset = ops (l1 ++ l2) ∩ (t :: S).toFinset := by
        apply Finset.eq_of_subset_of_card_le hKFsub
        omega
      have hand : Nat.land (orv sn KF) EM = EM := by
        change orv sn KF &&& EM = EM
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_land]
        cases hE : EM.testBit i with
        | false => simp
        | true =>
          rw [Bool.and_true]
          by_contra hne
          have hne' : (orv sn KF).testBit i = false := by simpa using hne
          obtain ⟨p, q, hFp, hTT, ht⟩ := hsn i hE
          refine hTT (agree hFp hval2' ?_ T hTo2)
          intro c hcS hco
          apply ht
          have hcK : c ∈ KF := by
            rw [← List.mem_toFinset, heq]; exact Finset.mem_inter.2 ⟨hco, hcS⟩
          cases hh : (sn c).testBit i with
          | false => rfl
          | true =>
            exfalso
            clear hc3 hKF3 hn3 hKF hKFsub hKFcard hKFlen he he' heq
            revert hne' hcK
            clear hne
            induction KF with
            | nil => intro _ h; simp at h
            | cons d KF ih =>
              rw [orv_cons, Nat.testBit_lor]
              intro h1 h2
              rw [Bool.or_eq_false_iff] at h1
              rcases List.mem_cons.1 h2 with rfl | h2
              · rw [hh] at h1; exact absurd h1.1 (by simp)
              · exact ih h1.2 h2
      rw [hand]
      exact Nat.beq_refl EM
  simp only [hhit, Bool.cond_true] at hc3
  cases hp : pend KF R2 with
  | true =>
    obtain ⟨h, hh, hz, c, hcK, hcc⟩ := pend_sound hp
    obtain ⟨g1, g2, g3⟩ := hR2 h hh
    have h02 : 0 ∈ (t :: S).toFinset := hS2 ▸ Finset.mem_union_left _ h0
    have hF2 : F ∈ (t :: S).toFinset := hS2 ▸ Finset.mem_union_left _ hF
    have := img_const hval2' h02 hF2 g1 (hKF c hcK).2 hcc
    rw [hWeq, ← List.toFinset_cons] at g3
    omega
  | false =>
    rw [hp] at hc3
    refine hst _ _ _ _ _ _ _ _ _ hc3 (pre ++ [s']) (l1 ++ l2) hm2 hS2 hlen2 hTS2 ?_ hk ?_ hK2 hU2
      ⟨hn3, hKF, ?_⟩ ?_
    · intro u hu
      rw [tb_ins]
      have hu1 : u ∈ outs F (l1 ++ s :: l2) := by
        rw [outs_append] at hu
        rw [outs_append, outs_cons]
        simp only [Finset.mem_union, Finset.mem_insert] at hu ⊢
        tauto
      rw [hX u hu1]
      have hne : u ≠ t := by
        rintro rfl
        have := (mn_fresh hT0 hm2).1
        refine Finset.disjoint_left.1 this ?_ hu
        rw [outs_append, hout1]; simp
      simp [hne]
    · intro s2 hs2 hn2 hin
      rcases List.mem_cons.1 hin with h | h
      · simp [h]
      · exact absurd h (hN s2 hs2 hn2)
    · omega
    · intro h hh
      rw [← hWeq2, List.toFinset_cons]
      exact hR2 h hh

set_option maxHeartbeats 2000000 in
lemma srch_sound {sn : ℕ → ℕ} {F T EM : ℕ} {S0 : Finset ℕ}
    (hsn : SnOk sn F T EM) (h0 : 0 ∈ S0) (hF : F ∈ S0) (hT0 : T ∉ S0) (r : ℕ) :
    Sound sn F T EM S0 r (srch sn F T EM r) := by
  induction r with
  | zero =>
    intro k N S K U KF e X R _ pre l hm hS hl hTS
    intros
    have : l = [] := List.length_eq_zero_iff.1 (by omega)
    subst this
    have := hm.1.2.2
    rw [List.append_nil] at this
    exact hTS (List.mem_toFinset.1 (hS ▸ Finset.mem_union_right _ this))
  | succ r ih =>
    intro k N S K U KF e X R hst pre l hm hS hl hTS hX hk hN hK hU hKF hR
    have hst' : cond (cond k
        (lpn (fun t a => chd sn T EM r (srch sn F T EM r) false t a a S K U X R) F X N) true)
        (lp2 (fun Y t a b => chd sn T EM r (srch sn F T EM r) k t a b S K U Y R) (prl S KF e) X)
        false = true := hst
    have hval : Val F S.toFinset l := hS ▸ (val_append.1 hm.1.1).2
    have hfr := mn_fresh hT0 hm
    have hTo : T ∈ outs F l := by
      have := hm.1.2.2
      rw [outs_append, Finset.mem_union] at this
      rcases this with h | h
      · exact absurd (List.mem_toFinset.1 (hS ▸ Finset.mem_union_right _ h)) hTS
      · exact h
    have hn1 : l.countP nt ≤ 1 := by
      have := hm.1.2.1
      rw [List.countP_append] at this; omega
    cases hcn : (cond k
        (lpn (fun t a => chd sn T EM r (srch sn F T EM r) false t a a S K U X R) F X N) true) with
    | false => rw [hcn] at hst'; cases hst'
    | true =>
    rw [hcn] at hst'
    -- no negation step among the remaining ones reads an available element
    have hnone : ∀ s ∈ l, nt s = true → s.2.1 ∉ S := by
      intro s hs hns hin
      cases k with
      | false => have := hk rfl s hs; rw [hns] at this; cases this
      | true =>
        have haN := hN s hs hns hin
        obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hs
        have hout : out F s = F ^^^ s.2.1 := by
          have h1 : s.1 ≠ 0 := by intro h; simp [nt, h] at hns
          have h2 : s.1 ≠ 1 := by intro h; simp [nt, h] at hns
          simp [out, h1, h2]
        have hnol : ∀ s2 ∈ l1 ++ l2, nt s2 = false := by
          intro s2 hs2
          have hcnt : (l1 ++ l2).countP nt = 0 := by
            rw [List.countP_append, List.countP_cons_of_pos hns] at hn1
            rw [List.countP_append]; omega
          have := List.countP_eq_zero.1 hcnt s2 hs2
          simpa using this
        change lpn (fun t a => chd sn T EM r (srch sn F T EM r) false t a a S K U X R) F X N = true at hcn
        rcases lpn_sound hcn s.2.1 haN with h | h
        · rw [← hout, hX _ (mem_outs.2 ⟨s, by simp, rfl⟩)] at h; cases h
        · have hs22 : s.2.2 = s.2.1 := by
            have hv := (val_append.1 hval).2
            exact (hv.1.2.2 hns).symm
          refine chd_sound hsn h0 hF hT0 ih h hm hS hl hTS hX (fun _ => hnol) ?_ hK hU hR
            (s' := (s.1, s.2.1, s.2.1)) rfl ?_ hout ⟨?_, ?_, fun _ => rfl⟩ ?_
          · intro s2 hs2 hn2
            rw [hnol s2 hs2] at hn2; cases hn2
          · simp [out, hs22]
          · exact List.mem_toFinset.2 hin
          · exact List.mem_toFinset.2 hin
          · intro _; exact hns
    have hpairs : ∀ p ∈ prl S KF e, p.1 ∈ S ∧ p.2 ∈ S := by
      intro p hp
      match e, hp with
      | 0, hp =>
        have := ups_sub (A := KF) hp
        exact ⟨(hKF.2.1 _ this.1).1, (hKF.2.1 _ this.2).1⟩
      | 1, hp =>
        have := mem_prs.1 hp
        exact ⟨(hKF.2.1 _ this.1).1, this.2⟩
      | (n + 2), hp => exact ups_sub (A := S) hp
    have hchild : ∀ Y, (∀ u ∈ outs F l, tb Y u = false) → ∀ p ∈ prl S KF e, ∀ c t,
        (c = 0 ∧ t = p.1 &&& p.2) ∨ (c = 1 ∧ t = p.1 ||| p.2) →
        chd sn T EM r (srch sn F T EM r) k t p.1 p.2 S K U Y R = true → t ∉ outs F l := by
      intro Y hY p hp c t hct hch htin
      obtain ⟨s, hs, hst⟩ := mem_outs.1 htin
      obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hs
      obtain ⟨hp1, hp2⟩ := hpairs p hp
      have hntc : nt (c, p.1, p.2) = false := by
        rcases hct with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
      refine chd_sound hsn h0 hF hT0 ih hch hm hS hl hTS hY ?_ ?_ hK hU hR
        (s' := (c, p.1, p.2)) rfl ?_ hst ⟨List.mem_toFinset.2 hp1, List.mem_toFinset.2 hp2, ?_⟩ ?_
      · intro hkk s2 hs2
        refine hk hkk s2 ?_
        simp only [List.mem_append, List.mem_cons] at hs2 ⊢; tauto
      · intro s2 hs2
        refine hnone s2 ?_
        simp only [List.mem_append, List.mem_cons] at hs2 ⊢; tauto
      · rw [hst]
        rcases hct with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [out]
      · intro hh; rw [hntc] at hh; cases hh
      · intro hh; rw [hntc] at hh; cases hh
    have hloop := lp2_sound (O := outs F l) (Ps := prl S KF e)
      (child := fun Y t a b => chd sn T EM r (srch sn F T EM r) k t a b S K U Y R)
      (fun Y hY p hp => ⟨fun hh => hchild Y hY p hp 0 _ (Or.inl ⟨rfl, rfl⟩) hh,
        fun hh => hchild Y hY p hp 1 _ (Or.inr ⟨rfl, rfl⟩) hh⟩) hst' hX
    -- the first remaining step is a candidate
    cases l with
    | nil => simp at hTo
    | cons s1 l =>
    have ha : s1.2.1 ∈ S := List.mem_toFinset.1 hval.1.1
    have hb : s1.2.2 ∈ S := List.mem_toFinset.1 hval.1.2.1
    have hn1 : nt s1 = false := by
      cases hh : nt s1 with
      | false => rfl
      | true => exact absurd ha (hnone s1 (List.mem_cons_self ..) hh)
    have hout : out F s1 ∈ outs F (s1 :: l) := mem_outs.2 ⟨s1, List.mem_cons_self .., rfl⟩
    have hoc : out F s1 = s1.2.1 &&& s1.2.2 ∨ out F s1 = s1.2.1 ||| s1.2.2 := by
      unfold out
      by_cases h1 : s1.1 = 0
      · exact Or.inl (by simp [h1])
      · by_cases h2 : s1.1 = 1
        · exact Or.inr (by simp [h2])
        · simp [nt, h1, h2] at hn1
    have hne : s1.2.1 ≠ s1.2.2 := by
      intro he
      have : out F s1 = s1.2.1 := by
        rcases hoc with h | h
        · rw [h, ← he, Nat.and_self]
        · rw [h, ← he, Nat.or_self]
      refine Finset.disjoint_left.1 hfr.1 ?_ hout
      rw [this, ← hS]
      exact List.mem_toFinset.2 ha
    have hop1 : s1.2.1 ∈ ops (s1 :: l) := mem_ops.2 ⟨s1, List.mem_cons_self .., Or.inl rfl⟩
    have hop2 : s1.2.2 ∈ ops (s1 :: l) := mem_ops.2 ⟨s1, List.mem_cons_self .., Or.inr rfl⟩
    have hmem : (s1.2.1, s1.2.2) ∈ prl S KF e ∨ (s1.2.2, s1.2.1) ∈ prl S KF e := by
      have hrd := mn_rd hT0 hm
      rw [← hS] at hrd
      obtain ⟨hKn, hKs, hKl⟩ := hKF
      have hKFsub : KF.toFinset ⊆ ops (s1 :: l) ∩ S.toFinset := by
        intro c hcc
        have := hKs c (List.mem_toFinset.1 hcc)
        exact Finset.mem_inter.2 ⟨this.2, List.mem_toFinset.2 this.1⟩
      have hKFcard : KF.toFinset.card = KF.length := List.toFinset_card_of_nodup hKn
      have hI1 : s1.2.1 ∈ ops (s1 :: l) ∩ S.toFinset :=
        Finset.mem_inter.2 ⟨hop1, List.mem_toFinset.2 ha⟩
      have hI2 : s1.2.2 ∈ ops (s1 :: l) ∩ S.toFinset :=
        Finset.mem_inter.2 ⟨hop2, List.mem_toFinset.2 hb⟩
      match e, hKl with
      | 0, hKl =>
        have heq : KF.toFinset = ops (s1 :: l) ∩ S.toFinset := by
          apply Finset.eq_of_subset_of_card_le hKFsub; omega
        rw [← heq] at hI1 hI2
        exact mem_ups (List.mem_toFinset.1 hI1) (List.mem_toFinset.1 hI2) hne
      | 1, hKl =>
        by_cases h1 : s1.2.1 ∈ KF
        · exact Or.inl (mem_prs.2 ⟨h1, hb⟩)
        · by_cases h2 : s1.2.2 ∈ KF
          · exact Or.inr (mem_prs.2 ⟨h2, ha⟩)
          · exfalso
            have hsub : insert s1.2.1 (insert s1.2.2 KF.toFinset) ⊆ ops (s1 :: l) ∩ S.toFinset := by
              intro c hcc
              rcases Finset.mem_insert.1 hcc with rfl | hcc
              · exact hI1
              · rcases Finset.mem_insert.1 hcc with rfl | hcc
                · exact hI2
                · exact hKFsub hcc
            have := Finset.card_le_card hsub
            rw [Finset.card_insert_of_notMem (by simp [hne, h1]),
              Finset.card_insert_of_notMem (by simp [h2])] at this
            omega
      | (n + 2), _ => exact mem_ups ha hb hne
    rcases hmem with h | h
    · have := hloop _ h
      rcases hoc with h' | h'
      · rw [h'] at hout; exact this.1 hout
      · rw [h'] at hout; exact this.2 hout
    · have := hloop _ h
      rcases hoc with h' | h'
      · rw [h', Nat.land_comm] at hout; exact this.1 hout
      · rw [h', Nat.lor_comm] at hout; exact this.2 hout

-- homomorphisms of tables
def Hom (h : ℕ → ℕ) (F F' : ℕ) : Prop :=
  (∀ a b, h (a &&& b) = h a &&& h b) ∧ (∀ a b, h (a ||| b) = h a ||| h b) ∧
    (∀ a, h (F ^^^ a) = F' ^^^ h a)

def ms (h : ℕ → ℕ) (s : Stp) : Stp := (s.1, h s.2.1, h s.2.2)

lemma out_ms {h : ℕ → ℕ} {F F' : ℕ} (hh : Hom h F F') (s : Stp) :
    out F' (ms h s) = h (out F s) := by
  unfold out ms
  simp only
  split_ifs
  · rw [hh.1]
  · rw [hh.2.1]
  · rw [hh.2.2]

lemma val_ms {h : ℕ → ℕ} {F F' : ℕ} (hh : Hom h F F') {l : List Stp} : ∀ {S : Finset ℕ},
    Val F S l → Val F' (S.image h) (l.map (ms h)) := by
  induction l with
  | nil => intros; trivial
  | cons s l ih =>
    intro S hv
    obtain ⟨⟨h1, h2, h3⟩, hv2⟩ := hv
    refine ⟨⟨Finset.mem_image_of_mem _ h1, Finset.mem_image_of_mem _ h2, ?_⟩, ?_⟩
    · intro hn
      have := h3 hn
      simp only [ms, this]
    · have := ih hv2
      rw [Finset.image_insert, ← out_ms hh] at this
      exact this

lemma outs_ms {h : ℕ → ℕ} {F F' : ℕ} (hh : Hom h F F') (l : List Stp) :
    outs F' (l.map (ms h)) = (outs F l).image h := by
  induction l with
  | nil => simp
  | cons s l ih => rw [List.map_cons, outs_cons, outs_cons, Finset.image_insert, ih, out_ms hh]

lemma countP_ms (h : ℕ → ℕ) (l : List Stp) : (l.map (ms h)).countP nt = l.countP nt := by
  rw [List.countP_map]; rfl

lemma ch_ms {h : ℕ → ℕ} {F F' : ℕ} (hh : Hom h F F') {S : Finset ℕ} {T : ℕ} {l : List Stp}
    (hc : Ch F S T l) : Ch F' (S.image h) (h T) (l.map (ms h)) := by
  refine ⟨val_ms hh hc.1, ?_, ?_⟩
  · rw [countP_ms]; exact hc.2.1
  · rw [outs_ms hh]; exact Finset.mem_image_of_mem _ hc.2.2

lemma dedup {F : ℕ} {l : List Stp} : ∀ {S : Finset ℕ}, Val F S l →
    ∃ l', Val F S l' ∧ l'.countP nt ≤ l.countP nt ∧ S ∪ outs F l' = S ∪ outs F l ∧
      S.card + l'.length ≤ (S ∪ outs F l).card := by
  induction l with
  | nil => intro S _; exact ⟨[], trivial, le_refl _, rfl, by simp⟩
  | cons s l ih =>
    intro S hv
    by_cases hs : out F s ∈ S
    · have hv2 := hv.2
      rw [Finset.insert_eq_of_mem hs] at hv2
      obtain ⟨l', h1, h2, h3, h4⟩ := ih hv2
      have he : S ∪ outs F (s :: l) = S ∪ outs F l := by
        rw [outs_cons, Finset.union_insert, Finset.insert_eq_of_mem]
        exact Finset.mem_union_left _ hs
      refine ⟨l', h1, ?_, by rw [he, h3], by rw [he]; exact h4⟩
      rw [List.countP_cons]; omega
    · obtain ⟨l', h1, h2, h3, h4⟩ := ih hv.2
      refine ⟨s :: l', ⟨hv.1, h1⟩, ?_, ?_, ?_⟩
      · rw [List.countP_cons, List.countP_cons]; omega
      · rw [outs_cons, outs_cons, Finset.union_insert, Finset.union_insert, ← Finset.insert_union,
          ← Finset.insert_union, h3]
      · rw [Finset.card_insert_of_notMem hs, Finset.insert_union, ← Finset.union_insert,
          ← outs_cons] at h4
        simp only [List.length_cons]; omega

lemma fact_card {h : ℕ → ℕ} {F F' : ℕ} (hh : Hom h F F') {S S' : Finset ℕ} {T T' L : ℕ}
    (hS : S.image h = S') (hT : h T = T') (hT' : T' ∉ S')
    (hL : ∀ l, Ch F' S' T' l → L ≤ l.length) {l : List Stp} (hc : Ch F S T l) :
    S'.card + L ≤ ((S ∪ outs F l).image h).card := by
  obtain ⟨h1, h2, h3⟩ := ch_ms hh hc
  rw [hS] at h1
  rw [hT] at h3
  obtain ⟨l', g1, g2, g3, g4⟩ := dedup h1
  have hin : T' ∈ outs F' l' := by
    have : T' ∈ S' ∪ outs F' l' := by rw [g3]; exact Finset.mem_union_right _ h3
    rcases Finset.mem_union.1 this with h | h
    · exact absurd h hT'
    · exact h
  have := hL l' ⟨g1, g2.trans h2, hin⟩
  rw [Finset.image_union, hS, ← outs_ms hh]
  omega

-- selection of bit positions
noncomputable def sel (L : List ℕ) (t : ℕ) : ℕ :=
  List.rec 0 (fun i _ ih => cond (tb t i) (Nat.add (Nat.mul 2 ih) 1) (Nat.mul 2 ih)) L

lemma sel_nil (t : ℕ) : sel [] t = 0 := rfl

lemma sel_cons (i : ℕ) (L : List ℕ) (t : ℕ) : sel (i :: L) t = Nat.bit (t.testBit i) (sel L t) := by
  rw [← tb_eq]; rfl

lemma sel_and (L : List ℕ) (a b : ℕ) : sel L (a &&& b) = sel L a &&& sel L b := by
  induction L with
  | nil => simp [sel_nil]
  | cons i L ih => rw [sel_cons, sel_cons, sel_cons, Nat.land_bit, ih, Nat.testBit_land]

lemma sel_or (L : List ℕ) (a b : ℕ) : sel L (a ||| b) = sel L a ||| sel L b := by
  induction L with
  | nil => simp [sel_nil]
  | cons i L ih => rw [sel_cons, sel_cons, sel_cons, Nat.lor_bit, ih, Nat.testBit_lor]

lemma sel_xor (L : List ℕ) (a b : ℕ) : sel L (a ^^^ b) = sel L a ^^^ sel L b := by
  induction L with
  | nil => simp [sel_nil]
  | cons i L ih =>
    rw [sel_cons, sel_cons, sel_cons, Nat.xor_bit, ih, Nat.testBit_xor]

lemma sel_hom (L : List ℕ) (F : ℕ) : Hom (sel L) F (sel L F) :=
  ⟨sel_and L, sel_or L, fun a => sel_xor L F a⟩

lemma sel_mask {L : List ℕ} {M : ℕ} (h : ∀ i ∈ L, M.testBit i = true) (t : ℕ) :
    sel L (t &&& M) = sel L t := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    rw [sel_cons, sel_cons, ih (fun j hj => h j (List.mem_cons_of_mem _ hj)), Nat.testBit_land,
      h i (List.mem_cons_self ..), Bool.and_true]

lemma sel_bit {L : List ℕ} : ∀ {t i : ℕ}, (hi : i < L.length) → (sel L t).testBit i = t.testBit L[i] := by
  induction L with
  | nil => intro t i hi; simp at hi
  | cons j L ih =>
    intro t i hi
    rw [sel_cons]
    cases i with
    | zero => rw [Nat.testBit_bit_zero]; rfl
    | succ i =>
      rw [Nat.testBit_bit_succ]
      simp only [List.getElem_cons_succ]
      exact ih (by simpa using hi)

-- separation functions built from two lists of positions
noncomputable def snl (P Q : List ℕ) (t : ℕ) : ℕ := Nat.xor (sel P t) (sel Q t)

lemma snl_bit {P Q : List ℕ} {n : ℕ} (hP : P.length = n) (hQ : Q.length = n) {t i : ℕ} (hi : i < n) :
    (snl P Q t).testBit i = (t.testBit (P.getD i 0) ^^ t.testBit (Q.getD i 0)) := by
  have h1 : (snl P Q t).testBit i = (sel P t ^^^ sel Q t).testBit i := rfl
  rw [h1, Nat.testBit_xor, sel_bit (hP ▸ hi), sel_bit (hQ ▸ hi),
    List.getD_eq_getElem _ _ (hP ▸ hi), List.getD_eq_getElem _ _ (hQ ▸ hi)]

lemma sn_ok {sn : ℕ → ℕ} {P Q : List ℕ} {F T EM n : ℕ}
    (hsn : ∀ t i, i < n → (sn t).testBit i = (t.testBit (P.getD i 0) ^^ t.testBit (Q.getD i 0)))
    (hE : EM < 2 ^ n)
    (h : ∀ i < n, F.testBit (P.getD i 0) = F.testBit (Q.getD i 0) ∧
      T.testBit (P.getD i 0) ≠ T.testBit (Q.getD i 0)) : SnOk sn F T EM := by
  intro i hi
  have hin : i < n := by
    by_contra hge
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hE (Nat.pow_le_pow_right (by norm_num)
      (not_lt.1 hge)))] at hi
    cases hi
  refine ⟨_, _, (h i hin).1, (h i hin).2, ?_⟩
  intro t ht
  rw [hsn t i hin] at ht
  simpa using ht

noncomputable def bmp (L : List ℕ) : ℕ :=
  List.rec 0 (fun h _ ih => Nat.lor ih (Nat.shiftLeft 1 h)) L

lemma tb_bmp (L : List ℕ) (t : ℕ) : tb (bmp L) t = decide (t ∈ L) := by
  induction L with
  | nil => rw [tb_eq]; simp [bmp]
  | cons h L ih =>
    have : bmp (h :: L) = Nat.lor (bmp L) (Nat.shiftLeft 1 h) := rfl
    rw [this, tb_ins, ih]
    by_cases h1 : t = h <;> simp [h1]

-- the root of the search
lemma root_lb {sn : ℕ → ℕ} {F T EM : ℕ} {S : List ℕ} {U : UL} {KF : List ℕ} {e r : ℕ} {R : List RS}
    (hsn : SnOk sn F T EM) (h0 : 0 ∈ S) (hF : F ∈ S) (hT : T ∉ S) (hU : UOk sn EM S.toFinset U)
    (hKF : KF.Nodup ∧ (∀ c ∈ KF, ∃ h ∈ U, h.1 = c) ∧ KF.length + e = r + 1)
    (hR : ∀ l, Ch F S.toFinset T l → ∀ h ∈ R, RecOk F h S.toFinset (S.toFinset ∪ outs F l) r)
    (hs : srch sn F T EM r true S S [] U KF e (bmp S) R = true) :
    ∀ l, Ch F S.toFinset T l → r + 1 ≤ l.length := by
  intro l hc
  by_contra hlt
  obtain ⟨m, hm, hml⟩ := exists_mn hc
  have hT' : T ∉ S.toFinset := by simpa using hT
  have hfr := mn_fresh (p := []) (l := m) hT' (by simpa using hm)
  refine srch_sound hsn (List.mem_toFinset.2 h0) (List.mem_toFinset.2 hF) hT' r
    true S S [] U KF e (bmp S) R hs [] m (by simpa using hm) (by simp) (by omega) hT ?_ ?_ ?_ ?_ hU ?_ ?_
  · intro t ht
    rw [tb_bmp]
    have : t ∉ S := fun hh => Finset.disjoint_left.1 hfr.1 (by simp [hh]) ht
    simp [this]
  · intro h; cases h
  · intro s _ _ h; exact h
  · simp
  · refine ⟨hKF.1, ?_, hKF.2.2⟩
    intro c hcc
    obtain ⟨h, hh, rfl⟩ := hKF.2.1 c hcc
    exact ⟨List.mem_toFinset.1 (hU h hh).1, uok_ops hsn hU hm.1.1 hm.1.2.2 h hh⟩
  · intro h hh
    simpa using hR m hm.1 h hh

-- the bound from forced reads alone
lemma read_lb {sn : ℕ → ℕ} {F T EM : ℕ} {S : List ℕ} {U : UL} {n : ℕ}
    (hsn : SnOk sn F T EM) (hT : T ∉ S) (hU : UOk sn EM S.toFinset U)
    (hn : (U.map Prod.fst).toFinset.card = n + 1) :
    ∀ l, Ch F S.toFinset T l → n ≤ l.length := by
  intro l hc
  obtain ⟨m, hm, hml⟩ := exists_mn hc
  have hT' : T ∉ S.toFinset := by simpa using hT
  have hrd := mn_rd (p := []) (l := m) hT' (by simpa using hm)
  have hsub : (U.map Prod.fst).toFinset ⊆ ops m ∩ (S.toFinset ∪ outs F []) := by
    intro c hcc
    obtain ⟨h, hh, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hcc)
    refine Finset.mem_inter.2 ⟨uok_ops hsn hU hm.1.1 hm.1.2.2 h hh, ?_⟩
    simp only [outs_nil, Finset.union_empty]
    exact (hU h hh).1
  have := Finset.card_le_card hsub
  omega

-- a decidable form of the condition on forced elements
lemma uok_of {sn : ℕ → ℕ} {EM : ℕ} {S : List ℕ} {U : UL}
    (h : ∀ h ∈ U, h.1 ∈ S ∧ h.2 ≠ 0 ∧ h.2 &&& EM = h.2 ∧ ∀ c ∈ S, c ≠ h.1 → h.2 &&& sn c = 0) :
    UOk sn EM S.toFinset U := by
  intro x hx
  obtain ⟨h1, h2, h3, h4⟩ := h x hx
  refine ⟨List.mem_toFinset.2 h1, h2, ?_⟩
  intro i hi
  constructor
  · rw [← h3, Nat.testBit_land] at hi
    simp only [Bool.and_eq_true] at hi
    exact hi.2
  · intro c hc hne
    have := h4 c (List.mem_toFinset.1 hc) hne
    have h5 : (x.2 &&& sn c).testBit i = false := by rw [this]; simp
    rw [Nat.testBit_land, hi, Bool.true_and] at h5
    exact h5

-- a record from a lower bound for a restricted problem
lemma rec_of {F T M sl r L : ℕ} {I : List ℕ} {S : List ℕ} {idx : List ℕ} {S' : List ℕ} {T' F' : ℕ}
    (hFM : F &&& M = M) (hI : I.toFinset = img M S.toFinset)
    (hidx : ∀ i ∈ idx, M.testBit i = true) (hF' : sel idx F = F')
    (hS : S.toFinset.image (sel idx) = S'.toFinset) (hT : sel idx T = T') (hT' : T' ∉ S')
    (hL : ∀ l, Ch F' S'.toFinset T' l → L ≤ l.length)
    (hn : (img M S.toFinset).card + r ≤ S'.toFinset.card + L + sl) :
    ∀ l, Ch F S.toFinset T l → RecOk F (M, sl, I) S.toFinset (S.toFinset ∪ outs F l) r := by
  intro l hc
  refine ⟨hFM, hI, ?_⟩
  have h1 := fact_card (hF' ▸ sel_hom idx F) hS hT (by simpa using hT') hL hc
  have h2 : ((S.toFinset ∪ outs F l).image (sel idx)) =
      (img M (S.toFinset ∪ outs F l)).image (sel idx) := by
    unfold img
    rw [Finset.image_image]
    refine Finset.image_congr ?_
    intro x _
    exact (sel_mask hidx x).symm
  rw [h2] at h1
  have h3 := Finset.card_image_le (s := img M (S.toFinset ∪ outs F l)) (f := sel idx)
  simp only
  omega

-- splitting the main loop
noncomputable def xa (X : ℕ) (Ps : List (ℕ × ℕ)) : ℕ :=
  List.rec (fun X => X) (fun p _ ih => fun X =>
    ih (Nat.lor (Nat.lor X (Nat.shiftLeft 1 (Nat.land p.1 p.2))) (Nat.shiftLeft 1 (Nat.lor p.1 p.2))))
    Ps X

lemma ins_same {X t : ℕ} (h : tb X t = true) : Nat.lor X (Nat.shiftLeft 1 t) = X := by
  apply Nat.eq_of_testBit_eq
  intro i
  have := tb_ins X t i
  rw [tb_eq, tb_eq] at this
  rw [this]
  by_cases hi : i = t
  · subst hi; rw [← tb_eq, h]; simp
  · simp [hi]

lemma one_eq {child : ℕ → ℕ → ℕ → ℕ → Bool} {t a b X : ℕ} {k : ℕ → Bool}
    (h : one child t a b X (fun _ => true) = true) :
    one child t a b X k = k (Nat.lor X (Nat.shiftLeft 1 t)) := by
  unfold one at h ⊢
  cases ht : tb X t with
  | true => rw [ins_same ht]; rfl
  | false =>
    rw [ht] at h
    cases hc : child X t a b with
    | true => rfl
    | false => rw [hc] at h; cases h

lemma one_weak {child : ℕ → ℕ → ℕ → ℕ → Bool} {t a b X : ℕ} {k : ℕ → Bool}
    (h : one child t a b X k = true) : one child t a b X (fun _ => true) = true := by
  unfold one at h ⊢
  cases ht : tb X t with
  | true => rfl
  | false =>
    rw [ht] at h
    cases hc : child X t a b with
    | true => rfl
    | false => rw [hc] at h; cases h

lemma lp2_append {child : ℕ → ℕ → ℕ → ℕ → Bool} {A B : List (ℕ × ℕ)} : ∀ {X : ℕ},
    lp2 child A X = true → lp2 child B (xa X A) = true → lp2 child (A ++ B) X = true := by
  induction A with
  | nil => intro X _ h; exact h
  | cons p A ih =>
    intro X h1 h2
    have h1' : one child (Nat.land p.1 p.2) p.1 p.2 X
      (fun Y => one child (Nat.lor p.1 p.2) p.1 p.2 Y (lp2 child A)) = true := h1
    have h2' : lp2 child B (xa (Nat.lor (Nat.lor X (Nat.shiftLeft 1 (Nat.land p.1 p.2)))
      (Nat.shiftLeft 1 (Nat.lor p.1 p.2))) A) = true := h2
    have hw1 := one_weak h1'
    rw [one_eq hw1] at h1'
    have hw2 := one_weak h1'
    rw [one_eq hw2] at h1'
    change one child (Nat.land p.1 p.2) p.1 p.2 X
      (fun Y => one child (Nat.lor p.1 p.2) p.1 p.2 Y (lp2 child (A ++ B))) = true
    rw [one_eq hw1, one_eq hw2]
    exact ih h1' h2'

-- from circuits to chains of tables
def pt (p : ℕ) : Fin 5 → Bool := fun i => p.testBit i

def enc (pts : List ℕ) (f : (Fin 5 → Bool) → Bool) : ℕ :=
  match pts with
  | [] => 0
  | p :: pts => Nat.bit (f (pt p)) (enc pts f)

lemma enc_cons (p : ℕ) (pts : List ℕ) (f : (Fin 5 → Bool) → Bool) :
    enc (p :: pts) f = Nat.bit (f (pt p)) (enc pts f) := rfl

lemma enc_and (pts : List ℕ) (f g : (Fin 5 → Bool) → Bool) :
    enc pts (fun x => f x && g x) = enc pts f &&& enc pts g := by
  induction pts with
  | nil => simp [enc]
  | cons p pts ih => rw [enc_cons, enc_cons, enc_cons, Nat.land_bit, ih]

lemma enc_or (pts : List ℕ) (f g : (Fin 5 → Bool) → Bool) :
    enc pts (fun x => f x || g x) = enc pts f ||| enc pts g := by
  induction pts with
  | nil => simp [enc]
  | cons p pts ih => rw [enc_cons, enc_cons, enc_cons, Nat.lor_bit, ih]

lemma enc_not (pts : List ℕ) (f : (Fin 5 → Bool) → Bool) :
    enc pts (fun x => !f x) = enc pts (fun _ => true) ^^^ enc pts f := by
  induction pts with
  | nil => simp [enc]
  | cons p pts ih =>
    rw [enc_cons, enc_cons, enc_cons, Nat.xor_bit, ih]
    congr 1
    cases f (pt p) <;> rfl

lemma enc_false (pts : List ℕ) : enc pts (fun _ => false) = 0 := by
  induction pts with
  | nil => rfl
  | cons p pts ih => rw [enc_cons, ih]; rfl

abbrev Wf := (Fin 5 → Bool) → Bool

def gf (g : Gate) (W : List Wf) : Wf :=
  fun x => g.op.eval (g.inputs.map fun i => (W.map (fun f => f x)).getD i false)

def wv (W : List Wf) (i : ℕ) : Wf := W.getD i (fun _ => false)

lemma wv_eq (W : List Wf) (i : ℕ) (x : Fin 5 → Bool) :
    (W.map (fun f => f x)).getD i false = wv W i x := by
  unfold wv
  induction W generalizing i with
  | nil => simp
  | cons f W ih =>
    cases i with
    | zero => simp
    | succ i => simpa using ih i

def isNot (g : Gate) : Bool :=
  match g.op with
  | GateOp.not => true
  | _ => false

def SW (pts : List ℕ) (W : List Wf) : Finset ℕ :=
  insert 0 (insert (enc pts (fun _ => true)) (W.map (enc pts)).toFinset)

lemma wv_mem (pts : List ℕ) (W : List Wf) (i : ℕ) : enc pts (wv W i) ∈ SW pts W := by
  unfold wv SW
  by_cases hi : i < W.length
  · rw [List.getD_eq_getElem _ _ hi]
    refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (List.mem_toFinset.2 ?_))
    exact List.mem_map_of_mem (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (not_lt.1 hi), enc_false]
    exact Finset.mem_insert_self _ _

lemma gate_step (pts : List ℕ) (g : Gate) (W : List Wf)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    ∃ s : Stp, Ok (SW pts W) s ∧ out (enc pts (fun _ => true)) s = enc pts (gf g W) ∧
      (nt s = true → isNot g = true) := by
  obtain ⟨op, inp⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen
  have h0 : 0 ∈ SW pts W := Finset.mem_insert_self _ _
  have hF : enc pts (fun _ => true) ∈ SW pts W :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  rcases hop with rfl | rfl | rfl
  · match inp, hlen with
    | [], _ =>
      refine ⟨(0, enc pts (fun _ => true), enc pts (fun _ => true)), ⟨hF, hF, fun _ => rfl⟩, ?_, ?_⟩
      · simp only [out, ite_true, Nat.and_self]
        congr 1
      · intro h; simp [nt] at h
    | [i], _ =>
      refine ⟨(0, enc pts (wv W i), enc pts (wv W i)),
        ⟨wv_mem .., wv_mem .., fun _ => rfl⟩, ?_, ?_⟩
      · simp only [out, ite_true, Nat.and_self]
        congr 1
        funext x
        simp [gf, GateOp.eval, ← wv_eq]
      · intro h; simp [nt] at h
    | [i, j], _ =>
      refine ⟨(0, enc pts (wv W i), enc pts (wv W j)),
        ⟨wv_mem .., wv_mem .., fun h => by simp [nt] at h⟩, ?_, ?_⟩
      · simp only [out, ite_true]
        rw [← enc_and]
        congr 1
        funext x
        simp [gf, GateOp.eval, ← wv_eq]
      · intro h; simp [nt] at h
  · match inp, hlen with
    | [], _ =>
      refine ⟨(1, 0, 0), ⟨h0, h0, fun _ => rfl⟩, ?_, ?_⟩
      · have : gf ⟨GateOp.or, []⟩ W = fun _ => false := rfl
        rw [this, enc_false]; rfl
      · intro h; simp [nt] at h
    | [i], _ =>
      refine ⟨(1, enc pts (wv W i), enc pts (wv W i)),
        ⟨wv_mem .., wv_mem .., fun _ => rfl⟩, ?_, ?_⟩
      · simp only [out, one_ne_zero, ite_false, ite_true, Nat.or_self]
        congr 1
        funext x
        simp [gf, GateOp.eval, ← wv_eq]
      · intro h; simp [nt] at h
    | [i, j], _ =>
      refine ⟨(1, enc pts (wv W i), enc pts (wv W j)),
        ⟨wv_mem .., wv_mem .., fun h => by simp [nt] at h⟩, ?_, ?_⟩
      · simp only [out, one_ne_zero, ite_false, ite_true]
        rw [← enc_or]
        congr 1
        funext x
        simp [gf, GateOp.eval, ← wv_eq]
      · intro h; simp [nt] at h
  · match inp, hlen with
    | [], _ =>
      refine ⟨(2, 0, 0), ⟨h0, h0, fun _ => rfl⟩, ?_, fun _ => rfl⟩
      simp only [out, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ite_false, Nat.xor_zero]
      congr 1
    | i :: t, _ =>
      refine ⟨(2, enc pts (wv W i), enc pts (wv W i)),
        ⟨wv_mem .., wv_mem .., fun _ => rfl⟩, ?_, fun _ => rfl⟩
      simp only [out, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, ite_false]
      rw [← enc_not]
      congr 1
      funext x
      simp [gf, GateOp.eval, ← wv_eq]

lemma gates_chain (pts : List ℕ) (gates : List Gate) : ∀ (W : List Wf),
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
    ∃ (l : List Stp) (W' : List Wf), Val (enc pts (fun _ => true)) (SW pts W) l ∧
      l.length = gates.length ∧ l.countP nt ≤ gates.countP isNot ∧
      (∀ x, gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (W.map (fun f => f x)) = W'.map (fun f => f x)) ∧
      SW pts W' = SW pts W ∪ outs (enc pts (fun _ => true)) l := by
  induction gates with
  | nil => intro W _; exact ⟨[], W, trivial, rfl, by simp, fun x => rfl, by simp⟩
  | cons g gates ih =>
    intro W hg
    obtain ⟨s, hs1, hs2, hs3⟩ := gate_step pts g W (hg g (List.mem_cons_self ..))
    obtain ⟨l, W', h1, h2, h3, h4, h5⟩ := ih (W ++ [gf g W])
      (fun g hh => hg g (List.mem_cons_of_mem _ hh))
    have hSW : SW pts (W ++ [gf g W]) = insert (out (enc pts (fun _ => true)) s) (SW pts W) := by
      rw [hs2]
      unfold SW
      ext y
      simp only [List.map_append, List.map_cons, List.map_nil, List.toFinset_append,
        List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.mem_union,
        Finset.notMem_empty, or_false]
      tauto
    refine ⟨s :: l, W', ⟨hs1, ?_⟩, by simp [h2], ?_, ?_, ?_⟩
    · rw [← hSW]; exact h1
    · rw [List.countP_cons, List.countP_cons]
      by_cases hn : nt s = true
      · simp only [hn, hs3 hn, ite_true]; omega
      · simp only [hn]; simp; omega
    · intro x
      rw [List.foldl_cons, ← h4 x]
      simp only [List.map_append, List.map_cons, List.map_nil]
      rfl
    · rw [h5, hSW, outs_cons, Finset.insert_union, Finset.union_insert]

lemma countP_le_one {p : Gate → Bool} {gates : List Gate}
    (h : ∀ i j : Fin gates.length, p (gates.get i) = true → p (gates.get j) = true → i = j) :
    gates.countP p ≤ 1 := by
  induction gates with
  | nil => simp
  | cons g gates ih =>
    rw [List.countP_cons]
    by_cases hg : p g = true
    · have : gates.countP p = 0 := by
        rw [List.countP_eq_zero]
        intro g' hg' hp
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg'
        have := h ⟨0, by simp⟩ ⟨j + 1, by simpa using hj⟩ (by simpa using hg) (by simpa using hp)
        simp at this
      simp [this, hg]
    · have := ih (fun i j hi hj => by
        have := h ⟨i + 1, by simp⟩ ⟨j + 1, by simp⟩ (by simpa using hi) (by simpa using hj)
        ext; simpa using this)
      simp only [hg]; simpa using this

-- the truth table value of an input
def tv (T : ℕ) : Wf := fun x => Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

lemma pt_sum : ∀ p < 32, (∑ i : Fin 5, if pt p i then 2 ^ (i : ℕ) else 0) = p := by
  decide +kernel

lemma enc_tv {pts : List ℕ} (h : ∀ p ∈ pts, p < 32) (T : ℕ) : enc pts (tv T) = sel pts T := by
  induction pts with
  | nil => rfl
  | cons p pts ih =>
    rw [enc_cons, sel_cons, ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    unfold tv
    rw [pt_sum p (h p (List.mem_cons_self ..))]

def W0 : List Wf := List.ofFn (fun i : Fin 5 => fun x : Fin 5 → Bool => x i)

-- the lower bound transferred to circuits
lemma circ_lb {T F T' L : ℕ} {pts S : List ℕ} (hp : ∀ p ∈ pts, p < 32)
    (hF : enc pts (fun _ => true) = F) (hS : S.toFinset = SW pts W0) (hT' : sel pts T = T')
    (hTS : T' ∉ S) (hL : ∀ l, Ch F S.toFinset T' l → L ≤ l.length)
    {gates : List Gate} {o : ℕ}
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hn : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) : L ≤ gates.length := by
  obtain ⟨l, W', h1, h2, h3, h4, h5⟩ := gates_chain pts gates W0 hg
  rw [hF] at h1 h5
  have hW0 : ∀ x : Fin 5 → Bool, W0.map (fun f => f x) = List.ofFn x := by
    intro x; unfold W0; rw [List.map_ofFn]; rfl
  have hfun : wv W' o = tv T := by
    funext x
    rw [← wv_eq, ← h4 x, hW0 x]
    exact he x
  have hnn : gates.countP isNot ≤ 1 := by
    refine countP_le_one fun i j hi hj => hn i j ?_ ?_
    · unfold isNot at hi
      split at hi
      · assumption
      · cases hi
    · unfold isNot at hj
      split at hj
      · assumption
      · cases hj
  have hmem : T' ∈ SW pts W' := by
    rw [← hT', ← enc_tv hp, ← hfun]
    exact wv_mem pts W' o
  rw [h5, ← hS] at hmem
  have hout : T' ∈ outs F l := by
    rcases Finset.mem_union.1 hmem with h | h
    · exact absurd (List.mem_toFinset.1 h) hTS
    · exact h
  rw [← h2]
  exact hL l ⟨hS ▸ h1, h3.trans hnn, hout⟩

-- checking an explicit circuit
lemma all_bool {P : (Fin 5 → Bool) → Prop} (h : ∀ a b c d e : Bool, P ![a, b, c, d, e]) (x) : P x := by
  have : x = ![x 0, x 1, x 2, x 3, x 4] := by
    funext i; fin_cases i <;> rfl
  rw [this]; exact h _ _ _ _ _

def A (i j : ℕ) : Gate := ⟨GateOp.and, [i, j]⟩
def O (i j : ℕ) : Gate := ⟨GateOp.or, [i, j]⟩

def Mono (gates : List Gate) : Prop :=
  ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma mono_nil : Mono [] := by intro g hg; simp at hg
lemma mono_A {i j : ℕ} {l : List Gate} (h : Mono l) : Mono (A i j :: l) := by
  intro g hg
  rcases List.mem_cons.1 hg with rfl | hg
  · exact ⟨Or.inl rfl, le_refl 2⟩
  · exact h g hg
lemma mono_O {i j : ℕ} {l : List Gate} (h : Mono l) : Mono (O i j :: l) := by
  intro g hg
  rcases List.mem_cons.1 hg with rfl | hg
  · exact ⟨Or.inr rfl, le_refl 2⟩
  · exact h g hg

lemma ub1 : ∀ x, Circuit.eval ⟨[A 3 4, A 2 5, A 1 6, A 0 7], 8⟩ (List.ofFn x) = tv 0x80000000 x :=
  all_bool (by decide +kernel)
lemma ub2 : ∀ x, Circuit.eval ⟨[A 0 1, O 3 4, A 2 5, A 6 7], 8⟩ (List.ofFn x) = tv 0x80808000 x :=
  all_bool (by decide +kernel)
lemma ub3 : ∀ x, Circuit.eval ⟨[A 0 1, A 3 4, O 3 4, O 2 6, A 5 8, A 7 9], 10⟩ (List.ofFn x) =
    tv 0x88808000 x := all_bool (by decide +kernel)
lemma ub4 : ∀ x, Circuit.eval ⟨[A 0 1, A 3 4, O 2 6, A 5 7], 8⟩ (List.ofFn x) = tv 0x88808080 x :=
  all_bool (by decide +kernel)
lemma ub5 : ∀ x, Circuit.eval ⟨[A 2 3, O 2 3, A 1 5, O 1 5, A 4 6, O 7 9, A 8 10, A 0 11], 12⟩
    (List.ofFn x) = tv 0xa8808000 x := all_bool (by decide +kernel)
lemma ub6 : ∀ x, Circuit.eval ⟨[A 3 4, A 2 5, O 2 5, A 1 7, O 6 8, A 0 9], 10⟩ (List.ofFn x) =
    tv 0xa8808080 x := all_bool (by decide +kernel)
lemma ub7 : ∀ x, Circuit.eval ⟨[A 0 1, O 0 1, O 2 3, A 3 6, A 4 7, A 2 8, A 5 9, O 5 9, A 10 12,
    O 11 13], 14⟩ (List.ofFn x) = tv 0xe8808000 x := all_bool (by decide +kernel)
lemma ub8 : ∀ x, Circuit.eval ⟨[O 2 4, O 3 5, A 0 6, A 1 7], 8⟩ (List.ofFn x) = tv 0x88888880 x :=
  all_bool (by decide +kernel)
lemma ub9 : ∀ x, Circuit.eval ⟨[A 2 3, O 2 3, A 4 5, O 1 7, A 0 8, A 6 9], 10⟩ (List.ofFn x) =
    tv 0xa8808880 x := all_bool (by decide +kernel)
lemma ub10 : ∀ x, Circuit.eval ⟨[A 2 3, A 1 4, O 5 6, A 0 7], 8⟩ (List.ofFn x) = tv 0xa888a000 x :=
  all_bool (by decide +kernel)

-- data: ten or fifteen of the 32 points

lemma snl_ok {P Q : List ℕ} {F T EM n : ℕ} (hP : P.length = n) (hQ : Q.length = n)
    (hE : EM < 2 ^ n)
    (h : ∀ i < n, F.testBit (P.getD i 0) = F.testBit (Q.getD i 0) ∧
      T.testBit (P.getD i 0) ≠ T.testBit (Q.getD i 0)) : SnOk (snl P Q) F T EM :=
  sn_ok (fun _ _ hi => snl_bit hP hQ hi) hE h

-- threshold three of four on the points of weight two and three
def P4 : List ℕ := [6, 6, 6, 7, 7, 7, 8, 8, 8, 9, 9, 9]
def Q4 : List ℕ := [0, 1, 2, 0, 3, 4, 1, 3, 5, 2, 4, 5]
def S4 : List ℕ := [459, 725, 870, 952, 0, 1023]
def U4 : UL := [(459, 292), (725, 2066), (870, 1153), (952, 584)]

lemma sn4_ok : SnOk (snl P4 Q4) 1023 960 4095 :=
  snl_ok (n := 12) rfl rfl (by norm_num) (by decide +kernel)

lemma t43_run : srch (snl P4 Q4) 1023 960 4095 6 true S4 S4 [] U4 [459, 725, 870, 952] 3 (bmp S4) [] = true := by
  decide +kernel

lemma u4_ok : UOk (snl P4 Q4) 4095 S4.toFinset U4 := uok_of (by decide +kernel)

lemma lb43 : ∀ l, Ch 1023 S4.toFinset 960 l → 7 ≤ l.length :=
  root_lb sn4_ok (by decide) (by decide) (by decide) u4_ok
    ⟨by decide, by decide, rfl⟩ (by intro l _ h hh; simp at hh) t43_run

-- the slice of weights three and four
def pts15 : List ℕ := [7, 11, 13, 14, 19, 21, 22, 25, 26, 28, 15, 23, 27, 29, 30]
def S5 : List ℕ := [15543, 23899, 28269, 30606, 31728, 0, 32767]
lemma pts15_lt : ∀ p ∈ pts15, p < 32 := by decide
lemma enc15 : enc pts15 (fun _ => true) = 32767 := by decide +kernel
lemma S5_eq : S5.toFinset = SW pts15 W0 := by decide +kernel

def P3a : List ℕ := [10, 10, 10, 10, 11, 11, 11, 11, 12, 12, 12, 12]
def Q3a : List ℕ := [0, 1, 2, 3, 0, 4, 5, 6, 1, 4, 7, 8]
def U3a : UL := [(15543, 2184), (23899, 1092), (28269, 34), (30606, 513), (31728, 272)]
lemma run3 : srch (snl P3a Q3a) 32767 7168 4095 5 true S5 S5 [] U3a [15543, 23899, 28269, 30606, 31728] 1 (bmp S5)
    [] = true := by decide +kernel
lemma clb3 : ∀ l, Ch 32767 S5.toFinset 7168 l → 6 ≤ l.length :=
  root_lb (snl_ok (n := 12) rfl rfl (by norm_num) (by decide +kernel)) (by decide) (by decide) (by decide)
    (uok_of (by decide +kernel)) ⟨by decide, by decide, rfl⟩
    (by intro l _ h hh; simp at hh) run3

def P6a : List ℕ := [10, 10, 10, 11, 11, 11, 12, 12, 12, 12, 13, 13, 13, 13]
def Q6a : List ℕ := [1, 2, 3, 4, 5, 6, 1, 4, 7, 8, 2, 5, 7, 9]
def U6a : UL := [(15543, 8740), (23899, 274), (28269, 4105), (30606, 2176), (31728, 1088)]
lemma run6 : srch (snl P6a Q6a) 32767 15361 16383 5 true S5 S5 [] U6a [15543, 23899, 28269, 30606, 31728] 1 (bmp S5)
    [] = true := by decide +kernel
lemma clb6 : ∀ l, Ch 32767 S5.toFinset 15361 l → 6 ≤ l.length :=
  root_lb (snl_ok (n := 14) rfl rfl (by norm_num) (by decide +kernel)) (by decide) (by decide) (by decide)
    (uok_of (by decide +kernel)) ⟨by decide, by decide, rfl⟩
    (by intro l _ h hh; simp at hh) run6

def P9a : List ℕ := [10, 10, 11, 11, 11, 12, 12, 12, 13, 13, 13, 13]
def Q9a : List ℕ := [2, 3, 4, 5, 6, 4, 7, 8, 2, 5, 7, 9]
def U9a : UL := [(15543, 2194), (23899, 73), (28269, 1028), (30606, 544), (31728, 256)]
lemma run9 : srch (snl P9a Q9a) 32767 15363 4095 5 true S5 S5 [] U9a [15543, 23899, 28269, 30606, 31728] 1 (bmp S5)
    [] = true := by decide +kernel
lemma clb9 : ∀ l, Ch 32767 S5.toFinset 15363 l → 6 ≤ l.length :=
  root_lb (snl_ok (n := 12) rfl rfl (by norm_num) (by decide +kernel)) (by decide) (by decide) (by decide)
    (uok_of (by decide +kernel)) ⟨by decide, by decide, rfl⟩
    (by intro l _ h hh; simp at hh) run9

def P5a : List ℕ := [10, 10, 10, 10, 11, 11, 11, 11, 12, 12, 12, 12, 13, 13, 13, 13]
def Q5a : List ℕ := [0, 1, 2, 3, 0, 4, 5, 6, 1, 4, 7, 8, 2, 5, 7, 9]
def U5a : UL := [(15543, 34952), (23899, 1092), (28269, 16418), (30606, 8705), (31728, 4368)]
lemma run5 : srch (snl P5a Q5a) 32767 15360 65535 7 true S5 S5 [] U5a [15543, 23899, 28269, 30606, 31728] 3 (bmp S5)
    [(15543, 0, [0, 7187, 11301, 13446, 14512, 15543])] = true := by decide +kernel
lemma clb5 : ∀ l, Ch 32767 S5.toFinset 15360 l → 8 ≤ l.length :=
  root_lb (snl_ok (n := 16) rfl rfl (by norm_num) (by decide +kernel)) (by decide) (by decide) (by decide)
    (uok_of (by decide +kernel)) ⟨by decide, by decide, rfl⟩
    (by
      intro l hl h hh
      rw [List.mem_singleton.1 hh]
      exact rec_of (idx := [0, 1, 2, 4, 5, 7, 10, 11, 12, 13]) (S' := S4) (T' := 960) (F' := 1023) (L := 7)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) lb43 (by decide +kernel) l hl) run5

lemma clb1 : ∀ l, Ch 1023 ([1021, 1015, 991, 895, 511, 0, 1023] : List ℕ).toFinset 341 l → 4 ≤ l.length :=
  read_lb (sn := snl [0, 2, 4, 6, 8] [1, 3, 5, 7, 9]) (EM := 31) (U := [(1021, 1), (1015, 2), (991, 4), (895, 8), (511, 16)])
    (snl_ok (n := 5) rfl rfl (by norm_num) (by decide +kernel)) (by decide)
    (uok_of (by decide +kernel)) (by decide +kernel)

lemma clb2 : ∀ l, Ch 1023 ([1021, 1015, 991, 127, 256, 0, 1023] : List ℕ).toFinset 341 l → 4 ≤ l.length :=
  read_lb (sn := snl [0, 2, 4, 6, 8] [1, 3, 5, 7, 9]) (EM := 31) (U := [(1021, 1), (1015, 2), (991, 4), (127, 8), (256, 16)])
    (snl_ok (n := 5) rfl rfl (by norm_num) (by decide +kernel)) (by decide)
    (uok_of (by decide +kernel)) (by decide +kernel)

lemma clb4 : ∀ l, Ch 1023 ([1021, 1015, 31, 832, 448, 0, 1023] : List ℕ).toFinset 341 l → 4 ≤ l.length :=
  read_lb (sn := snl [0, 2, 4, 6, 8] [1, 3, 5, 7, 9]) (EM := 31) (U := [(1021, 1), (1015, 2), (31, 4), (832, 8), (448, 16)])
    (snl_ok (n := 5) rfl rfl (by norm_num) (by decide +kernel)) (by decide)
    (uok_of (by decide +kernel)) (by decide +kernel)

lemma clb8 : ∀ l, Ch 1023 ([1021, 1015, 31, 64, 256, 0, 1023] : List ℕ).toFinset 341 l → 4 ≤ l.length :=
  read_lb (sn := snl [0, 2, 4, 6, 8] [1, 3, 5, 7, 9]) (EM := 31) (U := [(1021, 1), (1015, 2), (31, 4), (64, 8), (256, 16)])
    (snl_ok (n := 5) rfl rfl (by norm_num) (by decide +kernel)) (by decide)
    (uok_of (by decide +kernel)) (by decide +kernel)

lemma clb10 : ∀ l, Ch 1023 ([1021, 772, 211, 115, 268, 0, 1023] : List ℕ).toFinset 341 l → 4 ≤ l.length :=
  read_lb (sn := snl [0, 2, 4, 6, 8] [1, 3, 5, 7, 9]) (EM := 31) (U := [(1021, 1), (772, 2), (211, 4), (115, 8), (268, 16)])
    (snl_ok (n := 5) rfl rfl (by norm_num) (by decide +kernel)) (by decide)
    (uok_of (by decide +kernel)) (by decide +kernel)

-- threshold four of five
def sn5 (t : ℕ) : ℕ :=
  Nat.xor (Nat.land (Nat.shiftRight 4562440617559947989626235637702310327080102784885885581411418995984235537839698594139748366414710358012532362161689218990639528696667155482193516039161505898619330423004177543506792408494899200 (Nat.mul 20 (Nat.land (Nat.shiftRight t 10) 31))) 1048575)
    (Nat.mul 1025 (Nat.land t 1023))
def P7a : List ℕ := [10, 10, 10, 10, 11, 11, 11, 12, 12, 13, 11, 12, 13, 14, 12, 13, 14, 13, 14, 14]
def Q7a : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
def Xs5 : List ℕ := [15543, 23899, 28269, 30606, 31728]
def U5 : UL := [(15543, 840), (23899, 524452), (28269, 393234), (30606, 114689), (31728, 15360)]
def R5 : List RS := [(15543, 2, [0, 7187, 11301, 13446, 14512, 15543]), (23899, 2, [0, 7187, 19529, 21770, 22864, 23899]), (28269, 2, [0, 11301, 19529, 26124, 27232, 28269]), (30606, 2, [0, 13446, 21770, 26124, 29568, 30606]), (31728, 2, [0, 14512, 22864, 27232, 29568, 31728])]

lemma sn5_a : ∀ h < 32, ∀ i < 20,
    (Nat.land (Nat.shiftRight 4562440617559947989626235637702310327080102784885885581411418995984235537839698594139748366414710358012532362161689218990639528696667155482193516039161505898619330423004177543506792408494899200 (Nat.mul 20 h)) 1048575).testBit i = h.testBit (P7a.getD i 0 - 10) := by
  decide +kernel

lemma sn5_b : ∀ m < 1024, ∀ i < 20, (Nat.mul 1025 m).testBit i = m.testBit (Q7a.getD i 0) := by
  decide +kernel

lemma sn5_c : ∀ i < 20, 10 ≤ P7a.getD i 0 ∧ P7a.getD i 0 - 10 < 5 ∧ Q7a.getD i 0 < 10 := by decide +kernel
lemma sn5_d : ∀ i < 5, (31).testBit i = true := by decide +kernel
lemma sn5_e : ∀ i < 10, (1023).testBit i = true := by decide +kernel

lemma sn5_bit (t i : ℕ) (hi : i < 20) :
    (sn5 t).testBit i = (t.testBit (P7a.getD i 0) ^^ t.testBit (Q7a.getD i 0)) := by
  have h1 : sn5 t = (Nat.land (Nat.shiftRight 4562440617559947989626235637702310327080102784885885581411418995984235537839698594139748366414710358012532362161689218990639528696667155482193516039161505898619330423004177543506792408494899200 (Nat.mul 20 ((t >>> 10) &&& 31))) 1048575) ^^^
    (Nat.mul 1025 (t &&& 1023)) := rfl
  have hA : (t >>> 10) &&& 31 < 32 := by
    have : (t >>> 10) &&& 31 ≤ 31 := Nat.and_le_right
    omega
  have hB : t &&& 1023 < 1024 := by
    have : t &&& 1023 ≤ 1023 := Nat.and_le_right
    omega
  obtain ⟨c1, c2, c3⟩ := sn5_c i hi
  rw [h1, Nat.testBit_xor, sn5_a _ hA i hi, sn5_b _ hB i hi, Nat.testBit_land, Nat.testBit_land,
    sn5_d _ c2, sn5_e _ c3, Nat.testBit_shiftRight, Bool.and_true, Bool.and_true]
  congr 2
  omega

lemma sn5_ok : SnOk sn5 32767 31744 1048575 :=
  sn_ok (n := 20) sn5_bit (by norm_num) (by decide +kernel)

lemma u5_ok : UOk sn5 1048575 S5.toFinset U5 := uok_of (by decide +kernel)

lemma r5_ok : ∀ l, Ch 32767 S5.toFinset 31744 l → ∀ h ∈ R5,
    RecOk 32767 h S5.toFinset (S5.toFinset ∪ outs 32767 l) 9 := by
  intro l hl h hh
  simp only [R5, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl | rfl
  · exact rec_of (idx := [0, 1, 2, 4, 5, 7, 10, 11, 12, 13]) (S' := S4) (T' := 960) (F' := 1023) (L := 7)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) lb43 (by decide +kernel) l hl
  · exact rec_of (idx := [0, 1, 3, 4, 6, 8, 10, 11, 12, 14]) (S' := S4) (T' := 960) (F' := 1023) (L := 7)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) lb43 (by decide +kernel) l hl
  · exact rec_of (idx := [0, 2, 3, 5, 6, 9, 10, 11, 13, 14]) (S' := S4) (T' := 960) (F' := 1023) (L := 7)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) lb43 (by decide +kernel) l hl
  · exact rec_of (idx := [1, 2, 3, 7, 8, 9, 10, 12, 13, 14]) (S' := S4) (T' := 960) (F' := 1023) (L := 7)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) lb43 (by decide +kernel) l hl
  · exact rec_of (idx := [4, 5, 6, 7, 8, 9, 11, 12, 13, 14]) (S' := S4) (T' := 960) (F' := 1023) (L := 7)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) lb43 (by decide +kernel) l hl

def PI : List (List ℕ) := [[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], [0, 2, 1, 3, 5, 4, 6, 7, 9, 8, 10, 11, 13, 12, 14], [1, 2, 0, 3, 7, 4, 8, 5, 9, 6, 10, 12, 13, 11, 14], [4, 5, 0, 6, 7, 1, 8, 2, 9, 3, 11, 12, 13, 10, 14], [0, 1, 3, 2, 4, 6, 5, 8, 7, 9, 10, 11, 12, 14, 13], [0, 3, 1, 2, 6, 4, 5, 8, 9, 7, 10, 11, 14, 12, 13], [1, 3, 0, 2, 8, 4, 7, 6, 9, 5, 10, 12, 14, 11, 13], [4, 6, 0, 5, 8, 1, 7, 3, 9, 2, 11, 12, 14, 10, 13], [0, 2, 3, 1, 5, 6, 4, 9, 7, 8, 10, 11, 13, 14, 12], [0, 3, 2, 1, 6, 5, 4, 9, 8, 7, 10, 11, 14, 13, 12], [2, 3, 0, 1, 9, 5, 7, 6, 8, 4, 10, 13, 14, 11, 12], [5, 6, 0, 4, 9, 2, 7, 3, 8, 1, 11, 13, 14, 10, 12], [1, 2, 3, 0, 7, 8, 4, 9, 5, 6, 10, 12, 13, 14, 11], [1, 3, 2, 0, 8, 7, 4, 9, 6, 5, 10, 12, 14, 13, 11], [2, 3, 1, 0, 9, 7, 5, 8, 6, 4, 10, 13, 14, 12, 11], [7, 8, 1, 4, 9, 2, 5, 3, 6, 0, 12, 13, 14, 10, 11], [4, 5, 6, 0, 7, 8, 1, 9, 2, 3, 11, 12, 13, 14, 10], [4, 6, 5, 0, 8, 7, 1, 9, 3, 2, 11, 12, 14, 13, 10], [5, 6, 4, 0, 9, 7, 2, 8, 3, 1, 11, 13, 14, 12, 10], [7, 8, 4, 1, 9, 5, 2, 6, 3, 0, 12, 13, 14, 11, 10]]

lemma pi_ok : ∀ x ∈ Xs5, ∀ y ∈ Xs5, x ≠ y → ∃ idx ∈ PI, sel idx x = 15543 ∧ sel idx y = 23899 ∧
    sel idx 32767 = 32767 ∧ sel idx 31744 = 31744 ∧ S5.toFinset.image (sel idx) = S5.toFinset := by
  decide +kernel

lemma mn_perm {idx : List ℕ} (h1 : sel idx 32767 = 32767) (h2 : sel idx 31744 = 31744)
    (h3 : S5.toFinset.image (sel idx) = S5.toFinset) {l : List Stp}
    (hm : Mn 32767 S5.toFinset 31744 l) : Mn 32767 S5.toFinset 31744 (l.map (ms (sel idx))) := by
  refine ⟨?_, ?_⟩
  · have hh : Hom (sel idx) 32767 32767 := by
      have := sel_hom idx 32767
      rwa [h1] at this
    have := ch_ms hh hm.1
    rwa [h2, h3] at this
  · intro l' hl'
    rw [List.length_map]
    exact hm.2 l' hl'

lemma run_c : chd sn5 31744 1048575 8 (srch sn5 32767 31744 1048575 8) false (Nat.xor 32767 15543)
    15543 15543 S5 [] U5 (bmp S5) R5 = true := by decide +kernel

lemma run_b : chd sn5 31744 1048575 8 (srch sn5 32767 31744 1048575 8) true (Nat.lor 15543 23899)
    15543 23899 S5 [] U5 (bmp ([7187, 11301, 19529, 13446, 21770, 26124, 14512, 22864, 27232, 29568] ++ S5)) R5 = true := by decide +kernel

def SA : List ℕ := [7187, 15543, 23899, 28269, 30606, 31728, 0, 32767]
def KA : List ℕ := [7187]
def UA : UL := [(31728, 15360), (30606, 114689), (28269, 393234), (23899, 524288), (15543, 512)]
def KFA : List ℕ := [31728, 30606, 28269, 23899, 15543, 7187]
def RA : List RS := [(15543, 1, [0, 7187, 11301, 13446, 14512, 15543]), (23899, 1, [0, 7187, 19529, 21770, 22864, 23899]), (28269, 2, [3073, 0, 11301, 19529, 26124, 27232, 28269]), (30606, 2, [5122, 0, 13446, 21770, 26124, 29568, 30606]), (31728, 2, [6160, 0, 14512, 22864, 27232, 29568, 31728])]

noncomputable def ch7 : ℕ → ℕ → ℕ → ℕ → Bool := fun Y t a b =>
  chd sn5 31744 1048575 7 (srch sn5 32767 31744 1048575 7) true t a b SA KA UA Y RA

lemma chA (st : ST) : chd sn5 31744 1048575 8 st true (Nat.land 15543 23899) 15543 23899 S5 [] U5 (bmp S5) R5 =
    st true [7187] SA KA UA KFA 3 (bmp SA) RA := rfl

lemma run_n : lpn (fun t a => chd sn5 31744 1048575 7 (srch sn5 32767 31744 1048575 7) false t a a
    SA KA UA (bmp SA) RA) 32767 (bmp SA) [7187] = true := by decide +kernel
noncomputable def Y0 : ℕ := bmp SA
lemma run_0 : lp2 ch7 [(7187, 15543)] Y0 = true := by decide +kernel
noncomputable def Y1 : ℕ := xa Y0 [(7187, 15543)]
lemma run_1 : lp2 ch7 [(7187, 23899)] Y1 = true := by decide +kernel
noncomputable def Y2 : ℕ := xa Y1 [(7187, 23899)]
lemma run_2 : lp2 ch7 [(7187, 28269)] Y2 = true := by decide +kernel
noncomputable def Y3 : ℕ := xa Y2 [(7187, 28269)]
lemma run_3 : lp2 ch7 [(7187, 30606)] Y3 = true := by decide +kernel
noncomputable def Y4 : ℕ := xa Y3 [(7187, 30606)]
lemma run_4 : lp2 ch7 [(7187, 31728)] Y4 = true := by decide +kernel
noncomputable def Y5 : ℕ := xa Y4 [(7187, 31728)]
lemma run_5 : lp2 ch7 [(7187, 0)] Y5 = true := by decide +kernel
noncomputable def Y6 : ℕ := xa Y5 [(7187, 0)]
lemma run_6 : lp2 ch7 [(7187, 32767)] Y6 = true := by decide +kernel
noncomputable def Y7 : ℕ := xa Y6 [(7187, 32767)]
lemma run_7 : lp2 ch7 [(15543, 23899)] Y7 = true := by decide +kernel
noncomputable def Y8 : ℕ := xa Y7 [(15543, 23899)]
lemma run_8 : lp2 ch7 [(15543, 28269)] Y8 = true := by decide +kernel
noncomputable def Y9 : ℕ := xa Y8 [(15543, 28269)]
lemma run_9 : lp2 ch7 [(15543, 30606)] Y9 = true := by decide +kernel
noncomputable def Y10 : ℕ := xa Y9 [(15543, 30606)]
lemma run_10 : lp2 ch7 [(15543, 31728)] Y10 = true := by decide +kernel
noncomputable def Y11 : ℕ := xa Y10 [(15543, 31728)]
lemma run_11 : lp2 ch7 [(15543, 0)] Y11 = true := by decide +kernel
noncomputable def Y12 : ℕ := xa Y11 [(15543, 0)]
lemma run_12 : lp2 ch7 [(15543, 32767)] Y12 = true := by decide +kernel
noncomputable def Y13 : ℕ := xa Y12 [(15543, 32767)]
lemma run_13 : lp2 ch7 [(23899, 28269)] Y13 = true := by decide +kernel
noncomputable def Y14 : ℕ := xa Y13 [(23899, 28269)]
lemma run_14 : lp2 ch7 [(23899, 30606)] Y14 = true := by decide +kernel
noncomputable def Y15 : ℕ := xa Y14 [(23899, 30606)]
lemma run_15 : lp2 ch7 [(23899, 31728)] Y15 = true := by decide +kernel
noncomputable def Y16 : ℕ := xa Y15 [(23899, 31728)]
lemma run_16 : lp2 ch7 [(23899, 0)] Y16 = true := by decide +kernel
noncomputable def Y17 : ℕ := xa Y16 [(23899, 0)]
lemma run_17 : lp2 ch7 [(23899, 32767)] Y17 = true := by decide +kernel
noncomputable def Y18 : ℕ := xa Y17 [(23899, 32767)]
lemma run_18 : lp2 ch7 [(28269, 30606)] Y18 = true := by decide +kernel
noncomputable def Y19 : ℕ := xa Y18 [(28269, 30606)]
lemma run_19 : lp2 ch7 [(28269, 31728)] Y19 = true := by decide +kernel
noncomputable def Y20 : ℕ := xa Y19 [(28269, 31728)]
lemma run_20 : lp2 ch7 [(28269, 0)] Y20 = true := by decide +kernel
noncomputable def Y21 : ℕ := xa Y20 [(28269, 0)]
lemma run_21 : lp2 ch7 [(28269, 32767)] Y21 = true := by decide +kernel
noncomputable def Y22 : ℕ := xa Y21 [(28269, 32767)]
lemma run_22 : lp2 ch7 [(30606, 31728)] Y22 = true := by decide +kernel
noncomputable def Y23 : ℕ := xa Y22 [(30606, 31728)]
lemma run_23 : lp2 ch7 [(30606, 0)] Y23 = true := by decide +kernel
noncomputable def Y24 : ℕ := xa Y23 [(30606, 0)]
lemma run_24 : lp2 ch7 [(30606, 32767)] Y24 = true := by decide +kernel
noncomputable def Y25 : ℕ := xa Y24 [(30606, 32767)]
lemma run_25 : lp2 ch7 [(31728, 0)] Y25 = true := by decide +kernel
noncomputable def Y26 : ℕ := xa Y25 [(31728, 0)]
lemma run_26 : lp2 ch7 [(31728, 32767)] Y26 = true := by decide +kernel
noncomputable def Y27 : ℕ := xa Y26 [(31728, 32767)]
lemma run_27 : lp2 ch7 [(0, 32767)] Y27 = true := by decide +kernel
noncomputable def Y28 : ℕ := xa Y27 [(0, 32767)]

lemma ups_split : ups SA = [(7187, 15543)] ++ ([(7187, 23899)] ++ ([(7187, 28269)] ++ ([(7187, 30606)] ++ ([(7187, 31728)] ++ ([(7187, 0)] ++ ([(7187, 32767)] ++ ([(15543, 23899)] ++ ([(15543, 28269)] ++ ([(15543, 30606)] ++ ([(15543, 31728)] ++ ([(15543, 0)] ++ ([(15543, 32767)] ++ ([(23899, 28269)] ++ ([(23899, 30606)] ++ ([(23899, 31728)] ++ ([(23899, 0)] ++ ([(23899, 32767)] ++ ([(28269, 30606)] ++ ([(28269, 31728)] ++ ([(28269, 0)] ++ ([(28269, 32767)] ++ ([(30606, 31728)] ++ ([(30606, 0)] ++ ([(30606, 32767)] ++ ([(31728, 0)] ++ ([(31728, 32767)] ++ ([(0, 32767)]))))))))))))))))))))))))))) := by decide +kernel

set_option maxRecDepth 4000 in
lemma run_p : lp2 ch7 (ups SA) (bmp SA) = true := by
  rw [ups_split]
  exact lp2_append (X := Y0) run_0 (lp2_append (X := Y1) run_1 (lp2_append (X := Y2) run_2 (lp2_append (X := Y3) run_3 (lp2_append (X := Y4) run_4 (lp2_append (X := Y5) run_5 (lp2_append (X := Y6) run_6 (lp2_append (X := Y7) run_7 (lp2_append (X := Y8) run_8 (lp2_append (X := Y9) run_9 (lp2_append (X := Y10) run_10 (lp2_append (X := Y11) run_11 (lp2_append (X := Y12) run_12 (lp2_append (X := Y13) run_13 (lp2_append (X := Y14) run_14 (lp2_append (X := Y15) run_15 (lp2_append (X := Y16) run_16 (lp2_append (X := Y17) run_17 (lp2_append (X := Y18) run_18 (lp2_append (X := Y19) run_19 (lp2_append (X := Y20) run_20 (lp2_append (X := Y21) run_21 (lp2_append (X := Y22) run_22 (lp2_append (X := Y23) run_23 (lp2_append (X := Y24) run_24 (lp2_append (X := Y25) run_25 (lp2_append (X := Y26) run_26 (run_27)))))))))))))))))))))))))))

lemma run_a : chd sn5 31744 1048575 8 (srch sn5 32767 31744 1048575 8) true (Nat.land 15543 23899)
    15543 23899 S5 [] U5 (bmp S5) R5 = true := by
  rw [chA]
  change cond (cond true (lpn (fun t a => chd sn5 31744 1048575 7 (srch sn5 32767 31744 1048575 7) false t a a
    SA KA UA (bmp SA) RA) 32767 (bmp SA) [7187]) true) (lp2 ch7 (ups SA) (bmp SA)) false = true
  rw [run_n, run_p]
  rfl

lemma S5_cases : ∀ x ∈ S5, x = 0 ∨ x = 32767 ∨ x ∈ Xs5 := by decide +kernel
lemma Xs5_sub : ∀ x ∈ Xs5, x ∈ S5 := by decide +kernel
lemma Xs5_other : ∀ x ∈ Xs5, ∃ y ∈ Xs5, x ≠ y := by decide +kernel
lemma S5_and : ∀ x ∈ S5, ∀ y ∈ S5, x &&& y ∈ S5 ∨ ∃ u ∈ Xs5, ∃ v ∈ Xs5, u ≠ v ∧ x &&& y = u &&& v := by
  decide +kernel
lemma S5_or : ∀ x ∈ S5, ∀ y ∈ S5, x ||| y ∈ S5 ∨ ∃ u ∈ Xs5, ∃ v ∈ Xs5, u ≠ v ∧ x ||| y = u ||| v := by
  decide +kernel
def ands5 : List ℕ := [7187, 11301, 19529, 13446, 21770, 26124, 14512, 22864, 27232, 29568]
lemma ands5_eq : ∀ t ∈ ands5, ∃ u ∈ Xs5, ∃ v ∈ Xs5, u ≠ v ∧ t = u &&& v := by decide +kernel

abbrev S5f : Finset ℕ := S5.toFinset
lemma t_notin : 31744 ∉ S5f := by decide +kernel
lemma t_notin' : 31744 ∉ S5 := by decide +kernel
lemma z_in : 0 ∈ S5f := by decide +kernel
lemma x0_in : 15543 ∈ S5f := by decide +kernel
lemma f_in : 32767 ∈ S5f := by decide +kernel

lemma fresh5 {l : List Stp} (hm : Mn 32767 S5f 31744 l) : ∀ t ∈ outs 32767 l, t ∉ S5 := by
  intro t ht hS
  have := (mn_fresh (p := []) t_notin (by simpa using hm)).1
  exact Finset.disjoint_left.1 this (by simpa using hS) ht

lemma bits5 {l : List Stp} (hm : Mn 32767 S5f 31744 l) : ∀ t ∈ outs 32767 l, tb (bmp S5) t = false := by
  intro t ht
  rw [tb_bmp]
  simp [fresh5 hm t ht]

lemma out_nt {F : ℕ} {s : Stp} (hns : nt s = true) : out F s = F ^^^ s.2.1 := by
  have h1 : s.1 ≠ 0 := by intro h; simp [nt, h] at hns
  have h2 : s.1 ≠ 1 := by intro h; simp [nt, h] at hns
  simp [out, h1, h2]

lemma rec5 {l : List Stp} (hm : Mn 32767 S5f 31744 l) : ∀ h ∈ R5,
    RecOk 32767 h S5.toFinset (S5f ∪ outs 32767 ([] ++ l)) (8 + 1) := r5_ok l hm.1

lemma noNot0 {l : List Stp} (hm : Mn 32767 S5f 31744 l) (hl : l.length ≤ 9) :
    ∀ s ∈ l, nt s = true → s.2.1 ≠ 15543 := by
  intro s hs hns hx
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hs
  have hnol : ∀ s2 ∈ l1 ++ l2, nt s2 = false := by
    intro s2 hs2
    have hcnt : (l1 ++ l2).countP nt = 0 := by
      have hn1 := hm.1.2.1
      rw [List.countP_append, List.countP_cons_of_pos hns] at hn1
      rw [List.countP_append]; omega
    have := List.countP_eq_zero.1 hcnt s2 hs2
    simpa using this
  have hout := out_nt (F := 32767) hns
  have hs22 : s.2.2 = 15543 := by
    have hv := (val_append.1 hm.1.1).2
    rw [← hx]
    exact (hv.1.2.2 hns).symm
  refine chd_sound sn5_ok z_in f_in t_notin (srch_sound sn5_ok z_in f_in t_notin 8) run_c
    (pre := []) (l1 := l1) (l2 := l2) (s := s) (s' := (s.1, 15543, 15543)) (by simpa using hm)
    (by simp) hl t_notin' (bits5 hm) (fun _ => hnol) ?_ (by simp) u5_ok (rec5 hm) rfl ?_ ?_
    ⟨x0_in, x0_in, fun _ => rfl⟩ (fun _ => hns)
  · intro s2 hs2 hn2
    rw [hnol s2 hs2] at hn2; cases hn2
  · unfold out; rw [hx, hs22]
  · rw [hout, hx]; rfl

lemma noNot {l : List Stp} (hm : Mn 32767 S5f 31744 l) (hl : l.length ≤ 9) :
    ∀ s ∈ l, nt s = true → s.2.1 ∉ S5 := by
  intro s hs hns hx
  have hout := out_nt (F := 32767) hns
  have hfr := fresh5 hm _ (mem_outs.2 ⟨s, hs, rfl⟩)
  rw [hout] at hfr
  rcases S5_cases _ hx with h | h | h
  · rw [h] at hfr; exact hfr (by decide +kernel)
  · rw [h] at hfr; exact hfr (by decide +kernel)
  · obtain ⟨y, hy, hne⟩ := Xs5_other _ h
    obtain ⟨idx, _, h1, h2, h3, h4, h5⟩ := pi_ok _ h _ hy hne
    refine noNot0 (mn_perm h3 h4 h5 hm) (by simpa using hl) (ms (sel idx) s)
      (List.mem_map_of_mem hs) hns ?_
    exact h1

lemma noAnd0 {l : List Stp} (hm : Mn 32767 S5f 31744 l) (hl : l.length ≤ 9) :
    Nat.land 15543 23899 ∉ outs 32767 l := by
  intro hin
  obtain ⟨s, hs, hst⟩ := mem_outs.1 hin
  have hnn := noNot hm hl
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hs
  refine chd_sound sn5_ok z_in f_in t_notin (srch_sound sn5_ok z_in f_in t_notin 8) run_a
    (pre := []) (l1 := l1) (l2 := l2) (s := s) (s' := (0, 15543, 23899)) (by simpa using hm)
    (by simp) hl t_notin' (bits5 hm) (fun h => by cases h) ?_ (by simp) u5_ok (rec5 hm) rfl ?_ hst
    ⟨by decide +kernel, by decide +kernel, fun h => by cases h⟩ (fun h => by cases h)
  · intro s2 hs2
    refine hnn s2 ?_
    simp only [List.mem_append, List.mem_cons] at hs2 ⊢; tauto
  · rw [hst]; rfl

lemma noAnd {l : List Stp} (hm : Mn 32767 S5f 31744 l) (hl : l.length ≤ 9) :
    ∀ x ∈ Xs5, ∀ y ∈ Xs5, x ≠ y → x &&& y ∉ outs 32767 l := by
  intro x hx y hy hne hin
  obtain ⟨idx, _, h1, h2, h3, h4, h5⟩ := pi_ok _ hx _ hy hne
  refine noAnd0 (mn_perm h3 h4 h5 hm) (by simpa using hl) ?_
  have hh : Hom (sel idx) 32767 32767 := by
    have := sel_hom idx 32767
    rwa [h3] at this
  rw [outs_ms hh]
  refine Finset.mem_image.2 ⟨_, hin, ?_⟩
  rw [sel_and, h1, h2]; rfl

lemma noOr0 {l : List Stp} (hm : Mn 32767 S5f 31744 l) (hl : l.length ≤ 9) :
    Nat.lor 15543 23899 ∉ outs 32767 l := by
  intro hin
  obtain ⟨s, hs, hst⟩ := mem_outs.1 hin
  have hnn := noNot hm hl
  have hna := noAnd hm hl
  have hX : ∀ t ∈ outs 32767 l, tb (bmp ([7187, 11301, 19529, 13446, 21770, 26124, 14512, 22864, 27232, 29568] ++ S5)) t = false := by
    intro t ht
    rw [tb_bmp]
    have h1 := fresh5 hm t ht
    have h2 : t ∉ ands5 := by
      intro h
      obtain ⟨u, hu, v, hv, huv, rfl⟩ := ands5_eq t h
      exact hna u hu v hv huv ht
    rw [decide_eq_false_iff_not, List.mem_append]
    rintro (h | h)
    · exact h2 h
    · exact h1 h
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hs
  refine chd_sound sn5_ok z_in f_in t_notin (srch_sound sn5_ok z_in f_in t_notin 8) run_b
    (pre := []) (l1 := l1) (l2 := l2) (s := s) (s' := (1, 15543, 23899)) (by simpa using hm)
    (by simp) hl t_notin' hX (fun h => by cases h) ?_ (by simp) u5_ok (rec5 hm) rfl ?_ hst
    ⟨by decide +kernel, by decide +kernel, fun h => by cases h⟩ (fun h => by cases h)
  · intro s2 hs2
    refine hnn s2 ?_
    simp only [List.mem_append, List.mem_cons] at hs2 ⊢; tauto
  · rw [hst]; rfl

lemma noOr {l : List Stp} (hm : Mn 32767 S5f 31744 l) (hl : l.length ≤ 9) :
    ∀ x ∈ Xs5, ∀ y ∈ Xs5, x ≠ y → x ||| y ∉ outs 32767 l := by
  intro x hx y hy hne hin
  obtain ⟨idx, _, h1, h2, h3, h4, h5⟩ := pi_ok _ hx _ hy hne
  refine noOr0 (mn_perm h3 h4 h5 hm) (by simpa using hl) ?_
  have hh : Hom (sel idx) 32767 32767 := by
    have := sel_hom idx 32767
    rwa [h3] at this
  rw [outs_ms hh]
  refine Finset.mem_image.2 ⟨_, hin, ?_⟩
  rw [sel_or, h1, h2]; rfl

lemma clb7 : ∀ l, Ch 32767 S5.toFinset 31744 l → 10 ≤ l.length := by
  intro l hc
  by_contra hlt
  obtain ⟨m, hm, hml⟩ := exists_mn hc
  have hl : m.length ≤ 9 := by omega
  have hnn := noNot hm hl
  have hna := noAnd hm hl
  have hno := noOr hm hl
  have hfr := fresh5 hm
  cases m with
  | nil => have := hm.1.2.2; simp at this
  | cons s m =>
    have hv := hm.1.1.1
    have ha : s.2.1 ∈ S5 := List.mem_toFinset.1 hv.1
    have hb : s.2.2 ∈ S5 := List.mem_toFinset.1 hv.2.1
    have hout : out 32767 s ∈ outs 32767 (s :: m) := mem_outs.2 ⟨s, List.mem_cons_self .., rfl⟩
    have hf := hfr _ hout
    by_cases h1 : s.1 = 0
    · have ho : out 32767 s = s.2.1 &&& s.2.2 := by simp [out, h1]
      rw [ho] at hout hf
      rcases S5_and _ ha _ hb with h | ⟨u, hu, v, hv, huv, h⟩
      · exact hf h
      · rw [h] at hout; exact hna u hu v hv huv hout
    · by_cases h2 : s.1 = 1
      · have ho : out 32767 s = s.2.1 ||| s.2.2 := by simp [out, h2]
        rw [ho] at hout hf
        rcases S5_or _ ha _ hb with h | ⟨u, hu, v, hv, huv, h⟩
        · exact hf h
        · rw [h] at hout; exact hno u hu v hv huv hout
      · exact hnn s (List.mem_cons_self ..) (by simp [nt, h1, h2]) ha

-- the final form, one truth table at a time
def Goal (T : ℕ) : Prop := ∀ (gates : List Gate) (o : ℕ),
  (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
  (∀ i j : Fin gates.length, (gates.get i).op = GateOp.not → (gates.get j).op = GateOp.not → i = j) →
  (∀ x : Fin 5 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) =
    Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) →
  ∃ (gates' : List Gate) (o' : ℕ),
    (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

lemma goal_of {T F T' L : ℕ} {pts S : List ℕ} (hp : ∀ p ∈ pts, p < 32)
    (hF : enc pts (fun _ => true) = F) (hS : S.toFinset = SW pts W0) (hT' : sel pts T = T')
    (hTS : T' ∉ S) (hL : ∀ l, Ch F S.toFinset T' l → L ≤ l.length)
    {gates' : List Gate} {o' : ℕ} (hm : Mono gates') (hlen : gates'.length = L)
    (hu : ∀ x, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = tv T x) : Goal T := by
  intro gates o hg hn he
  refine ⟨gates', o', hm, ?_, hu⟩
  rw [hlen]
  exact circ_lb hp hF hS hT' hTS hL hg hn he

lemma goal1 : Goal 0x80000000 :=
  goal_of (pts := [31, 30, 31, 29, 31, 27, 31, 23, 31, 15]) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) clb1 (mono_A (mono_A (mono_A (mono_A mono_nil)))) rfl ub1

lemma goal2 : Goal 0x80808000 :=
  goal_of (pts := [15, 14, 15, 13, 15, 11, 15, 7, 23, 7]) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) clb2 (mono_A (mono_O (mono_A (mono_A mono_nil)))) rfl ub2

lemma goal3 : Goal 0x88808000 :=
  goal_of pts15_lt enc15 S5_eq (by decide +kernel) (by decide +kernel) clb3 (mono_A (mono_A (mono_O (mono_O (mono_A (mono_A mono_nil)))))) rfl ub3

lemma goal4 : Goal 0x88808080 :=
  goal_of (pts := [7, 6, 7, 5, 7, 3, 27, 19, 27, 11]) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) clb4 (mono_A (mono_A (mono_O (mono_A mono_nil)))) rfl ub4

lemma goal5 : Goal 0xa8808000 :=
  goal_of pts15_lt enc15 S5_eq (by decide +kernel) (by decide +kernel) clb5 (mono_A (mono_O (mono_A (mono_O (mono_A (mono_O (mono_A (mono_A mono_nil)))))))) rfl ub5

lemma goal6 : Goal 0xa8808080 :=
  goal_of pts15_lt enc15 S5_eq (by decide +kernel) (by decide +kernel) clb6 (mono_A (mono_A (mono_O (mono_A (mono_O (mono_A mono_nil)))))) rfl ub6

lemma goal7 : Goal 0xe8808000 :=
  goal_of pts15_lt enc15 S5_eq (by decide +kernel) (by decide +kernel) clb7 (mono_A (mono_O (mono_O (mono_A (mono_A (mono_A (mono_A (mono_O (mono_A (mono_O mono_nil)))))))))) rfl ub7

lemma goal8 : Goal 0x88888880 :=
  goal_of (pts := [7, 6, 7, 5, 7, 3, 11, 3, 19, 3]) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) clb8 (mono_O (mono_O (mono_A (mono_A mono_nil)))) rfl ub8

lemma goal9 : Goal 0xa8808880 :=
  goal_of pts15_lt enc15 S5_eq (by decide +kernel) (by decide +kernel) clb9 (mono_A (mono_O (mono_A (mono_O (mono_A (mono_A mono_nil)))))) rfl ub9

lemma goal10 : Goal 0xa888a000 :=
  goal_of (pts := [13, 12, 19, 17, 13, 9, 13, 5, 19, 3]) (by decide) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) clb10 (mono_A (mono_A (mono_O (mono_A mono_nil)))) rfl ub10

end PEqualNP.Outside.L_meta_1415

theorem PEqualNP.Outside.L_meta_1415 : ∀ T ∈ ({0x80000000, 0x80808000, 0x88808000, 0x88808080, 0xa8808000, 0xa8808080, 0xe8808000, 0x88888880, 0xa8808880, 0xa888a000} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T hT
  simp only [Finset.mem_insert, Finset.mem_singleton] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact PEqualNP.Outside.L_meta_1415.goal1
  · exact PEqualNP.Outside.L_meta_1415.goal2
  · exact PEqualNP.Outside.L_meta_1415.goal3
  · exact PEqualNP.Outside.L_meta_1415.goal4
  · exact PEqualNP.Outside.L_meta_1415.goal5
  · exact PEqualNP.Outside.L_meta_1415.goal6
  · exact PEqualNP.Outside.L_meta_1415.goal7
  · exact PEqualNP.Outside.L_meta_1415.goal8
  · exact PEqualNP.Outside.L_meta_1415.goal9
  · exact PEqualNP.Outside.L_meta_1415.goal10
