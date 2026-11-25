import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970.Semantic

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

theorem val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

theorem val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
    val (gs ++ [g]) x i =
      if i = n + gs.length then g.op.eval (g.inputs.map fun j => val gs x j)
      else val gs x i := by
  unfold val
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, step]
  have hl : (gs.foldl step (List.ofFn x)).length = n + gs.length := by
    rw [fold_length]
    simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z : X) :
    (∀ y, g.op.eval (g.inputs.map (f y)) = false) ∨
    ∃ a b, g.op.eval (g.inputs.map (f z)) = false →
      (f z a = false ∧ f z b = false ∧
        ∀ y, g.op.eval (g.inputs.map (f y)) = true → f y a = true ∨ f y b = true) := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · right
      exact ⟨0, 0, by simp [GateOp.eval]⟩
    · left
      simp [GateOp.eval]
  | [a], _ =>
    right
    refine ⟨a, a, ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval]
  | [a, b], _ =>
    rcases hop with rfl | rfl
    · right
      by_cases h : f z a = false
      · refine ⟨a, a, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro _
        exact ⟨h, h, fun y hy => Or.inl hy.1⟩
      · refine ⟨b, b, ?_⟩
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          Bool.and_true, id_eq, Bool.and_eq_true]
        intro hz
        have hb : f z b = false := by
          cases ha : f z a <;> cases hb : f z b <;> simp_all
        exact ⟨hb, hb, fun y hy => Or.inl hy.2⟩
    · right
      refine ⟨a, b, ?_⟩
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        Bool.or_false, id_eq, Bool.or_eq_true, Bool.or_eq_false_iff]
      intro hz
      exact ⟨hz.1, hz.2, fun y hy => hy⟩
  | _ :: _ :: _ :: _, h => simp at h

def Zof {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun c => decide (c ∉ S)

def eof {n : ℕ} (u : Fin n) : Fin n → Bool := fun c => decide (c = u)

def Inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (l : Fin n → Fin n) : Prop :=
  ∀ i u v, val gs (Zof S) i = false → val gs (eof u) i = true → val gs (eof v) i = true →
    u ∈ S ∧ l u = l v

def Cnt {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (i : ℕ) : Prop :=
  val gs (Zof S) i = false ∧
    ∃ u v : Fin n, u ≠ v ∧ val gs (eof u) i = true ∧ val gs (eof v) i = true

open Classical in
noncomputable def D {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i =>
    Cnt S gs i ∧ (gs[i - n]?).map Gate.op = some GateOp.or

open Classical in
noncomputable def orGates (n : ℕ) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter fun i =>
    (gs[i - n]?).map Gate.op = some GateOp.or

theorem D_mono {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D S gs ⊆ D S (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨⟨hz, u, v, huv, hu, hv⟩, hop⟩ := hi.2
  constructor
  · refine ⟨?_, u, v, huv, ?_, ?_⟩
    · rw [val_snoc, ite_eq_right hne]; exact hz
    · rw [val_snoc, ite_eq_right hne]; exact hu
    · rw [val_snoc, ite_eq_right hne]; exact hv
  · rw [List.getElem?_append_left (by omega)]
    exact hop

lemma merging_is_or {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (l : Fin n → Fin n) (hinv : Inv S gs l) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hz : g.op.eval (g.inputs.map fun j => val gs (Zof S) j) = false)
    {u v : Fin n}
    (hu : g.op.eval (g.inputs.map fun j => val gs (eof u) j) = true)
    (hv : g.op.eval (g.inputs.map fun j => val gs (eof v) j) = true)
    (hne : l u ≠ l v) : g.op = GateOp.or := by
  rcases hop with hop | hop
  · exfalso
    rw [hop] at hz hu hv
    simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq,
      List.all_eq_true] at hu hv
    have hnot : ¬ ∀ i ∈ g.inputs, val gs (Zof S) i = true := by
      intro hall
      have htrue : GateOp.and.eval (g.inputs.map fun j => val gs (Zof S) j) = true := by
        simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
        exact hall
      simp_all
    push Not at hnot
    obtain ⟨i, hi, hfalse⟩ := hnot
    have hz' : val gs (Zof S) i = false := by
      cases h : val gs (Zof S) i <;> simp_all
    exact hne (hinv i u v hz' (hu i hi) (hv i hi)).2
  · exact hop

theorem main_inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ l : Fin n → Fin n, Inv S gs l ∧ S.card ≤ (S.image l).card + (D S gs).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ?_, by simp⟩
    intro i u v hz hu hv
    rw [val_nil] at hz hu hv
    by_cases h : i < n
    · simp only [h, dite_true, Zof, eof, decide_eq_false_iff_not, not_not,
        decide_eq_true_eq] at hz hu hv
      subst hu
      subst hv
      exact ⟨hz, rfl⟩
    · simp [h] at hu
  | append_singleton gs g ih =>
    obtain ⟨l, hinv, hcard⟩ := ih (fun g' hg' => hg g' (by simp [hg']))
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    set N := n + gs.length with hN
    set P : (Fin n → Bool) → Bool := fun x => g.op.eval (g.inputs.map fun j => val gs x j)
      with hP
    have hnew : ∀ x : Fin n → Bool, val (gs ++ [g]) x N = P x := by
      intro x
      rw [val_snoc, ite_eq_left hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, ite_eq_right hi]
    -- facts about the new wire from the old invariant
    have key : P (Zof S) = false → ∀ u, P (eof u) = true →
        u ∈ S ∧ ∃ A B : Fin n → Prop, (∀ w, P (eof w) = true → A w ∨ B w) ∧
          (∀ w w', A w → A w' → l w = l w') ∧ (∀ w w', B w → B w' → l w = l w') := by
      intro hz u hu
      rcases gate_cases g hop hlen (fun x j => val gs x j) (Zof S) with hall | ⟨a, b, hab⟩
      · have := hall (eof u)
        simp only [hP] at hu
        rw [this] at hu
        exact absurd hu (by simp)
      · obtain ⟨ha, hb, hy⟩ := hab hz
        refine ⟨?_, fun w => val gs (eof w) a = true, fun w => val gs (eof w) b = true,
          fun w hw => hy (eof w) hw, fun w w' hw hw' => (hinv a w w' ha hw hw').2,
          fun w w' hw hw' => (hinv b w w' hb hw hw').2⟩
        rcases hy (eof u) hu with h | h
        · exact (hinv a u u ha h h).1
        · exact (hinv b u u hb h h).1
    by_cases hm : P (Zof S) = false ∧ ∃ u v, P (eof u) = true ∧ P (eof v) = true ∧ l u ≠ l v
    · obtain ⟨hz, u0, v0, hu0, hv0, hne⟩ := hm
      have hgor : g.op = GateOp.or := merging_is_or S gs l hinv g hop hz hu0 hv0 hne
      refine ⟨fun w => if l w = l v0 then l u0 else l w, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, A, B, hAB, hA, hB⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          have two : ∀ w, P (eof w) = true → l w = l u0 ∨ l w = l v0 := by
            intro w hw
            rcases hAB w hw with h | h <;> rcases hAB u0 hu0 with h0 | h0 <;>
              rcases hAB v0 hv0 with h1 | h1
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inl (hA w u0 h h0)
            · exact Or.inr (hA w v0 h h1)
            · exact absurd (hB u0 v0 h0 h1) hne
            · exact absurd (hA u0 v0 h0 h1) hne
            · exact Or.inr (hB w v0 h h1)
            · exact Or.inl (hB w u0 h h0)
            · exact Or.inl (hB w u0 h h0)
          have red : ∀ w, P (eof w) = true → (if l w = l v0 then l u0 else l w) = l u0 := by
            intro w hw
            rcases two w hw with h | h
            · rw [h]; split_ifs <;> rfl
            · rw [ite_eq_left h]
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [red u hiu, red v hiv]
        · rw [hold _ _ hi] at hiz hiu hiv
          obtain ⟨huS, hl⟩ := hinv i u v hiz hiu hiv
          refine ⟨huS, ?_⟩
          show (if l u = l v0 then l u0 else l u) = (if l v = l v0 then l u0 else l v)
          rw [hl]
      · have himg : S.image l ⊆
            insert (l v0) (S.image fun w => if l w = l v0 then l u0 else l w) := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
          by_cases h : l w = l v0
          · rw [h]; exact Finset.mem_insert_self _ _
          · refine Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨w, hw, ?_⟩)
            rw [ite_eq_right h]
        have h1 : (S.image l).card ≤
            (S.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNin : N ∈ D S (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ⟨?_, u0, v0, ?_, ?_, ?_⟩, ?_⟩
          · rw [hnew]; exact hz
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
          · simp [hN, hgor]
        have hNnot : N ∉ D S gs := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico]
          intro h
          omega
        have h2 : (D S gs).card + 1 ≤ (D S (gs ++ [g])).card := by
          rw [← Finset.card_insert_of_notMem hNnot]
          apply Finset.card_le_card
          intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · exact hNin
          · exact D_mono S gs g hi
        omega
    · refine ⟨l, ?_, ?_⟩
      · intro i u v hiz hiu hiv
        by_cases hi : i = N
        · subst hi
          rw [hnew] at hiz hiu hiv
          obtain ⟨huS, -⟩ := key hiz u hiu
          refine ⟨huS, ?_⟩
          by_contra hne
          exact hm ⟨hiz, u, v, hiu, hiv, hne⟩
        · rw [hold _ _ hi] at hiz hiu hiv
          exact hinv i u v hiz hiu hiv
      · have := Finset.card_le_card (D_mono S gs g)
        omega

lemma or_outputs_bound : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ (orGates n gates).card := by
  classical
  intro n m S hS gates out hg hev
  have hval : ∀ (w : Fin m) (x : Fin n → Bool),
      val gates x (out w) = decide (∃ v ∈ S w, x v = true) := fun w x => hev w x
  have hZ : ∀ w, val gates (Zof (S w)) (out w) = false := by
    intro w
    rw [hval]
    simp [Zof]
  have hE : ∀ w, ∀ u ∈ S w, val gates (eof u) (out w) = true := by
    intro w u hu
    rw [hval]
    simp only [decide_eq_true_eq]
    exact ⟨u, hu, by simp [eof]⟩
  choose l hinv hcard using fun w => main_inv (S w) gates hg
  have hbound : ∀ w, (S w).card - 1 ≤ (D (S w) gates).card := by
    intro w
    have h1 : ((S w).image (l w)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact (hinv w (out w) u v (hZ w) (hE w u hu) (hE w v hv)).2
    have := hcard w
    omega
  have hdisj : ∀ a ∈ (Finset.univ : Finset (Fin m)), ∀ b ∈ (Finset.univ : Finset (Fin m)),
      a ≠ b → Disjoint (D (S a) gates) (D (S b) gates) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro i hia hib
    simp only [D, Finset.mem_filter, Finset.mem_Ico] at hia hib
    obtain ⟨-, ⟨hza, u, v, huv, hu, hv⟩, -⟩ := hia
    obtain ⟨-, ⟨hzb, -⟩, -⟩ := hib
    have hua := (hinv a i u u hza hu hu).1
    have hva := (hinv a i v v hza hv hv).1
    have hub := (hinv b i u u hzb hu hu).1
    have hvb := (hinv b i v v hzb hv hv).1
    have hsub : ({u, v} : Finset (Fin n)) ⊆ S a ∩ S b := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hua, hub⟩
      · exact Finset.mem_inter.mpr ⟨hva, hvb⟩
    have h2 : ({u, v} : Finset (Fin n)).card = 2 := Finset.card_pair huv
    have := Finset.card_le_card hsub
    have := hS a b hab
    omega
  calc ∑ w, ((S w).card - 1) ≤ ∑ w, (D (S w) gates).card :=
        Finset.sum_le_sum fun w _ => hbound w
    _ = (Finset.univ.biUnion fun w => D (S w) gates).card :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ (orGates n gates).card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hi
        simp only [D, Finset.mem_filter] at hw
        exact Finset.mem_filter.mpr ⟨hw.1, hw.2.2⟩


def bilinear {p l : ℕ} (E : Finset (Fin p × Fin l))
    (x : Fin (p+l) → Bool) : Bool :=
  decide (∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)

def adjacent {p l : ℕ} (E : Finset (Fin p × Fin l)) (u v : Fin (p+l)) : Prop :=
  ∃ a b, (a,b) ∈ E ∧
    ((u = Fin.castAdd l a ∧ v = Fin.natAdd p b) ∨
      (v = Fin.castAdd l a ∧ u = Fin.natAdd p b))

lemma left_ne_right {p l : ℕ} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  have := a.isLt
  omega

lemma fin_split {p l : ℕ} (u : Fin (p+l)) :
    (∃ a : Fin p, u = Fin.castAdd l a) ∨ ∃ b : Fin l, u = Fin.natAdd p b :=
  Fin.addCases (fun a => Or.inl ⟨a, rfl⟩) (fun b => Or.inr ⟨b, rfl⟩) u

lemma adjacent_left_left {p l : ℕ} (E : Finset (Fin p × Fin l)) (a a' : Fin p) :
    ¬ adjacent E (Fin.castAdd l a) (Fin.castAdd l a') := by
  rintro ⟨b,c,_,h|h⟩
  · exact left_ne_right a' c h.2
  · exact left_ne_right a c h.2

lemma adjacent_right_right {p l : ℕ} (E : Finset (Fin p × Fin l)) (b b' : Fin l) :
    ¬ adjacent E (Fin.natAdd p b) (Fin.natAdd p b') := by
  rintro ⟨a,c,_,h|h⟩
  · exact left_ne_right a b h.1.symm
  · exact left_ne_right a b' h.1.symm

lemma adjacent_left_right {p l : ℕ} (E : Finset (Fin p × Fin l)) (a : Fin p) (b : Fin l) :
    adjacent E (Fin.castAdd l a) (Fin.natAdd p b) ↔ (a,b) ∈ E := by
  constructor
  · rintro ⟨a',b',he,h|h⟩
    · have ha : a = a' := Fin.ext (congrArg (fun z : Fin (p+l) => z.val) h.1)
      have hb : b = b' := by
        apply Fin.ext
        have := congrArg Fin.val h.2
        simp only [Fin.val_natAdd] at this
        omega
      simpa [ha,hb] using he
    · exact (left_ne_right a b' h.2).elim
  · intro he
    exact ⟨a,b,he,Or.inl ⟨rfl,rfl⟩⟩

lemma adjacent_symm {p l : ℕ} (E : Finset (Fin p × Fin l)) {u v : Fin (p+l)} :
    adjacent E u v → adjacent E v u := by
  rintro ⟨a,b,he,h⟩
  exact ⟨a,b,he,h.symm⟩

lemma adjacent_right_left {p l : ℕ} (E : Finset (Fin p × Fin l)) (a : Fin p) (b : Fin l) :
    adjacent E (Fin.natAdd p b) (Fin.castAdd l a) ↔ (a,b) ∈ E := by
  constructor
  · intro h
    exact (adjacent_left_right E a b).mp (adjacent_symm E h)
  · intro h
    exact adjacent_symm E ((adjacent_left_right E a b).mpr h)

lemma adjacent_four_cycle_free {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    {u u' v v' : Fin (p+l)} (hu : u ≠ u') (hv : v ≠ v')
    (h11 : adjacent E u v) (h12 : adjacent E u v')
    (h21 : adjacent E u' v) (h22 : adjacent E u' v') : False := by
  rcases fin_split u with ⟨a,rfl⟩ | ⟨b,rfl⟩ <;>
    rcases fin_split u' with ⟨a',rfl⟩ | ⟨b',rfl⟩ <;>
    rcases fin_split v with ⟨c,rfl⟩ | ⟨d,rfl⟩ <;>
    rcases fin_split v' with ⟨c',rfl⟩ | ⟨d',rfl⟩
  all_goals simp only [adjacent_left_left, adjacent_right_right, adjacent_left_right,
    adjacent_right_left] at *
  · exact hcycle a a' d d' (fun h => hu (congrArg (Fin.castAdd l) h))
      (fun h => hv (congrArg (Fin.natAdd p) h)) ⟨h11,h12,h21,h22⟩
  · exact hcycle c c' b b' (fun h => hv (congrArg (Fin.castAdd l) h))
      (fun h => hu (congrArg (Fin.natAdd p) h)) ⟨h11,h21,h12,h22⟩


def pair {n : ℕ} (u v : Fin n) : Fin n → Bool :=
  fun i => decide (i = u ∨ i = v)

lemma bilinear_pair_iff {p l : ℕ} (E : Finset (Fin p × Fin l)) (u v : Fin (p+l)) :
    bilinear E (pair u v) = true ↔ adjacent E u v := by
  constructor
  · intro h
    obtain ⟨a,b,he,ha,hb⟩ := of_decide_eq_true h
    have ha' : Fin.castAdd l a = u ∨ Fin.castAdd l a = v := of_decide_eq_true ha
    have hb' : Fin.natAdd p b = u ∨ Fin.natAdd p b = v := of_decide_eq_true hb
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb'
    · exact (left_ne_right a b (ha'.trans hb'.symm)).elim
    · exact ⟨a,b,he,Or.inl ⟨ha'.symm,hb'.symm⟩⟩
    · exact ⟨a,b,he,Or.inr ⟨ha'.symm,hb'.symm⟩⟩
    · exact (left_ne_right a b (ha'.trans hb'.symm)).elim
  · rintro ⟨a,b,he,h|h⟩
    · exact decide_eq_true ⟨a,b,he,by simp [pair,h.1,h.2],by simp [pair,h.1,h.2]⟩
    · exact decide_eq_true ⟨a,b,he,by simp [pair,h.1,h.2],by simp [pair,h.1,h.2]⟩

def support {n : ℕ} (f : (Fin n → Bool) → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun u => f (eof u) = true

lemma support_cross {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f g : (Fin (p+l) → Bool) → Bool)
    (hf : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hg : ∀ x y, (∀ i, x i = true → y i = true) → g x = true → g y = true)
    (hbelow : ∀ x, f x = true → g x = true → bilinear E x = true)
    {u v : Fin (p+l)} (hu : u ∈ support f) (hv : v ∈ support g) : adjacent E u v := by
  apply (bilinear_pair_iff E u v).mp
  apply hbelow
  · apply hf (eof u) (pair u v) _ (Finset.mem_filter.mp hu).2
    intro i hi
    have h : i = u := of_decide_eq_true hi
    simp [pair,h]
  · apply hg (eof v) (pair u v) _ (Finset.mem_filter.mp hv).2
    intro i hi
    have h : i = v := of_decide_eq_true hi
    simp [pair,h]

lemma cross_is_star {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (A B : Finset (Fin (p+l))) (hcross : ∀ u ∈ A, ∀ v ∈ B, adjacent E u v) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_cases ha : A.card ≤ 1
  · exact Or.inl ha
  by_cases hb : B.card ≤ 1
  · exact Or.inr hb
  obtain ⟨u,hu,u',hu',huu⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  obtain ⟨v,hv,v',hv',hvv⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
  exact (adjacent_four_cycle_free E hcycle huu hvv
    (hcross u hu v hv) (hcross u hu v' hv')
    (hcross u' hu' v hv) (hcross u' hu' v' hv')).elim

lemma boundary_and_star {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hcycle : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a,b) ∈ E ∧ (a,b') ∈ E ∧ (a',b) ∈ E ∧ (a',b') ∈ E))
    (f g : (Fin (p+l) → Bool) → Bool)
    (hf : ∀ x y, (∀ i, x i = true → y i = true) → f x = true → f y = true)
    (hg : ∀ x y, (∀ i, x i = true → y i = true) → g x = true → g y = true)
    (hbelow : ∀ x, f x = true → g x = true → bilinear E x = true)
    (hneF : (support f).Nonempty) (hneG : (support g).Nonempty) :
    (∃ u, support f = {u} ∧ ∀ v ∈ support g, adjacent E u v) ∨
      (∃ v, support g = {v} ∧ ∀ u ∈ support f, adjacent E u v) := by
  have hcross : ∀ u ∈ support f, ∀ v ∈ support g, adjacent E u v :=
    fun u hu v hv => support_cross E f g hf hg hbelow hu hv
  rcases cross_is_star E hcycle (support f) (support g) hcross with hf1 | hg1
  · obtain ⟨u,hu⟩ := hneF
    have heq : support f = {u} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hu,?_⟩
      intro v hv
      exact Finset.card_le_one.mp hf1 v hv u hu
    exact Or.inl ⟨u,heq,fun v hv => hcross u hu v hv⟩
  · obtain ⟨v,hv⟩ := hneG
    have heq : support g = {v} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hv,?_⟩
      intro u hu
      exact Finset.card_le_one.mp hg1 u hu v hv
    exact Or.inr ⟨v,heq,fun u hu => hcross u hu v hv⟩


lemma gate_eval_monotone (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : ℕ → Bool) (hxy : ∀ i, x i = true → y i = true) :
    g.op.eval (g.inputs.map x) = true → g.op.eval (g.inputs.map y) = true := by
  rcases hg with hg | hg
  · rw [hg]
    simp only [GateOp.eval, List.all_map, Function.comp_def, id_eq, List.all_eq_true]
    intro h i hi
    exact hxy i (h i hi)
  · rw [hg]
    simp only [GateOp.eval, List.any_map, Function.comp_def, id_eq, List.any_eq_true]
    rintro ⟨i,hi,h⟩
    exact ⟨i,hi,hxy i h⟩

lemma val_monotone {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ i, val gs x i = true → val gs y i = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    rw [val_nil] at hi ⊢
    split_ifs at hi ⊢ with h
    · exact hxy ⟨i,h⟩ hi
  | append_singleton gs g ih =>
    have hold := ih (fun v hv => hg v (by simp [hv]))
    intro i hi
    rw [val_snoc] at hi ⊢
    split_ifs at hi ⊢ with h
    · exact gate_eval_monotone g (hg g (by simp)) _ _ hold hi
    · exact hold i hi


lemma pure_or_preserved {n : ℕ} (Q : Finset (Fin n))
    (f h : (Fin n → Bool) → Bool)
    (hf : ∀ x, f x = decide (∃ u ∈ Q, x u = true))
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → h x = true → h y = true)
    (hbelow : ∀ x, h x = true → f x = true)
    (hsingle : ∀ u, h (eof u) = f (eof u)) : h = f := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact hbelow x
  · intro hx
    obtain ⟨u,hu,hxu⟩ := of_decide_eq_true ((hf x).symm ▸ hx)
    apply hmono (eof u) x
    · intro i hi
      have heq : i = u := of_decide_eq_true hi
      simpa [heq] using hxu
    · rw [hsingle,hf]
      exact decide_eq_true ⟨u,hu,by simp [eof]⟩


def zeroGate : Gate := ⟨GateOp.or, []⟩

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) :
    (step w g).getD i false =
      if i = w.length then g.op.eval (g.inputs.map fun j => w.getD j false)
      else w.getD i false := by
  unfold step
  rcases lt_trichotomy i w.length with h | h | h
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left h]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [h]
  · rw [ite_eq_right (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma step_monotone (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (hlen : w.length = v.length)
    (hle : ∀ i, w.getD i false = true → v.getD i false = true) :
    ∀ i, (step w g).getD i false = true → (step v g).getD i false = true := by
  intro i hi
  rw [step_getD] at hi ⊢
  rw [← hlen]
  split_ifs at hi ⊢ with h
  · exact gate_eval_monotone g hg _ _ hle hi
  · exact hle i hi

lemma fold_state_monotone (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w v : List Bool) (hlen : w.length = v.length)
    (hle : ∀ i, w.getD i false = true → v.getD i false = true) :
    ∀ i, (gs.foldl step w).getD i false = true → (gs.foldl step v).getD i false = true := by
  induction gs generalizing w v with
  | nil => exact hle
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
    · simp [step,hlen]
    · exact step_monotone g (hg g List.mem_cons_self) w v hlen hle

lemma val_append_old {n : ℕ} (pre post : List Gate) (x : Fin n → Bool)
    (i : ℕ) (hi : i < n + pre.length) : val (pre ++ post) x i = val pre x i := by
  induction post using List.reverseRecOn with
  | nil => simp
  | append_singleton post g ih =>
    have hne : i ≠ n + (pre ++ post).length := by
      simp only [List.length_append]
      omega
    rw [← List.append_assoc, val_snoc, ite_eq_right hne]
    exact ih

lemma cut_zero_agrees {n : ℕ} (pre post : List Gate) (g : Gate) (x : Fin n → Bool)
    (hz : val (pre ++ [g] ++ post) x (n + pre.length) = false) :
    ∀ i, val (pre ++ [zeroGate] ++ post) x i = val (pre ++ [g] ++ post) x i := by
  have hp : val (pre ++ [g]) x (n + pre.length) = false := by
    have heq := val_append_old (pre ++ [g]) post x (n + pre.length) (by simp)
    exact heq.symm.trans hz
  rw [val_snoc, ite_eq_left rfl] at hp
  have hs : step (pre.foldl step (List.ofFn x)) zeroGate =
      step (pre.foldl step (List.ofFn x)) g := by
    change g.op.eval (g.inputs.map fun j =>
      (pre.foldl step (List.ofFn x)).getD j false) = false at hp
    exact congrArg (fun b => pre.foldl step (List.ofFn x) ++ [b]) hp.symm
  intro i
  simp only [val, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [hs]

lemma cut_zero_below {n : ℕ} (pre post : List Gate) (g : Gate)
    (hpost : ∀ k ∈ post, k.op = GateOp.and ∨ k.op = GateOp.or)
    (x : Fin n → Bool) :
    ∀ i, val (pre ++ [zeroGate] ++ post) x i = true →
      val (pre ++ [g] ++ post) x i = true := by
  simp only [val, List.foldl_append, List.foldl_cons, List.foldl_nil]
  apply fold_state_monotone post hpost
  · simp [step]
  · intro i hi
    rw [step_getD] at hi ⊢
    split_ifs at hi ⊢ with h
    · simp [zeroGate,GateOp.eval] at hi
    · exact hi

lemma cut_zero_preserves_or {n : ℕ} (pre post : List Gate) (g : Gate)
    (hg : ∀ k ∈ pre ++ [g] ++ post, k.op = GateOp.and ∨ k.op = GateOp.or)
    (Q : Finset (Fin n)) (out : ℕ)
    (hor : ∀ x, val (pre ++ [g] ++ post) x out = decide (∃ u ∈ Q, x u = true))
    (hzero : ∀ u : Fin n, val (pre ++ [g] ++ post) (eof u) (n + pre.length) = false) :
    ∀ x, val (pre ++ [zeroGate] ++ post) x out = decide (∃ u ∈ Q, x u = true) := by
  have hp : ∀ k ∈ post, k.op = GateOp.and ∨ k.op = GateOp.or := by
    intro k hk
    exact hg k (by simp [hk])
  have hnew : ∀ k ∈ pre ++ [zeroGate] ++ post, k.op = GateOp.and ∨ k.op = GateOp.or := by
    intro k hk
    simp only [List.mem_append, List.mem_singleton] at hk
    rcases hk with (hk | rfl) | hk
    · exact hg k (by simp [hk])
    · exact Or.inr rfl
    · exact hp k hk
  have heq := pure_or_preserved Q
    (fun x => val (pre ++ [g] ++ post) x out)
    (fun x => val (pre ++ [zeroGate] ++ post) x out) hor
    (fun x y hxy => val_monotone _ hnew x y hxy out)
    (fun x => cut_zero_below pre post g hp x out)
    (fun u => cut_zero_agrees pre post g (eof u) (hzero u) out)
  intro x
  exact congrFun heq x |>.trans (hor x)


lemma cut_zero_lift {n : ℕ} (pre post : List Gate) (g : Gate)
    (ancestor out : ℕ)
    (hreader : ∀ x : Fin n → Bool,
      val (pre ++ [g] ++ post) x (n + pre.length) = true →
        val (pre ++ [g] ++ post) x ancestor = true)
    (hbelow : ∀ x : Fin n → Bool,
      val (pre ++ [g] ++ post) x ancestor = true →
        val (pre ++ [g] ++ post) x out = true) :
    ∀ x : Fin n → Bool,
      val (pre ++ [g] ++ post) x out =
        (val (pre ++ [zeroGate] ++ post) x out ||
          val (pre ++ [g] ++ post) x ancestor) := by
  intro x
  cases ha : val (pre ++ [g] ++ post) x ancestor with
  | false =>
    have hz : val (pre ++ [g] ++ post) x (n + pre.length) = false := by
      cases h : val (pre ++ [g] ++ post) x (n + pre.length)
      · rfl
      · have htrue := hreader x h
        rw [ha] at htrue
        cases htrue
    rw [Bool.or_false, cut_zero_agrees pre post g x hz out]
  | true =>
    rw [Bool.or_true, hbelow x ha]

lemma and_pure_or_operand {n : ℕ} (Q : Finset (Fin n)) (inputs : List ℕ)
    (f : ℕ → (Fin n → Bool) → Bool)
    (hmono : ∀ i ∈ inputs, ∀ x y,
      (∀ u, x u = true → y u = true) → f i x = true → f i y = true)
    (hfun : ∀ x, (inputs.map (fun i => f i x)).all id =
      decide (∃ u ∈ Q, x u = true)) :
    ∃ i ∈ inputs, ∀ x, f i x = decide (∃ u ∈ Q, x u = true) := by
  have hz : (inputs.map (fun i => f i (Zof Q))).all id = false := by
    rw [hfun]
    simp [Zof]
  obtain ⟨i, hi, hiz⟩ : ∃ i ∈ inputs, f i (Zof Q) = false := by
    simpa [List.all_map, List.all_eq_false] using hz
  have hsingle : ∀ u ∈ Q, f i (eof u) = true := by
    intro u hu
    have h := hfun (eof u)
    have ht : decide (∃ v ∈ Q, eof u v = true) = true :=
      decide_eq_true ⟨u, hu, by simp [eof]⟩
    rw [ht] at h
    simp only [List.all_map, Function.comp_apply, id_eq, List.all_eq_true] at h
    exact h i hi
  refine ⟨i, hi, fun x => Bool.eq_iff_iff.mpr ⟨?_, ?_⟩⟩
  · intro hx
    apply decide_eq_true
    by_contra hnone
    have hle : ∀ u, x u = true → Zof Q u = true := by
      intro u hu
      apply decide_eq_true
      intro hmem
      exact hnone ⟨u, hmem, hu⟩
    have bad := hmono i hi x (Zof Q) hle hx
    rw [hiz] at bad
    cases bad
  · intro hx
    obtain ⟨u, hu, hxu⟩ := of_decide_eq_true hx
    apply hmono i hi (eof u) x
    · intro v hv
      have hve : v = u := of_decide_eq_true hv
      simpa [hve] using hxu
    · exact hsingle u hu

lemma pure_or_has_or_gate {n : ℕ} (Q : Finset (Fin n)) (hQ : 2 ≤ Q.card)
    (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (out : ℕ) (hout : ∀ x : Fin n → Bool,
      val gs x out = decide (∃ u ∈ Q, x u = true)) :
    ∃ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
      ∀ x : Fin n → Bool, val gs x (n + j) = decide (∃ u ∈ Q, x u = true) := by
  induction gs using List.reverseRecOn generalizing out with
  | nil =>
    have hmembers : ∀ u ∈ Q, u.val = out := by
      intro u hu
      have ht : val [] (eof u) out = true :=
        (hout (eof u)).trans (decide_eq_true ⟨u, hu, by simp [eof]⟩)
      rw [val_nil] at ht
      split_ifs at ht with h
      · have heq : (⟨out, h⟩ : Fin n) = u := of_decide_eq_true ht
        exact (congrArg Fin.val heq).symm
    have hone : Q.card ≤ 1 := Finset.card_le_one.mpr (by
      intro u hu v hv
      exact Fin.ext ((hmembers u hu).trans (hmembers v hv).symm))
    omega
  | append_singleton gs g ih =>
    have hpre : ∀ k ∈ gs, k.op = GateOp.and ∨ k.op = GateOp.or :=
      fun k hk => hgs k (by simp [hk])
    have lift : (∃ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∀ x : Fin n → Bool, val gs x (n + j) = decide (∃ u ∈ Q, x u = true)) →
        ∃ j < (gs ++ [g]).length, ((gs ++ [g]).getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
          ∀ x : Fin n → Bool, val (gs ++ [g]) x (n + j) =
            decide (∃ u ∈ Q, x u = true) := by
      rintro ⟨j, hj, hop, hval⟩
      refine ⟨j, by simp; omega, ?_, ?_⟩
      · simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj] using hop
      · intro x
        rw [val_snoc, ite_eq_right (by omega)]
        exact hval x
    by_cases ho : out = n + gs.length
    · have hlast : ∀ x : Fin n → Bool,
          g.op.eval (g.inputs.map fun i => val gs x i) = decide (∃ u ∈ Q, x u = true) := by
        intro x
        simpa [ho, val_snoc] using hout x
      rcases hgs g (by simp) with hop | hop
      · obtain ⟨i, _, hi⟩ := and_pure_or_operand Q g.inputs (fun i x => val gs x i)
          (fun i _ x y hxy => val_monotone gs hpre x y hxy i)
          (by simpa only [hop, GateOp.eval] using hlast)
        exact lift (ih hpre i hi)
      · refine ⟨gs.length, by simp, ?_, ?_⟩
        · simpa [List.getD_eq_getElem?_getD] using hop
        · simpa only [ho] using hout
    · apply lift
      apply ih hpre out
      intro x
      simpa only [val_snoc, ite_eq_right ho] using hout x

lemma circuit_pure_or_has_or_gate {n : ℕ} (Q : Finset (Fin n)) (hQ : 2 ≤ Q.card)
    (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n C) (out : ℕ)
    (hout : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD out false = decide (∃ u ∈ Q, x u = true)) :
    ∃ j < C.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = GateOp.or ∧
      ∀ x : Fin n → Bool,
        (C.wires (List.ofFn x)).getD (n + j) false = decide (∃ u ∈ Q, x u = true) := by
  exact pure_or_has_or_gate Q hQ C.gates hAO.1 out hout

end PEqualNP.Outside.L_meta_4970.Semantic
