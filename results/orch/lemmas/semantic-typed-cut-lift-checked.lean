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

end PEqualNP.Outside.L_meta_4970.Semantic

namespace PEqualNP.Outside.L_meta_4970.Compression

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



def u (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del : Finset ℕ) (L : ℕ → List ℕ) (x : List Bool)
    (w : ℕ) : Bool :=
  if w < n then x.getD w false
  else if w - n ∈ Del then false
  else if A (w - n) = true then
    ((if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
      (L (w - n)).any (fun t => x.getD t false)) &&
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
  else
    (if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
termination_by w

section Parameters
variable {n : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ} {x : List Bool}

theorem u_in {w : ℕ} (h : w < n) : u n A a b Del L x w = x.getD w false := by
  rw [u, ite_eq_left h]

theorem u_del {j : ℕ} (h : j ∈ Del) : u n A a b Del L x (n + j) = false := by
  rw [u, ite_eq_right (by omega), Nat.add_sub_cancel_left, ite_eq_left h]

theorem u_and {j : ℕ} (h : j ∉ Del) (hA : A j = true) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = ((u n A a b Del L x (a j) ||
      (L j).any (fun t => x.getD t false)) && u n A a b Del L x (b j)) := by
  rw [u, ite_eq_right (by omega), Nat.add_sub_cancel_left, ite_eq_right h, ite_eq_left hA, dite_eq_left ha, dite_eq_left hb]

theorem u_or {j : ℕ} (h : j ∉ Del) (hA : A j = false) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = (u n A a b Del L x (a j) || u n A a b Del L x (b j)) := by
  rw [u, ite_eq_right (by omega), Nat.add_sub_cancel_left, ite_eq_right h, ite_eq_right (by simp [hA]), dite_eq_left ha,
    dite_eq_left hb]
end Parameters

def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

theorem ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

open Classical in
noncomputable def dc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter fun i => (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧
    ∃ x : Fin n → Bool, (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false).card

open Classical in
theorem dc_snoc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) (g : Gate) :
    dc n F (gs ++ [g]) ≤ dc n F gs + if g.op = GateOp.and ∧
      ∃ x : Fin n → Bool, (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧
        F x = false then 1 else 0 := by
  unfold dc
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have e : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
  rw [e]
  have h1 : ((Finset.range gs.length).filter fun i =>
      ((gs ++ [g]).getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + i) false = true ∧ F x = false) =
      (Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false := by
    refine Finset.filter_congr fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [getD_ltz _ _ _ _ hi']
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs [g] _ _ (by simp; omega)]
  rw [h1]
  split_ifs with h
  · exact (Finset.card_insert_le _ _)
  · simp

def ov (gs : List Gate) (x : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => (run gs x).getD w false

theorem ov_ext (gs hs : List Gate) (x : List Bool) (o : Option ℕ)
    (h : ∀ w, o = some w → w < x.length + gs.length) : ov (gs ++ hs) x o = ov gs x o := by
  cases o with
  | none => rfl
  | some w => exact run_prefix gs hs x w (h w rfl)

theorem ov_new (gs : List Gate) (n : ℕ) (x : List Bool) (hx : x.length = n) (o : GateOp) (s t : ℕ)
    (hs : s < n + gs.length) (ht : t < n + gs.length) :
    ov (gs ++ [⟨o, [s, t]⟩]) x (some (n + gs.length)) =
      o.eval [(run gs x).getD s false, (run gs x).getD t false] := by
  unfold ov
  simp only
  rw [run_snoc]
  have : n + gs.length = (run gs x).length := by rw [run_length, hx]
  rw [this, getD_at]
  rfl

theorem chain (n : ℕ) (F : (Fin n → Bool) → Bool) : ∀ (l : List ℕ), (∀ t ∈ l, t < n) →
    ∀ (gs : List Gate), Ok n gs → ∀ o : Option ℕ, (∀ w, o = some w → w < n + gs.length) →
    ∃ (hs : List Gate) (o' : Option ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ l.length ∧
      dc n F (gs ++ hs) ≤ dc n F gs ∧ (∀ w, o' = some w → w < n + (gs ++ hs).length) ∧
      ∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o' =
        (ov gs (List.ofFn x) o || l.any (fun t => (List.ofFn x).getD t false)) := by
  intro l
  induction l with
  | nil =>
    intro _ gs hgs o ho
    exact ⟨[], o, by simpa using hgs, by simp, by simp, by simpa using ho, by simp⟩
  | cons t l ih =>
    intro hl gs hgs o ho
    have ht : t < n := hl t (by simp)
    have hl' : ∀ t ∈ l, t < n := fun s hs => hl s (by simp [hs])
    cases o with
    | none =>
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' gs hgs (some t) (by
        intro w hw; cases hw; omega)
      refine ⟨hs, o', h1, by simp; omega, h3, h4, fun x => ?_⟩
      rw [h5 x]
      have : ov gs (List.ofFn x) (some t) = (List.ofFn x).getD t false :=
        run_input _ _ _ (by simpa using ht)
      rw [this]; simp [ov]
    | some w =>
      have hw := ho w rfl
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' (gs ++ [⟨GateOp.or, [w, t]⟩])
        (ok_snoc hgs (Or.inr rfl) hw (by omega)) (some (n + gs.length)) (by
          intro w hw; cases hw; simp)
      refine ⟨⟨GateOp.or, [w, t]⟩ :: hs, o', by simpa using h1, by simp; omega, ?_,
        by simpa using h4, fun x => ?_⟩
      · have := dc_snoc n F gs ⟨GateOp.or, [w, t]⟩
        rw [ite_eq_right (by simp)] at this
        have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e]; omega
      · have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e, h5 x, ov_new gs n _ (by simp) _ _ _ hw (by omega)]
        rw [run_input gs (List.ofFn x) t (by simpa using ht)]
        simp [ov, GateOp.eval, Bool.or_assoc]

open Classical in
theorem build (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del R : Finset ℕ) (L : ℕ → List ℕ)
    (F : (Fin n → Bool) → Bool) (hL : ∀ j, ∀ t ∈ L j, t < n)
    (hR : ∀ j ∈ R, A j = false ∧ j ∉ Del ∧ ∃ d ∈ Del, d < j ∧ (a j = n + d ∨ b j = n + d)) :
    ∀ p, (∀ j < p, a j < n + j ∧ b j < n + j) →
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n + p, (∀ w', m w = some w' → w' < n + gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) = u n A a b Del L (List.ofFn x) w) ∧
      (∀ d ∈ Del, d < p → m (n + d) = none) ∧
      gs.length + ((Finset.range p).filter (· ∈ Del)).card +
        ((Finset.range p).filter (· ∈ R)).card ≤ p + ∑ j ∈ Finset.range p, (L j).length ∧
      dc n F gs ≤ ((Finset.range p).filter fun j => A j = true ∧ j ∉ Del ∧
        ∃ x : Fin n → Bool, u n A a b Del L (List.ofFn x) (n + j) = true ∧ F x = false).card := by
  intro p
  induction p with
  | zero =>
    intro _
    refine ⟨[], fun w => some w, by intro j hj; simp at hj, ?_, by simp, by simp, by simp [dc]⟩
    intro w hw
    refine ⟨by intro w' h; cases h; simpa using hw, fun x => ?_⟩
    rw [u_in (by omega)]; rfl
  | succ p ih =>
    intro hab
    obtain ⟨gs, m, hok, hm, hd, hc, hj⟩ := ih fun j hj => hab j (by omega)
    obtain ⟨hap, hbp⟩ := hab p (by omega)
    suffices hh : ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧
        (∀ w, o = some w → w < n + (gs ++ hs).length) ∧ (p ∈ Del → o = none) ∧
        (∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o =
          u n A a b Del L (List.ofFn x) (n + p)) ∧
        hs.length + (if p ∈ Del then 1 else 0) + (if p ∈ R then 1 else 0) ≤ 1 + (L p).length ∧
        dc n F (gs ++ hs) ≤ dc n F gs + if A p = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
          u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false then 1 else 0 by
      obtain ⟨hs, o, h1, h2, h3, h4, h5, h6⟩ := hh
      refine ⟨gs ++ hs, Function.update m (n + p) o, h1, ?_, ?_, ?_, ?_⟩
      · intro w hw
        by_cases hwp : w = n + p
        · subst hwp; rw [Function.update_self]; exact ⟨h2, h4⟩
        · rw [Function.update_of_ne hwp]
          obtain ⟨q1, q2⟩ := hm w (by omega)
          refine ⟨fun w' hw' => by have := q1 w' hw'; simp; omega, fun x => ?_⟩
          rw [ov_ext gs hs _ _ (by simpa using q1), q2]
      · intro d hdd hdp
        by_cases hdp' : d = p
        · subst hdp'; rw [Function.update_self]; exact h3 hdd
        · rw [Function.update_of_ne (by omega)]; exact hd d hdd (by omega)
      · rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert,
          Finset.sum_insert (by simp), List.length_append]
        split_ifs at h5 ⊢ with q1 q2 q2 <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;> omega
      · rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs at h6 ⊢ with q1
        · rw [Finset.card_insert_of_notMem (by simp)]; omega
        · omega
    by_cases hpd : p ∈ Del
    · have hpR : p ∉ R := fun h => (hR p h).2.1 hpd
      refine ⟨[], none, by simpa using hok, by simp, fun _ => rfl, fun x => ?_, ?_, by simp⟩
      · rw [u_del hpd]; rfl
      · rw [ite_eq_left hpd, ite_eq_right hpR]; simp
    obtain ⟨a1, a2⟩ := hm (a p) hap
    obtain ⟨b1, b2⟩ := hm (b p) hbp
    cases hA : A p with
    | false =>
      have hu := fun x : Fin n → Bool => u_or (L := L) (x := List.ofFn x) hpd hA hap hbp
      rcases ha0 : m (a p) with _ | s
      · refine ⟨[], m (b p), by simpa using hok, by simpa using b1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, ha0]; simp [ov]
        · rw [ite_eq_right hpd]; split_ifs <;> simp
      rcases hb0 : m (b p) with _ | t
      · refine ⟨[], m (a p), by simpa using hok, by simpa using a1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, hb0]; simp [ov]
        · rw [ite_eq_right hpd]; split_ifs <;> simp
      have hpR : p ∉ R := by
        intro h
        obtain ⟨_, _, d, hd1, hd2, hd3⟩ := hR p h
        have := hd d hd1 hd2
        rcases hd3 with h | h
        · rw [h, this] at ha0; cases ha0
        · rw [h, this] at hb0; cases hb0
      have hs := a1 s ha0
      have ht := b1 t hb0
      refine ⟨[⟨GateOp.or, [s, t]⟩], some (n + gs.length), ok_snoc hok (Or.inr rfl) hs ht,
        by intro w hw; cases hw; simp, fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [ov_new gs n _ (by simp) _ _ _ hs ht, hu x, ← a2 x, ← b2 x, ha0, hb0]
        simp [ov, GateOp.eval]
      · rw [ite_eq_right hpd, ite_eq_right hpR]; simp
      · have := dc_snoc n F gs ⟨GateOp.or, [s, t]⟩
        rw [ite_eq_right (by simp)] at this
        omega
    | true =>
      have hu := fun x : Fin n → Bool => u_and (L := L) (x := List.ofFn x) hpd hA hap hbp
      have hpR : p ∉ R := fun h => by rw [(hR p h).1] at hA; cases hA
      obtain ⟨hs, o', c1, c2, c3, c4, c5⟩ := chain n F (L p) (hL p) gs hok (m (a p)) a1
      rcases ho : o' with _ | s
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := c5 x
          rw [ho, a2 x] at this
          rw [hu x, ← this]; simp [ov]
        · rw [ite_eq_right hpd, ite_eq_right hpR]; omega
      rcases hb0 : m (b p) with _ | t
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := b2 x
          rw [hb0] at this
          rw [hu x, ← this]; simp [ov]
        · rw [ite_eq_right hpd, ite_eq_right hpR]; omega
      have hs' := c4 s ho
      have ht : t < n + (gs ++ hs).length := by have := b1 t hb0; simp; omega
      have hval : ∀ x : Fin n → Bool, ov (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)
          (some (n + (gs ++ hs).length)) = u n A a b Del L (List.ofFn x) (n + p) := by
        intro x
        rw [ov_new (gs ++ hs) n _ (by simp) _ _ _ hs' ht, hu x, ← a2 x, ← b2 x, ← c5 x, ho, hb0,
          ← ov_ext gs hs (List.ofFn x) (some t) (by intro w hw; cases hw; simpa using b1 t hb0)]
        simp [ov, GateOp.eval]
      refine ⟨hs ++ [⟨GateOp.and, [s, t]⟩], some (n + (gs ++ hs).length), ?_, ?_,
        fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [← List.append_assoc]; exact ok_snoc c1 (Or.inl rfl) hs' ht
      · intro w hw; cases hw; simp
      · rw [← List.append_assoc]; exact hval x
      · rw [ite_eq_right hpd, ite_eq_right hpR]; simp; omega
      · rw [← List.append_assoc]
        have := dc_snoc n F (gs ++ hs) ⟨GateOp.and, [s, t]⟩
        have e : ((⟨GateOp.and, [s, t]⟩ : Gate).op = GateOp.and ∧ ∃ x : Fin n → Bool,
            (run (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)).getD
              (n + (gs ++ hs).length) false = true ∧ F x = false) ↔
            (true = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
              u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false) := by
          refine ⟨fun h => ⟨rfl, hpd, ?_⟩, fun h => ⟨rfl, ?_⟩⟩
          · obtain ⟨x, h1, h2⟩ := h.2
            exact ⟨x, by rw [← hval x]; exact h1, h2⟩
          · obtain ⟨x, h1, h2⟩ := h.2.2
            exact ⟨x, by rw [← hval x] at h1; exact h1, h2⟩
        rw [if_congr e rfl rfl] at this
        omega

lemma compress_zero_program (n N : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del : Finset ℕ)
    (hab : ∀ j < N, a j < n+j ∧ b j < n+j) :
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n+N, (∀ w', m w = some w' → w' < n+gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) =
          u n A a b Del (fun _ => []) (List.ofFn x) w) ∧
      gs.length + ((Finset.range N).filter (· ∈ Del)).card ≤ N := by
  obtain ⟨gs,m,hok,hsem,hdel,hsize,hdirty⟩ :=
    build n A a b Del ∅ (fun _ => []) (fun _ => false) (by simp) (by simp) N hab
  refine ⟨gs,m,hok,hsem,?_⟩
  simpa using hsize


lemma u_matches_run (n : ℕ) (gs : List Gate) (A : ℕ → Bool)
    (a b : ℕ → ℕ) (Del : Finset ℕ)
    (hab : ∀ j < gs.length, a j < n+j ∧ b j < n+j)
    (hgate : ∀ j (hj : j < gs.length), gs[j] =
      if j ∈ Del then ⟨GateOp.or, []⟩
      else ⟨if A j then GateOp.and else GateOp.or, [a j,b j]⟩)
    (x : Fin n → Bool) :
    ∀ w < n+gs.length, u n A a b Del (fun _ => []) (List.ofFn x) w =
      (run gs (List.ofFn x)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hin : w < n
    · rw [u_in hin, run_input gs (List.ofFn x) w (by simpa using hin)]
    have hn : n ≤ w := by omega
    obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
    have hj : j < gs.length := by omega
    obtain ⟨ha,hb⟩ := hab j hj
    have hra : u n A a b Del (fun _ => []) (List.ofFn x) (a j) =
        (run gs (List.ofFn x)).getD (a j) false := ih (a j) ha (by omega)
    have hrb : u n A a b Del (fun _ => []) (List.ofFn x) (b j) =
        (run gs (List.ofFn x)).getD (b j) false := ih (b j) hb (by omega)
    have hr := run_gate gs (List.ofFn x) j hj
    simp only [List.length_ofFn] at hr
    rw [hr,hgate j hj]
    by_cases hd : j ∈ Del
    · rw [u_del hd,ite_eq_left hd]
      rfl
    · rw [ite_eq_right hd]
      cases hA : A j with
      | false =>
        rw [u_or hd hA ha hb,hra,hrb]
        simp [hA,GateOp.eval,ha,hb]
      | true =>
        rw [u_and hd hA ha hb,hra,hrb]
        simp [hA,GateOp.eval,ha,hb]

lemma compress_zero_circuit (n : ℕ) (C : Circuit) (A : ℕ → Bool)
    (a b : ℕ → ℕ) (Del : Finset ℕ)
    (hab : ∀ j < C.gates.length, a j < n+j ∧ b j < n+j)
    (hgate : ∀ j (hj : j < C.gates.length), C.gates[j] =
      if j ∈ Del then ⟨GateOp.or, []⟩
      else ⟨if A j then GateOp.and else GateOp.or, [a j,b j]⟩) :
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n+C.gates.length, (∀ w', m w = some w' → w' < n+gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) =
          (C.wires (List.ofFn x)).getD w false) ∧
      gs.length + ((Finset.range C.gates.length).filter (· ∈ Del)).card ≤ C.gates.length := by
  obtain ⟨gs,m,hok,hsem,hsize⟩ := compress_zero_program n C.gates.length A a b Del hab
  refine ⟨gs,m,hok,?_,hsize⟩
  intro w hw
  obtain ⟨hbound,hval⟩ := hsem w hw
  refine ⟨hbound,?_⟩
  intro x
  rw [hval,u_matches_run n C.gates A a b Del hab hgate x w hw]
  rfl

theorem ok_ao {n : ℕ} {gs : List Gate} {w : ℕ} (hok : Ok n gs) : TopForm.IsAO2 n ⟨gs, w⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; exact h2
  · intro j hj i hi
    obtain ⟨o', s', t', h1, h2, h3, h4⟩ := hok j hj
    have e1 : gateAt ⟨gs, w⟩ j = gs[j] := List.getD_eq_getElem _ _ hj
    rw [e1, h1] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; rfl

theorem gate2 {n : ℕ} {C : Circuit} (h : TopForm.IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j] = gateAt C j ∧ (gateAt C j).inputs = [TopForm.opnd C j 0, TopForm.opnd C j 1] ∧
    TopForm.opnd C j 0 < n + j ∧ TopForm.opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  have hl := h.2.2 _ hm
  obtain ⟨s, t, hst⟩ := List.length_eq_two.1 hl
  have hb := h.2.1 j hj
  rw [hst] at hb
  have e0 : TopForm.opnd C j 0 = s := by unfold TopForm.opnd; rw [hst]; rfl
  have e1 : TopForm.opnd C j 1 = t := by unfold TopForm.opnd; rw [hst]; rfl
  refine ⟨e.symm, by rw [hst, e0, e1], by rw [e0]; exact hb s (by simp),
    by rw [e1]; exact hb t (by simp), h.1 _ hm⟩

def zeroCut (C : Circuit) (j : ℕ) : Circuit :=
  ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩

lemma compress_one_cut {n : ℕ} (C : Circuit) (hC : TopForm.IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n+C.gates.length, (∀ w', m w = some w' → w' < n+gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) =
          ((zeroCut C j).wires (List.ofFn x)).getD w false) ∧
      gs.length+1 ≤ C.gates.length := by
  classical
  let A : ℕ → Bool := fun i => decide ((gateAt C i).op = GateOp.and)
  let a : ℕ → ℕ := fun i => TopForm.opnd C i 0
  let b : ℕ → ℕ := fun i => TopForm.opnd C i 1
  have hab : ∀ i < (zeroCut C j).gates.length, a i < n+i ∧ b i < n+i := by
    intro i hi
    have hi' : i < C.gates.length := by simpa [zeroCut] using hi
    obtain ⟨_,_,ha,hb,_⟩ := gate2 hC hi'
    exact ⟨ha,hb⟩
  have hgate : ∀ i (hi : i < (zeroCut C j).gates.length), (zeroCut C j).gates[i] =
      if i ∈ ({j} : Finset ℕ) then ⟨GateOp.or, []⟩
      else ⟨if A i then GateOp.and else GateOp.or, [a i,b i]⟩ := by
    intro i hi
    have hi' : i < C.gates.length := by simpa [zeroCut] using hi
    obtain ⟨he,hin,ha,hb,hop⟩ := gate2 hC hi'
    by_cases hij : i=j
    · subst i
      simp [zeroCut]
    · simp only [Finset.mem_singleton,ite_eq_right hij]
      have hs : (zeroCut C j).gates[i] = C.gates[i] := by
        simp [zeroCut,List.getElem_set,hij,Ne.symm hij]
      rw [hs,he]
      have hop' : (gateAt C i).op = if A i then GateOp.and else GateOp.or := by
        rcases hop with hop | hop <;> simp [A,hop]
      cases hgc : gateAt C i with
      | mk o ins =>
        simp only [hgc] at hin hop'
        rw [hop',hin]
  obtain ⟨gs,m,hok,hsem,hsize⟩ := compress_zero_circuit n (zeroCut C j) A a b {j} hab hgate
  refine ⟨gs,m,hok,?_,?_⟩
  · simpa [zeroCut] using hsem
  · have hfilter : ((Finset.range (zeroCut C j).gates.length).filter (· ∈ ({j} : Finset ℕ))) = {j} := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · intro hij
        subst i
        exact ⟨by simpa [zeroCut] using hj,rfl⟩
    rw [hfilter,Finset.card_singleton] at hsize
    simpa [zeroCut] using hsize

lemma join_optional {n : ℕ} (gs : List Gate) (hok : Ok n gs) (s t : Option ℕ)
    (hs : ∀ w, s = some w → w < n+gs.length)
    (ht : ∀ w, t = some w → w < n+gs.length) :
    ∃ D : Circuit, TopForm.IsAO2 n D ∧ D.size ≤ gs.length+1 ∧
      (∀ x : Fin n → Bool, circuitFun n D x =
        (ov gs (List.ofFn x) s || ov gs (List.ofFn x) t)) ∧
      (∀ w < n+gs.length, ∀ x : Fin n → Bool,
        (D.wires (List.ofFn x)).getD w false = (run gs (List.ofFn x)).getD w false) := by
  cases s with
  | none =>
    cases t with
    | none =>
      refine ⟨⟨gs,n+gs.length⟩,ok_ao hok,by simp [Circuit.size],?_,?_⟩
      · intro x
        change (run gs (List.ofFn x)).getD (n+gs.length) false = false
        exact List.getD_eq_default _ _ (by simp [run_length])
      · intro w hw x; rfl
    | some t =>
      refine ⟨⟨gs,t⟩,ok_ao hok,by simp [Circuit.size],?_,?_⟩
      · intro x
        change (run gs (List.ofFn x)).getD t false =
          (false || (run gs (List.ofFn x)).getD t false)
        simp
      · intro w hw x; rfl
  | some s =>
    cases t with
    | none =>
      refine ⟨⟨gs,s⟩,ok_ao hok,by simp [Circuit.size],?_,?_⟩
      · intro x
        change (run gs (List.ofFn x)).getD s false =
          ((run gs (List.ofFn x)).getD s false || false)
        simp
      · intro w hw x; rfl
    | some t =>
      have hs' := hs s rfl
      have ht' := ht t rfl
      refine ⟨⟨gs ++ [⟨GateOp.or,[s,t]⟩],n+gs.length⟩,
        ok_ao (ok_snoc hok (Or.inr rfl) hs' ht'),by simp [Circuit.size],?_,?_⟩
      · intro x
        change ov (gs ++ [⟨GateOp.or,[s,t]⟩]) (List.ofFn x) (some (n+gs.length)) = _
        rw [ov_new gs n _ (by simp) _ _ _ hs' ht']
        simp [GateOp.eval,ov]
      · intro w hw x
        exact run_prefix gs [⟨GateOp.or,[s,t]⟩] (List.ofFn x) w (by simpa using hw)

lemma zeroCut_split (pre post : List Gate) (g : Gate) (out : ℕ) :
    (zeroCut ⟨pre ++ [g] ++ post,out⟩ pre.length).gates =
      pre ++ [Semantic.zeroGate] ++ post := by
  simp [zeroCut,List.set_append,Semantic.zeroGate]

lemma cut_lift_preserves {n : ℕ} (pre post : List Gate) (g : Gate) (out ancestor : ℕ)
    (hC : TopForm.IsAO2 n ⟨pre ++ [g] ++ post,out⟩)
    (hout : out < n+(pre ++ [g] ++ post).length)
    (hanc : ancestor < n+pre.length)
    (hreader : ∀ x : Fin n → Bool,
      Semantic.val (pre ++ [g] ++ post) x (n+pre.length) = true →
        Semantic.val (pre ++ [g] ++ post) x ancestor = true)
    (hbelow : ∀ x : Fin n → Bool,
      Semantic.val (pre ++ [g] ++ post) x ancestor = true →
        Semantic.val (pre ++ [g] ++ post) x out = true)
    (hzero : ∀ u : Fin n,
      Semantic.val (pre ++ [g] ++ post) (Semantic.eof u) (n+pre.length) = false) :
    ∃ D : Circuit, TopForm.IsAO2 n D ∧ D.size ≤ (pre ++ [g] ++ post).length ∧
      (∀ x : Fin n → Bool, circuitFun n D x = Semantic.val (pre ++ [g] ++ post) x out) ∧
      ∀ (Q : Finset (Fin n)), Q.Nonempty → ∀ w, w < n+(pre ++ [g] ++ post).length →
        (∀ x, Semantic.val (pre ++ [g] ++ post) x w = decide (∃ u ∈ Q,x u=true)) →
        ∃ v, ∀ x, (D.wires (List.ofFn x)).getD v false = decide (∃ u ∈ Q,x u=true) := by
  classical
  let C : Circuit := ⟨pre ++ [g] ++ post,out⟩
  have hj : pre.length < C.gates.length := by simp [C]
  obtain ⟨gs,m,hok,hsem,hsize⟩ := compress_one_cut C hC pre.length hj
  have hget : ∀ w < n+C.gates.length, ∀ x : Fin n → Bool,
      ov gs (List.ofFn x) (m w) = Semantic.val (pre ++ [Semantic.zeroGate] ++ post) x w := by
    intro w hw x
    rw [(hsem w hw).2 x]
    change ((zeroCut C pre.length).gates.foldl _ (List.ofFn x)).getD w false = _
    rw [show (zeroCut C pre.length).gates = pre ++ [Semantic.zeroGate] ++ post from
      zeroCut_split pre post g out]
    rfl
  have hac : ancestor < n+C.gates.length := by simp only [C,List.length_append,List.length_singleton]; omega
  obtain ⟨D,hD,hDs,hfun,hpres⟩ := join_optional gs hok (m out) (m ancestor)
    (hsem out hout).1 (hsem ancestor hac).1
  refine ⟨D,hD,by change D.size ≤ C.gates.length; omega,?_,?_⟩
  · intro x
    rw [hfun x,hget out hout x,hget ancestor hac x]
    have hc : Semantic.val (pre ++ [Semantic.zeroGate] ++ post) x ancestor =
        Semantic.val (pre ++ [g] ++ post) x ancestor := by
      have h1 := Semantic.val_append_old pre ([Semantic.zeroGate] ++ post) x ancestor hanc
      have h2 := Semantic.val_append_old pre ([g] ++ post) x ancestor hanc
      simpa [List.append_assoc] using h1.trans h2.symm
    rw [hc]
    exact (Semantic.cut_zero_lift pre post g ancestor out hreader hbelow x).symm
  · intro Q hQ w hw hOR
    have hp := Semantic.cut_zero_preserves_or pre post g hC.1 Q w hOR hzero
    cases hm : m w with
    | none =>
      obtain ⟨u,hu⟩ := hQ
      have he := hget w hw (fun _ => true)
      rw [hm,hp] at he
      have ht : decide (∃ u ∈ Q,(fun _ : Fin n => true) u=true) = true := by
        exact decide_eq_true ⟨u,hu,rfl⟩
      rw [ht] at he
      cases he
    | some v =>
      refine ⟨v,?_⟩
      intro x
      rw [hpres v ((hsem w hw).1 v hm) x]
      change ov gs (List.ofFn x) (some v) = _
      rw [← hm,hget w hw x,hp]

end PEqualNP.Outside.L_meta_4970.Compression

namespace PEqualNP.Outside.L_meta_4970.TypedCompression
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4970.Compression
theorem orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

theorem orSets_length (n : ℕ) (C : Circuit) :
    (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
  unfold PEqualNP.CleanedNonEdge.orSets
  rw [orSets_len]; simp

theorem orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.CleanedNonEdge.orStep n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (PEqualNP.CleanedNonEdge.orStep n
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

theorem orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
  have h := orSets_char n C.gates x k
  unfold PEqualNP.CleanedNonEdge.orSets gateAt
  rw [h]
  constructor
  · rintro ⟨_, h3⟩; exact h3
  · intro h3; exact ⟨hk, h3⟩

theorem orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

theorem orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

theorem orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C i g) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g :=
  (orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

theorem orReaches_bound (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → n + g ≤ w ∧ w < n + C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp hr
    rcases h3 with h3 | ⟨_, i, _, hlt, hri⟩
    · omega
    · have := ih i hlt hri
      omega

theorem orReaches_trans (n : ℕ) (C : Circuit) (k g : ℕ) (hkg : PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w k → PEqualNP.CleanedNonEdge.OrReaches n C w g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨m, rfl⟩ : ∃ m, w = n + m := ⟨w - n, by omega⟩
    obtain ⟨hm, h3⟩ := (orReaches_iff n C m k).mp hr
    rcases h3 with h3 | ⟨hop, i, hi, hlt, hri⟩
    · rw [← h3]; exact hkg
    · exact orReaches_step n C m i g hm hop hi hlt (ih i hlt hri)

theorem orIn_mem_filter {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

theorem mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  exact ⟨fun h => ((orIn_mem_filter _ _ _ _).1 h).2,
    fun h => (orIn_mem_filter _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

theorem orIn_self (n : ℕ) (C : Circuit) (i : Fin n) : i ∈ PEqualNP.TopForm.orIn n C i :=
  (mem_orIn n C i i).mpr (Or.inl rfl)

theorem orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ PEqualNP.TopForm.orIn n C i) : a ∈ PEqualNP.TopForm.orIn n C (n + j) := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩

theorem orIn_reach (n : ℕ) (C : Circuit) (b k : ℕ) (a : Fin n)
    (hr : PEqualNP.CleanedNonEdge.OrReaches n C b k)
    (h : a ∈ PEqualNP.TopForm.orIn n C (n + k)) : a ∈ PEqualNP.TopForm.orIn n C b := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨m, hm, hrm, hopm, hin⟩
  · exfalso; have := a.isLt; omega
  · exact ⟨m, hm, orReaches_trans n C k m hrm b hr, hopm, hin⟩


def MonoLabel {n : ℕ} (isLine : ℕ → Bool) (S : Finset (Fin n)) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, isLine a = isLine b

def Labels (n : ℕ) (isLine : ℕ → Bool) (gs : List Gate)
    (lab : ℕ → Finset (Fin n)) : Prop :=
  (∀ i : Fin n, lab i = {i}) ∧
  ∀ j (hj : j < gs.length), gs[j].op = GateOp.or →
    (∀ w ∈ gs[j].inputs, lab w ⊆ lab (n+j)) ∧ MonoLabel isLine (lab (n+j))

lemma labels_reaches {n : ℕ} (isLine : ℕ → Bool) (gs : List Gate)
    (lab : ℕ → Finset (Fin n)) (hl : Labels n isLine gs lab) (k : ℕ) :
    ∀ w, PEqualNP.CleanedNonEdge.OrReaches n ⟨gs,0⟩ w k → lab (n+k) ⊆ lab w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨j,rfl⟩ : ∃ j, w = n+j := ⟨w-n,by omega⟩
    obtain ⟨hj,h⟩ := (orReaches_iff n ⟨gs,0⟩ j k).mp hr
    rcases h with rfl | ⟨hop,v,hv,hlt,hrv⟩
    · exact fun _ h => h
    · have he : gateAt ⟨gs,0⟩ j = gs[j] := by
        simp [gateAt,List.getD_eq_getElem?_getD,hj]
      rw [he] at hop hv
      exact (ih v hlt hrv).trans ((hl.2 j hj hop).1 v hv)

lemma labels_orIn {n : ℕ} (isLine : ℕ → Bool) (gs : List Gate)
    (lab : ℕ → Finset (Fin n)) (hl : Labels n isLine gs lab) (w : ℕ) :
    PEqualNP.TopForm.orIn n ⟨gs,0⟩ w ⊆ lab w := by
  intro i hi
  rcases (mem_orIn n ⟨gs,0⟩ w i).mp hi with h | ⟨k,hk,hr,hop,hin⟩
  · rw [← h,hl.1 i]
    exact Finset.mem_singleton_self i
  · have he : gateAt ⟨gs,0⟩ k = gs[k] := by
      simp [gateAt,List.getD_eq_getElem?_getD,hk]
    rw [he] at hop hin
    have hli : i ∈ lab i := by rw [hl.1 i]; exact Finset.mem_singleton_self i
    exact labels_reaches isLine gs lab hl k w hr ((hl.2 k hk hop).1 i hin hli)

lemma labels_tCount {n : ℕ} (isLine : ℕ → Bool) (gs : List Gate)
    (lab : ℕ → Finset (Fin n)) (hl : Labels n isLine gs lab) :
    PEqualNP.TwoColour.tCount n ⟨gs,0⟩ isLine = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨_,hjl,hop,⟨a,ha,hac⟩,⟨b,hb,hbc⟩⟩ := Finset.mem_filter.mp hj
  have he : gateAt ⟨gs,0⟩ j = gs[j] := by
    simp [gateAt,List.getD_eq_getElem?_getD,hjl]
  rw [he] at hop
  have hmono := (hl.2 j hjl hop).2 a (labels_orIn isLine gs lab hl _ ha)
    b (labels_orIn isLine gs lab hl _ hb)
  rw [hac,hbc] at hmono
  cases hmono

lemma labels_snoc {n : ℕ} (isLine : ℕ → Bool) (gs : List Gate)
    (lab : ℕ → Finset (Fin n)) (hl : Labels n isLine gs lab) (hok : Ok n gs)
    (o : GateOp) (a b : ℕ) (ha : a < n+gs.length) (hb : b < n+gs.length)
    (T : Finset (Fin n))
    (hT : o = GateOp.or → lab a ⊆ T ∧ lab b ⊆ T ∧ MonoLabel isLine T) :
    Labels n isLine (gs ++ [⟨o,[a,b]⟩]) (Function.update lab (n+gs.length) T) := by
  classical
  refine ⟨?_,?_⟩
  · intro i
    rw [Function.update_of_ne (by have := i.isLt; omega)]
    exact hl.1 i
  · intro j hj hop
    by_cases hjs : j < gs.length
    · rw [List.getElem_append_left hjs] at hop ⊢
      obtain ⟨ho,hm⟩ := hl.2 j hjs hop
      have hnj : n+j ≠ n+gs.length := by omega
      rw [Function.update_of_ne hnj]
      refine ⟨?_,hm⟩
      intro w hw
      obtain ⟨o',a',b',hg,_,ha',hb'⟩ := hok j hjs
      have hwlt : w < n+gs.length := by
        rw [hg] at hw
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
        rcases hw with rfl | rfl <;> omega
      rw [Function.update_of_ne (by omega)]
      exact ho w hw
    · have hje : j=gs.length := by simp at hj; omega
      subst j
      have he : (gs ++ [⟨o,[a,b]⟩])[gs.length] = (⟨o,[a,b]⟩ : Gate) := by simp
      rw [he] at hop ⊢
      rw [Function.update_self]
      obtain ⟨hTa,hTb,hTm⟩ := hT hop
      refine ⟨?_,hTm⟩
      intro w hw
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
      rcases hw with rfl | rfl
      · rw [Function.update_of_ne (by omega)]; exact hTa
      · rw [Function.update_of_ne (by omega)]; exact hTb

def andGate (g : Gate) : Bool :=
  match g.op with
  | .and => true
  | _ => false

def andNum (gs : List Gate) : ℕ := gs.countP andGate

lemma typed_build (n : ℕ) (isLine : ℕ → Bool) (A : ℕ → Bool)
    (a b : ℕ → ℕ) (Del : Finset ℕ) (B : ℕ → Finset (Fin n))
    (hB : ∀ i : Fin n, B i = {i}) :
    ∀ p, (∀ j < p, a j < n+j ∧ b j < n+j) →
    (∀ j < p, A j = false → B (a j) ⊆ B (n+j) ∧ B (b j) ⊆ B (n+j) ∧
      MonoLabel isLine (B (n+j))) →
    ∃ (gs : List Gate) (m : ℕ → Option ℕ) (lab : ℕ → Finset (Fin n)),
      Ok n gs ∧ Labels n isLine gs lab ∧
      (∀ w < n+p,
        (∀ w', m w = some w' → w' < n+gs.length ∧ lab w' ⊆ B w) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) =
          u n A a b Del (fun _ => []) (List.ofFn x) w) ∧
      gs.length + ((Finset.range p).filter (· ∈ Del)).card ≤ p ∧
      andNum gs ≤ ((Finset.range p).filter fun j => A j = true ∧ j ∉ Del).card := by
  classical
  intro p
  induction p with
  | zero =>
    intro _ _
    refine ⟨[],fun w => some w,B,?_,?_,?_,by simp [andNum]⟩
    · intro j hj; simp at hj
    · exact ⟨hB,by intro j hj; simp at hj⟩
    · intro w hw
      refine ⟨?_,?_⟩
      · intro w' he; cases he; exact ⟨by simpa using hw,fun _ h => h⟩
      · intro x; rw [u_in (by omega)]; rfl
  | succ p ih =>
    intro hab hOR
    obtain ⟨gs,m,lab,hok,hl,hm,hsize,hand⟩ := ih
      (fun j hj => hab j (by omega)) (fun j hj => hOR j (by omega))
    obtain ⟨ha,hb⟩ := hab p (by omega)
    have finish (hs : List Gate) (o : Option ℕ) (lab' : ℕ → Finset (Fin n))
        (hok' : Ok n (gs++hs)) (hl' : Labels n isLine (gs++hs) lab')
        (hlext : ∀ w < n+gs.length, lab' w = lab w)
        (ho : ∀ w', o = some w' → w' < n+(gs++hs).length ∧ lab' w' ⊆ B (n+p))
        (hv : ∀ x : Fin n → Bool, ov (gs++hs) (List.ofFn x) o =
          u n A a b Del (fun _ => []) (List.ofFn x) (n+p))
        (hc : hs.length + (if p ∈ Del then 1 else 0) ≤ 1)
        (hcand : andNum hs ≤ if A p = true ∧ p ∉ Del then 1 else 0) :
        ∃ (gs : List Gate) (m : ℕ → Option ℕ) (lab : ℕ → Finset (Fin n)),
          Ok n gs ∧ Labels n isLine gs lab ∧
          (∀ w < n+(p+1),
            (∀ w', m w = some w' → w' < n+gs.length ∧ lab w' ⊆ B w) ∧
            ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) =
              u n A a b Del (fun _ => []) (List.ofFn x) w) ∧
          gs.length + ((Finset.range (p+1)).filter (· ∈ Del)).card ≤ p+1 ∧
          andNum gs ≤ ((Finset.range (p+1)).filter fun j => A j = true ∧ j ∉ Del).card := by
      refine ⟨gs++hs,Function.update m (n+p) o,lab',hok',hl',?_,?_,?_⟩
      · intro w hw
        by_cases he : w=n+p
        · subst w; rw [Function.update_self]; exact ⟨ho,hv⟩
        · rw [Function.update_of_ne he]
          obtain ⟨hwm,hws⟩ := hm w (by omega)
          refine ⟨?_,?_⟩
          · intro w' he'
            obtain ⟨hwb,hwl⟩ := hwm w' he'
            exact ⟨by simp; omega,by rw [hlext w' hwb]; exact hwl⟩
          · intro x
            rw [ov_ext gs hs (List.ofFn x) (m w) (by
              intro w' he'; simpa using (hwm w' he').1)]
            exact hws x
      · rw [Finset.range_add_one,Finset.filter_insert,List.length_append]
        split_ifs at hc ⊢ with hd
        · rw [Finset.card_insert_of_notMem (by simp)]
          omega
        · omega
      · have he : andNum (gs++hs) = andNum gs + andNum hs := by simp [andNum]
        rw [he,Finset.range_add_one,Finset.filter_insert]
        split_ifs at hcand ⊢ with hnew
        · rw [Finset.card_insert_of_notMem (by simp)]
          omega
        · omega
    by_cases hd : p ∈ Del
    · apply finish [] none lab (by simpa using hok) (by simpa using hl)
        (fun _ _ => rfl) (by simp) ?_ (by simp [hd]) (by simp [andNum,andGate,hd])
      intro x; rw [u_del hd]; rfl
    obtain ⟨hama,hva⟩ := hm (a p) ha
    obtain ⟨hamb,hvb⟩ := hm (b p) hb
    cases hA : A p with
    | false =>
      obtain ⟨hBa,hBb,hMono⟩ := hOR p (by omega) hA
      have hu := fun x : Fin n → Bool => u_or (L := fun _ => [])
        (x := List.ofFn x) hd hA ha hb
      cases hma : m (a p) with
      | none =>
        apply finish [] (m (b p)) lab (by simpa using hok) (by simpa using hl)
          (fun _ _ => rfl) ?_ ?_ (by simp [hd]) (by simp [andNum,andGate,hd])
        · intro w' he
          obtain ⟨hw,hsub⟩ := hamb w' he
          exact ⟨by simpa using hw,hsub.trans hBb⟩
        · intro x; rw [hu x,←hva x,←hvb x,hma]; simp [ov]
      | some s =>
        cases hmb : m (b p) with
        | none =>
          apply finish [] (m (a p)) lab (by simpa using hok) (by simpa using hl)
            (fun _ _ => rfl) ?_ ?_ (by simp [hd]) (by simp [andNum,andGate,hd])
          · intro w' he
            obtain ⟨hw,hsub⟩ := hama w' he
            exact ⟨by simpa using hw,hsub.trans hBa⟩
          · intro x; rw [hu x,←hva x,←hvb x,hmb]; simp [ov]
        | some t =>
          obtain ⟨hs,hsubS⟩ := hama s hma
          obtain ⟨ht,hsubT⟩ := hamb t hmb
          let lab' := Function.update lab (n+gs.length) (B (n+p))
          apply finish [⟨GateOp.or,[s,t]⟩] (some (n+gs.length)) lab'
            (ok_snoc hok (Or.inr rfl) hs ht)
            (labels_snoc isLine gs lab hl hok .or s t hs ht (B (n+p))
              (fun _ => ⟨hsubS.trans hBa,hsubT.trans hBb,hMono⟩)) ?_ ?_ ?_ (by simp [hd]) (by simp [andNum,andGate,hd])
          · intro w hw; exact Function.update_of_ne (by omega) _ _
          · intro w' he; cases he
            exact ⟨by simp,by simp [lab']⟩
          · intro x
            rw [ov_new gs n _ (by simp) _ _ _ hs ht,hu x,←hva x,←hvb x,hma,hmb]
            simp [ov,GateOp.eval]
    | true =>
      have hu := fun x : Fin n → Bool => u_and (L := fun _ => [])
        (x := List.ofFn x) hd hA ha hb
      cases hma : m (a p) with
      | none =>
        apply finish [] none lab (by simpa using hok) (by simpa using hl)
          (fun _ _ => rfl) (by simp) ?_ (by simp [hd]) (by simp [andNum,andGate,hd])
        intro x; rw [hu x,←hva x,hma]; simp [ov]
      | some s =>
        cases hmb : m (b p) with
        | none =>
          apply finish [] none lab (by simpa using hok) (by simpa using hl)
            (fun _ _ => rfl) (by simp) ?_ (by simp [hd]) (by simp [andNum,andGate,hd])
          intro x; rw [hu x,←hvb x,hmb]; simp [ov]
        | some t =>
          have hs := (hama s hma).1
          have ht := (hamb t hmb).1
          let lab' := Function.update lab (n+gs.length) ∅
          apply finish [⟨GateOp.and,[s,t]⟩] (some (n+gs.length)) lab'
            (ok_snoc hok (Or.inl rfl) hs ht)
            (labels_snoc isLine gs lab hl hok .and s t hs ht ∅ (by simp)) ?_ ?_ ?_ (by simp [hd]) (by simp [andNum,andGate,hd,hA])
          · intro w hw; exact Function.update_of_ne (by omega) _ _
          · intro w' he; cases he
            exact ⟨by simp,by simp [lab']⟩
          · intro x
            rw [ov_new gs n _ (by simp) _ _ _ hs ht,hu x,←hva x,←hvb x,hma,hmb]
            simp [ov,GateOp.eval]

lemma orIn_input {n : ℕ} (C : Circuit) (i : Fin n) :
    PEqualNP.TopForm.orIn n C i = {i} := by
  ext v
  rw [mem_orIn,Finset.mem_singleton]
  constructor
  · rintro (hv | ⟨k,hk,hr,hop,hin⟩)
    · exact Fin.val_injective hv
    · have := hr.1; have := i.isLt; omega
  · intro h; subst v; exact Or.inl rfl

lemma original_mono {n : ℕ} (isLine : ℕ → Bool) (C : Circuit)
    (ht : PEqualNP.TwoColour.tCount n C isLine = 0) (j : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    MonoLabel isLine (PEqualNP.TopForm.orIn n C (n+j)) := by
  intro a ha b hb
  by_contra hne
  have hne2 : isLine a ≠ isLine b := hne
  have htwo : PEqualNP.TwoColour.IsTwoColour n C isLine j := by
    refine ⟨hj,hop,?_,?_⟩
    · cases hca : isLine a with
      | false => exact ⟨a,ha,hca⟩
      | true => exact ⟨b,hb,by cases hcb : isLine b <;> simp_all⟩
    · cases hca : isLine a with
      | true => exact ⟨a,ha,hca⟩
      | false => exact ⟨b,hb,by cases hcb : isLine b <;> simp_all⟩
  have hm : j ∈ PEqualNP.TwoColour.twoColour n C isLine :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,htwo⟩
  have he : PEqualNP.TwoColour.twoColour n C isLine = ∅ := Finset.card_eq_zero.mp ht
  rw [he] at hm
  exact Finset.notMem_empty _ hm

lemma typed_compress_program (n : ℕ) (C : Circuit) (isLine : ℕ → Bool)
    (A : ℕ → Bool) (a b : ℕ → ℕ) (Del : Finset ℕ)
    (ht : PEqualNP.TwoColour.tCount n C isLine = 0)
    (hab : ∀ j < C.gates.length, a j < n+j ∧ b j < n+j)
    (hOR : ∀ j < C.gates.length, A j = false → (gateAt C j).op = GateOp.or ∧
      a j ∈ (gateAt C j).inputs ∧ b j ∈ (gateAt C j).inputs) :
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      PEqualNP.TwoColour.tCount n ⟨gs,0⟩ isLine = 0 ∧
      (∀ w < n+C.gates.length,
        (∀ w', m w = some w' → w' < n+gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) =
          u n A a b Del (fun _ => []) (List.ofFn x) w) ∧
      gs.length + ((Finset.range C.gates.length).filter (· ∈ Del)).card ≤ C.gates.length := by
  let B := PEqualNP.TopForm.orIn n C
  have hB : ∀ i : Fin n, B i = {i} := orIn_input C
  have hlabels : ∀ j < C.gates.length, A j = false → B (a j) ⊆ B (n+j) ∧
      B (b j) ⊆ B (n+j) ∧ MonoLabel isLine (B (n+j)) := by
    intro j hj hA
    obtain ⟨hop,hai,hbi⟩ := hOR j hj hA
    obtain ⟨ha,hb⟩ := hab j hj
    exact ⟨fun v hv => orIn_up n C j (a j) v hj hop hai ha hv,
      fun v hv => orIn_up n C j (b j) v hj hop hbi hb hv,original_mono isLine C ht j hj hop⟩
  obtain ⟨gs,m,lab,hok,hl,hm,hs,hand⟩ := typed_build n isLine A a b Del B hB C.gates.length hab hlabels
  refine ⟨gs,m,hok,labels_tCount isLine gs lab hl,?_,hs⟩
  intro w hw
  exact ⟨fun w' he => ((hm w hw).1 w' he).1,(hm w hw).2⟩

lemma orIn_non_or {n : ℕ} (C : Circuit) (j : ℕ)
    (hop : (gateAt C j).op ≠ GateOp.or) :
    PEqualNP.TopForm.orIn n C (n+j) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  rcases (mem_orIn n C (n+j) v).mp hv with hv | ⟨k,hk,hr,hko,hin⟩
  · have := v.isLt; omega
  · obtain ⟨_,h⟩ := (orReaches_iff n C j k).mp hr
    rcases h with rfl | ⟨hjo,_⟩
    · exact hop hko
    · exact hop hjo

lemma original_wire_mono {n : ℕ} (isLine : ℕ → Bool) (C : Circuit)
    (ht : PEqualNP.TwoColour.tCount n C isLine = 0) (w : ℕ) :
    MonoLabel isLine (PEqualNP.TopForm.orIn n C w) := by
  by_cases hi : w < n
  · have he := orIn_input C (⟨w,hi⟩ : Fin n)
    rw [he]
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b; rfl
  · obtain ⟨j,rfl⟩ : ∃ j, w=n+j := ⟨w-n,by omega⟩
    by_cases hj : j < C.gates.length
    · by_cases hop : (gateAt C j).op = GateOp.or
      · exact original_mono isLine C ht j hj hop
      · rw [orIn_non_or C j hop]
        intro a ha; exact (Finset.notMem_empty _ ha).elim
    · intro a ha
      rcases (mem_orIn n C (n+j) a).mp ha with ha | ⟨k,hk,hr,hop,hin⟩
      · have := a.isLt; omega
      · exact (hj ((orReaches_iff n C j k).mp hr).1).elim

lemma typed_compress_labeled (n : ℕ) (C : Circuit) (isLine : ℕ → Bool)
    (A : ℕ → Bool) (a b : ℕ → ℕ) (Del : Finset ℕ)
    (ht : PEqualNP.TwoColour.tCount n C isLine = 0)
    (hab : ∀ j < C.gates.length, a j < n+j ∧ b j < n+j)
    (hOR : ∀ j < C.gates.length, A j = false → (gateAt C j).op = GateOp.or ∧
      a j ∈ (gateAt C j).inputs ∧ b j ∈ (gateAt C j).inputs) :
    ∃ (gs : List Gate) (m : ℕ → Option ℕ) (lab : ℕ → Finset (Fin n)),
      Ok n gs ∧ Labels n isLine gs lab ∧
      (∀ w < n+C.gates.length,
        (∀ w', m w = some w' → w' < n+gs.length ∧
          lab w' ⊆ PEqualNP.TopForm.orIn n C w) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) =
          u n A a b Del (fun _ => []) (List.ofFn x) w) ∧
      gs.length + ((Finset.range C.gates.length).filter (· ∈ Del)).card ≤ C.gates.length ∧
      andNum gs ≤ ((Finset.range C.gates.length).filter fun j => A j = true ∧ j ∉ Del).card := by
  let B := PEqualNP.TopForm.orIn n C
  have hB : ∀ i : Fin n, B i = {i} := orIn_input C
  have hlabels : ∀ j < C.gates.length, A j = false → B (a j) ⊆ B (n+j) ∧
      B (b j) ⊆ B (n+j) ∧ MonoLabel isLine (B (n+j)) := by
    intro j hj hA
    obtain ⟨hop,hai,hbi⟩ := hOR j hj hA
    obtain ⟨ha,hb⟩ := hab j hj
    exact ⟨fun v hv => orIn_up n C j (a j) v hj hop hai ha hv,
      fun v hv => orIn_up n C j (b j) v hj hop hbi hb hv,original_mono isLine C ht j hj hop⟩
  exact typed_build n isLine A a b Del B hB C.gates.length hab hlabels

lemma typed_join_optional {n : ℕ} (isLine : ℕ → Bool) (gs : List Gate)
    (hok : Ok n gs) (lab : ℕ → Finset (Fin n)) (hl : Labels n isLine gs lab)
    (s t : Option ℕ) (T : Finset (Fin n)) (hT : MonoLabel isLine T)
    (hs : ∀ w, s = some w → w < n+gs.length ∧ lab w ⊆ T)
    (ht : ∀ w, t = some w → w < n+gs.length ∧ lab w ⊆ T) :
    ∃ D : Circuit, TopForm.IsAO2 n D ∧
      PEqualNP.TwoColour.tCount n D isLine = 0 ∧ D.size ≤ gs.length+1 ∧
      andNum D.gates = andNum gs ∧
      (∀ x : Fin n → Bool, circuitFun n D x =
        (ov gs (List.ofFn x) s || ov gs (List.ofFn x) t)) ∧
      (∀ w < n+gs.length, ∀ x : Fin n → Bool,
        (D.wires (List.ofFn x)).getD w false = (run gs (List.ofFn x)).getD w false) := by
  cases s with
  | none =>
    cases t with
    | none =>
      refine ⟨⟨gs,n+gs.length⟩,ok_ao hok,labels_tCount isLine gs lab hl,
        by simp [Circuit.size],rfl,?_,?_⟩
      · intro x
        change (run gs (List.ofFn x)).getD (n+gs.length) false = false
        exact List.getD_eq_default _ _ (by simp [run_length])
      · intro w hw x; rfl
    | some t =>
      refine ⟨⟨gs,t⟩,ok_ao hok,labels_tCount isLine gs lab hl,
        by simp [Circuit.size],rfl,?_,?_⟩
      · intro x
        change (run gs (List.ofFn x)).getD t false =
          (false || (run gs (List.ofFn x)).getD t false)
        simp
      · intro w hw x; rfl
  | some s =>
    cases t with
    | none =>
      refine ⟨⟨gs,s⟩,ok_ao hok,labels_tCount isLine gs lab hl,
        by simp [Circuit.size],rfl,?_,?_⟩
      · intro x
        change (run gs (List.ofFn x)).getD s false =
          ((run gs (List.ofFn x)).getD s false || false)
        simp
      · intro w hw x; rfl
    | some t =>
      obtain ⟨hs',hls⟩ := hs s rfl
      obtain ⟨ht',hlt⟩ := ht t rfl
      have hln := labels_snoc isLine gs lab hl hok .or s t hs' ht' T (fun _ => ⟨hls,hlt,hT⟩)
      refine ⟨⟨gs ++ [⟨GateOp.or,[s,t]⟩],n+gs.length⟩,
        ok_ao (ok_snoc hok (Or.inr rfl) hs' ht'),labels_tCount isLine _ _ hln,
        by simp [Circuit.size],by simp [andNum,andGate],?_,?_⟩
      · intro x
        change ov (gs ++ [⟨GateOp.or,[s,t]⟩]) (List.ofFn x) (some (n+gs.length)) = _
        rw [ov_new gs n _ (by simp) _ _ _ hs' ht']
        simp [GateOp.eval,ov]
      · intro w hw x
        exact run_prefix gs [⟨GateOp.or,[s,t]⟩] (List.ofFn x) w (by simpa using hw)

end PEqualNP.Outside.L_meta_4970.TypedCompression

namespace PEqualNP.Outside.L_meta_4970.Compression
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma ao_descriptors {n : ℕ} (C : Circuit) (hC : TopForm.IsAO2 n C) :
    ∃ (A : ℕ → Bool) (a b : ℕ → ℕ),
      (∀ i < C.gates.length, a i < n+i ∧ b i < n+i) ∧
      (∀ i (hi : i < C.gates.length), C.gates[i] =
        ⟨if A i then GateOp.and else GateOp.or,[a i,b i]⟩) ∧
      (∀ i < C.gates.length, A i=false → (gateAt C i).op=GateOp.or ∧
        a i ∈ (gateAt C i).inputs ∧ b i ∈ (gateAt C i).inputs) ∧
      (∀ i, A i=true ↔ (gateAt C i).op=GateOp.and) := by
  classical
  let A : ℕ → Bool := fun i => decide ((gateAt C i).op=GateOp.and)
  let a : ℕ → ℕ := fun i => TopForm.opnd C i 0
  let b : ℕ → ℕ := fun i => TopForm.opnd C i 1
  refine ⟨A,a,b,?_,?_,?_,?_⟩
  · intro i hi
    obtain ⟨_,_,ha,hb,_⟩ := gate2 hC hi
    exact ⟨ha,hb⟩
  · intro i hi
    obtain ⟨he,hin,_,_,hop⟩ := gate2 hC hi
    rw [he]
    have hop' : (gateAt C i).op = if A i then GateOp.and else GateOp.or := by
      rcases hop with hop | hop <;> simp [A,hop]
    cases hgc : gateAt C i with
    | mk o ins =>
      simp only [hgc] at hin hop'
      rw [hop',hin]
  · intro i hi hA
    obtain ⟨_,hin,_,_,hop⟩ := gate2 hC hi
    have ho : (gateAt C i).op=GateOp.or := by
      rcases hop with hop | hop
      · simp [A,hop] at hA
      · exact hop
    exact ⟨ho,by rw [hin]; simp [a],by rw [hin]; simp [b]⟩
  · intro i
    simp [A]

end PEqualNP.Outside.L_meta_4970.Compression

namespace PEqualNP.Outside.L_meta_4970.TypedCompression
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_4970.Compression

open Classical in
lemma typed_compress_one_cut {n : ℕ} (C : Circuit) (hC : TopForm.IsAO2 n C)
    (isLine : ℕ → Bool) (ht : PEqualNP.TwoColour.tCount n C isLine=0)
    (j : ℕ) (hj : j<C.gates.length) :
    ∃ (gs : List Gate) (m : ℕ → Option ℕ) (lab : ℕ → Finset (Fin n)),
      Ok n gs ∧ Labels n isLine gs lab ∧
      (∀ w < n+C.gates.length,
        (∀ w', m w=some w' → w'<n+gs.length ∧ lab w' ⊆ TopForm.orIn n C w) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) =
          ((zeroCut C j).wires (List.ofFn x)).getD w false) ∧
      gs.length+1 ≤ C.gates.length ∧
      andNum gs ≤ ((Finset.range C.gates.length).filter fun i =>
        (gateAt C i).op=GateOp.and ∧ i≠j).card := by
  classical
  obtain ⟨A,a,b,hab,hgate,hOR,hA⟩ := ao_descriptors C hC
  have hab' : ∀ i < (zeroCut C j).gates.length, a i<n+i ∧ b i<n+i := by
    simpa [zeroCut] using hab
  have hgate' : ∀ i (hi : i<(zeroCut C j).gates.length), (zeroCut C j).gates[i] =
      if i ∈ ({j} : Finset ℕ) then ⟨GateOp.or,[]⟩
      else ⟨if A i then GateOp.and else GateOp.or,[a i,b i]⟩ := by
    intro i hi
    have hi' : i<C.gates.length := by simpa [zeroCut] using hi
    by_cases hij : i=j
    · subst i
      simp [zeroCut]
    · have hs : (zeroCut C j).gates[i]=C.gates[i] := by
        simp [zeroCut,Ne.symm hij]
      rw [hs,hgate i hi']
      simp [hij]
  obtain ⟨gs,m,lab,hok,hl,hm,hs,hand⟩ :=
    typed_compress_labeled n C isLine A a b {j} ht hab hOR
  refine ⟨gs,m,lab,hok,hl,?_,?_,?_⟩
  · intro w hw
    refine ⟨(hm w hw).1,?_⟩
    intro x
    rw [(hm w hw).2 x,u_matches_run n (zeroCut C j).gates A a b {j} hab' hgate' x w
      (by simpa [zeroCut] using hw)]
    rfl
  · have hfilter : ((Finset.range C.gates.length).filter (· ∈ ({j} : Finset ℕ)))={j} := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_singleton]
      exact ⟨fun h => h.2,fun h => ⟨h ▸ hj,h⟩⟩
    rw [hfilter] at hs
    simpa using hs
  · have he : ((Finset.range C.gates.length).filter fun i => A i=true ∧ i∉({j} : Finset ℕ)) =
        ((Finset.range C.gates.length).filter fun i => (gateAt C i).op=GateOp.and ∧ i≠j) := by
      apply Finset.filter_congr
      intro i hi
      simp [hA i]
    rw [he] at hand
    exact hand

end PEqualNP.Outside.L_meta_4970.TypedCompression

namespace PEqualNP.Outside.L_meta_4970.TypedCompression
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma andGate_true (g : Gate) : andGate g = true ↔ g.op = GateOp.and := by
  cases g with
  | mk op ins => cases op <;> simp [andGate]

open Classical in
lemma andNum_filter (gs : List Gate) :
    andNum gs = ((Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or,[]⟩).op = GateOp.and).card := by
  classical
  induction gs using List.reverseRecOn with
  | nil => simp [andNum]
  | append_singleton gs g ih =>
    have he : (gs ++ [g]).getD gs.length ⟨GateOp.or,[]⟩ = g := by
      simp [List.getD_eq_getElem?_getD]
    have hf : ((Finset.range gs.length).filter fun i =>
        ((gs ++ [g]).getD i ⟨GateOp.or,[]⟩).op = GateOp.and) =
        ((Finset.range gs.length).filter fun i =>
        (gs.getD i ⟨GateOp.or,[]⟩).op = GateOp.and) := by
      apply Finset.filter_congr
      intro i hi
      have hit : i < gs.length := Finset.mem_range.mp hi
      simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hit]
    rw [List.length_append,List.length_singleton,Finset.range_add_one,
      Finset.filter_insert,he,hf]
    have hn : gs.length ∉ ((Finset.range gs.length).filter fun i =>
        (gs.getD i ⟨GateOp.or,[]⟩).op = GateOp.and) := by simp
    have hc : andNum (gs ++ [g]) = andNum gs + [g].countP andGate := by simp [andNum]
    rw [hc,ih]
    by_cases hg : g.op = GateOp.and
    · have hb := (andGate_true g).mpr hg
      simp [hg,hb,Finset.card_insert_of_notMem hn]
    · have hb : andGate g = false := by
        cases he : andGate g
        · rfl
        · exact False.elim (hg ((andGate_true g).mp he))
      simp [hg,hb]

open Classical in
lemma andNum_deleted_lt (C : Circuit) (gs : List Gate) (j : ℕ)
    (hj : j < C.gates.length) (hAND : (gateAt C j).op = GateOp.and)
    (hbound : andNum gs ≤ ((Finset.range C.gates.length).filter fun i =>
      (gateAt C i).op = GateOp.and ∧ i ∉ ({j} : Finset ℕ)).card) :
    andNum gs < andNum C.gates := by
  classical
  let S := (Finset.range C.gates.length).filter fun i => (gateAt C i).op = GateOp.and
  have hjS : j ∈ S := by simp [S,hj,hAND]
  have hfilter : ((Finset.range C.gates.length).filter fun i =>
      (gateAt C i).op = GateOp.and ∧ i ∉ ({j} : Finset ℕ)) = S.erase j := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_singleton,
      Finset.mem_erase,S]
    tauto
  have hcount : S.card = andNum C.gates := by
    rw [andNum_filter]
    rfl
  rw [hfilter] at hbound
  have hc := Finset.card_erase_add_one hjS
  omega

lemma andNum_join_or (gs : List Gate) (s t : ℕ) :
    andNum (gs ++ [⟨GateOp.or,[s,t]⟩]) = andNum gs := by
  simp [andNum,andGate]

open PEqualNP.Outside.L_meta_4970.Compression

lemma typed_cut_lift_preserves {n : ℕ} (pre post : List Gate) (g : Gate) (out a : ℕ)
    (hC : TopForm.IsAO2 n ⟨pre ++ [g] ++ post,out⟩)
    (isLine : ℕ → Bool)
    (ht : PEqualNP.TwoColour.tCount n ⟨pre ++ [g] ++ post,out⟩ isLine=0)
    (hout : out < n+(pre ++ [g] ++ post).length) (ha : a<pre.length)
    (haAND : (gateAt ⟨pre ++ [g] ++ post,out⟩ a).op=GateOp.and)
    (hgAND : g.op=GateOp.and)
    (hreader : ∀ x : Fin n → Bool,
      Semantic.val (pre ++ [g] ++ post) x (n+pre.length)=true →
        Semantic.val (pre ++ [g] ++ post) x (n+a)=true)
    (hbelow : ∀ x : Fin n → Bool,
      Semantic.val (pre ++ [g] ++ post) x (n+a)=true →
        Semantic.val (pre ++ [g] ++ post) x out=true)
    (hzero : ∀ u : Fin n,
      Semantic.val (pre ++ [g] ++ post) (Semantic.eof u) (n+pre.length)=false) :
    ∃ D : Circuit, TopForm.IsAO2 n D ∧ PEqualNP.TwoColour.tCount n D isLine=0 ∧
      D.size ≤ (pre ++ [g] ++ post).length ∧
      andNum D.gates < andNum (pre ++ [g] ++ post) ∧
      (∀ x : Fin n → Bool, circuitFun n D x = Semantic.val (pre ++ [g] ++ post) x out) ∧
      ∀ (Q : Finset (Fin n)), Q.Nonempty → ∀ w, w < n+(pre ++ [g] ++ post).length →
        (∀ x, Semantic.val (pre ++ [g] ++ post) x w = decide (∃ u ∈ Q,x u=true)) →
        ∃ v, ∀ x, (D.wires (List.ofFn x)).getD v false = decide (∃ u ∈ Q,x u=true) := by
  classical
  let C : Circuit := ⟨pre ++ [g] ++ post,out⟩
  have hj : pre.length<C.gates.length := by simp [C]
  obtain ⟨gs,m,lab,hok,hl,hsem,hsize,hand⟩ := typed_compress_one_cut C hC isLine ht pre.length hj
  have hget : ∀ w < n+C.gates.length, ∀ x : Fin n → Bool,
      ov gs (List.ofFn x) (m w) = Semantic.val (pre ++ [Semantic.zeroGate] ++ post) x w := by
    intro w hw x
    rw [(hsem w hw).2 x]
    change ((zeroCut C pre.length).gates.foldl _ (List.ofFn x)).getD w false = _
    rw [show (zeroCut C pre.length).gates = pre ++ [Semantic.zeroGate] ++ post from
      zeroCut_split pre post g out]
    rfl
  have hac : n+a<n+C.gates.length := by simp only [C,List.length_append,List.length_singleton]; omega
  have hancempty : TopForm.orIn n C (n+a)=∅ :=
    orIn_non_or C a (by rw [haAND]; intro he; cases he)
  have hanclabel : ∀ w, m (n+a)=some w → w<n+gs.length ∧ lab w ⊆ TopForm.orIn n C out := by
    intro w hw
    obtain ⟨hb,hs⟩ := (hsem (n+a) hac).1 w hw
    rw [hancempty] at hs
    exact ⟨hb,hs.trans (Finset.empty_subset _)⟩
  obtain ⟨D,hD,hDt,hDs,hDa,hfun,hpres⟩ := typed_join_optional isLine gs hok lab hl
    (m out) (m (n+a)) (TopForm.orIn n C out) (original_wire_mono isLine C ht out)
    (hsem out hout).1 hanclabel
  have hcutAND : (gateAt C pre.length).op=GateOp.and := by
    have he : gateAt C pre.length=g := by
      simp [gateAt,C,List.getD_eq_getElem?_getD]
    rw [he]
    exact hgAND
  have handlt : andNum gs < andNum C.gates :=
    andNum_deleted_lt C gs pre.length hj hcutAND (by simpa using hand)
  refine ⟨D,hD,hDt,by change D.size ≤ C.gates.length; omega,?_,?_,?_⟩
  · rw [hDa]
    exact handlt
  · intro x
    rw [hfun x,hget out hout x,hget (n+a) hac x]
    have hc : Semantic.val (pre ++ [Semantic.zeroGate] ++ post) x (n+a) =
        Semantic.val (pre ++ [g] ++ post) x (n+a) := by
      have h1 := Semantic.val_append_old pre ([Semantic.zeroGate] ++ post) x (n+a) (by omega)
      have h2 := Semantic.val_append_old pre ([g] ++ post) x (n+a) (by omega)
      simpa [List.append_assoc] using h1.trans h2.symm
    rw [hc]
    exact (Semantic.cut_zero_lift pre post g (n+a) out hreader hbelow x).symm
  · intro Q hQ w hw hOR
    have hp := Semantic.cut_zero_preserves_or pre post g hC.1 Q w hOR hzero
    cases hm : m w with
    | none =>
      obtain ⟨u,hu⟩ := hQ
      have he := hget w hw (fun _ => true)
      rw [hm,hp] at he
      have ht : decide (∃ u ∈ Q,(fun _ : Fin n => true) u=true) = true := by
        exact decide_eq_true ⟨u,hu,rfl⟩
      rw [ht] at he
      cases he
    | some v =>
      refine ⟨v,?_⟩
      intro x
      rw [hpres v (((hsem w hw).1 v hm).1) x]
      change ov gs (List.ofFn x) (some v) = _
      rw [← hm,hget w hw x,hp]

end PEqualNP.Outside.L_meta_4970.TypedCompression
