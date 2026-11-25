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

end PEqualNP.Outside.L_meta_4970.Semantic


namespace PEqualNP.Outside.L_meta_4970.ORCover

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4970.Semantic

def fill {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Fin n → Bool :=
  fun i => if i ∈ S then x i else true

def wireMap {n : ℕ} (S : Finset (Fin n)) (i : ℕ) : ℕ :=
  if h : i < n then if (⟨i, h⟩ : Fin n) ∈ S then i else n else i + 1

def gateMap {n : ℕ} (S : Finset (Fin n)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wireMap S)⟩

def fixedGates {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) : List Gate :=
  ⟨.and, []⟩ :: gs.map (gateMap S)

lemma wireMap_new {n : ℕ} (S : Finset (Fin n)) (i k : ℕ) :
    wireMap S i = n + k + 1 ↔ i = n + k := by
  unfold wireMap
  split_ifs with h hs <;> omega

lemma fixed_val {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (x : Fin n → Bool) (i : ℕ) :
    val (fixedGates S gs) x (wireMap S i) = val gs (fill S x) i := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    change val ([] ++ [⟨GateOp.and, []⟩]) x (wireMap S i) = val [] (fill S x) i
    rw [val_snoc]
    simp only [List.length_nil, Nat.add_zero, GateOp.eval, List.map_nil, List.all_nil]
    by_cases h : i < n
    · by_cases hs : (⟨i, h⟩ : Fin n) ∈ S
      · simp [wireMap, h, hs, val_nil, fill, show i ≠ n by omega]
      · simp [wireMap, h, hs, val_nil, fill]
    · simp [wireMap, h, val_nil, show i + 1 ≠ n by omega, show ¬ i + 1 < n by omega]
  | append_singleton gs g ih =>
    have hgs : fixedGates S (gs ++ [g]) = fixedGates S gs ++ [gateMap S g] := by
      simp [fixedGates]
    rw [hgs, val_snoc, val_snoc]
    have hlen : n + (fixedGates S gs).length = n + gs.length + 1 := by
      simp [fixedGates]; omega
    rw [hlen]
    simp only [wireMap_new]
    split_ifs
    · change g.op.eval ((g.inputs.map (wireMap S)).map (fun j => val (fixedGates S gs) x j)) = _
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j hj
      exact ih j
    · exact ih i

lemma fixed_getOp {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (k : ℕ) :
    ((fixedGates S gs)[k + 1]?).map Gate.op = (gs[k]?).map Gate.op := by
  simp [fixedGates, List.getElem?_map, Option.map_map, gateMap, Function.comp_def]

lemma fixed_good {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ fixedGates S gs,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [fixedGates, List.mem_cons, List.mem_map] at hg
  rcases hg with rfl | ⟨g, hg, rfl⟩
  · exact ⟨Or.inl rfl, by simp⟩
  · simpa [gateMap] using h g hg

lemma fixed_orGates {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) :
    orGates n (fixedGates S gs) = (orGates n gs).image (fun i => i + 1) := by
  classical
  ext i
  simp only [orGates, Finset.mem_filter, Finset.mem_Ico, Finset.mem_image]
  constructor
  · rintro ⟨⟨hni, hib⟩, hop⟩
    have hini : i ≠ n := by
      intro heq
      subst i
      simp [fixedGates] at hop
    have hlt : n < i := by omega
    refine ⟨i - 1, ⟨⟨by omega, ?_⟩, ?_⟩, by omega⟩
    · simp [fixedGates] at hib
      omega
    · have hind : i - n = (i - 1 - n) + 1 := by omega
      rw [hind, fixed_getOp] at hop
      exact hop
  · rintro ⟨j, ⟨⟨hnj, hjb⟩, hop⟩, rfl⟩
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · simp [fixedGates]
      omega
    · have hind : j + 1 - n = (j - n) + 1 := by omega
      rw [hind, fixed_getOp]
      exact hop

lemma fixed_orGates_card {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) :
    (orGates n (fixedGates S gs)).card = (orGates n gs).card := by
  classical
  rw [fixed_orGates, Finset.card_image_of_injective]
  intro i j h
  exact Nat.add_right_cancel h

lemma or_restriction_bound {n : ℕ} (S : Finset (Fin n)) (C : Circuit)
    (hgood : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (heval : ∀ x : Fin n → Bool,
      C.eval (List.ofFn (fill S x)) = decide (∃ v ∈ S, x v = true)) :
    S.card - 1 ≤ (orGates n C.gates).card := by
  classical
  have h := or_outputs_bound n 1 (fun _ => S) (by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim)
    (fixedGates S C.gates) (fun _ => wireMap S C.output) (fixed_good S C.gates hgood) (by
      intro w x
      change val (fixedGates S C.gates) x (wireMap S C.output) = _
      rw [fixed_val]
      exact heval x)
  simpa only [Fin.sum_univ_one, fixed_orGates_card] using h

end PEqualNP.Outside.L_meta_4970.ORCover
