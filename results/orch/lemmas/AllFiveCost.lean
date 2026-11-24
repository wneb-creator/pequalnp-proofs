import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1024_aux.Global

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (gs.foldl step (List.ofFn x)).getD i false

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma val_nil {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    val [] x i = if h : i < n then x ⟨i, h⟩ else false := by
  unfold val
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

lemma val_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ) :
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
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma gate_cases {X : Type} (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
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
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt S gs i

lemma D_mono {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D S gs ⊆ D S (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huv, hu, hv⟩ := hi.2
  refine ⟨?_, u, v, huv, ?_, ?_⟩
  · rw [val_snoc, if_neg hne]; exact hz
  · rw [val_snoc, if_neg hne]; exact hu
  · rw [val_snoc, if_neg hne]; exact hv

lemma main_inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
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
      rw [val_snoc, if_pos hN]
    have hold : ∀ (x : Fin n → Bool) (i : ℕ), i ≠ N → val (gs ++ [g]) x i = val gs x i := by
      intro x i hi
      rw [val_snoc, if_neg hi]
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
            · rw [if_pos h]
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
            rw [if_neg h]
        have h1 : (S.image l).card ≤
            (S.image fun w => if l w = l v0 then l u0 else l w).card + 1 :=
          (Finset.card_le_card himg).trans (Finset.card_insert_le _ _)
        have hNin : N ∈ D S (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ?_, u0, v0, ?_, ?_, ?_⟩
          · rw [hnew]; exact hz
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
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

lemma family_bound : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length := by
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
    obtain ⟨-, hza, u, v, huv, hu, hv⟩ := hia
    obtain ⟨-, hzb, -⟩ := hib
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
    _ ≤ (Finset.Ico n (n + gates.length)).card := by
        apply Finset.card_le_card
        intro i hi
        obtain ⟨w, -, hw⟩ := Finset.mem_biUnion.mp hi
        simp only [D, Finset.mem_filter] at hw
        exact hw.1
    _ = gates.length := by simp

def line (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma line_intersection : ∀ i j : Fin 13, i ≠ j → (line i ∩ line j).card ≤ 1 := by
  decide +kernel

lemma line_card : ∀ w : Fin 13, (line w).card = 4 := by decide +kernel

lemma global_bound (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (he : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = decide (∃ p ∈ line w, x p = true)) :
    39 ≤ gs.length := by
  have h := family_bound 13 13 line line_intersection gs out hg he
  simpa [line_card] using h

end PEqualNP.Outside.L_meta_1024_aux.Global

namespace PEqualNP.Outside.L_meta_1024_aux.Support

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l₁ l₂ : List Bool) (hlen : l₁.length = l₂.length)
    (hle : ∀ i, l₁.getD i false = true → l₂.getD i false = true) :
    op.eval l₁ = true → op.eval l₂ = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro h b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      have hi1 : i < l₁.length := by omega
      rw [List.getD_eq_getElem _ _ hi1]
      exact h _ (List.getElem_mem hi1)
    have h2 := hle i h1
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    rintro ⟨b, hb, rfl⟩
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb
    have h1 : l₁.getD i false = true := by
      rw [List.getD_eq_getElem _ _ hi]; exact hbi
    have h2 := hle i h1
    have hi2 : i < l₂.length := by omega
    rw [List.getD_eq_getElem _ _ hi2] at h2
    exact ⟨l₂[i], List.getElem_mem hi2, h2⟩

lemma wiresFrom_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w₁ w₂ : List Bool), w₁.length = w₂.length →
      (∀ i, w₁.getD i false = true → w₂.getD i false = true) →
      ∀ i, (wiresFrom gs w₁).getD i false = true → (wiresFrom gs w₂).getD i false = true := by
  induction gs with
  | nil =>
    intro w₁ w₂ _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w₁ w₂ hlen hle i hi
    have hstep1 : wiresFrom (g :: gs) w₁ =
        wiresFrom gs (w₁ ++ [g.op.eval (g.inputs.map fun j => w₁.getD j false)]) := rfl
    have hstep2 : wiresFrom (g :: gs) w₂ =
        wiresFrom gs (w₂ ++ [g.op.eval (g.inputs.map fun j => w₂.getD j false)]) := rfl
    rw [hstep1] at hi
    rw [hstep2]
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg')) _ _ (by simp [hlen]) _ i hi
    intro j hj
    by_cases hlt : j < w₁.length
    · rw [List.getD_append _ _ _ _ hlt] at hj
      rw [List.getD_append _ _ _ _ (by omega)]
      exact hle j hj
    · by_cases heq : j = w₁.length
      · subst heq
        rw [getD_snoc_eq] at hj
        rw [hlen, getD_snoc_eq]
        exact gateOp_eval_mono g.op (hmono g List.mem_cons_self)
          (g.inputs.map fun k => w₁.getD k false) (g.inputs.map fun k => w₂.getD k false)
          (by simp) (by
            intro t ht
            by_cases ht_lt : t < g.inputs.length
            · rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)] at ht
              rw [List.getD_eq_getElem _ _ (by simpa using ht_lt)]
              simp only [List.getElem_map] at ht ⊢
              exact hle _ ht
            · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt ht_lt)] at ht
              exact Bool.noConfusion ht) hj
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
        exact Bool.noConfusion hj


def line (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

def zeroSet (x : Fin 13 → Bool) : Finset (Fin 13) :=
  Finset.univ.filter (fun p => x p = false)

def Band (x : Fin 13 → Bool) : Prop := (zeroSet x).card = 5 ∨ (zeroSet x).card = 6

def target (w : Fin 13) (x : Fin 13 → Bool) : Bool := decide (∃ p ∈ line w, x p = true)

def row (w p : Fin 13) : Bool :=
  decide (p ∉ (({0, 1, 2, 3, 4, 9} : Finset (Fin 13)).image (fun u => u + w)))

def flip (w p q : Fin 13) : Bool := if q = p then true else row w q

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma row_spec : ∀ w : Fin 13, (zeroSet (row w)).card = 6 ∧ target w (row w) = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma flip_spec : ∀ w p : Fin 13, p ∈ line w →
    (zeroSet (flip w p)).card = 5 ∧ target w (flip w p) = true := by
  decide +kernel

def Supports (f : (Fin 13 → Bool) → Bool) (S : Finset (Fin 13)) : Prop :=
  ∀ x y, (∀ p ∈ S, x p = y p) → f x = f y

lemma support_contains_line (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Band x → f x = target w x) (S : Finset (Fin 13))
    (hsupport : Supports f S) : line w ⊆ S := by
  intro p hp
  by_contra hnot
  have hsame : f (row w) = f (flip w p) := by
    apply hsupport
    intro q hq
    have hqp : q ≠ p := by intro he; subst q; exact hnot hq
    simp [flip, hqp]
  rw [hcorrect _ (Or.inr (row_spec w).1),
    hcorrect _ (Or.inl (flip_spec w p hp).1), (row_spec w).2,
    (flip_spec w p hp).2] at hsame
  exact Bool.noConfusion hsame

def fromZeros (Z : Finset (Fin 13)) (p : Fin 13) : Bool := decide (p ∉ Z)

lemma zeroSet_fromZeros (Z : Finset (Fin 13)) : zeroSet (fromZeros Z) = Z := by
  ext p
  simp [zeroSet, fromZeros]

lemma complete_input (S : Finset (Fin 13)) (hS : S.card ≤ 7) (x : Fin 13 → Bool)
    (hz : (S.filter (fun p => x p = false)).card ≤ 6) :
    ∃ y : Fin 13 → Bool, Band y ∧ ∀ p ∈ S, y p = x p := by
  let Z := S.filter (fun p => x p = false)
  have hzc : Z.card ≤ 6 := hz
  have hcomp : 6 ≤ (Finset.univ \ S).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨B, hB, hBc⟩ := Finset.exists_subset_card_eq
    (show 6 - Z.card ≤ (Finset.univ \ S).card by omega)
  have hd : Disjoint Z B := by
    rw [Finset.disjoint_left]
    intro p hpZ hpB
    exact (Finset.mem_sdiff.mp (hB hpB)).2 (Finset.mem_filter.mp hpZ).1
  refine ⟨fromZeros (Z ∪ B), Or.inr ?_, ?_⟩
  · rw [zeroSet_fromZeros, Finset.card_union_of_disjoint hd, hBc]
    omega
  · intro p hpS
    have hpB : p ∉ B := fun h => (Finset.mem_sdiff.mp (hB h)).2 hpS
    cases hx : x p <;> simp [fromZeros, Z, hpS, hpB, hx]

lemma target_eq_of_agree (w : Fin 13) (S : Finset (Fin 13)) (hline : line w ⊆ S)
    (x y : Fin 13 → Bool) (hxy : ∀ p ∈ S, x p = y p) : target w x = target w y := by
  apply Bool.eq_iff_iff.mpr
  simp only [target, decide_eq_true_eq]
  constructor
  · rintro ⟨p, hp, hx⟩
    exact ⟨p, hp, (hxy p (hline hp)).symm.trans hx⟩
  · rintro ⟨p, hp, hy⟩
    exact ⟨p, hp, (hxy p (hline hp)).trans hy⟩

lemma small_support_exact (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Band x → f x = target w x) (hzero : f (fun _ => false) = false)
    (S : Finset (Fin 13)) (hS : S.card ≤ 7) (hsupport : Supports f S) :
    ∀ x, f x = target w x := by
  have hline := support_contains_line w f hcorrect S hsupport
  intro x
  by_cases hz : (S.filter (fun p => x p = false)).card ≤ 6
  · obtain ⟨y, hy, hxy⟩ := complete_input S hS x hz
    calc f x = f y := hsupport x y (fun p hp => (hxy p hp).symm)
      _ = target w y := hcorrect y hy
      _ = target w x := target_eq_of_agree w S hline y x hxy
  · have hle := Finset.card_le_card (Finset.filter_subset (fun p => x p = false) S)
    have he : S.filter (fun p => x p = false) = S :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have hfalse : ∀ p ∈ S, x p = false := by
      intro p hp
      have hmem : p ∈ S.filter (fun p => x p = false) := he.symm ▸ hp
      exact (Finset.mem_filter.mp hmem).2
    have ht : target w x = false := by
      apply decide_eq_false_iff_not.mpr
      rintro ⟨p, hp, hx⟩
      rw [hfalse p (hline hp)] at hx
      exact Bool.noConfusion hx
    rw [ht, ← hzero]
    exact hsupport x (fun _ => false) hfalse

lemma zero_input_read (n i : ℕ) :
    (List.ofFn (fun _ : Fin n => false)).getD i false = false := by
  by_cases h : i < n <;> simp [List.getD_eq_getElem?_getD, h]

lemma circuit_zero (gs : List Gate) (o : ℕ)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (y : Fin 13 → Bool) (hy : Circuit.eval ⟨gs, o⟩ (List.ofFn y) = false) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn (fun _ : Fin 13 => false)) = false := by
  cases hzero : Circuit.eval ⟨gs, o⟩ (List.ofFn (fun _ : Fin 13 => false)) with
  | false => rfl
  | true =>
    have hm := wiresFrom_mono gs hmono
      (List.ofFn (fun _ : Fin 13 => false)) (List.ofFn y) (by simp)
      (by intro i hi; rw [zero_input_read] at hi; exact Bool.noConfusion hi) o hzero
    change Circuit.eval ⟨gs, o⟩ (List.ofFn y) = true at hm
    rw [hy] at hm
    exact Bool.noConfusion hm

lemma circuit_support_exact (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hcorrect : ∀ x, Band x → Circuit.eval ⟨gs, o⟩ (List.ofFn x) = target w x)
    (S : Finset (Fin 13)) (hS : S.card ≤ 7)
    (hsupport : Supports (fun x => Circuit.eval ⟨gs, o⟩ (List.ofFn x)) S) :
    ∀ x, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = target w x := by
  apply small_support_exact w _ hcorrect _ S hS hsupport
  apply circuit_zero gs o hmono (row w)
  rw [hcorrect _ (Or.inr (row_spec w).1)]
  exact (row_spec w).2

end PEqualNP.Outside.L_meta_1024_aux.Support

namespace PEqualNP.Outside.L_meta_1024_aux.Clamp

open PEqualNP.Outside.L_meta_1024_aux.Support

lemma line_card : ∀ w : Fin 13, (line w).card = 4 := by decide +kernel

lemma row_line_false : ∀ w q : Fin 13, q ∈ line w → row w q = false := by
  decide +kernel

lemma extend_eight (w : Fin 13) (Q : Finset (Fin 13))
    (hQ : Q ⊆ Finset.univ \ line w) (hcard : Q.card ≤ 8) :
    ∃ Y : Finset (Fin 13), Q ⊆ Y ∧ Y ⊆ Finset.univ \ line w ∧ Y.card = 8 := by
  have houtside : (Finset.univ \ line w).card = 9 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), line_card]
    decide
  have havail : 8 - Q.card ≤ ((Finset.univ \ line w) \ Q).card := by
    rw [Finset.card_sdiff_of_subset hQ, houtside]
    omega
  obtain ⟨B, hB, hBc⟩ := Finset.exists_subset_card_eq havail
  have hd : Disjoint Q B := by
    rw [Finset.disjoint_left]
    intro p hpQ hpB
    exact (Finset.mem_sdiff.mp (hB hpB)).2 hpQ
  refine ⟨Q ∪ B, Finset.subset_union_left, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hQ h
    · exact (Finset.mem_sdiff.mp (hB h)).1
  · rw [Finset.card_union_of_disjoint hd, hBc]
    omega

def fromTrue (Y : Finset (Fin 13)) (p : Fin 13) : Bool := decide (p ∈ Y)
def singleton (q p : Fin 13) : Bool := decide (p = q)

lemma fromTrue_band (Y : Finset (Fin 13)) (hY : Y.card = 8) : Band (fromTrue Y) := by
  apply Or.inl
  have hz : zeroSet (fromTrue Y) = Finset.univ \ Y := by
    ext p
    simp [zeroSet, fromTrue]
  rw [hz, Finset.card_sdiff_of_subset (Finset.subset_univ _), hY]
  decide

lemma fromTrue_misses (w : Fin 13) (Y : Finset (Fin 13))
    (hY : Y ⊆ Finset.univ \ line w) : target w (fromTrue Y) = false := by
  apply decide_eq_false_iff_not.mpr
  rintro ⟨p, hp, htrue⟩
  have hin : p ∈ Y := by simpa [fromTrue] using htrue
  exact (Finset.mem_sdiff.mp (hY hin)).2 hp

lemma supported_mono {m : ℕ} (F : (Fin m → Bool) → Bool) (E : Finset (Fin m))
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (a b : Fin m → Bool) (hab : ∀ i ∈ E, a i = true → b i = true)
    (ha : F a = true) : F b = true := by
  let c : Fin m → Bool := fun i => if i ∈ E then b i else a i
  have hc : F c = true := hmono a c (by
    intro i hi
    by_cases he : i ∈ E
    · simpa [c, he] using hab i he hi
    · simpa [c, he] using hi) ha
  have he : F c = F b := hsupport c b (by intro i hi; simp [c, hi])
  exact he ▸ hc

set_option maxHeartbeats 2000000 in
lemma missing_raw_impossible {m : ℕ} (w p : Fin 13) (hp : p ∈ line w)
    (E : Finset (Fin m)) (hE : E.card ≤ 8) (F : (Fin m → Bool) → Bool)
    (leaf : Fin m → (Fin 13 → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hleaf : ∀ i ∈ E, ∀ x y, (∀ q, x q = true → y q = true) →
      leaf i x = true → leaf i y = true)
    (hcorrect : ∀ x, Band x → F (fun i => leaf i x) = target w x)
    (hclass : ∀ i ∈ E,
      (∃ q ∈ line w, q ≠ p ∧ ∀ x, leaf i x = x q) ∨
      ∃ q : Fin 13, q ∉ line w ∧ leaf i (singleton q) = true) : False := by
  classical
  let foreign : Fin m → Prop := fun i => ∃ q : Fin 13,
    q ∉ line w ∧ leaf i (singleton q) = true
  let q : Fin m → Fin 13 := fun i => if h : foreign i then Classical.choose h else 0
  have q_spec (i : Fin m) (hi : foreign i) :
      q i ∉ line w ∧ leaf i (singleton (q i)) = true := by
    simpa only [q, dite_eq_left hi] using Classical.choose_spec hi
  let Q := (E.filter foreign).image q
  have hQcard : Q.card ≤ 8 :=
    (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans hE
  have hQ : Q ⊆ Finset.univ \ line w := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (q_spec i (Finset.mem_filter.mp hi).2).1⟩
  obtain ⟨Y, hQY, hY, hYcard⟩ := extend_eight w Q hQ hQcard
  have hpband : Band (Support.flip w p) := Or.inl (flip_spec w p hp).1
  have hptrue : F (fun i => leaf i (Support.flip w p)) = true :=
    (hcorrect _ hpband).trans (flip_spec w p hp).2
  have hyfalse : F (fun i => leaf i (fromTrue Y)) = false :=
    (hcorrect _ (fromTrue_band Y hYcard)).trans (fromTrue_misses w Y hY)
  have hcompare : ∀ i ∈ E, leaf i (Support.flip w p) = true → leaf i (fromTrue Y) = true := by
    intro i hi hpos
    rcases hclass i hi with ⟨r, hr, hrp, hraw⟩ | hforeign
    · rw [hraw, Support.flip, ite_eq_right hrp, row_line_false w r hr] at hpos
      exact Bool.noConfusion hpos
    · have hfor : foreign i := hforeign
      have hqi : q i ∈ Y := hQY (Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨hi, hfor⟩, rfl⟩)
      apply hleaf i hi (singleton (q i)) (fromTrue Y) _ (q_spec i hfor).2
      intro r hr
      have he : r = q i := by simpa [singleton] using hr
      subst r
      simp [fromTrue, hqi]
  have hytrue := supported_mono F E hmono hsupport _ _ hcompare hptrue
  rw [hyfalse] at hytrue
  exact Bool.noConfusion hytrue

end PEqualNP.Outside.L_meta_1024_aux.Clamp

namespace PEqualNP.Outside.L_meta_1024_aux.Charges

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1024_aux.Global

lemma disjoint_charges (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (a b : Fin 13) (hab : a ≠ b) : Disjoint (D (line a) gs) (D (line b) gs) := by
  classical
  obtain ⟨la, hia, _⟩ := main_inv (line a) gs hg
  obtain ⟨lb, hib, _⟩ := main_inv (line b) gs hg
  rw [Finset.disjoint_left]
  intro i hiA hiB
  simp only [D, Finset.mem_filter, Finset.mem_Ico] at hiA hiB
  obtain ⟨_, hza, u, v, huv, hu, hv⟩ := hiA
  obtain ⟨_, hzb, _⟩ := hiB
  have hua := (hia i u u hza hu hu).1
  have hva := (hia i v v hza hv hv).1
  have hub := (hib i u u hzb hu hu).1
  have hvb := (hib i v v hzb hv hv).1
  have hsub : ({u, v} : Finset (Fin 13)) ⊆ line a ∩ line b := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact Finset.mem_inter.mpr ⟨hua, hub⟩
    · exact Finset.mem_inter.mpr ⟨hva, hvb⟩
  have h2 : ({u, v} : Finset (Fin 13)).card = 2 := Finset.card_pair huv
  have := Finset.card_le_card hsub
  have := line_intersection a b hab
  omega

lemma ordinary_charge_count (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (he : ∀ x : Fin 13 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) =
      decide (∃ p ∈ line w, x p = true)) : 3 ≤ (D (line w) gs).card := by
  classical
  obtain ⟨l, hinv, hcard⟩ := main_inv (line w) gs hg
  have hZ : val gs (Zof (line w)) o = false := by
    change Circuit.eval ⟨gs, o⟩ (List.ofFn _) = false
    rw [he]
    simp [Zof]
  have hE : ∀ u ∈ line w, val gs (eof u) o = true := by
    intro u hu
    change Circuit.eval ⟨gs, o⟩ (List.ofFn _) = true
    rw [he]
    simp only [decide_eq_true_eq]
    exact ⟨u, hu, by simp [eof]⟩
  have himg : ((line w).image l).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    exact (hinv o u v hZ (hE u hu) (hE v hv)).2
  rw [line_card] at hcard
  omega

lemma charge_outside (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w a : Fin 13) (hwa : a ≠ w) (i : ℕ) (hi : i ∈ D (line a) gs) :
    ∃ q : Fin 13, q ∉ line w ∧ val gs (eof q) i = true := by
  classical
  obtain ⟨l, hinv, _⟩ := main_inv (line a) gs hg
  simp only [D, Finset.mem_filter, Finset.mem_Ico] at hi
  obtain ⟨_, hz, u, v, huv, hu, hv⟩ := hi
  have hua := (hinv i u u hz hu hu).1
  have hva := (hinv i v v hz hv hv).1
  by_cases huw : u ∈ line w
  · refine ⟨v, ?_, hv⟩
    intro hvw
    have hsub : ({u, v} : Finset (Fin 13)) ⊆ line a ∩ line w := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · exact Finset.mem_inter.mpr ⟨hua, huw⟩
      · exact Finset.mem_inter.mpr ⟨hva, hvw⟩
    have h2 : ({u, v} : Finset (Fin 13)).card = 2 := Finset.card_pair huv
    have := Finset.card_le_card hsub
    have := line_intersection a w hwa
    omega
  · exact ⟨u, huw, hu⟩

lemma twelve_ordinary_charges (gs : List Gate) (out : Fin 13 → ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hordinary : ∀ a : Fin 13, a ≠ w → ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out a⟩ (List.ofFn x) = decide (∃ p ∈ line a, x p = true)) :
    ∃ P : Finset ℕ, P ⊆ Finset.Ico 13 (13 + gs.length) ∧ 36 ≤ P.card ∧
      ∀ i ∈ P, ∃ q : Fin 13, q ∉ line w ∧ val gs (eof q) i = true := by
  classical
  let W : Finset (Fin 13) := Finset.univ.erase w
  let P := W.biUnion (fun a => D (line a) gs)
  have hW : W.card = 12 := by simp [W]
  have hne (a : Fin 13) (ha : a ∈ W) : a ≠ w := (Finset.mem_erase.mp ha).1
  have hsubset : P ⊆ Finset.Ico 13 (13 + gs.length) := by
    intro i hi
    obtain ⟨a, _, hai⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hai).1
  have hcount : 36 ≤ P.card := by
    have hd : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → Disjoint (D (line a) gs) (D (line b) gs) := by
      intro a _ b _ hab
      exact disjoint_charges gs hg a b hab
    have hsum : (∑ _a ∈ W, (3 : ℕ)) ≤ ∑ a ∈ W, (D (line a) gs).card := by
      apply Finset.sum_le_sum
      intro a ha
      exact ordinary_charge_count gs (out a) a hg (hordinary a (hne a ha))
    rw [← Finset.card_biUnion hd] at hsum
    simpa [P, hW] using hsum
  refine ⟨P, hsubset, hcount, ?_⟩
  intro i hi
  obtain ⟨a, ha, hai⟩ := Finset.mem_biUnion.mp hi
  exact charge_outside gs hg w a (hne a ha) i hai

end PEqualNP.Outside.L_meta_1024_aux.Charges

namespace PEqualNP.Outside.L_meta_1024_aux.Bridge

open PEqualNP.CircuitLowerBounds

lemma val_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
    Global.val gs x i.val = x i := by
  induction gs using List.reverseRecOn with
  | nil => simp [Global.val_nil, i.isLt]
  | append_singleton gs g ih =>
    rw [Global.val_snoc, ite_eq_right (by omega)]
    exact ih

lemma val_mono (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin 13 → Bool) (hxy : ∀ p, x p = true → y p = true)
    (i : ℕ) (hx : Global.val gs x i = true) : Global.val gs y i = true := by
  apply Support.wiresFrom_mono gs hg (List.ofFn x) (List.ofFn y) (by simp) _ i hx
  intro k hk
  by_cases hlt : k < 13
  · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hlt)] at hk
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using hlt)]
    simp only [List.getElem_ofFn] at hk ⊢
    exact hxy ⟨k, hlt⟩ hk
  · rw [List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using Nat.le_of_not_lt hlt)] at hk
    exact Bool.noConfusion hk

def rawIndex (gs : List Gate) (p : Fin 13) : Fin (13 + gs.length) :=
  ⟨p.val, by omega⟩

lemma raw_line_members (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      Global.val gs x o = Support.target w x)
    (P : Finset ℕ)
    (hPoutside : ∀ i ∈ P, ∃ q : Fin 13,
      q ∉ Global.line w ∧ Global.val gs (Global.eof q) i = true)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (E : Finset (Fin (13 + gs.length))) (hEcard : E.card ≤ 8)
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hfactor : ∀ x : Fin 13 → Bool, F (fun i => Global.val gs x i.val) = Global.val gs x o)
    (p : Fin 13) (hp : p ∈ Global.line w) : rawIndex gs p ∈ E := by
  classical
  by_contra hpnot
  apply Clamp.missing_raw_impossible w p hp E hEcard F
    (fun i x => Global.val gs x i.val) hmono hsupport
  · intro i _ x y hxy hx
    exact val_mono gs hg x y hxy i.val hx
  · intro x hx
    rw [hfactor]
    exact hcorrect x hx
  · intro i hi
    rcases hallowed i hi with hiraw | hipaid
    · let q : Fin 13 := ⟨i.val, hiraw⟩
      have hraw : ∀ x : Fin 13 → Bool, Global.val gs x i.val = x q := fun x => val_input gs x q
      by_cases hql : q ∈ Global.line w
      · left
        refine ⟨q, hql, ?_, hraw⟩
        intro hqp
        have hie : i = rawIndex gs p := by
          apply Fin.ext
          exact congrArg (fun t : Fin 13 => t.val) hqp
        exact hpnot (hie ▸ hi)
      · right
        refine ⟨q, hql, ?_⟩
        rw [hraw]
        simp [Clamp.singleton]
    · obtain ⟨q, hq, hqtrue⟩ := hPoutside i.val hipaid
      exact Or.inr ⟨q, hq, hqtrue⟩

lemma cut_contradiction (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      Global.val gs x o = Support.target w x)
    (hsmall : gs.length < 39)
    (P : Finset ℕ) (hP : P ⊆ Finset.Ico 13 (13 + gs.length)) (hPcard : 36 ≤ P.card)
    (hPoutside : ∀ i ∈ P, ∃ q : Fin 13,
      q ∉ Global.line w ∧ Global.val gs (Global.eof q) i = true)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (E : Finset (Fin (13 + gs.length)))
    (hEcard : E.card ≤ gs.length - P.card + 1)
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hfactor : ∀ x : Fin 13 → Bool, F (fun i => Global.val gs x i.val) = Global.val gs x o) :
    False := by
  classical
  have hPupper : P.card ≤ gs.length := by
    have hh := Finset.card_le_card hP
    simpa using hh
  have hE3 : E.card ≤ 3 := by omega
  have hinj : Function.Injective (rawIndex gs) := by
    intro a b h
    apply Fin.ext
    exact congrArg (fun t : Fin (13 + gs.length) => t.val) h
  have hlinecard : ((Global.line w).image (rawIndex gs)).card = 4 := by
    rw [Finset.card_image_of_injective _ hinj, Global.line_card]
  have hsub : (Global.line w).image (rawIndex gs) ⊆ E := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact raw_line_members gs o w (fun g hm => (hg g hm).1) hcorrect P hPoutside F E
      (by omega) hallowed hmono hsupport hfactor p hp
  have hh := Finset.card_le_card hsub
  omega

end PEqualNP.Outside.L_meta_1024_aux.Bridge

namespace PEqualNP.Outside.L_meta_1024_aux.Cut

open PEqualNP.CircuitLowerBounds

def source {M : ℕ} (x : Fin M → Bool) (i : ℕ) : Bool :=
  (List.ofFn x).getD i false

lemma source_eq {M : ℕ} (x : Fin M → Bool) (i : ℕ) :
    source x i = if h : i < M then x ⟨i, h⟩ else false := by
  unfold source
  by_cases h : i < M <;> simp [List.getD_eq_getElem?_getD, h]

lemma source_dep {M : ℕ} (x y : Fin M → Bool) (i : ℕ) (t : Fin M)
    (hxy : ∀ j, j ≠ t → x j = y j) (hne : source x i ≠ source y i) : t.val = i := by
  rw [source_eq, source_eq] at hne
  by_cases h : i < M
  · simp only [h, dite_true] at hne
    have he : (⟨i, h⟩ : Fin M) = t := by
      by_contra ht
      exact hne (hxy _ ht)
    exact (congrArg Fin.val he).symm
  · simp [h] at hne

def cutStep {M : ℕ} (P : Finset ℕ) (x : Fin M → Bool) (w : List Bool) (g : Gate) :
    List Bool :=
  w ++ [if w.length ∈ P then source x w.length
    else g.op.eval (g.inputs.map fun i => w.getD i false)]

def cutRun {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (x : Fin M → Bool) :
    List Bool :=
  gs.foldl (cutStep P x) (List.ofFn (fun i : Fin n => source x i.val))

def cutVal {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (x : Fin M → Bool)
    (i : ℕ) : Bool := (cutRun n P gs x).getD i false

lemma fold_length {M : ℕ} (P : Finset ℕ) (x : Fin M → Bool) (gs : List Gate)
    (w : List Bool) :
    (gs.foldl (cutStep P x) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_cons, cutStep, List.length_append,
      List.length_cons, List.length_nil]
    omega

lemma run_length {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (x : Fin M → Bool) :
    (cutRun n P gs x).length = n + gs.length := by
  simp [cutRun, fold_length]

lemma cutVal_nil {M : ℕ} (n : ℕ) (P : Finset ℕ) (x : Fin M → Bool) (i : ℕ) :
    cutVal n P [] x i = if i < n then source x i else false := by
  unfold cutVal cutRun
  by_cases h : i < n <;> simp [List.getD_eq_getElem?_getD, h]

lemma cutVal_snoc {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (g : Gate)
    (x : Fin M → Bool) (i : ℕ) :
    cutVal n P (gs ++ [g]) x i =
      if i = n + gs.length then
        if i ∈ P then source x i
        else g.op.eval (g.inputs.map fun j => cutVal n P gs x j)
      else cutVal n P gs x i := by
  unfold cutVal cutRun
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, cutStep]
  have hl : (gs.foldl (cutStep P x) (List.ofFn (fun i : Fin n => source x i.val))).length =
      n + gs.length := by rw [fold_length]; simp
  rcases lt_trichotomy i (n + gs.length) with h | h | h
  · rw [ite_eq_right (show i ≠ n + gs.length by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · rw [ite_eq_left h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hl, h]
  · rw [ite_eq_right (show i ≠ n + gs.length by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

def unpaid (n : ℕ) (P : Finset ℕ) (gs : List Gate) : ℕ :=
  ((Finset.Ico n (n + gs.length)) \ P).card

lemma unpaid_nil (n : ℕ) (P : Finset ℕ) : unpaid n P [] = 0 := by simp [unpaid]

lemma unpaid_snoc (n : ℕ) (P : Finset ℕ) (gs : List Gate) (g : Gate) :
    unpaid n P (gs ++ [g]) = unpaid n P gs + if n + gs.length ∈ P then 0 else 1 := by
  have he : Finset.Ico n (n + (gs ++ [g]).length) =
      insert (n + gs.length) (Finset.Ico n (n + gs.length)) := by
    simp only [List.length_append, List.length_cons, List.length_nil]
    rw [← Nat.add_assoc]
    exact Nat.Ico_succ_right_eq_insert_Ico (by omega)
  unfold unpaid
  rw [he]
  by_cases hp : n + gs.length ∈ P
  · rw [Finset.insert_sdiff_of_mem _ hp]
    simp [hp]
  · rw [Finset.insert_sdiff_of_notMem _ hp, Finset.card_insert_of_notMem]
    · simp [hp]
    · simp

lemma unpaid_eq_sub (n : ℕ) (P : Finset ℕ) (gs : List Gate)
    (hP : P ⊆ Finset.Ico n (n + gs.length)) :
    unpaid n P gs = gs.length - P.card := by
  rw [unpaid, Finset.card_sdiff_of_subset hP]
  simp

def Depends {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (i : ℕ) (t : Fin M) : Prop :=
  ∃ x y : Fin M → Bool, (∀ j, j ≠ t → x j = y j) ∧
    cutVal n P gs x i ≠ cutVal n P gs y i

lemma two_inputs (ins : List ℕ) (h : ins.length ≤ 2) :
    ∃ a b : ℕ, ∀ j ∈ ins, j = a ∨ j = b := by
  match ins, h with
  | [], _ => exact ⟨0, 0, by simp⟩
  | [a], _ => exact ⟨a, a, by simp⟩
  | [a, b], _ => exact ⟨a, b, by simp⟩
  | _ :: _ :: _ :: _, h => simp at h

lemma components {M : ℕ} (n : ℕ) (P : Finset ℕ) (S : Finset (Fin M))
    (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    ∃ (label : Fin M → ℕ) (wire : ℕ → ℕ),
      S.card ≤ (S.image label).card + unpaid n P gs ∧
      ∀ i t, Depends n P gs i t → label t = wire i := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨Fin.val, id, ?_, ?_⟩
    · simp [unpaid_nil, Finset.card_image_of_injective _ Fin.val_injective]
    · rintro i t ⟨x, y, hxy, hne⟩
      rw [cutVal_nil, cutVal_nil] at hne
      by_cases hi : i < n
      · simp only [hi, ite_true] at hne
        exact source_dep x y i t hxy hne
      · simp [hi] at hne
  | append_singleton gs g ih =>
    obtain ⟨label, wire, hcount, hdep⟩ := ih (fun g' h => hg g' (by simp [h]))
    by_cases hp : n + gs.length ∈ P
    · refine ⟨label, fun i => if h : i = n + gs.length then
        if hi : i < M then label ⟨i, hi⟩ else 0 else wire i, ?_, ?_⟩
      · simpa [unpaid_snoc, hp] using hcount
      · rintro i t ⟨x, y, hxy, hne⟩
        rw [cutVal_snoc, cutVal_snoc] at hne
        by_cases hi : i = n + gs.length
        · simp only [hi, ite_true, hp] at hne ⊢
          have ht := source_dep x y (n + gs.length) t hxy hne
          have hlt : n + gs.length < M := by omega
          simp only [hlt, dite_true]
          congr 1
          exact Fin.ext ht
        · simp only [hi, ite_false, dite_false] at hne ⊢
          exact hdep i t ⟨x, y, hxy, hne⟩
    · obtain ⟨a, b, hinputs⟩ := two_inputs g.inputs (hg g (by simp))
      let merge (k : ℕ) := if k = wire b then wire a else k
      have ha : merge (wire a) = wire a := by simp [merge]
      have hb : merge (wire b) = wire a := by simp [merge]
      refine ⟨merge ∘ label,
        fun i => if i = n + gs.length then wire a else merge (wire i), ?_, ?_⟩
      · have hsub : S.image label ⊆ insert (wire b) (S.image (merge ∘ label)) := by
          intro v hv
          obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
          by_cases he : label t = wire b
          · simp [he]
          · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨t, ht, by simp [merge, he]⟩)
        have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
        rw [unpaid_snoc]
        simp only [hp, ite_false]
        omega
      · rintro i t ⟨x, y, hxy, hne⟩
        rw [cutVal_snoc, cutVal_snoc] at hne
        by_cases hi : i = n + gs.length
        · simp only [hi, ite_true, hp, ite_false, Function.comp_apply] at hne ⊢
          have hd : cutVal n P gs x a ≠ cutVal n P gs y a ∨
              cutVal n P gs x b ≠ cutVal n P gs y b := by
            by_contra! hh
            apply hne
            apply congrArg g.op.eval
            apply List.map_congr_left
            intro j hj
            rcases hinputs j hj with rfl | rfl
            · exact hh.1
            · exact hh.2
          rcases hd with hd | hd
          · rw [hdep a t ⟨x, y, hxy, hd⟩, ha]
          · rw [hdep b t ⟨x, y, hxy, hd⟩, hb]
        · simp only [hi, ite_false, Function.comp_apply] at hne ⊢
          rw [hdep i t ⟨x, y, hxy, hne⟩]

open Classical in
noncomputable def essential {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (o : ℕ) :
    Finset (Fin M) := Finset.univ.filter (Depends n P gs o)

lemma essential_card {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (essential (M := M) n P gs o).card ≤ unpaid n P gs + 1 := by
  classical
  obtain ⟨label, wire, hc, hd⟩ := components n P (essential (M := M) n P gs o) gs hg
  have hsmall : ((essential (M := M) n P gs o).image label).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
    exact (hd o u (Finset.mem_filter.mp hu).2).trans
      (hd o v (Finset.mem_filter.mp hv).2).symm
  omega


lemma source_congr {M : ℕ} (x y : Fin M → Bool) (i : ℕ)
    (hxy : ∀ t : Fin M, t.val = i → x t = y t) : source x i = source y i := by
  rw [source_eq, source_eq]
  split_ifs with hi
  · exact hxy ⟨i, hi⟩ rfl
  · rfl

lemma cutVal_congr {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate)
    (x y : Fin M → Bool) (hxy : ∀ t, t.val < n ∨ t.val ∈ P → x t = y t) :
    ∀ i, cutVal n P gs x i = cutVal n P gs y i := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    rw [cutVal_nil, cutVal_nil]
    split_ifs with hi
    · exact source_congr x y i (fun t ht => hxy t (Or.inl (by omega)))
    · rfl
  | append_singleton gs g ih =>
    intro i
    rw [cutVal_snoc, cutVal_snoc]
    split_ifs with hi hp
    · exact source_congr x y i (fun t ht => hxy t (Or.inr (ht ▸ hp)))
    · congr 1
      exact List.map_congr_left (fun j _ => ih j)
    · exact ih i

lemma essential_sources {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (o : ℕ)
    (t : Fin M) (ht : t ∈ essential n P gs o) : t.val < n ∨ t.val ∈ P := by
  classical
  obtain ⟨x, y, hxy, hne⟩ := (Finset.mem_filter.mp ht).2
  by_contra hn
  apply hne
  apply cutVal_congr
  intro u hu
  apply hxy u
  intro he
  subst u
  exact hn hu

lemma essential_supports {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (o : ℕ)
    (x y : Fin M → Bool) (hxy : ∀ t ∈ essential n P gs o, x t = y t) :
    cutVal n P gs x o = cutVal n P gs y o := by
  classical
  have key : ∀ S : Finset (Fin M), (∀ t ∈ S, ¬ Depends n P gs o t) →
      ∀ x y : Fin M → Bool, (∀ t, t ∉ S → x t = y t) →
        cutVal n P gs x o = cutVal n P gs y o := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ x y h
      have he : x = y := funext (fun t => h t (by simp))
      rw [he]
    | @insert a S ha ih =>
      intro hS x y h
      let z : Fin M → Bool := Function.update x a (y a)
      have hfirst : cutVal n P gs x o = cutVal n P gs z o := by
        by_contra hne
        apply hS a (Finset.mem_insert_self a S)
        refine ⟨x, z, ?_, hne⟩
        intro j hj
        simp [z, Function.update_of_ne hj]
      have hnext : cutVal n P gs z o = cutVal n P gs y o := by
        apply ih (fun t ht => hS t (Finset.mem_insert_of_mem ht)) z y
        intro j hj
        by_cases he : j = a
        · subst j
          simp [z]
        · rw [show z j = x j by simp [z, Function.update_of_ne he]]
          exact h j (by simp [he, hj])
      exact hfirst.trans hnext
  apply key (Finset.univ \ essential n P gs o)
  · intro t ht
    have hn := (Finset.mem_sdiff.mp ht).2
    simpa [essential] using hn
  · intro t ht
    apply hxy t
    simpa using ht

lemma source_mono {M : ℕ} (x y : Fin M → Bool) (hxy : ∀ t, x t = true → y t = true)
    (i : ℕ) (hi : source x i = true) : source y i = true := by
  rw [source_eq] at hi ⊢
  split_ifs at hi ⊢ with h
  · exact hxy ⟨i, h⟩ hi

lemma gate_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (f h : ℕ → Bool) (hfh : ∀ i, f i = true → h i = true)
    (hf : g.op.eval (g.inputs.map f) = true) : g.op.eval (g.inputs.map h) = true := by
  rcases hop with hop | hop
  · rw [hop] at hf ⊢
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hf ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact hfh i (hf _ ⟨i, hi, rfl⟩)
  · rw [hop] at hf ⊢
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hf ⊢
    obtain ⟨b, ⟨i, hi, rfl⟩, hf⟩ := hf
    exact ⟨h i, ⟨i, hi, rfl⟩, hfh i hf⟩

lemma cutVal_mono {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin M → Bool) (hxy : ∀ t, x t = true → y t = true) :
    ∀ i, cutVal n P gs x i = true → cutVal n P gs y i = true := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi
    rw [cutVal_nil] at hi ⊢
    split_ifs at hi ⊢ with h
    · exact source_mono x y hxy i hi
  | append_singleton gs g ih =>
    have hprev := ih (fun g' hg' => hg g' (by simp [hg']))
    intro i hi
    rw [cutVal_snoc] at hi ⊢
    split_ifs at hi ⊢ with he hp
    · exact source_mono x y hxy i hi
    · exact gate_mono g (hg g (by simp)) _ _ hprev hi
    · exact hprev i hi

lemma essential_bound {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hP : P ⊆ Finset.Ico n (n + gs.length)) :
    (essential (M := M) n P gs o).card ≤ gs.length - P.card + 1 := by
  rw [← unpaid_eq_sub n P gs hP]
  exact essential_card n P gs o hg


lemma cut_empty {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) :
    cutVal n ∅ gs x i = Circuit.eval ⟨gs, i⟩ (List.ofFn x) := by
  have he : (fun j : Fin n => source x j.val) = x := by
    funext j
    simp [source_eq]
  unfold cutVal cutRun
  simp only [cutStep, Finset.notMem_empty, ite_false, he]
  rfl

lemma cutVal_factor {M n : ℕ} (P : Finset ℕ) (gs : List Gate)
    (x : Fin n → Bool) (y : Fin M → Bool)
    (hsrc : ∀ i, i < n + gs.length → source y i = cutVal n ∅ gs x i) :
    ∀ i, cutVal n P gs y i = cutVal n ∅ gs x i := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    rw [cutVal_nil, cutVal_nil]
    by_cases hi : i < n
    · simpa [cutVal_nil, hi] using hsrc i (by simpa using hi)
    · simp [hi]
  | append_singleton gs g ih =>
    have hprevsrc : ∀ i, i < n + gs.length → source y i = cutVal n ∅ gs x i := by
      intro i hi
      have h := hsrc i (by simp; omega)
      rw [cutVal_snoc, ite_eq_right (show i ≠ n + gs.length by omega)] at h
      exact h
    have hprev := ih hprevsrc
    intro i
    rw [cutVal_snoc, cutVal_snoc]
    by_cases hi : i = n + gs.length
    · simp only [hi, ite_true, Finset.notMem_empty, ite_false]
      by_cases hp : n + gs.length ∈ P
      · rw [ite_eq_left hp]
        have h := hsrc (n + gs.length) (by simp)
        rw [cutVal_snoc, ite_eq_left rfl] at h
        simpa using h
      · rw [ite_eq_right hp]
        congr 1
        exact List.map_congr_left (fun j _ => hprev j)
    · simp only [hi, ite_false]
      exact hprev i

def actualSources {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    Fin (n + gs.length) → Bool :=
  fun t => Circuit.eval ⟨gs, t.val⟩ (List.ofFn x)

lemma source_actual {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : i < n + gs.length) :
    source (actualSources gs x) i = Circuit.eval ⟨gs, i⟩ (List.ofFn x) := by
  simp [source_eq, hi, actualSources]

lemma factor {n : ℕ} (P : Finset ℕ) (gs : List Gate) (x : Fin n → Bool) (i : ℕ) :
    cutVal n P gs (actualSources gs x) i = Circuit.eval ⟨gs, i⟩ (List.ofFn x) := by
  apply (cutVal_factor P gs x (actualSources gs x) ?_ i).trans (cut_empty gs x i)
  intro j hj
  rw [source_actual gs x j hj, cut_empty]

lemma actualSources_mono {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ t, x t = true → y t = true)
    (i : Fin (n + gs.length)) (hi : actualSources gs x i = true) :
    actualSources gs y i = true := by
  unfold actualSources at hi ⊢
  rw [← cut_empty] at hi ⊢
  exact cutVal_mono n ∅ gs hg x y hxy i.val hi

end PEqualNP.Outside.L_meta_1024_aux.Cut

namespace PEqualNP.Outside.L_meta_1024_aux.Bridge

open PEqualNP.CircuitLowerBounds

lemma one_exotic_bound (gs : List Gate) (out : Fin 13 → ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (a : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out a⟩ (List.ofFn x) = Support.target a x)
    (hordinary : ∀ a : Fin 13, a ≠ w → ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out a⟩ (List.ofFn x) = decide (∃ p ∈ Global.line a, x p = true)) :
    39 ≤ gs.length := by
  classical
  by_contra! hsmall
  obtain ⟨P, hP, hPcard, hPoutside⟩ := Charges.twelve_ordinary_charges gs out w hg hordinary
  let F : (Fin (13 + gs.length) → Bool) → Bool := fun x => Cut.cutVal 13 P gs x (out w)
  let E := Cut.essential (M := 13 + gs.length) 13 P gs (out w)
  apply cut_contradiction gs (out w) w hg (hcorrect w) hsmall P hP hPcard hPoutside F E
  · exact Cut.essential_bound 13 P gs (out w) (fun g hm => (hg g hm).2) hP
  · exact Cut.essential_sources 13 P gs (out w)
  · intro a b hab ha
    exact Cut.cutVal_mono 13 P gs (fun g hm => (hg g hm).1) a b hab (out w) ha
  · exact Cut.essential_supports 13 P gs (out w)
  · intro x
    exact Cut.factor P gs x (out w)

end PEqualNP.Outside.L_meta_1024_aux.Bridge

namespace PEqualNP.Outside.L_meta_1024_aux.Charges

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1024_aux.Global

lemma ordinary_charge_family (gs : List Gate) (out : Fin 13 → ℕ) (W : Finset (Fin 13))
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hordinary : ∀ a ∈ W, ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out a⟩ (List.ofFn x) = decide (∃ p ∈ line a, x p = true)) :
    ∃ P : Finset ℕ, P ⊆ Finset.Ico 13 (13 + gs.length) ∧ 3 * W.card ≤ P.card ∧
      ∀ w ∉ W, ∀ i ∈ P, ∃ q : Fin 13, q ∉ line w ∧ val gs (eof q) i = true := by
  classical
  let P := W.biUnion (fun a => D (line a) gs)
  have hsubset : P ⊆ Finset.Ico 13 (13 + gs.length) := by
    intro i hi
    obtain ⟨a, _, hai⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hai).1
  have hcount : 3 * W.card ≤ P.card := by
    have hd : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → Disjoint (D (line a) gs) (D (line b) gs) := by
      intro a _ b _ hab
      exact disjoint_charges gs hg a b hab
    have hsum : (∑ _a ∈ W, (3 : ℕ)) ≤ ∑ a ∈ W, (D (line a) gs).card := by
      apply Finset.sum_le_sum
      intro a ha
      exact ordinary_charge_count gs (out a) a hg (hordinary a ha)
    rw [← Finset.card_biUnion hd] at hsum
    simpa [P, Nat.mul_comm] using hsum
  refine ⟨P, hsubset, hcount, ?_⟩
  intro w hw i hi
  obtain ⟨a, ha, hai⟩ := Finset.mem_biUnion.mp hi
  have hne : a ≠ w := fun he => hw (he ▸ ha)
  exact charge_outside gs hg w a hne i hai

end PEqualNP.Outside.L_meta_1024_aux.Charges

namespace PEqualNP.Outside.L_meta_1024_aux.Bridge

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma pair_geometry : ∀ a b : Fin 13, a ≠ b →
    (Global.line a ∪ Global.line b).card = 7 ∧
      ∃ p : Fin 13, p ∈ Global.line a ∧ p ∈ Global.line b := by
  decide +kernel

lemma two_exotic_bound (gs : List Gate) (out : Fin 13 → ℕ)
    (a b : Fin 13) (hab : a ≠ b)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hordinary : ∀ w : Fin 13, w ≠ a → w ≠ b → ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = decide (∃ p ∈ Global.line w, x p = true)) :
    39 ≤ gs.length := by
  classical
  by_contra! hsmall
  let W : Finset (Fin 13) := (Finset.univ.erase a).erase b
  have hW : W.card = 11 := by simp [W, hab, Ne.symm hab]
  have hord : ∀ w ∈ W, ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = decide (∃ p ∈ Global.line w, x p = true) := by
    intro w hw
    have hwb : w ≠ b := (Finset.mem_erase.mp hw).1
    have hwa : w ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1
    exact hordinary w hwa hwb
  obtain ⟨P, hP, hPcard, hPoutside⟩ := Charges.ordinary_charge_family gs out W hg hord
  have hP33 : 33 ≤ P.card := by simpa [hW] using hPcard
  have hPupper : P.card ≤ gs.length := by simpa using Finset.card_le_card hP
  have hbudget : Cut.unpaid 13 P gs ≤ 5 := by
    rw [Cut.unpaid_eq_sub 13 P gs hP]
    omega
  let E (w : Fin 13) := Cut.essential (M := 13 + gs.length) 13 P gs (out w)
  have hraw (w : Fin 13) (hw : w = a ∨ w = b) (p : Fin 13) (hp : p ∈ Global.line w) :
      rawIndex gs p ∈ E w := by
    have hnot : w ∉ W := by rcases hw with rfl | rfl <;> simp [W]
    apply raw_line_members gs (out w) w (fun g hm => (hg g hm).1) (hcorrect w) P
      (hPoutside w hnot) (fun x => Cut.cutVal 13 P gs x (out w)) (E w)
    · have hh := Cut.essential_card (M := 13 + gs.length) 13 P gs (out w)
        (fun g hm => (hg g hm).2)
      change (E w).card ≤ _ at hh
      omega
    · exact Cut.essential_sources 13 P gs (out w)
    · intro x y hxy hx
      exact Cut.cutVal_mono 13 P gs (fun g hm => (hg g hm).1) x y hxy (out w) hx
    · exact Cut.essential_supports 13 P gs (out w)
    · intro x
      exact Cut.factor P gs x (out w)
    · exact hp
  let S := (Global.line a ∪ Global.line b).image (rawIndex gs)
  have hinj : Function.Injective (rawIndex gs) := by
    intro p q hpq
    apply Fin.ext
    exact congrArg (fun t : Fin (13 + gs.length) => t.val) hpq
  have hS : S.card = 7 := by
    rw [Finset.card_image_of_injective _ hinj]
    exact (pair_geometry a b hab).1
  obtain ⟨label, wire, hc, hd⟩ := Cut.components 13 P S gs (fun g hm => (hg g hm).2)
  have hl (w : Fin 13) (hw : w = a ∨ w = b) (p : Fin 13) (hp : p ∈ Global.line w) :
      label (rawIndex gs p) = wire (out w) := by
    exact hd (out w) (rawIndex gs p) (Finset.mem_filter.mp (hraw w hw p hp)).2
  obtain ⟨p, hpa, hpb⟩ := (pair_geometry a b hab).2
  have hwire : wire (out a) = wire (out b) :=
    (hl a (Or.inl rfl) p hpa).symm.trans (hl b (Or.inr rfl) p hpb)
  have himg : S.image label ⊆ {wire (out a)} := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hi
    apply Finset.mem_singleton.mpr
    rcases Finset.mem_union.mp hq with hqa | hqb
    · exact hl a (Or.inl rfl) q hqa
    · exact (hl b (Or.inr rfl) q hqb).trans hwire.symm
  have hcard : (S.image label).card ≤ 1 := by
    simpa using Finset.card_le_card himg
  rw [hS] at hc
  omega

end PEqualNP.Outside.L_meta_1024_aux.Bridge

namespace PEqualNP.Outside.L_meta_1024_aux.Clamp9

set_option maxHeartbeats 2000000 in
lemma positive_frontier_impossible {m : ℕ} (w : Fin 13)
    (E : Finset (Fin m)) (F : (Fin m → Bool) → Bool)
    (leaf : Fin m → (Fin 13 → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hleaf : ∀ i ∈ E, ∀ x y, (∀ q, x q = true → y q = true) →
      leaf i x = true → leaf i y = true)
    (hcorrect : ∀ x, Support.Band x → F (fun i => leaf i x) = Support.target w x)
    (x : Fin 13 → Bool) (hx : Support.Band x) (hpos : Support.target w x = true)
    (hcount : (E.filter (fun i => leaf i x = true)).card ≤ 8)
    (hforeign : ∀ i ∈ E, leaf i x = true →
      ∃ q : Fin 13, q ∉ Support.line w ∧ leaf i (Clamp.singleton q) = true) : False := by
  classical
  let T := E.filter (fun i => leaf i x = true)
  let q : Fin m → Fin 13 := fun i => if h : i ∈ T then
    Classical.choose (hforeign i (Finset.mem_filter.mp h).1 (Finset.mem_filter.mp h).2) else 0
  have q_spec (i : Fin m) (hi : i ∈ T) :
      q i ∉ Support.line w ∧ leaf i (Clamp.singleton (q i)) = true := by
    simpa only [q, dite_eq_left hi] using Classical.choose_spec
      (hforeign i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2)
  let Q := T.image q
  have hQcard : Q.card ≤ 8 := Finset.card_image_le.trans hcount
  have hQ : Q ⊆ Finset.univ \ Support.line w := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (q_spec i hi).1⟩
  obtain ⟨Y, hQY, hY, hYcard⟩ := Clamp.extend_eight w Q hQ hQcard
  have hptrue : F (fun i => leaf i x) = true := (hcorrect x hx).trans hpos
  have hyfalse : F (fun i => leaf i (Clamp.fromTrue Y)) = false :=
    (hcorrect _ (Clamp.fromTrue_band Y hYcard)).trans (Clamp.fromTrue_misses w Y hY)
  have hcompare : ∀ i ∈ E, leaf i x = true → leaf i (Clamp.fromTrue Y) = true := by
    intro i hi hix
    have hiT : i ∈ T := Finset.mem_filter.mpr ⟨hi, hix⟩
    have hqi : q i ∈ Y := hQY (Finset.mem_image.mpr ⟨i, hiT, rfl⟩)
    apply hleaf i hi (Clamp.singleton (q i)) (Clamp.fromTrue Y) _ (q_spec i hiT).2
    intro r hr
    have he : r = q i := by simpa [Clamp.singleton] using hr
    subst r
    simp [Clamp.fromTrue, hqi]
  have hytrue := Clamp.supported_mono F E hmono hsupport _ _ hcompare hptrue
  rw [hyfalse] at hytrue
  exact Bool.noConfusion hytrue

set_option maxHeartbeats 2000000 in
lemma missing_raw_impossible {m : ℕ} (w p : Fin 13) (hp : p ∈ Support.line w)
    (E : Finset (Fin m)) (hE : E.card ≤ 9) (F : (Fin m → Bool) → Bool)
    (leaf : Fin m → (Fin 13 → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hleaf : ∀ i ∈ E, ∀ x y, (∀ q, x q = true → y q = true) →
      leaf i x = true → leaf i y = true)
    (hcorrect : ∀ x, Support.Band x → F (fun i => leaf i x) = Support.target w x)
    (hclass : ∀ i ∈ E,
      (∃ q ∈ Support.line w, q ≠ p ∧ ∀ x, leaf i x = x q) ∨
      ∃ q : Fin 13, q ∉ Support.line w ∧ leaf i (Clamp.singleton q) = true)
    (hnotabove : ∀ i ∈ E, ∃ x : Fin 13 → Bool,
      Support.Band x ∧ Support.target w x = true ∧ leaf i x = false) : False := by
  classical
  let x := Support.flip w p
  have hx : Support.Band x := Or.inl (Support.flip_spec w p hp).1
  have hxpos : Support.target w x = true := (Support.flip_spec w p hp).2
  have hforeign (i : Fin m) (hi : i ∈ E) (hit : leaf i x = true) :
      ∃ q : Fin 13, q ∉ Support.line w ∧ leaf i (Clamp.singleton q) = true := by
    rcases hclass i hi with ⟨q, hq, hqp, hraw⟩ | hforeign
    · have hfalse : leaf i x = false := by
        rw [hraw]
        exact (ite_eq_right hqp).trans (Clamp.row_line_false w q hq)
      rw [hfalse] at hit
      exact Bool.noConfusion hit
    · exact hforeign
  let T := E.filter (fun i => leaf i x = true)
  by_cases hT : T.card ≤ 8
  · exact positive_frontier_impossible w E F leaf hmono hsupport hleaf hcorrect x hx hxpos hT hforeign
  have hTE : T = E := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have hE9 : E.card = 9 := by rw [hTE] at hT; omega
  have hEpos : E.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi⟩ := hEpos
  obtain ⟨y, hy, hypos, hiy⟩ := hnotabove i hi
  have hforeignall (j : Fin m) (hj : j ∈ E) :
      ∃ q : Fin 13, q ∉ Support.line w ∧ leaf j (Clamp.singleton q) = true := by
    apply hforeign j hj
    have hjT : j ∈ T := hTE.symm ▸ hj
    exact (Finset.mem_filter.mp hjT).2
  have hcount : (E.filter (fun j => leaf j y = true)).card ≤ 8 := by
    have hs : E.filter (fun j => leaf j y = true) ⊆ E.erase i := by
      intro j hj
      obtain ⟨hjE, hjtrue⟩ := Finset.mem_filter.mp hj
      apply Finset.mem_erase.mpr
      refine ⟨?_, hjE⟩
      intro he
      subst j
      rw [hiy] at hjtrue
      exact Bool.noConfusion hjtrue
    have hh := Finset.card_le_card hs
    rw [Finset.card_erase_of_mem hi, hE9] at hh
    exact hh
  exact positive_frontier_impossible w E F leaf hmono hsupport hleaf hcorrect y hy hypos hcount
    (fun j hj _ => hforeignall j hj)

end PEqualNP.Outside.L_meta_1024_aux.Clamp9

namespace PEqualNP.Outside.L_meta_1024_aux.Charges

open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma line_difference : ∀ w a : Fin 13, a ≠ w →
    ∃ p ∈ Global.line w, p ∉ Global.line a := by decide +kernel

lemma charge_not_above (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w a : Fin 13) (hwa : a ≠ w) (i : ℕ) (hi : i ∈ Global.D (Global.line a) gs) :
    ∃ x : Fin 13 → Bool, Support.Band x ∧ Support.target w x = true ∧
      Global.val gs x i = false := by
  classical
  obtain ⟨p, hpw, hpa⟩ := line_difference w a hwa
  have hsub : ({p} : Finset (Fin 13)) ⊆ Finset.univ \ Support.line a := by
    intro q hq
    have he : q = p := Finset.mem_singleton.mp hq
    subst q
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpa⟩
  obtain ⟨Y, hpY, hY, hYcard⟩ := Clamp.extend_eight a {p} hsub (by simp)
  refine ⟨Clamp.fromTrue Y, Clamp.fromTrue_band Y hYcard, ?_, ?_⟩
  · apply decide_eq_true_iff.mpr
    exact ⟨p, hpw, by simp [Clamp.fromTrue, hpY (Finset.mem_singleton_self p)]⟩
  · have hz : Global.val gs (Global.Zof (Global.line a)) i = false :=
      (Finset.mem_filter.mp hi).2.1
    cases he : Global.val gs (Clamp.fromTrue Y) i
    · rfl
    · have ht := Bridge.val_mono gs hg (Clamp.fromTrue Y) (Global.Zof (Global.line a))
        (by
          intro q hq
          have hqY : q ∈ Y := by simpa [Clamp.fromTrue] using hq
          simpa [Global.Zof, Global.line, Support.line] using (Finset.mem_sdiff.mp (hY hqY)).2) i he
      rw [hz] at ht
      exact Bool.noConfusion ht

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma raw_not_above : ∀ w q : Fin 13, ∃ r : Fin 13,
    Support.target w (Support.row r) = true ∧ Support.row r q = false := by
  decide +kernel

end PEqualNP.Outside.L_meta_1024_aux.Charges

namespace PEqualNP.Outside.L_meta_1024_aux.Charges
open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_1024_aux.Global
lemma ordinary_charge_family_strong (gs : List Gate) (out : Fin 13 → ℕ) (W : Finset (Fin 13))
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hordinary : ∀ a ∈ W, ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out a⟩ (List.ofFn x) = decide (∃ p ∈ Global.line a, x p = true)) :
    ∃ P : Finset ℕ, P ⊆ Finset.Ico 13 (13 + gs.length) ∧ 3 * W.card ≤ P.card ∧
      ∀ w ∉ W, ∀ i ∈ P, (∃ q : Fin 13, q ∉ Global.line w ∧ val gs (eof q) i = true) ∧
      (∃ x : Fin 13 → Bool, Support.Band x ∧ Support.target w x = true ∧ val gs x i = false) := by
  classical
  let P := W.biUnion (fun a => D (Global.line a) gs)
  have hsubset : P ⊆ Finset.Ico 13 (13 + gs.length) := by
    intro i hi
    obtain ⟨a, _, hai⟩ := Finset.mem_biUnion.mp hi
    exact (Finset.mem_filter.mp hai).1
  have hcount : 3 * W.card ≤ P.card := by
    have hd : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → Disjoint (D (Global.line a) gs) (D (Global.line b) gs) := by
      intro a _ b _ hab
      exact disjoint_charges gs hg a b hab
    have hsum : (∑ _a ∈ W, (3 : ℕ)) ≤ ∑ a ∈ W, (D (Global.line a) gs).card := by
      apply Finset.sum_le_sum
      intro a ha
      exact ordinary_charge_count gs (out a) a hg (hordinary a ha)
    rw [← Finset.card_biUnion hd] at hsum
    simpa [P, Nat.mul_comm] using hsum
  refine ⟨P, hsubset, hcount, ?_⟩
  intro w hw i hi
  obtain ⟨a, ha, hai⟩ := Finset.mem_biUnion.mp hi
  have hne : a ≠ w := fun he => hw (he ▸ ha)
  exact ⟨charge_outside gs hg w a hne i hai,
    charge_not_above gs (fun g hm => (hg g hm).1) w a hne i hai⟩

end PEqualNP.Outside.L_meta_1024_aux.Charges

namespace PEqualNP.Outside.L_meta_1024_aux.Bridge
open PEqualNP.CircuitLowerBounds
lemma raw_line_members9 (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      Global.val gs x o = Support.target w x)
    (P : Finset ℕ)
    (hPoutside : ∀ i ∈ P, ∃ q : Fin 13,
      q ∉ Global.line w ∧ Global.val gs (Global.eof q) i = true)
    (hPnotabove : ∀ i ∈ P, ∃ x : Fin 13 → Bool, Support.Band x ∧
      Support.target w x = true ∧ Global.val gs x i = false)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (E : Finset (Fin (13 + gs.length))) (hEcard : E.card ≤ 9)
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hfactor : ∀ x : Fin 13 → Bool, F (fun i => Global.val gs x i.val) = Global.val gs x o)
    (p : Fin 13) (hp : p ∈ Global.line w) : rawIndex gs p ∈ E := by
  classical
  by_contra hpnot
  apply Clamp9.missing_raw_impossible w p hp E hEcard F
    (fun i x => Global.val gs x i.val) hmono hsupport
  · intro i _ x y hxy hx
    exact val_mono gs hg x y hxy i.val hx
  · intro x hx
    rw [hfactor]
    exact hcorrect x hx
  · intro i hi
    rcases hallowed i hi with hiraw | hipaid
    · let q : Fin 13 := ⟨i.val, hiraw⟩
      have hraw : ∀ x : Fin 13 → Bool, Global.val gs x i.val = x q := fun x => val_input gs x q
      by_cases hql : q ∈ Global.line w
      · left
        refine ⟨q, hql, ?_, hraw⟩
        intro hqp
        have hie : i = rawIndex gs p := by
          apply Fin.ext
          exact congrArg (fun t : Fin 13 => t.val) hqp
        exact hpnot (hie ▸ hi)
      · right
        refine ⟨q, hql, ?_⟩
        rw [hraw]
        simp [Clamp.singleton]
    · obtain ⟨q, hq, hqtrue⟩ := hPoutside i.val hipaid
      exact Or.inr ⟨q, hq, hqtrue⟩
  · intro i hi
    rcases hallowed i hi with hiraw | hipaid
    · let q : Fin 13 := ⟨i.val, hiraw⟩
      obtain ⟨r, hrt, hrq⟩ := Charges.raw_not_above w q
      refine ⟨Support.row r, Or.inr (Support.row_spec r).1, hrt, ?_⟩
      exact (val_input gs (Support.row r) q).trans hrq
    · exact hPnotabove i.val hipaid

lemma output_index (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      Global.val gs x o = Support.target w x) : 13 ≤ o ∧ o < 13 + gs.length := by
  constructor
  · by_contra! ho
    let q : Fin 13 := ⟨o, ho⟩
    obtain ⟨r, hrt, hrq⟩ := Charges.raw_not_above w q
    have hval := hcorrect (Support.row r) (Or.inr (Support.row_spec r).1)
    have hi : Global.val gs (Support.row r) o = false :=
      (val_input gs (Support.row r) q).trans hrq
    rw [hi, hrt] at hval
    exact Bool.noConfusion hval
  · by_contra! ho
    have hne : (Global.line w).Nonempty := Finset.card_pos.mp (by rw [Global.line_card]; decide)
    obtain ⟨p, hp⟩ := hne
    have hv : Global.val gs (Support.flip w p) o = false := by
      unfold Global.val
      apply List.getD_eq_default
      rw [Global.fold_length, List.length_ofFn]
      exact ho
    have hh := hcorrect (Support.flip w p) (Or.inl (Support.flip_spec w p hp).1)
    rw [hv, (Support.flip_spec w p hp).2] at hh
    exact Bool.noConfusion hh

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma row_targets : ∀ a b : Fin 13, a ≠ b → Support.target b (Support.row a) = true := by
  decide +kernel

lemma output_distinct (gs : List Gate) (out : Fin 13 → ℕ)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out w) = Support.target w x) : Function.Injective out := by
  intro a b hab
  by_contra hne
  have ha := hcorrect a (Support.row a) (Or.inr (Support.row_spec a).1)
  have hb := hcorrect b (Support.row a) (Or.inr (Support.row_spec a).1)
  rw [hab, hb, (Support.row_spec a).2, row_targets a b hne] at ha
  exact Bool.noConfusion ha

end PEqualNP.Outside.L_meta_1024_aux.Bridge

namespace PEqualNP.Outside.L_meta_1024_aux.Cut
open PEqualNP.CircuitLowerBounds

lemma cutVal_append_old {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs hs : List Gate)
    (x : Fin M → Bool) (i : ℕ) (hi : i < n + gs.length) :
    cutVal n P (gs ++ hs) x i = cutVal n P gs x i := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, cutVal_snoc,
      ite_eq_right (show i ≠ n + (gs ++ hs).length by simp; omega)]
    exact ih

lemma cutVal_take {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate)
    (x : Fin M → Bool) (k i : ℕ) (hk : k ≤ gs.length) (hi : i < n + k) :
    cutVal n P gs x i = cutVal n P (gs.take k) x i := by
  have hlen : (gs.take k).length = k := by simp [List.length_take, Nat.min_eq_left hk]
  have h := cutVal_append_old n P (gs.take k) (gs.drop k) x i (by rw [hlen]; exact hi)
  simpa only [List.take_append_drop] using h

lemma essential_take {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate)
    (k i : ℕ) (hk : k ≤ gs.length) (hi : i < n + k) :
    essential (M := M) n P gs i = essential n P (gs.take k) i := by
  classical
  ext t
  simp only [essential, Finset.mem_filter, Finset.mem_univ, true_and, Depends]
  constructor
  · rintro ⟨x, y, hxy, hne⟩
    refine ⟨x, y, hxy, ?_⟩
    rwa [cutVal_take n P gs x k i hk hi, cutVal_take n P gs y k i hk hi] at hne
  · rintro ⟨x, y, hxy, hne⟩
    refine ⟨x, y, hxy, ?_⟩
    rwa [cutVal_take n P gs x k i hk hi, cutVal_take n P gs y k i hk hi]

lemma unpaid_two_later (n : ℕ) (P : Finset ℕ) (gs : List Gate) (k i j : ℕ)
    (hk : k ≤ gs.length) (hi : n + k ≤ i) (hj : n + k ≤ j)
    (hiend : i < n + gs.length) (hjend : j < n + gs.length)
    (hip : i ∉ P) (hjp : j ∉ P) (hij : i ≠ j) :
    unpaid n P (gs.take k) + 2 ≤ unpaid n P gs := by
  classical
  let D := (Finset.Ico n (n + (gs.take k).length)) \ P
  let F := (Finset.Ico n (n + gs.length)) \ P
  have hlen : (gs.take k).length = k := by simp [List.length_take, Nat.min_eq_left hk]
  have hD : D ⊆ F := by
    intro a ha
    simp only [D, F, Finset.mem_sdiff, Finset.mem_Ico] at ha ⊢
    exact ⟨⟨ha.1.1, by rw [hlen] at ha; omega⟩, ha.2⟩
  have hiD : i ∉ D := by
    simp only [D, Finset.mem_sdiff, Finset.mem_Ico, hlen]
    omega
  have hjD : j ∉ D := by
    simp only [D, Finset.mem_sdiff, Finset.mem_Ico, hlen]
    omega
  have hiF : i ∈ F := by
    simp only [F, Finset.mem_sdiff, Finset.mem_Ico]
    exact ⟨⟨by omega, hiend⟩, hip⟩
  have hjF : j ∈ F := by
    simp only [F, Finset.mem_sdiff, Finset.mem_Ico]
    exact ⟨⟨by omega, hjend⟩, hjp⟩
  have hsub : insert i (insert j D) ⊆ F :=
    Finset.insert_subset_iff.mpr ⟨hiF, Finset.insert_subset_iff.mpr ⟨hjF, hD⟩⟩
  have hc := Finset.card_le_card hsub
  have hnot : i ∉ insert j D := by simp [hij, hiD]
  rw [Finset.card_insert_of_notMem hnot, Finset.card_insert_of_notMem hjD] at hc
  change D.card + 2 ≤ F.card
  omega

def rawSupport {M n : ℕ} (E : Finset (Fin M)) (hraw : ∀ t ∈ E, t.val < n) :
    Finset (Fin n) :=
  E.attach.image fun t => (⟨t.val.val, hraw t.val t.property⟩ : Fin n)

lemma rawSupport_card {M n : ℕ} (E : Finset (Fin M)) (hraw : ∀ t ∈ E, t.val < n) :
    (rawSupport E hraw).card ≤ E.card := by
  exact (Finset.card_image_le).trans_eq Finset.card_attach

lemma actualSources_raw {n : ℕ} (gs : List Gate) (x : Fin n → Bool)
    (t : Fin (n + gs.length)) (ht : t.val < n) :
    actualSources gs x t = x ⟨t.val, ht⟩ := by
  unfold actualSources
  rw [← cut_empty]
  have h := cutVal_append_old n ∅ [] gs x t.val (by simpa using ht)
  simp only [List.nil_append] at h
  rw [h, cutVal_nil]
  simp [ht, source_eq]

lemma raw_essential_support {n : ℕ} (P : Finset ℕ) (gs : List Gate) (o : ℕ)
    (hraw : ∀ t ∈ essential (M := n + gs.length) n P gs o, t.val < n) :
    ∀ x y : Fin n → Bool,
      (∀ p ∈ rawSupport (essential n P gs o) hraw, x p = y p) →
      Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Circuit.eval ⟨gs, o⟩ (List.ofFn y) := by
  intro x y hxy
  rw [← factor P gs x o, ← factor P gs y o]
  apply essential_supports n P gs o
  intro t ht
  rw [actualSources_raw gs x t (hraw t ht), actualSources_raw gs y t (hraw t ht)]
  apply hxy
  exact Finset.mem_image.mpr ⟨⟨t, ht⟩, by simp, rfl⟩

lemma raw_support_exists {n : ℕ} (P : Finset ℕ) (gs : List Gate) (o b : ℕ)
    (hraw : ∀ t ∈ essential (M := n + gs.length) n P gs o, t.val < n)
    (hcard : (essential (M := n + gs.length) n P gs o).card ≤ b) :
    ∃ S : Finset (Fin n), S.card ≤ b ∧
      ∀ x y : Fin n → Bool, (∀ p ∈ S, x p = y p) →
        Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Circuit.eval ⟨gs, o⟩ (List.ofFn y) := by
  exact ⟨rawSupport (essential n P gs o) hraw,
    (rawSupport_card _ hraw).trans hcard, raw_essential_support P gs o hraw⟩

end PEqualNP.Outside.L_meta_1024_aux.Cut

namespace PEqualNP.Outside.L_meta_1024_aux.Bridge
open PEqualNP.CircuitLowerBounds

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma triple_geometry : ∀ a b c : Fin 13, a ≠ b → a ≠ c → b ≠ c →
    9 ≤ ((Global.line a ∪ Global.line b) ∪ Global.line c).card := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma three_exotic_core (gs : List Gate) (out : Fin 13 → ℕ)
    (a b c : Fin 13) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hordinary : ∀ w : Fin 13, w ≠ a → w ≠ b → w ≠ c → ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hnona : ¬ ∀ x : Fin 13 → Bool, Circuit.eval ⟨gs, out a⟩ (List.ofFn x) = Support.target a x)
    (hminb : out a ≤ out b) (hminc : out a ≤ out c) : 39 ≤ gs.length := by
  classical
  by_contra! hsmall
  let T : Finset (Fin 13) := {a, b, c}
  let W : Finset (Fin 13) := Finset.univ \ T
  have hT : T.card = 3 := by simp [T, hab, hac, hbc]
  have hW : W.card = 10 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hT]
    decide
  have hord : ∀ w ∈ W, ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = decide (∃ p ∈ Global.line w, x p = true) := by
    intro w hw
    have hnt := (Finset.mem_sdiff.mp hw).2
    have hwa : w ≠ a := fun h => hnt (by simp [T, h])
    have hwb : w ≠ b := fun h => hnt (by simp [T, h])
    have hwc : w ≠ c := fun h => hnt (by simp [T, h])
    exact hordinary w hwa hwb hwc
  obtain ⟨P, hP, hPcard, hPprops⟩ := Charges.ordinary_charge_family_strong gs out W hg hord
  have hP30 : 30 ≤ P.card := by simpa [hW] using hPcard
  have hPupper : P.card ≤ gs.length := by simpa using Finset.card_le_card hP
  have hbudget : Cut.unpaid 13 P gs ≤ 8 := by
    rw [Cut.unpaid_eq_sub 13 P gs hP]
    omega
  have hnotW (w : Fin 13) (hw : w ∈ T) : w ∉ W := by
    intro hh
    exact (Finset.mem_sdiff.mp hh).2 hw
  let E (w : Fin 13) := Cut.essential (M := 13 + gs.length) 13 P gs (out w)
  have hraw (w : Fin 13) (hw : w ∈ T) (p : Fin 13) (hp : p ∈ Global.line w) :
      rawIndex gs p ∈ E w := by
    apply raw_line_members9 gs (out w) w (fun g hm => (hg g hm).1) (hcorrect w) P
      (fun i hi => (hPprops w (hnotW w hw) i hi).1)
      (fun i hi => (hPprops w (hnotW w hw) i hi).2)
      (fun x => Cut.cutVal 13 P gs x (out w)) (E w)
    · have hh := Cut.essential_card (M := 13 + gs.length) 13 P gs (out w)
        (fun g hm => (hg g hm).2)
      change (E w).card ≤ _ at hh
      omega
    · exact Cut.essential_sources 13 P gs (out w)
    · intro x y hxy hx
      exact Cut.cutVal_mono 13 P gs (fun g hm => (hg g hm).1) x y hxy (out w) hx
    · exact Cut.essential_supports 13 P gs (out w)
    · intro x
      exact Cut.factor P gs x (out w)
    · exact hp
  let S := (E a ∪ E b) ∪ E c
  obtain ⟨label, wire, hcomponents, hdepends⟩ := Cut.components 13 P S gs (fun g hm => (hg g hm).2)
  have hlabel (w : Fin 13) (i : Fin (13 + gs.length)) (hi : i ∈ E w) :
      label i = wire (out w) :=
    hdepends (out w) i (Finset.mem_filter.mp hi).2
  have habwire : wire (out a) = wire (out b) := by
    obtain ⟨p, hpa, hpb⟩ := (pair_geometry a b hab).2
    exact (hlabel a _ (hraw a (by simp [T]) p hpa)).symm.trans
      (hlabel b _ (hraw b (by simp [T]) p hpb))
  have hacwire : wire (out a) = wire (out c) := by
    obtain ⟨p, hpa, hpc⟩ := (pair_geometry a c hac).2
    exact (hlabel a _ (hraw a (by simp [T]) p hpa)).symm.trans
      (hlabel c _ (hraw c (by simp [T]) p hpc))
  have himg : S.image label ⊆ {wire (out a)} := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_singleton.mpr
    rcases Finset.mem_union.mp hi with hiab | hic
    · rcases Finset.mem_union.mp hiab with hia | hib
      · exact hlabel a i hia
      · exact (hlabel b i hib).trans habwire.symm
    · exact (hlabel c i hic).trans hacwire.symm
  have himgcard : (S.image label).card ≤ 1 := by simpa using Finset.card_le_card himg
  have hS9 : S.card ≤ 9 := by omega
  let R := ((Global.line a ∪ Global.line b) ∪ Global.line c).image (rawIndex gs)
  have hinj : Function.Injective (rawIndex gs) := by
    intro p q hpq
    apply Fin.ext
    exact congrArg (fun t : Fin (13 + gs.length) => t.val) hpq
  have hR9 : 9 ≤ R.card := by
    rw [Finset.card_image_of_injective _ hinj]
    exact triple_geometry a b c hab hac hbc
  have hRS : R ⊆ S := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    rcases Finset.mem_union.mp hp with hpab | hpc
    · rcases Finset.mem_union.mp hpab with hpa | hpb
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hraw a (by simp [T]) p hpa))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hraw b (by simp [T]) p hpb))
    · exact Finset.mem_union_right _ (hraw c (by simp [T]) p hpc)
  have hReq : R = S := Finset.eq_of_subset_of_card_le hRS (by omega)
  have hrawonly : ∀ i ∈ E a, i.val < 13 := by
    intro i hi
    have hiS : i ∈ S := Finset.mem_union_left _ (Finset.mem_union_left _ hi)
    have hiR : i ∈ R := hReq.symm ▸ hiS
    obtain ⟨p, _, he⟩ := Finset.mem_image.mp hiR
    rw [← he]
    exact p.isLt
  have hE8 : 8 ≤ (E a).card := by
    by_contra! hlt
    have hE7 : (E a).card ≤ 7 := by omega
    obtain ⟨Q, hQcard, hQsupport⟩ := Cut.raw_support_exists (n := 13) P gs (out a) 7 hrawonly hE7
    exact hnona (Support.circuit_support_exact gs (out a) a (fun g hm => (hg g hm).1)
      (hcorrect a) Q hQcard hQsupport)
  have hindices (w : Fin 13) := output_index gs (out w) w (hcorrect w)
  have houtinj := output_distinct gs out hcorrect
  have houtab : out a ≠ out b := fun he => hab (houtinj he)
  have houtac : out a ≠ out c := fun he => hac (houtinj he)
  have houtbc : out b ≠ out c := fun he => hbc (houtinj he)
  have hnotpaid (w : Fin 13) (hw : w ∈ T) : out w ∉ P := by
    intro hi
    obtain ⟨x, hx, hxt, hxf⟩ := (hPprops w (hnotW w hw) (out w) hi).2
    have hh := hcorrect w x hx
    change Global.val gs x (out w) = _ at hh
    rw [hxf, hxt] at hh
    exact Bool.noConfusion hh
  let k := out a + 1 - 13
  have hk : k ≤ gs.length := by have := hindices a; omega
  have hka : out a < 13 + k := by have := hindices a; omega
  have hkb : 13 + k ≤ out b := by have := hindices a; omega
  have hkc : 13 + k ≤ out c := by have := hindices a; omega
  have hprefix := Cut.essential_card (M := 13 + gs.length) 13 P (gs.take k) (out a)
    (fun g hm => (hg g (List.mem_of_mem_take hm)).2)
  rw [← Cut.essential_take 13 P gs k (out a) hk hka] at hprefix
  change (E a).card ≤ Cut.unpaid 13 P (gs.take k) + 1 at hprefix
  have hlater := Cut.unpaid_two_later 13 P gs k (out b) (out c) hk hkb hkc
    (hindices b).2 (hindices c).2 (hnotpaid b (by simp [T])) (hnotpaid c (by simp [T])) houtbc
  omega

end PEqualNP.Outside.L_meta_1024_aux.Bridge

namespace PEqualNP.Outside.L_meta_1024_aux.Bridge
open PEqualNP.CircuitLowerBounds

lemma three_exotic_bound (gs : List Gate) (out : Fin 13 → ℕ)
    (a b c : Fin 13) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hordinary : ∀ w : Fin 13, w ≠ a → w ≠ b → w ≠ c → ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x) : 39 ≤ gs.length := by
  classical
  by_cases ha : ∀ x : Fin 13 → Bool, Circuit.eval ⟨gs, out a⟩ (List.ofFn x) = Support.target a x
  · apply two_exotic_bound gs out b c hbc hg hcorrect
    intro w hwb hwc x
    by_cases hwa : w = a
    · subst w
      exact ha x
    · exact hordinary w hwa hwb hwc x
  by_cases hb : ∀ x : Fin 13 → Bool, Circuit.eval ⟨gs, out b⟩ (List.ofFn x) = Support.target b x
  · apply two_exotic_bound gs out a c hac hg hcorrect
    intro w hwa hwc x
    by_cases hwb : w = b
    · subst w
      exact hb x
    · exact hordinary w hwa hwb hwc x
  by_cases hc : ∀ x : Fin 13 → Bool, Circuit.eval ⟨gs, out c⟩ (List.ofFn x) = Support.target c x
  · apply two_exotic_bound gs out a b hab hg hcorrect
    intro w hwa hwb x
    by_cases hwc : w = c
    · subst w
      exact hc x
    · exact hordinary w hwa hwb hwc x
  rcases Nat.le_total (out a) (out b) with habo | hbao
  · rcases Nat.le_total (out a) (out c) with haco | hcao
    · exact three_exotic_core gs out a b c hab hac hbc hg hcorrect hordinary ha habo haco
    · exact three_exotic_core gs out c a b hac.symm hbc.symm hab hg hcorrect
        (fun w hwc hwa hwb => hordinary w hwa hwb hwc) hc hcao (hcao.trans habo)
  · rcases Nat.le_total (out b) (out c) with hbco | hcbo
    · exact three_exotic_core gs out b a c hab.symm hbc hac hg hcorrect
        (fun w hwb hwa hwc => hordinary w hwa hwb hwc) hb hbao hbco
    · exact three_exotic_core gs out c a b hac.symm hbc.symm hab hg hcorrect
        (fun w hwc hwa hwb => hordinary w hwa hwb hwc) hc (hcbo.trans hbao) hcbo

end PEqualNP.Outside.L_meta_1024_aux.Bridge

namespace PEqualNP.Outside.L_meta_1024_aux.Bridge
open PEqualNP.CircuitLowerBounds

lemma ten_ordinary_bound (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (W : Finset (Fin 13)) (hW : 10 ≤ W.card)
    (hordinary : ∀ w ∈ W, ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x) : 39 ≤ gs.length := by
  classical
  obtain ⟨V, hVW, hVcard⟩ := Finset.exists_subset_card_eq hW
  have hcomp : (Finset.univ \ V).card = 3 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hVcard]
    decide
  obtain ⟨a, b, c, hab, hac, hbc, hC⟩ := Finset.card_eq_three.mp hcomp
  apply three_exotic_bound gs out a b c hab hac hbc hg hcorrect
  intro w hwa hwb hwc x
  apply hordinary w (hVW ?_) x
  by_contra hwV
  have hh : w ∈ Finset.univ \ V := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwV⟩
  rw [hC] at hh
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with h | h | h
  · exact hwa h
  · exact hwb h
  · exact hwc h

noncomputable def exoticSet (gs : List Gate) (out : Fin 13 → ℕ) : Finset (Fin 13) := by
  classical
  exact Finset.univ.filter (fun w => ¬ ∀ x : Fin 13 → Bool,
    Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)

lemma four_exotic_outputs (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hsmall : gs.length < 39) : 4 ≤ (exoticSet gs out).card := by
  classical
  by_contra! hfew
  let W := Finset.univ \ exoticSet gs out
  have hW : 10 ≤ W.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hu : (Finset.univ : Finset (Fin 13)).card = 13 := by decide
    rw [hu]
    omega
  have hord : ∀ w ∈ W, ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x := by
    intro w hw
    have hn := (Finset.mem_sdiff.mp hw).2
    simpa [exoticSet] using hn
  have hh := ten_ordinary_bound gs out hg hcorrect W hW hord
  omega

end PEqualNP.Outside.L_meta_1024_aux.Bridge

namespace PEqualNP.Outside.L_meta_1024_aux.Bridge
open PEqualNP.CircuitLowerBounds

lemma ordinary_iff_extremes (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    (∀ x : Fin 13 → Bool, Global.val gs x o = Support.target w x) ↔
      Global.val gs (Global.Zof (Global.line w)) o = false ∧
      ∀ p ∈ Global.line w, Global.val gs (Global.eof p) o = true := by
  constructor
  · intro he
    constructor
    · rw [he]
      simp [Support.target, Support.line, Global.line, Global.Zof]
    · intro p hp
      rw [he]
      apply decide_eq_true_iff.mpr
      exact ⟨p, hp, by simp [Global.eof]⟩
  · rintro ⟨hz, he⟩ x
    cases ht : Support.target w x
    · cases hv : Global.val gs x o
      · rfl
      · have hm := val_mono gs hg x (Global.Zof (Global.line w)) (by
          intro q hqx
          have hnot : q ∉ Global.line w := by
            intro hq
            have hh : Support.target w x = true := decide_eq_true_iff.mpr ⟨q, hq, hqx⟩
            rw [ht] at hh
            exact Bool.noConfusion hh
          simpa [Global.Zof] using hnot) o hv
        rw [hz] at hm
        exact Bool.noConfusion hm
    · have hex : ∃ p ∈ Global.line w, x p = true := decide_eq_true_iff.mp ht
      obtain ⟨p, hp, hpx⟩ := hex
      exact val_mono gs hg (Global.eof p) x (by
        intro q hq
        have hqp : q = p := by simpa [Global.eof] using hq
        simpa [hqp] using hpx) o (he p hp)

lemma exotic_iff_extremes (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    (¬ ∀ x : Fin 13 → Bool, Global.val gs x o = Support.target w x) ↔
      Global.val gs (Global.Zof (Global.line w)) o = true ∨
      ∃ p ∈ Global.line w, Global.val gs (Global.eof p) o = false := by
  rw [ordinary_iff_extremes gs o w hg]
  simp only [not_and_or, not_forall, Bool.not_eq_false, Bool.not_eq_true, exists_prop]

lemma mem_exoticSet_iff (gs : List Gate) (out : Fin 13 → ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    w ∈ exoticSet gs out ↔
      Global.val gs (Global.Zof (Global.line w)) (out w) = true ∨
      ∃ p ∈ Global.line w, Global.val gs (Global.eof p) (out w) = false := by
  classical
  simp only [exoticSet, Finset.mem_filter, Finset.mem_univ, true_and]
  change (¬ ∀ x : Fin 13 → Bool, Global.val gs x (out w) = Support.target w x) ↔ _
  exact exotic_iff_extremes gs (out w) w hg

lemma four_exotic_witnesses (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hsmall : gs.length < 39) :
    4 ≤ (Finset.univ.filter (fun w : Fin 13 =>
      Global.val gs (Global.Zof (Global.line w)) (out w) = true ∨
      ∃ p ∈ Global.line w, Global.val gs (Global.eof p) (out w) = false)).card := by
  classical
  have he : exoticSet gs out = Finset.univ.filter (fun w : Fin 13 =>
      Global.val gs (Global.Zof (Global.line w)) (out w) = true ∨
      ∃ p ∈ Global.line w, Global.val gs (Global.eof p) (out w) = false) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact mem_exoticSet_iff gs out w (fun g hm => (hg g hm).1)
  rw [← he]
  exact four_exotic_outputs gs out hg hcorrect hsmall

end PEqualNP.Outside.L_meta_1024_aux.Bridge

namespace PEqualNP.Outside.L_meta_1024_aux.Sink
open PEqualNP.CircuitLowerBounds

def clamp (n : ℕ) (O : Finset ℕ) (i : ℕ) : Bool := decide (i < n ∧ i ∈ O)

noncomputable def gate (n : ℕ) (O : Finset ℕ) (g : Gate) : Gate := by
  classical
  exact if g.op = GateOp.or ∧ g.inputs.any (clamp n O) = true then ⟨GateOp.and, []⟩
  else ⟨g.op, g.inputs.filter (fun i => !(clamp n O i))⟩

noncomputable def transform (n : ℕ) (O : Finset ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => gate n O g :: transform (n + 1) O gs

lemma transform_length (n : ℕ) (O : Finset ℕ) (gs : List Gate) :
    (transform n O gs).length = gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp only [transform, List.length_cons, ih]

lemma transform_append (n : ℕ) (O : Finset ℕ) (gs hs : List Gate) :
    transform n O (gs ++ hs) = transform n O gs ++ transform (n + gs.length) O hs := by
  induction gs generalizing n with
  | nil => simp [transform]
  | cons g gs ih => simp [transform, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma gate_allowed (n : ℕ) (O : Finset ℕ) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ((gate n O g).op = GateOp.and ∨ (gate n O g).op = GateOp.or) ∧
      (gate n O g).inputs.length ≤ 2 := by
  unfold gate
  split
  · exact ⟨Or.inl rfl, by simp⟩
  · exact ⟨hg.1, (List.length_filter_le _ _).trans hg.2⟩

lemma gate_sink (n : ℕ) (O : Finset ℕ) (g : Gate) :
    ∀ i ∈ (gate n O g).inputs, i < n → i ∉ O := by
  intro i hi hn hO
  unfold gate at hi
  split at hi
  · simp at hi
  · have hh := (List.mem_filter.mp hi).2
    simp [clamp, hn, hO] at hh

lemma gate_ge (n : ℕ) (O : Finset ℕ) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (r s : ℕ → Bool) (hrs : ∀ i, r i = true → s i = true) :
    g.op.eval (g.inputs.map r) = true →
      (gate n O g).op.eval ((gate n O g).inputs.map s) = true := by
  intro ht
  unfold gate
  split
  · simp [GateOp.eval]
  · rename_i hn
    rcases hg with hop | hop
    · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂, id_eq] at ht ⊢
      intro i hi
      exact hrs i (ht i (List.mem_of_mem_filter hi))
    · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and,
        id_eq] at ht ⊢
      obtain ⟨i, hi, hir⟩ := ht
      refine ⟨i, ?_, hrs i hir⟩
      apply List.mem_filter.mpr
      refine ⟨hi, ?_⟩
      have hc : clamp n O i = false := by
        cases he : clamp n O i
        · rfl
        · exact False.elim (hn ⟨hop, List.any_eq_true.mpr ⟨i, hi, he⟩⟩)
      simp [hc]

lemma gate_eq (n : ℕ) (O : Finset ℕ) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (r : ℕ → Bool)
    (hclamp : ∀ i ∈ g.inputs, clamp n O i = true → r i = true) :
    (gate n O g).op.eval ((gate n O g).inputs.map r) = g.op.eval (g.inputs.map r) := by
  have hforward := gate_ge n O g hg r r (fun _ h => h)
  have hback : (gate n O g).op.eval ((gate n O g).inputs.map r) = true →
      g.op.eval (g.inputs.map r) = true := by
    intro ht
    unfold gate at ht
    split at ht
    · rename_i hc
      obtain ⟨i, hi, hic⟩ := List.any_eq_true.mp hc.2
      simp only [hc.1, GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and, id_eq]
      exact ⟨i, hi, hclamp i hi hic⟩
    · rcases hg with hop | hop
      · simp only [hop, GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂, id_eq] at ht ⊢
        intro i hi
        cases hc : clamp n O i
        · exact ht i (List.mem_filter.mpr ⟨hi, by simp [hc]⟩)
        · exact hclamp i hi hc
      · simp only [hop, GateOp.eval, List.any_eq_true, List.mem_map, exists_exists_and_eq_and,
          id_eq] at ht ⊢
        obtain ⟨i, hi, hir⟩ := ht
        exact ⟨i, List.mem_of_mem_filter hi, hir⟩
  cases h₁ : (gate n O g).op.eval ((gate n O g).inputs.map r) <;>
    cases h₂ : g.op.eval (g.inputs.map r) <;> simp_all

lemma transform_allowed (n : ℕ) (O : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ transform n O gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing n with
  | nil => simp [transform]
  | cons g gs ih =>
    intro h hh
    simp only [transform, List.mem_cons] at hh
    rcases hh with rfl | hh
    · exact gate_allowed n O g (hg g (by simp))
    · exact ih (n + 1) (fun k hk => hg k (List.mem_cons_of_mem g hk)) h hh

lemma val_ge {n : ℕ} (O : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) : ∀ i, Global.val gs x i = true → Global.val (transform n O gs) x i = true := by
  induction gs using List.reverseRecOn with
  | nil => exact fun _ h => h
  | append_singleton gs g ih =>
    have hgg := hg g (by simp)
    have hgs : ∀ h ∈ gs, h.op = GateOp.and ∨ h.op = GateOp.or :=
      fun h hh => hg h (List.mem_append_left _ hh)
    intro i hi
    rw [transform_append]
    simp only [transform, List.append_nil]
    rw [Global.val_snoc] at hi
    rw [Global.val_snoc, transform_length]
    by_cases he : i = n + gs.length
    · rw [ite_eq_left he] at hi ⊢
      exact gate_ge (n + gs.length) O g hgg _ _ (ih hgs) hi
    · rw [ite_eq_right he] at hi ⊢
      exact ih hgs i hi

lemma val_append_old {n : ℕ} (gs hs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : i < n + gs.length) : Global.val (gs ++ hs) x i = Global.val gs x i := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, Global.val_snoc,
      ite_eq_right (show i ≠ n + (gs ++ hs).length by simp; omega)]
    exact ih

lemma val_take {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k i : ℕ)
    (hk : k ≤ gs.length) (hi : i < n + k) :
    Global.val gs x i = Global.val (gs.take k) x i := by
  have hlen : (gs.take k).length = k := by simp [List.length_take, Nat.min_eq_left hk]
  have h := val_append_old (gs.take k) (gs.drop k) x i (by rw [hlen]; exact hi)
  simpa only [List.take_append_drop] using h

lemma prefix_eq {n : ℕ} (O : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) (t : ℕ) (hbound : n + gs.length ≤ t + 1)
    (hO : ∀ i ∈ O, i < t → i < n + gs.length → Global.val gs x i = true) :
    ∀ i, Global.val (transform n O gs) x i = Global.val gs x i := by
  induction gs using List.reverseRecOn with
  | nil => intro i; rfl
  | append_singleton gs g ih =>
    have hgs : ∀ h ∈ gs, h.op = GateOp.and ∨ h.op = GateOp.or :=
      fun h hh => hg h (List.mem_append_left _ hh)
    have hbound' : n + gs.length ≤ t + 1 := by simp only [List.length_append, List.length_singleton] at hbound; omega
    have hO' : ∀ i ∈ O, i < t → i < n + gs.length → Global.val gs x i = true := by
      intro i hiO hit hi
      have hh := hO i hiO hit (by simp; omega)
      rw [Global.val_snoc, ite_eq_right (by omega)] at hh
      exact hh
    have heq := ih hgs hbound' hO'
    intro i
    rw [transform_append]
    simp only [transform, List.append_nil]
    rw [Global.val_snoc, Global.val_snoc, transform_length]
    by_cases hi : i = n + gs.length
    · simp only [ite_eq_left hi]
      simp_rw [heq]
      apply gate_eq (n + gs.length) O g (hg g (by simp))
      intro k _ hk
      have hkc : k < n + gs.length ∧ k ∈ O := by simpa [clamp] using hk
      exact hO' k hkc.2 (by simp only [List.length_append, List.length_singleton] at hbound; omega) hkc.1
    · simp only [ite_eq_right hi]
      exact heq i

lemma output_eq {n : ℕ} (O : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) (o : ℕ) (ho : n ≤ o ∧ o < n + gs.length)
    (hO : ∀ i ∈ O, i < o → Global.val gs x i = true) :
    Global.val (transform n O gs) x o = Global.val gs x o := by
  let k := o + 1 - n
  have hk : k ≤ gs.length := by omega
  have hko : o < n + k := by omega
  have hlen : (gs.take k).length = k := by simp [List.length_take, Nat.min_eq_left hk]
  have hsplit : transform n O gs = transform n O (gs.take k) ++
      transform (n + k) O (gs.drop k) := by
    have hh := transform_append n O (gs.take k) (gs.drop k)
    rw [List.take_append_drop, hlen] at hh
    exact hh
  rw [hsplit, val_append_old _ _ _ _ (by rw [transform_length, hlen]; exact hko)]
  rw [prefix_eq O (gs.take k) (fun g hm => hg g (List.mem_of_mem_take hm)) x o
    (by rw [hlen]; omega) (by
      intro i hiO hio hi
      rw [← val_take gs x k i hk (by rwa [hlen] at hi)]
      exact hO i hiO hio)]
  exact (val_take gs x k o hk hko).symm

end PEqualNP.Outside.L_meta_1024_aux.Sink

namespace PEqualNP.Outside.L_meta_1024_aux.Sink
open PEqualNP.CircuitLowerBounds

lemma transform_get (n : ℕ) (O : Finset ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    (transform n O gs)[j]'(by rw [transform_length]; exact hj) = gate (n + j) O gs[j] := by
  induction gs generalizing n j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => simp [transform]
    | succ j =>
      have hh := ih (n + 1) j (by simpa using hj)
      simpa [transform, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh

lemma transform_sink (n : ℕ) (O : Finset ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∀ i ∈ ((transform n O gs)[j]'(by rw [transform_length]; exact hj)).inputs,
      i < n + j → i ∉ O := by
  rw [transform_get]
  exact gate_sink (n + j) O gs[j]

lemma false_target_zero (w : Fin 13) (x : Fin 13 → Bool) (hf : Support.target w x = false) :
    Global.line w ⊆ Support.zeroSet x := by
  intro p hp
  have hfalse : x p = false := by
    cases he : x p
    · rfl
    · have ht : Support.target w x = true := decide_eq_true_iff.mpr ⟨p, hp, he⟩
      rw [hf] at ht
      exact Bool.noConfusion ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfalse⟩

lemma other_target_true (a b : Fin 13) (hab : a ≠ b) (x : Fin 13 → Bool)
    (hx : Support.Band x) (ha : Support.target a x = false) : Support.target b x = true := by
  cases hb : Support.target b x
  · have hsub : Global.line a ∪ Global.line b ⊆ Support.zeroSet x :=
      Finset.union_subset (false_target_zero a x ha) (false_target_zero b x hb)
    have hc := Finset.card_le_card hsub
    rw [(Bridge.pair_geometry a b hab).1] at hc
    rcases hx with hx | hx <;> omega
  · rfl

lemma other_extreme_true (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out w) = Support.target w x)
    (w v : Fin 13) (hvw : v ≠ w) : Global.val gs (Global.Zof (Global.line w)) (out v) = true := by
  obtain ⟨p, hpv, hpw⟩ := Charges.line_difference v w hvw.symm
  have hsub : ({p} : Finset (Fin 13)) ⊆ Finset.univ \ Support.line w := by
    intro q hq
    have he := Finset.mem_singleton.mp hq
    subst q
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpw⟩
  obtain ⟨Y, hpY, hY, hYcard⟩ := Clamp.extend_eight w {p} hsub (by simp)
  have htarget : Support.target v (Clamp.fromTrue Y) = true := by
    apply decide_eq_true_iff.mpr
    exact ⟨p, hpv, by simp [Clamp.fromTrue, hpY (Finset.mem_singleton_self p)]⟩
  have hv : Global.val gs (Clamp.fromTrue Y) (out v) = true :=
    (hcorrect v _ (Clamp.fromTrue_band Y hYcard)).trans htarget
  apply Bridge.val_mono gs hg (Clamp.fromTrue Y) (Global.Zof (Global.line w)) _ (out v) hv
  intro q hq
  have hqY : q ∈ Y := by simpa [Clamp.fromTrue] using hq
  simpa [Global.Zof, Global.line, Support.line] using (Finset.mem_sdiff.mp (hY hqY)).2

lemma band_correct (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out w) = Support.target w x) :
    ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Global.val (transform 13 (Finset.univ.image out) gs) x (out w) = Support.target w x := by
  intro w x hx
  cases ht : Support.target w x
  · have heq := output_eq (Finset.univ.image out) gs hg x (out w)
      (Bridge.output_index gs (out w) w (hcorrect w)) (by
        intro i hi hio
        obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hi
        have hvw : v ≠ w := by intro he; subst v; omega
        exact (hcorrect v x hx).trans (other_target_true w v hvw.symm x hx ht))
    exact heq.trans ((hcorrect w x hx).trans ht)
  · exact val_ge (Finset.univ.image out) gs hg x (out w) ((hcorrect w x hx).trans ht)

lemma preserves_ordinary (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out w) = Support.target w x)
    (w : Fin 13) (hordinary : ∀ x : Fin 13 → Bool, Global.val gs x (out w) = Support.target w x) :
    ∀ x : Fin 13 → Bool,
      Global.val (transform 13 (Finset.univ.image out) gs) x (out w) = Support.target w x := by
  let O := Finset.univ.image out
  have hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hm => (hg g hm).1
  have hgnew := transform_allowed 13 O gs hg
  apply (Bridge.ordinary_iff_extremes (transform 13 O gs) (out w) w (fun g hm => (hgnew g hm).1)).mpr
  obtain ⟨hz, he⟩ := (Bridge.ordinary_iff_extremes gs (out w) w hop).mp hordinary
  constructor
  · have heq := output_eq O gs hop (Global.Zof (Global.line w)) (out w)
      (Bridge.output_index gs (out w) w (hcorrect w)) (by
        intro i hi hio
        obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hi
        have hvw : v ≠ w := by intro hh; subst v; omega
        exact other_extreme_true gs out hop hcorrect w v hvw)
    exact heq.trans hz
  · intro p hp
    exact val_ge O gs hop (Global.eof p) (out w) (he p hp)

lemma exotic_subset (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out w) = Support.target w x) :
    Bridge.exoticSet (transform 13 (Finset.univ.image out) gs) out ⊆ Bridge.exoticSet gs out := by
  classical
  intro w hw
  simp only [Bridge.exoticSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
  intro hord
  exact hw (preserves_ordinary gs out hg hcorrect w hord)

end PEqualNP.Outside.L_meta_1024_aux.Sink

namespace PEqualNP.Outside.L_meta_1024_aux.Sink
open PEqualNP.CircuitLowerBounds

def override (n : ℕ) (P : Finset ℕ) (r : ℕ → Bool) (i : ℕ) : Bool :=
  if clamp n P i then true else r i

lemma gate_override (n : ℕ) (P : Finset ℕ) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (r : ℕ → Bool) :
    (gate n P g).op.eval ((gate n P g).inputs.map r) =
      g.op.eval (g.inputs.map (override n P r)) := by
  have hmap : (gate n P g).inputs.map r = (gate n P g).inputs.map (override n P r) := by
    apply List.map_congr_left
    intro i hi
    have hc : clamp n P i = false := by
      cases he : clamp n P i
      · rfl
      · have hh : i < n ∧ i ∈ P := by simpa [clamp] using he
        exact False.elim (gate_sink n P g i hi hh.1 hh.2)
    simp [override, hc]
  rw [hmap]
  apply gate_eq n P g hg
  intro i _ hi
  simp [override, hi]

lemma override_succ_ne (m : ℕ) (P : Finset ℕ) (r : ℕ → Bool) (i : ℕ) (hne : i ≠ m) :
    override (m + 1) P r i = override m P r i := by
  by_cases hi : i < m
  · have hi' : i < m + 1 := by omega
    simp [override, clamp, hi, hi']
  · have hi' : ¬ i < m + 1 := by omega
    simp [override, clamp, hi, hi']

lemma transform_cut_eq {n M : ℕ} (P : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hP : ∀ i ∈ P, n ≤ i) (x : Fin n → Bool) (z : Fin M → Bool)
    (hinput : ∀ i : Fin n, Cut.source z i.val = x i)
    (hpaid : ∀ i ∈ P, n ≤ i → i < n + gs.length → Cut.source z i = true) :
    ∀ i, override (n + gs.length) P (Global.val (transform n P gs) x) i =
      Cut.cutVal n P gs z i := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i
    by_cases hi : i < n
    · have hin : i ∉ P := fun hp => by have := hP i hp; omega
      simp only [List.length_nil, Nat.add_zero, transform, override, clamp,
        Global.val_nil, Cut.cutVal_nil, hi, hin, and_false, decide_false, Bool.false_eq_true,
        if_false, dite_true]
      exact (hinput ⟨i, hi⟩).symm
    · simp [transform, override, clamp, Global.val_nil, Cut.cutVal_nil, hi]
  | append_singleton gs g ih =>
    have hop : ∀ h ∈ gs, h.op = GateOp.and ∨ h.op = GateOp.or :=
      fun h hh => hg h (List.mem_append_left _ hh)
    have hpast : ∀ i ∈ P, n ≤ i → i < n + gs.length → Cut.source z i = true := by
      intro i hi hn hb
      exact hpaid i hi hn (by simp; omega)
    have heq := ih hop hpast
    intro i
    have hval (j : ℕ) : Global.val (transform n P (gs ++ [g])) x j =
        if j = n + gs.length then
          (gate (n + gs.length) P g).op.eval
            ((gate (n + gs.length) P g).inputs.map (Global.val (transform n P gs) x))
        else Global.val (transform n P gs) x j := by
      rw [transform_append]
      simp only [transform, Global.val_snoc, transform_length]
    change (if clamp (n + (gs ++ [g]).length) P i then true
      else Global.val (transform n P (gs ++ [g])) x i) = _
    rw [hval, Cut.cutVal_snoc]
    simp only [List.length_append, List.length_singleton, ← Nat.add_assoc]
    by_cases hi : i = n + gs.length
    · subst i
      simp only [ite_eq_left]
      by_cases hp : n + gs.length ∈ P
      · have hz := hpaid (n + gs.length) hp (by omega) (by simp)
        simp [clamp, hp, hz]
      · simp only [clamp, hp, and_false, decide_false, Bool.false_eq_true, if_false]
        rw [gate_override (n + gs.length) P g (hg g (by simp))]
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro j _
        exact heq j
    · simp only [ite_eq_right hi]
      change override (n + gs.length + 1) P (Global.val (transform n P gs) x) i = _
      rw [override_succ_ne _ _ _ _ hi]
      exact heq i

lemma transform_cut_output {n M : ℕ} (P : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hP : ∀ i ∈ P, n ≤ i) (x : Fin n → Bool) (z : Fin M → Bool)
    (hinput : ∀ i : Fin n, Cut.source z i.val = x i)
    (hpaid : ∀ i ∈ P, n ≤ i → i < n + gs.length → Cut.source z i = true)
    (i : ℕ) (hi : i ∉ P) :
    Global.val (transform n P gs) x i = Cut.cutVal n P gs z i := by
  have hh := transform_cut_eq P gs hg hP x z hinput hpaid i
  simpa [override, clamp, hi] using hh

end PEqualNP.Outside.L_meta_1024_aux.Sink

namespace PEqualNP.Outside.L_meta_1024_aux.Dead
open PEqualNP.CircuitLowerBounds

def remap (n : ℕ) (cs : List Gate) (is : List ℕ) (i : ℕ) : ℕ :=
  if i < is.length then is.getD i 0 else n + cs.length

def step (n : ℕ) (P : Finset ℕ) (s : List Gate × List ℕ) (g : Gate) : List Gate × List ℕ :=
  if s.2.length ∈ P then (s.1, s.2 ++ [0])
  else (s.1 ++ [⟨g.op, g.inputs.map (remap n s.1 s.2)⟩], s.2 ++ [n + s.1.length])

def compile (n : ℕ) (P : Finset ℕ) (gs : List Gate) : List Gate × List ℕ :=
  gs.foldl (step n P) ([], List.range n)

def code (n : ℕ) (P : Finset ℕ) (gs : List Gate) : List Gate := (compile n P gs).1
def indices (n : ℕ) (P : Finset ℕ) (gs : List Gate) : List ℕ := (compile n P gs).2

lemma compile_snoc (n : ℕ) (P : Finset ℕ) (gs : List Gate) (g : Gate) :
    compile n P (gs ++ [g]) = step n P (compile n P gs) g := by
  simp [compile, List.foldl_append]

lemma step_length (n : ℕ) (P : Finset ℕ) (s : List Gate × List ℕ) (g : Gate) :
    (step n P s g).2.length = s.2.length + 1 := by
  unfold step
  split <;> simp

lemma indices_length (n : ℕ) (P : Finset ℕ) (gs : List Gate) :
    (indices n P gs).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [indices, compile]
  | append_singleton gs g ih =>
    change (compile n P (gs ++ [g])).2.length = _
    rw [compile_snoc, step_length]
    change (indices n P gs).length + 1 = _
    rw [ih]
    simp [Nat.add_assoc]

def nextGate (n : ℕ) (P : Finset ℕ) (gs : List Gate) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remap n (code n P gs) (indices n P gs))⟩

lemma code_snoc (n : ℕ) (P : Finset ℕ) (gs : List Gate) (g : Gate) :
    code n P (gs ++ [g]) = if n + gs.length ∈ P then code n P gs
      else code n P gs ++ [nextGate n P gs g] := by
  unfold code
  rw [compile_snoc]
  change (step n P (code n P gs, indices n P gs) g).1 = _
  unfold step
  rw [indices_length]
  split <;> rfl

lemma indices_snoc (n : ℕ) (P : Finset ℕ) (gs : List Gate) (g : Gate) :
    indices n P (gs ++ [g]) = indices n P gs ++
      [if n + gs.length ∈ P then 0 else n + (code n P gs).length] := by
  unfold indices
  rw [compile_snoc]
  change (step n P (code n P gs, indices n P gs) g).2 = _
  unfold step
  rw [indices_length]
  split <;> simp_all [indices]

lemma code_length (n : ℕ) (P : Finset ℕ) (gs : List Gate) :
    (code n P gs).length = Cut.unpaid n P gs := by
  induction gs using List.reverseRecOn with
  | nil => simp [code, compile, Cut.unpaid_nil]
  | append_singleton gs g ih =>
    rw [code_snoc, Cut.unpaid_snoc]
    by_cases hp : n + gs.length ∈ P <;> simp [hp, ih]

lemma code_allowed (n : ℕ) (P : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ code n P gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction gs using List.reverseRecOn with
  | nil => simp [code, compile]
  | append_singleton gs g ih =>
    have hgs : ∀ h ∈ gs, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2 :=
      fun h hh => hg h (List.mem_append_left _ hh)
    rw [code_snoc]
    split
    · exact ih hgs
    · intro h hh
      rcases List.mem_append.mp hh with hh | hh
      · exact ih hgs h hh
      · have he : h = nextGate n P gs g := by simpa using hh
        subst h
        have hgg := hg g (by simp)
        simpa [nextGate] using hgg

lemma mapped_valid (n : ℕ) (P : Finset ℕ) (gs : List Gate) :
    ∀ i, i < n + gs.length → i ∉ P → (indices n P gs).getD i 0 < n + (code n P gs).length := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi _
    have hil : i < n := by simpa using hi
    change (List.range n).getD i 0 < n
    rw [List.getD_eq_getElem _ _ (by simpa using hil)]
    simpa using hil
  | append_singleton gs g ih =>
    intro i hi hip
    rw [indices_snoc, code_snoc]
    by_cases he : i = n + gs.length
    · subst i
      have hget : (indices n P gs ++ [if n + gs.length ∈ P then 0 else n + (code n P gs).length]).getD
          (indices n P gs).length 0 = if n + gs.length ∈ P then 0 else n + (code n P gs).length := by simp
      rw [indices_length] at hget
      rw [hget]
      simp only [ite_eq_right hip, List.length_append, List.length_singleton]
      omega
    · have hit : i < n + gs.length := by simp only [List.length_append, List.length_singleton] at hi; omega
      rw [List.getD_append _ _ _ _ (by rw [indices_length]; exact hit)]
      have hh := ih i hit hip
      by_cases hp : n + gs.length ∈ P
      · simp only [ite_eq_left hp]
        exact hh
      · simp only [ite_eq_right hp, List.length_append, List.length_singleton]
        omega

end PEqualNP.Outside.L_meta_1024_aux.Dead

namespace PEqualNP.Outside.L_meta_1024_aux.Dead
open PEqualNP.CircuitLowerBounds

def NoReads (n : ℕ) (P : Finset ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∀ i ∈ gs[j].inputs, i < n + j → i ∉ P

lemma noReads_prefix (n : ℕ) (P : Finset ℕ) (gs : List Gate) (g : Gate)
    (h : NoReads n P (gs ++ [g])) : NoReads n P gs := by
  intro j hj i hi hn
  have hh := h j (by simp; omega) i
  apply hh
  · simpa only [List.getElem_append_left hj] using hi
  · exact hn

lemma noReads_last (n : ℕ) (P : Finset ℕ) (gs : List Gate) (g : Gate)
    (h : NoReads n P (gs ++ [g])) : ∀ i ∈ g.inputs, i < n + gs.length → i ∉ P := by
  simpa using h gs.length (by simp)

lemma transform_noReads (n : ℕ) (P : Finset ℕ) (gs : List Gate) :
    NoReads n P (Sink.transform n P gs) := by
  intro j hj
  have hjold : j < gs.length := by simpa [Sink.transform_length] using hj
  exact Sink.transform_sink n P gs j hjold

lemma val_invalid {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : n + gs.length ≤ i) : Global.val gs x i = false := by
  unfold Global.val
  apply List.getD_eq_default
  rw [Global.fold_length, List.length_ofFn]
  exact hi

lemma eval {n : ℕ} (P : Finset ℕ) (gs : List Gate) (hreads : NoReads n P gs)
    (x : Fin n → Bool) : ∀ i, i < n + gs.length → i ∉ P →
      Global.val (code n P gs) x ((indices n P gs).getD i 0) = Global.val gs x i := by
  induction gs using List.reverseRecOn with
  | nil =>
    intro i hi _
    have hil : i < n := by simpa using hi
    change Global.val [] x ((List.range n).getD i 0) = Global.val [] x i
    have hr : (List.range n).getD i 0 = i := by
      rw [List.getD_eq_getElem _ _ (by simpa using hil)]
      simp
    rw [hr]
  | append_singleton gs g ih =>
    have hprev := noReads_prefix n P gs g hreads
    have hlast := noReads_last n P gs g hreads
    intro i hi hip
    rw [code_snoc, indices_snoc]
    by_cases hp : n + gs.length ∈ P
    · simp only [ite_eq_left hp]
      have hne : i ≠ n + gs.length := by intro he; exact hip (he.symm ▸ hp)
      have hit : i < n + gs.length := by simp only [List.length_append, List.length_singleton] at hi; omega
      rw [List.getD_append _ _ _ _ (by rw [indices_length]; exact hit)]
      rw [Global.val_snoc, ite_eq_right hne]
      exact ih hprev i hit hip
    · simp only [ite_eq_right hp]
      by_cases he : i = n + gs.length
      · subst i
        have hget : (indices n P gs ++ [n + (code n P gs).length]).getD (indices n P gs).length 0 =
            n + (code n P gs).length := by simp
        rw [indices_length] at hget
        rw [hget]
        rw [Global.val_snoc, ite_eq_left rfl, Global.val_snoc, ite_eq_left rfl]
        change g.op.eval ((g.inputs.map (remap n (code n P gs) (indices n P gs))).map
          (fun j => Global.val (code n P gs) x j)) =
          g.op.eval (g.inputs.map (fun j => Global.val gs x j))
        rw [List.map_map]
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro j hj
        by_cases hjlt : j < n + gs.length
        · simp only [Function.comp_apply, remap, indices_length, ite_eq_left hjlt]
          exact ih hprev j hjlt (hlast j hj hjlt)
        · simp only [Function.comp_apply, remap, indices_length, ite_eq_right hjlt]
          rw [val_invalid _ _ _ (by omega), val_invalid _ _ _ (by omega)]
      · have hit : i < n + gs.length := by simp only [List.length_append, List.length_singleton] at hi; omega
        rw [List.getD_append _ _ _ _ (by rw [indices_length]; exact hit)]
        have hvalid := mapped_valid n P gs i hit hip
        rw [Global.val_snoc, ite_eq_right (show (indices n P gs).getD i 0 ≠ n + (code n P gs).length by omega)]
        rw [Global.val_snoc, ite_eq_right he]
        exact ih hprev i hit hip

lemma code_op_at (n : ℕ) (P : Finset ℕ) (gs : List Gate) (j : ℕ)
    (hj : j < gs.length) (hp : n + j ∉ P) :
    ∃ k : ℕ, ∃ hk : k < (code n P gs).length, (indices n P gs).getD (n + j) 0 = n + k ∧
      ((code n P gs)[k]'hk).op = gs[j].op := by
  induction gs using List.reverseRecOn generalizing j with
  | nil => simp at hj
  | append_singleton gs g ih =>
    by_cases hlast : j = gs.length
    · subst j
      refine ⟨(code n P gs).length, ?_, ?_, ?_⟩
      · rw [code_snoc, ite_eq_right hp]
        simp
      · rw [indices_snoc]
        have hget : (indices n P gs ++ [if n + gs.length ∈ P then 0 else n + (code n P gs).length]).getD
            (indices n P gs).length 0 = if n + gs.length ∈ P then 0 else n + (code n P gs).length := by simp
        rw [indices_length] at hget
        rw [hget, ite_eq_right hp]
      · simp only [code_snoc, ite_eq_right hp]
        simp [nextGate]
    · have hjold : j < gs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
      obtain ⟨k, hk, hmap, hop⟩ := ih j hjold hp
      have hget : (indices n P (gs ++ [g])).getD (n + j) 0 = (indices n P gs).getD (n + j) 0 := by
        rw [indices_snoc, List.getD_append _ _ _ _ (by rw [indices_length]; omega)]
      by_cases hpaid : n + gs.length ∈ P
      · refine ⟨k, ?_, hget.trans hmap, ?_⟩
        · simpa only [code_snoc, ite_eq_left hpaid] using hk
        · simpa only [code_snoc, ite_eq_left hpaid, List.getElem_append_left hjold] using hop
      · refine ⟨k, ?_, hget.trans hmap, ?_⟩
        · simp only [code_snoc, ite_eq_right hpaid, List.length_append, List.length_singleton]
          omega
        · simpa only [code_snoc, ite_eq_right hpaid, List.getElem_append_left hk,
            List.getElem_append_left hjold] using hop

end PEqualNP.Outside.L_meta_1024_aux.Dead

namespace PEqualNP.Outside.L_meta_1024_aux.Dead
open PEqualNP.CircuitLowerBounds

lemma wire_eq_gate {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) :
    Global.val gs x (n + j) = gs[j].op.eval (gs[j].inputs.map
      (fun i => if i < n + j then Global.val gs x i else false)) := by
  induction gs using List.reverseRecOn generalizing j with
  | nil => simp at hj
  | append_singleton gs g ih =>
    by_cases hlast : j = gs.length
    · subst j
      rw [Global.val_snoc, ite_eq_left rfl]
      have hget : (gs ++ [g])[gs.length]'(by simp) = g := by simp
      rw [hget]
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + gs.length
      · rw [ite_eq_left hi, Global.val_snoc, ite_eq_right (by omega)]
      · rw [ite_eq_right hi, val_invalid _ _ _ (by omega)]
    · have hjold : j < gs.length := by simp only [List.length_append, List.length_singleton] at hj; omega
      rw [Global.val_snoc, ite_eq_right (by omega), List.getElem_append_left hjold, ih j hjold]
      apply congrArg gs[j].op.eval
      apply List.map_congr_left
      intro i _
      by_cases hi : i < n + j
      · simp only [ite_eq_left hi]
        rw [Global.val_snoc, ite_eq_right (by omega)]
      · simp only [ite_eq_right hi]

lemma deleted_formula {n : ℕ} (P : Finset ℕ) (gs : List Gate) (hreads : NoReads n P gs)
    (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) :
    Global.val gs x (n + j) = gs[j].op.eval (gs[j].inputs.map
      (fun i => if i < n + j then Global.val (code n P gs) x ((indices n P gs).getD i 0) else false)) := by
  rw [wire_eq_gate gs x j hj]
  apply congrArg gs[j].op.eval
  apply List.map_congr_left
  intro i hi
  by_cases hib : i < n + j
  · simp only [ite_eq_left hib]
    exact (eval P gs hreads x i (by omega) (hreads j hj i hi hib)).symm
  · simp only [ite_eq_right hib]

noncomputable def paidCode (n : ℕ) (P : Finset ℕ) (gs : List Gate) : List Gate :=
  code n P (Sink.transform n P gs)

noncomputable def paidIndex (n : ℕ) (P : Finset ℕ) (gs : List Gate) (i : ℕ) : ℕ :=
  (indices n P (Sink.transform n P gs)).getD i 0

def trueSources {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : Fin (n + gs.length) → Bool :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else true

lemma trueSources_input {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : Fin n) :
    Cut.source (trueSources gs x) i.val = x i := by
  rw [Cut.source_eq]
  have hi : i.val < n + gs.length := by omega
  simp [trueSources, hi, i.isLt]

lemma trueSources_paid {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hin : n ≤ i) (hvalid : i < n + gs.length) : Cut.source (trueSources gs x) i = true := by
  rw [Cut.source_eq]
  simp [trueSources, hvalid, show ¬ i < n by omega]

lemma paid_length (n : ℕ) (P : Finset ℕ) (gs : List Gate) :
    (paidCode n P gs).length = Cut.unpaid n P gs := by
  rw [paidCode, code_length]
  simp only [Cut.unpaid, Sink.transform_length]

lemma paid_allowed (n : ℕ) (P : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ paidCode n P gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
  code_allowed n P (Sink.transform n P gs) (Sink.transform_allowed n P gs hg)

lemma paid_eval {n : ℕ} (P : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hP : ∀ i ∈ P, n ≤ i) (x : Fin n → Bool) (i : ℕ)
    (hvalid : i < n + gs.length) (hip : i ∉ P) :
    Global.val (paidCode n P gs) x (paidIndex n P gs i) =
      Cut.cutVal n P gs (trueSources gs x) i := by
  change Global.val (code n P (Sink.transform n P gs)) x
    ((indices n P (Sink.transform n P gs)).getD i 0) = _
  rw [eval P (Sink.transform n P gs) (transform_noReads n P gs) x i
    (by rwa [Sink.transform_length]) hip]
  exact Sink.transform_cut_output P gs hg hP x (trueSources gs x) (trueSources_input gs x)
    (fun i _ hn hi => trueSources_paid gs x i hn hi) i hip

end PEqualNP.Outside.L_meta_1024_aux.Dead

namespace PEqualNP.Outside.L_meta_1024_aux.Sink
open PEqualNP.CircuitLowerBounds

lemma or_preserved_of_false {n : ℕ} (P : Finset ℕ) (gs : List Gate) (j : ℕ)
    (hj : j < gs.length) (hor : gs[j].op = GateOp.or) (x : Fin n → Bool)
    (hf : Global.val (transform n P gs) x (n + j) = false) :
    ((transform n P gs)[j]'(by rw [transform_length]; exact hj)).op = GateOp.or := by
  classical
  by_cases hcl : gs[j].op = GateOp.or ∧ gs[j].inputs.any (clamp (n + j) P) = true
  · have hgate : (transform n P gs)[j]'(by rw [transform_length]; exact hj) = ⟨GateOp.and, []⟩ := by
      rw [transform_get n P gs j hj]
      unfold gate
      rw [ite_eq_left hcl]
    have he := Dead.wire_eq_gate (transform n P gs) x j (by rwa [transform_length])
    rw [hgate] at he
    simp only [List.map_nil, GateOp.eval, List.all_nil] at he
    rw [hf] at he
    exact Bool.noConfusion he
  · rw [transform_get n P gs j hj]
    unfold gate
    rw [ite_eq_right hcl]
    exact hor

end PEqualNP.Outside.L_meta_1024_aux.Sink

namespace PEqualNP.Outside.L_meta_1024_aux.Sink
open PEqualNP.CircuitLowerBounds

lemma gate_inputs_subset (n : ℕ) (P : Finset ℕ) (g : Gate) :
    ∀ i ∈ (gate n P g).inputs, i ∈ g.inputs := by
  intro i hi
  unfold gate at hi
  split at hi
  · simp at hi
  · exact List.mem_of_mem_filter hi

lemma preserves_noReads (n : ℕ) (P Q : Finset ℕ) (gs : List Gate)
    (hQ : Dead.NoReads n Q gs) : Dead.NoReads n Q (transform n P gs) := by
  intro j hj i hi hn
  have hjold : j < gs.length := by simpa [transform_length] using hj
  rw [transform_get n P gs j hjold] at hi
  exact hQ j hjold i (gate_inputs_subset (n + j) P gs[j] i hi) hn

end PEqualNP.Outside.L_meta_1024_aux.Sink

namespace PEqualNP.Outside.L_meta_1024_aux.Dead
open PEqualNP.CircuitLowerBounds

lemma noReads_union (n : ℕ) (P Q : Finset ℕ) (gs : List Gate)
    (hP : NoReads n P gs) (hQ : NoReads n Q gs) : NoReads n (P ∪ Q) gs := by
  intro j hj i hi hn hip
  rcases Finset.mem_union.mp hip with hp | hq
  · exact hP j hj i hi hn hp
  · exact hQ j hj i hi hn hq

lemma double_transform_noReads (n : ℕ) (P Q : Finset ℕ) (gs : List Gate) :
    NoReads n (P ∪ Q) (Sink.transform n P (Sink.transform n Q gs)) := by
  apply noReads_union
  · exact transform_noReads n P _
  · exact Sink.preserves_noReads n P Q _ (transform_noReads n Q gs)

end PEqualNP.Outside.L_meta_1024_aux.Dead

namespace PEqualNP.Outside.L_meta_1024_aux.Cut
open PEqualNP.CircuitLowerBounds

lemma cutVal_invalid {M : ℕ} (n : ℕ) (P : Finset ℕ) (gs : List Gate) (z : Fin M → Bool) (i : ℕ)
    (hi : n + gs.length ≤ i) : cutVal n P gs z i = false := by
  unfold cutVal cutRun
  apply List.getD_eq_default
  rw [fold_length, List.length_ofFn]
  exact hi

lemma cutVal_add_sinks {M : ℕ} (n : ℕ) (P Q : Finset ℕ) (gs : List Gate)
    (hreads : Dead.NoReads n Q gs) (z : Fin M → Bool) :
    ∀ i, i ∉ Q → cutVal n (P ∪ Q) gs z i = cutVal n P gs z i := by
  induction gs using List.reverseRecOn with
  | nil => intro i _; rfl
  | append_singleton gs g ih =>
    have hprev := Dead.noReads_prefix n Q gs g hreads
    have hlast := Dead.noReads_last n Q gs g hreads
    intro i hiQ
    rw [cutVal_snoc, cutVal_snoc]
    by_cases hi : i = n + gs.length
    · subst i
      simp only [ite_eq_left, Finset.mem_union, hiQ, or_false]
      by_cases hp : n + gs.length ∈ P
      · simp only [ite_eq_left hp]
      · simp only [ite_eq_right hp]
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro j hj
        by_cases hjlt : j < n + gs.length
        · exact ih hprev j (hlast j hj hjlt)
        · rw [cutVal_invalid _ _ _ _ _ (by omega), cutVal_invalid _ _ _ _ _ (by omega)]
    · simp only [ite_eq_right hi]
      exact ih hprev i hiQ

lemma essential_add_sinks {M : ℕ} (n : ℕ) (P Q : Finset ℕ) (gs : List Gate)
    (hreads : Dead.NoReads n Q gs) (o : ℕ) (ho : o ∉ Q) :
    essential (M := M) n (P ∪ Q) gs o = essential n P gs o := by
  classical
  ext t
  simp only [essential, Finset.mem_filter, Finset.mem_univ, true_and, Depends]
  constructor
  · rintro ⟨x, y, hxy, hne⟩
    refine ⟨x, y, hxy, ?_⟩
    rwa [cutVal_add_sinks n P Q gs hreads x o ho, cutVal_add_sinks n P Q gs hreads y o ho] at hne
  · rintro ⟨x, y, hxy, hne⟩
    refine ⟨x, y, hxy, ?_⟩
    rw [cutVal_add_sinks n P Q gs hreads x o ho, cutVal_add_sinks n P Q gs hreads y o ho]
    exact hne

end PEqualNP.Outside.L_meta_1024_aux.Cut

namespace PEqualNP.Outside.L_meta_1024_aux.PaidClamp
open PEqualNP.CircuitLowerBounds

lemma outside_true_row (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (w : Fin 13)
    (T : Finset (Fin (13 + gs.length))) (hT : T.card ≤ 8)
    (hforeign : ∀ i ∈ T, ∃ q : Fin 13,
      q ∉ Global.line w ∧ Global.val gs (Global.eof q) i.val = true) :
    ∃ x : Fin 13 → Bool, Support.Band x ∧ Support.target w x = false ∧
      ∀ i ∈ T, Global.val gs x i.val = true := by
  classical
  let q : Fin (13 + gs.length) → Fin 13 := fun i =>
    if h : i ∈ T then Classical.choose (hforeign i h) else 0
  have hq (i : Fin (13 + gs.length)) (hi : i ∈ T) :
      q i ∉ Global.line w ∧ Global.val gs (Global.eof (q i)) i.val = true := by
    simpa only [q, dite_eq_left hi] using Classical.choose_spec (hforeign i hi)
  let Q := T.image q
  have hQ : Q ⊆ Finset.univ \ Support.line w := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (hq i hi).1⟩
  have hQcard : Q.card ≤ 8 := Finset.card_image_le.trans hT
  obtain ⟨Y, hQY, hY, hYcard⟩ := Clamp.extend_eight w Q hQ hQcard
  refine ⟨Clamp.fromTrue Y, Clamp.fromTrue_band Y hYcard, Clamp.fromTrue_misses w Y hY, ?_⟩
  intro i hi
  have hqi : q i ∈ Y := hQY (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  apply Bridge.val_mono gs hg (Global.eof (q i)) (Clamp.fromTrue Y) _ i.val (hq i hi).2
  intro r hr
  have he : r = q i := by simpa [Global.eof] using hr
  subst r
  simp [Clamp.fromTrue, hqi]

set_option maxHeartbeats 2000000 in
lemma correct_and_bounded (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w : Fin 13) (P : Finset ℕ) (hP : ∀ i ∈ P, 13 ≤ i)
    (hPoutside : ∀ i ∈ P, ∃ q : Fin 13,
      q ∉ Global.line w ∧ Global.val gs (Global.eof q) i = true)
    (E : Finset (Fin (13 + gs.length))) (hEcard : E.card ≤ 12)
    (hallowed : ∀ i ∈ E, i.val < 13 ∨ i.val ∈ P)
    (hraw : ∀ p ∈ Global.line w, Bridge.rawIndex gs p ∈ E)
    (F : (Fin (13 + gs.length) → Bool) → Bool)
    (hmono : ∀ a b, (∀ i, a i = true → b i = true) → F a = true → F b = true)
    (hsupport : ∀ a b, (∀ i ∈ E, a i = b i) → F a = F b)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      F (fun i => Global.val gs x i.val) = Support.target w x) :
    (∀ x : Fin 13 → Bool, Support.target w x = false → F (Dead.trueSources gs x) = false) ∧
    (∀ x : Fin 13 → Bool, Support.Band x → F (Dead.trueSources gs x) = Support.target w x) := by
  classical
  let R := (Global.line w).image (Bridge.rawIndex gs)
  have hinj : Function.Injective (Bridge.rawIndex gs) := by
    intro p q hpq
    apply Fin.ext
    exact congrArg (fun i : Fin (13 + gs.length) => i.val) hpq
  have hRcard : R.card = 4 := by
    rw [Finset.card_image_of_injective _ hinj]
    exact Global.line_card w
  have hRE : R ⊆ E := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact hraw p hp
  let T := E \ R
  have hTcard : T.card ≤ 8 := by
    rw [Finset.card_sdiff_of_subset hRE, hRcard]
    omega
  have hforeign : ∀ i ∈ T, ∃ q : Fin 13,
      q ∉ Global.line w ∧ Global.val gs (Global.eof q) i.val = true := by
    intro i hi
    obtain ⟨hiE, hiR⟩ := Finset.mem_sdiff.mp hi
    rcases hallowed i hiE with hiraw | hipaid
    · let q : Fin 13 := ⟨i.val, hiraw⟩
      have hql : q ∉ Global.line w := by
        intro hq
        apply hiR
        exact Finset.mem_image.mpr ⟨q, hq, by apply Fin.ext; rfl⟩
      refine ⟨q, hql, ?_⟩
      change Global.val gs (Global.eof q) q.val = true
      rw [Bridge.val_input]
      simp [Global.eof]
    · exact hPoutside i.val hipaid
  obtain ⟨y, hyband, hyfalse, hyforeign⟩ := outside_true_row gs hg w T hTcard hforeign
  have hbound (x : Fin 13 → Bool) (hxt : Support.target w x = false) :
      F (Dead.trueSources gs x) = false := by
    cases hfx : F (Dead.trueSources gs x)
    · rfl
    · have hcompare : ∀ i ∈ E, Dead.trueSources gs x i = true → Global.val gs y i.val = true := by
        intro i hi hpos
        by_cases hiR : i ∈ R
        · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hiR
          have hxp : x p = false := (Finset.mem_filter.mp (Sink.false_target_zero w x hxt hp)).2
          have hh : Dead.trueSources gs x (Bridge.rawIndex gs p) = false := by
            simp [Dead.trueSources, Bridge.rawIndex, hxp]
          rw [hh] at hpos
          exact Bool.noConfusion hpos
        · exact hyforeign i (Finset.mem_sdiff.mpr ⟨hi, hiR⟩)
      have hytrue := Clamp.supported_mono F E hmono hsupport _ _ hcompare hfx
      have hyzero := (hcorrect y hyband).trans hyfalse
      rw [hyzero] at hytrue
      exact Bool.noConfusion hytrue
  refine ⟨hbound, ?_⟩
  intro x hx
  cases ht : Support.target w x
  · exact hbound x ht
  · have hpos : F (fun i => Global.val gs x i.val) = true := (hcorrect x hx).trans ht
    apply Clamp.supported_mono F E hmono hsupport _ _ _ hpos
    intro i hi hiv
    rcases hallowed i hi with hiraw | hipaid
    · let q : Fin 13 := ⟨i.val, hiraw⟩
      have he : Global.val gs x i.val = x q := Bridge.val_input gs x q
      rw [he] at hiv
      simpa only [Dead.trueSources, dite_eq_left hiraw] using hiv
    · have hn : ¬ i.val < 13 := by have := hP i.val hipaid; omega
      simp [Dead.trueSources, hn]

end PEqualNP.Outside.L_meta_1024_aux.PaidClamp

namespace PEqualNP.Outside.L_meta_1024_aux.AppendLine
open PEqualNP.CircuitLowerBounds

def pairGate (a b : Fin 13) : Gate := ⟨GateOp.or, [a.val, b.val]⟩

def appendLine (gs : List Gate) (w : Fin 13) : List Gate :=
  ((gs ++ [pairGate w (1 + w)]) ++ [pairGate (3 + w) (9 + w)]) ++
    [⟨GateOp.or, [13 + gs.length, 14 + gs.length]⟩]

lemma length (gs : List Gate) (w : Fin 13) : (appendLine gs w).length = gs.length + 3 := by
  simp [appendLine, Nat.add_assoc]

lemma allowed (gs : List Gate) (w : Fin 13)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ appendLine gs w, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hm
  simp only [appendLine, List.mem_append, List.mem_singleton] at hm
  rcases hm with ((hm | rfl) | rfl) | rfl
  · exact hg g hm
  · simp [pairGate]
  · simp [pairGate]
  · simp

lemma target_eq (w : Fin 13) (x : Fin 13 → Bool) :
    Support.target w x = ((x w || x (1 + w)) || (x (3 + w) || x (9 + w))) := by
  have he : Support.target w x = true ↔
      ((x w || x (1 + w)) || (x (3 + w) || x (9 + w))) = true := by
    simp [Support.target, Support.line, Finset.mem_image, Bool.or_eq_true, or_assoc]
  cases ht : Support.target w x <;>
    cases hv : ((x w || x (1 + w)) || (x (3 + w) || x (9 + w))) <;> simp_all

lemma eval (gs : List Gate) (w : Fin 13) (x : Fin 13 → Bool) :
    Global.val (appendLine gs w) x (15 + gs.length) = Support.target w x := by
  let l := pairGate w (1 + w)
  let r := pairGate (3 + w) (9 + w)
  let j : Gate := ⟨GateOp.or, [13 + gs.length, 14 + gs.length]⟩
  have hl : Global.val ((gs ++ [l]) ++ [r]) x (13 + gs.length) = (x w || x (1 + w)) := by
    rw [Global.val_snoc, ite_eq_right (by simp only [List.length_append, List.length_singleton]; omega), Global.val_snoc, ite_eq_left rfl]
    simp [l, pairGate, GateOp.eval, Bridge.val_input]
  have hr : Global.val ((gs ++ [l]) ++ [r]) x (14 + gs.length) = (x (3 + w) || x (9 + w)) := by
    rw [Global.val_snoc, ite_eq_left (by simp only [List.length_append, List.length_singleton]; omega)]
    simp [r, pairGate, GateOp.eval, Bridge.val_input]
  change Global.val (((gs ++ [l]) ++ [r]) ++ [j]) x (15 + gs.length) = _
  rw [Global.val_snoc, ite_eq_left (by simp only [List.length_append, List.length_singleton]; omega)]
  simp only [j, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rw [hl, hr]
  exact (target_eq w x).symm

lemma old (gs : List Gate) (w : Fin 13) (x : Fin 13 → Bool) (i : ℕ)
    (hi : i < 13 + gs.length) : Global.val (appendLine gs w) x i = Global.val gs x i := by
  have hs : appendLine gs w = gs ++ [pairGate w (1 + w), pairGate (3 + w) (9 + w),
      ⟨GateOp.or, [13 + gs.length, 14 + gs.length]⟩] := by simp [appendLine, List.append_assoc]
  rw [hs]
  exact Sink.val_append_old gs _ x i hi

lemma output_valid (gs : List Gate) (w : Fin 13) :
    13 ≤ 15 + gs.length ∧ 15 + gs.length < 13 + (appendLine gs w).length := by
  rw [length]
  omega

end PEqualNP.Outside.L_meta_1024_aux.AppendLine

namespace PEqualNP.Outside.L_meta_1024_aux.AppendLine
open PEqualNP.CircuitLowerBounds

def appendLines : List Gate → List (Fin 13) → List Gate
  | gs, [] => gs
  | gs, w :: ws => appendLines (appendLine gs w) ws

lemma lines_length (gs : List Gate) (ws : List (Fin 13)) :
    (appendLines gs ws).length = gs.length + 3 * ws.length := by
  induction ws generalizing gs with
  | nil => simp [appendLines]
  | cons w ws ih =>
    rw [appendLines, ih, length]
    simp only [List.length_cons]
    omega

lemma lines_allowed (gs : List Gate) (ws : List (Fin 13))
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ appendLines gs ws, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction ws generalizing gs with
  | nil => exact hg
  | cons w ws ih => exact ih (appendLine gs w) (allowed gs w hg)

lemma lines_old (gs : List Gate) (ws : List (Fin 13)) (x : Fin 13 → Bool) (i : ℕ)
    (hi : i < 13 + gs.length) : Global.val (appendLines gs ws) x i = Global.val gs x i := by
  induction ws generalizing gs with
  | nil => rfl
  | cons w ws ih =>
    exact (ih (appendLine gs w) (by rw [length]; omega)).trans (old gs w x i hi)

lemma lines_generated (gs : List Gate) (ws : List (Fin 13)) :
    ∀ w ∈ ws, ∃ i : ℕ, 13 ≤ i ∧ i < 13 + (appendLines gs ws).length ∧
      ∀ x : Fin 13 → Bool, Global.val (appendLines gs ws) x i = Support.target w x := by
  induction ws generalizing gs with
  | nil => simp
  | cons v ws ih =>
    intro w hw
    rcases List.mem_cons.mp hw with he | hw
    · subst w
      have hv := output_valid gs v
      refine ⟨15 + gs.length, hv.1, ?_, ?_⟩
      · rw [lines_length]
        simp only [List.length_cons]
        omega
      · intro x
        change Global.val (appendLines (appendLine gs v) ws) x (15 + gs.length) = _
        rw [lines_old _ _ _ _ hv.2]
        exact eval gs v x
    · exact ih (appendLine gs v) w hw

end PEqualNP.Outside.L_meta_1024_aux.AppendLine

namespace PEqualNP.Outside.L_meta_1024_aux.Dead
open PEqualNP.CircuitLowerBounds

lemma or_two (is : List ℕ) (his : is.length ≤ 2) (f : ℕ → Bool) (d : ℕ) (hd : f d = false) :
    GateOp.or.eval (is.map f) = (f (is.getD 0 d) || f (is.getD 1 d)) := by
  cases is with
  | nil => simp [GateOp.eval, hd]
  | cons a is =>
    cases is with
    | nil => simp [GateOp.eval, hd]
    | cons b is =>
      cases is with
      | nil => simp [GateOp.eval]
      | cons c is => simp at his

lemma deleted_or_pair (P : Finset ℕ) (gs : List Gate) (hreads : NoReads 13 P gs)
    (hsize : (code 13 P gs).length ≤ 7) (j : ℕ) (hj : j < gs.length)
    (hor : gs[j].op = GateOp.or) (hfan : gs[j].inputs.length ≤ 2) :
    ∃ a b : ℕ, ∀ x : Fin 13 → Bool, Global.val gs x (13 + j) =
      (Global.val (code 13 P gs) x a || Global.val (code 13 P gs) x b) := by
  let d := 13 + gs.length
  let ix : ℕ → ℕ := fun i => if i < 13 + j then (indices 13 P gs).getD i 0 else 20
  let a := ix (gs[j].inputs.getD 0 d)
  let b := ix (gs[j].inputs.getD 1 d)
  refine ⟨a, b, ?_⟩
  intro x
  have hz : Global.val (code 13 P gs) x 20 = false := val_invalid _ _ _ (by omega)
  have hmap : (fun i => if i < 13 + j then Global.val (code 13 P gs) x ((indices 13 P gs).getD i 0) else false) =
      (fun i => Global.val (code 13 P gs) x (ix i)) := by
    funext i
    by_cases hi : i < 13 + j <;> simp [ix, hi, hz]
  have hd : Global.val (code 13 P gs) x (ix d) = false := by
    have hn : ¬ d < 13 + j := by dsimp [d]; omega
    simp [ix, hn, hz]
  rw [deleted_formula P gs hreads x j hj, hor, hmap]
  exact or_two gs[j].inputs hfan (fun i => Global.val (code 13 P gs) x (ix i)) d hd

end PEqualNP.Outside.L_meta_1024_aux.Dead

namespace PEqualNP.Outside.L_meta_1024_aux.FourReduction
open PEqualNP.CircuitLowerBounds

lemma small_four_nonordinary (gs : List Gate) (hsize : gs.length ≤ 11)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin 4 → Fin 13) (hinj : Function.Injective lineId) (out : Fin 4 → ℕ)
    (hvalid : ∀ u, out u < 13 + gs.length)
    (hcorrect : ∀ u (x : Fin 13 → Bool), Support.Band x → Global.val gs x (out u) = Support.target (lineId u) x) :
    ∀ u, ¬ ∀ x : Fin 13 → Bool, Global.val gs x (out u) = Support.target (lineId u) x := by
  classical
  intro u₀ hexact
  let A : Finset (Fin 13) := Finset.univ.image lineId
  let W := Finset.univ \ A
  have hA : A.card = 4 := by
    rw [Finset.card_image_of_injective _ hinj]
    decide
  have hW : W.card = 9 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hA]
    decide
  have houtside (u : Fin 4) : lineId u ∉ W := by
    intro hu
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
  let cs := AppendLine.appendLines gs W.toList
  have hcs : cs.length ≤ 38 := by
    rw [AppendLine.lines_length, Finset.length_toList, hW]
    omega
  have hallowed := AppendLine.lines_allowed gs W.toList hg
  have hwitness : ∀ w : Fin 13, ∃ i : ℕ,
      (∀ x : Fin 13 → Bool, Support.Band x → Global.val cs x i = Support.target w x) ∧
      ((w ∈ W ∨ w = lineId u₀) → ∀ x : Fin 13 → Bool, Global.val cs x i = Support.target w x) := by
    intro w
    by_cases hw : w ∈ W
    · obtain ⟨i, _, _, hi⟩ := AppendLine.lines_generated gs W.toList w (by simpa using hw)
      exact ⟨i, fun x _ => hi x, fun _ => hi⟩
    · have hwA : w ∈ A := by simpa [W] using hw
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hwA
      have hold (x : Fin 13 → Bool) : Global.val cs x (out u) = Global.val gs x (out u) :=
        AppendLine.lines_old gs W.toList x (out u) (hvalid u)
      refine ⟨out u, ?_, ?_⟩
      · intro x hx
        exact (hold x).trans (hcorrect u x hx)
      · rintro (hu | he)
        · exact False.elim (hw hu)
        · have huu : u = u₀ := hinj he
          subst u
          intro x
          exact (hold x).trans (hexact x)
  choose out' hband hord using hwitness
  have hten : 10 ≤ (insert (lineId u₀) W).card := by
    rw [Finset.card_insert_of_notMem (houtside u₀), hW]
  have htenord : ∀ w ∈ insert (lineId u₀) W, ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨cs, out' w⟩ (List.ofFn x) = Support.target w x := by
    intro w hw
    rcases Finset.mem_insert.mp hw with he | hw
    · exact hord w (Or.inr he)
    · exact hord w (Or.inl hw)
  have hh := Bridge.ten_ordinary_bound cs out' hallowed hband (insert (lineId u₀) W) hten htenord
  omega

end PEqualNP.Outside.L_meta_1024_aux.FourReduction
namespace PEqualNP.Outside.L_meta_1024_aux.OneAnd

def line (w : Fin 13) : Finset (Fin 13) :=
  ({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)

def hit (S X : Finset (Fin 13)) : Bool := decide (∃ p ∈ S, p ∈ X)

lemma hit_true (S X : Finset (Fin 13)) (p : Fin 13) (hp : p ∈ S) (hx : p ∈ X) :
    hit S X = true := decide_eq_true ⟨p, hp, hx⟩

lemma hit_false (S X : Finset (Fin 13)) (h : Disjoint S X) : hit S X = false := by
  simp only [hit, decide_eq_false_iff_not]
  rintro ⟨p, hp, hx⟩
  exact Finset.disjoint_left.mp h hp hx

lemma line_card : ∀ w : Fin 13, (line w).card = 4 := by decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma line_meet : ∀ w u : Fin 13, w ≠ u → (line w ∩ line u).card = 1 := by decide +kernel

lemma outside_card (w : Fin 13) : (Finset.univ \ line w).card = 9 := by
  simp [Finset.card_sdiff, line_card]

lemma outside_row (w : Fin 13) (T : Finset (Fin 13)) (hT : Disjoint T (line w))
    (hc : T.card ≤ 7) :
    ∃ X, T ⊆ X ∧ X.card = 7 ∧ Disjoint (line w) X := by
  have hsub : T ⊆ Finset.univ \ line w := by
    intro p hp
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ p,
      fun h => Finset.disjoint_left.mp hT hp h⟩
  obtain ⟨X, hTX, hX, hcard⟩ := Finset.exists_subsuperset_card_eq hsub hc
    (by rw [outside_card]; omega)
  refine ⟨X, hTX, hcard, Finset.disjoint_left.mpr ?_⟩
  intro p hp hx
  exact (Finset.mem_sdiff.mp (hX hx)).2 hp

lemma one_point_row (w : Fin 13) (p : Fin 13) (hp : p ∈ line w) :
    ∃ X : Finset (Fin 13), X.card = 7 ∧ p ∈ X ∧
      ∀ q ∈ line w, q ∈ X → q = p := by
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq
    (show 6 ≤ (Finset.univ \ line w).card by rw [outside_card]; omega)
  have hn : p ∉ T := fun h => (Finset.mem_sdiff.mp (hT h)).2 hp
  refine ⟨insert p T, by simp [hn, hcard], Finset.mem_insert_self _ _, ?_⟩
  intro q hq hX
  rcases Finset.mem_insert.mp hX with h | h
  · exact h
  · exact ((Finset.mem_sdiff.mp (hT h)).2 hq).elim

def separatingRow (w u : Fin 13) (p : Fin 13) : Finset (Fin 13) :=
  insert p (Finset.univ \ (line w ∪ line u))

lemma separating_row (w u : Fin 13) (hwu : w ≠ u) (p : Fin 13)
    (hp : p ∈ line w) (hpu : p ∉ line u) :
    (separatingRow w u p).card = 7 ∧ p ∈ separatingRow w u p ∧
      Disjoint (line u) (separatingRow w u p) ∧
      ∀ q ∈ line w, q ∈ separatingRow w u p → q = p := by
  have hu : (line w ∪ line u).card = 7 := by
    have hc := Finset.card_union_add_card_inter (line w) (line u)
    rw [line_card, line_card, line_meet w u hwu] at hc
    omega
  have hn : p ∉ Finset.univ \ (line w ∪ line u) := by simp [hp]
  refine ⟨?_, Finset.mem_insert_self _ _, ?_, ?_⟩
  · simp [separatingRow, hn, Finset.card_sdiff, hu]
  · apply Finset.disjoint_left.mpr
    intro q hq hX
    rcases Finset.mem_insert.mp hX with h | h
    · exact hpu (h ▸ hq)
    · exact (Finset.mem_sdiff.mp h).2 (Finset.mem_union_right _ hq)
  · intro q hq hX
    rcases Finset.mem_insert.mp hX with h | h
    · exact h
    · exact ((Finset.mem_sdiff.mp h).2 (Finset.mem_union_left _ hq)).elim

end PEqualNP.Outside.L_meta_1024_aux.OneAnd


namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

open PEqualNP.CircuitLowerBounds

lemma three_triples_labels (A B C : Finset (Fin 13))
    (hAcard : A.card = 3) (hBcard : B.card = 3) (hCcard : C.card = 3)
    (hAB : Disjoint A B) (hAC : (A ∩ C).card ≤ 1) (hBC : (B ∩ C).card ≤ 1)
    (label : Fin 13 → ℕ) (a b c : ℕ)
    (hA : ∀ p ∈ A, label p = a) (hB : ∀ p ∈ B, label p = b)
    (hC : ∀ p ∈ C, label p = c) :
    6 + (((A ∪ B) ∪ C).image label).card ≤ ((A ∪ B) ∪ C).card := by
  have hABcard : (A ∪ B).card = 6 := by
    rw [Finset.card_union_of_disjoint hAB, hAcard, hBcard]
  have hdisj : Disjoint (A ∩ C) (B ∩ C) :=
    hAB.mono Finset.inter_subset_left Finset.inter_subset_left
  have hinter : ((A ∪ B) ∩ C).card = (A ∩ C).card + (B ∩ C).card := by
    have he : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
      ext p
      simp only [Finset.mem_inter, Finset.mem_union]
      tauto
    rw [he, Finset.card_union_of_disjoint hdisj]
  have hsum := Finset.card_union_add_card_inter (A ∪ B) C
  rw [hABcard, hCcard, hinter] at hsum
  have himage (K : Finset ℕ) (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) :
      (((A ∪ B) ∪ C).image label) ⊆ K := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact (hA p hp) ▸ ha
      · exact (hB p hp) ▸ hb
    · exact (hC p hp) ▸ hc
  by_cases ha : (A ∩ C).Nonempty
  · obtain ⟨p, hp⟩ := ha
    have hac : a = c := (hA p (Finset.mem_inter.mp hp).1).symm.trans
      (hC p (Finset.mem_inter.mp hp).2)
    by_cases hb : (B ∩ C).Nonempty
    · obtain ⟨q, hq⟩ := hb
      have hbc : b = c := (hB q (Finset.mem_inter.mp hq).1).symm.trans
        (hC q (Finset.mem_inter.mp hq).2)
      have hi := Finset.card_le_card (himage {c} (by simp [hac]) (by simp [hbc]) (by simp))
      simp only [Finset.card_singleton] at hi
      omega
    · have hb0 : (B ∩ C).card = 0 := by
        have hn : ¬ 0 < (B ∩ C).card := fun h => hb (Finset.card_pos.mp h)
        omega
      have hi := Finset.card_le_card (himage {b, c} (by simp [hac]) (by simp) (by simp))
      have hk : ({b, c} : Finset ℕ).card ≤ 2 := by
        simpa using List.toFinset_card_le [b, c]
      omega
  · have ha0 : (A ∩ C).card = 0 := by
      have hn : ¬ 0 < (A ∩ C).card := fun h => ha (Finset.card_pos.mp h)
      omega
    by_cases hb : (B ∩ C).Nonempty
    · obtain ⟨q, hq⟩ := hb
      have hbc : b = c := (hB q (Finset.mem_inter.mp hq).1).symm.trans
        (hC q (Finset.mem_inter.mp hq).2)
      have hi := Finset.card_le_card (himage {a, c} (by simp) (by simp [hbc]) (by simp))
      have hk : ({a, c} : Finset ℕ).card ≤ 2 := by
        simpa using List.toFinset_card_le [a, c]
      omega
    · have hb0 : (B ∩ C).card = 0 := by
        have hn : ¬ 0 < (B ∩ C).card := fun h => hb (Finset.card_pos.mp h)
        omega
      have hi := Finset.card_le_card (himage {a, b, c} (by simp) (by simp) (by simp))
      have hk : ({a, b, c} : Finset ℕ).card ≤ 3 := by
        simpa using List.toFinset_card_le [a, b, c]
      omega

lemma three_triples_lower (gs : List Gate) (o₁ o₂ o₃ : ℕ)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (A B C : Finset (Fin 13))
    (hAcard : A.card = 3) (hBcard : B.card = 3) (hCcard : C.card = 3)
    (hAB : Disjoint A B) (hAC : (A ∩ C).card ≤ 1) (hBC : (B ∩ C).card ≤ 1)
    (hA : ∀ p ∈ A, Cut.Depends 13 ∅ gs o₁ p)
    (hB : ∀ p ∈ B, Cut.Depends 13 ∅ gs o₂ p)
    (hC : ∀ p ∈ C, Cut.Depends 13 ∅ gs o₃ p) : 6 ≤ gs.length := by
  obtain ⟨label, wire, hcount, hdepends⟩ := Cut.components 13 ∅ ((A ∪ B) ∪ C) gs hg
  have hlabels := three_triples_labels A B C hAcard hBcard hCcard hAB hAC hBC
    label (wire o₁) (wire o₂) (wire o₃)
    (fun p hp => hdepends o₁ p (hA p hp))
    (fun p hp => hdepends o₂ p (hB p hp))
    (fun p hp => hdepends o₃ p (hC p hp))
  have hunpaid : Cut.unpaid 13 ∅ gs = gs.length := by
    rw [Cut.unpaid_eq_sub 13 ∅ gs (Finset.empty_subset _)]
    simp
  rw [hunpaid] at hcount
  omega

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks


namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

lemma four_two_ownership : ∀ (which : Fin 4 → Fin 2) (both : Fin 4 → Bool),
    (∀ a b, both a = true → both b = true → a = b) →
    ∃ a b c d : Fin 4,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      both a = false ∧ both b = false ∧ both c = false ∧
      which a = which b ∧ d ≠ c ∧
      (both d = true ∨ which d = which c) := by
  letI (which : Fin 4 → Fin 2) (both : Fin 4 → Bool) : Decidable
      (∃ a b c d : Fin 4,
        a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        both a = false ∧ both b = false ∧ both c = false ∧
        which a = which b ∧ d ≠ c ∧
        (both d = true ∨ which d = which c)) := by infer_instance
  decide

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks


namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

open PEqualNP.CircuitLowerBounds

lemma shared_parent_essential_band (a b : Fin 13) (hab : a ≠ b)
    (h k : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x → (h x || k x) = Support.target a x)
    (hupperh : ∀ x, Support.Band x → h x = true → Support.target b x = true)
    (hmono : ∀ x y, (∀ q, x q = true → y q = true) → k x = true → k y = true)
    (p : Fin 13) (hp : p ∈ Support.line a \ Support.line b) :
    ∃ x y : Fin 13 → Bool, (∀ q, q ≠ p → x q = y q) ∧ k x ≠ k y := by
  obtain ⟨hpa, hpb⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hcard, hpX, hBX, hAX⟩ := OneAnd.separating_row a b hab p hpa hpb
  let X := OneAnd.separatingRow a b p
  let x : Fin 13 → Bool := fun q => decide (q ∈ X)
  let y : Fin 13 → Bool := Function.update x p false
  have hzero : Support.zeroSet x = Finset.univ \ X := by
    ext q
    simp [Support.zeroSet, x]
  have hxband : Support.Band x := by
    apply Or.inr
    rw [hzero]
    simp [Finset.card_sdiff, show X.card = 7 from hcard]
  have hax : Support.target a x = true := by
    apply decide_eq_true
    exact ⟨p, hpa, by simp [x, X, hpX]⟩
  have hbx : Support.target b x = false := by
    simp only [Support.target, decide_eq_false_iff_not]
    rintro ⟨q, hqb, hqx⟩
    have hqX : q ∈ X := by simpa [x] using hqx
    exact Finset.disjoint_left.mp hBX hqb hqX
  have hhx : h x = false := by
    cases he : h x with
    | false => rfl
    | true =>
      have ht := hupperh x hxband he
      rw [hbx] at ht
      cases ht
  have hkx : k x = true := by
    have he := hcorrect x hxband
    simpa only [hhx, Bool.false_or, hax] using he
  let T := X.erase p
  have hTsub : T ⊆ Finset.univ \ Support.line a := by
    intro q hq
    obtain ⟨hqp, hqX⟩ := Finset.mem_erase.mp hq
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ q, fun hqa => hqp (hAX q hqa hqX)⟩
  have hTcard : T.card ≤ 8 := by
    have hle := Finset.card_le_card (Finset.erase_subset p X)
    change T.card ≤ X.card at hle
    have hc : X.card = 7 := hcard
    omega
  obtain ⟨Y, hTY, hYsub, hYcard⟩ := Clamp.extend_eight a T hTsub hTcard
  have hyY : ∀ q, y q = true → Clamp.fromTrue Y q = true := by
    intro q hyq
    apply decide_eq_true
    apply hTY
    apply Finset.mem_erase.mpr
    by_cases hqp : q = p
    · simp [y, hqp] at hyq
    · refine ⟨hqp, ?_⟩
      simpa [y, Function.update_of_ne hqp, x] using hyq
  have hky : k y = false := by
    cases he : k y with
    | false => rfl
    | true =>
      have hkY := hmono y (Clamp.fromTrue Y) hyY he
      have ht := hcorrect (Clamp.fromTrue Y) (Clamp.fromTrue_band Y hYcard)
      rw [hkY, Bool.or_true, Clamp.fromTrue_misses a Y hYsub] at ht
      cases ht
  refine ⟨x, y, ?_, ?_⟩
  · intro q hqp
    simp [y, Function.update_of_ne hqp]
  · rw [hkx, hky]
    decide

lemma shared_parent_cut_depends_band (gs : List Gate) (o : ℕ)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : Fin 13) (hab : a ≠ b) (h : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x →
      (h x || Cut.cutVal 13 ∅ gs x o) = Support.target a x)
    (hupperh : ∀ x, Support.Band x → h x = true → Support.target b x = true)
    (p : Fin 13) (hp : p ∈ Support.line a \ Support.line b) :
    Cut.Depends 13 ∅ gs o p := by
  exact shared_parent_essential_band a b hab h (fun x => Cut.cutVal 13 ∅ gs x o)
    hcorrect hupperh (fun x y hxy => Cut.cutVal_mono 13 ∅ gs hg x y hxy o) p hp

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

open PEqualNP.CircuitLowerBounds

lemma high_network_lower_band (gs : List Gate) (out : Fin 4 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin 4 → Fin 13) (hinj : Function.Injective lineId)
    (which : Fin 4 → Fin 2) (both : Fin 4 → Bool)
    (high : Fin 2 → (Fin 13 → Bool) → Bool)
    (f : Fin 4 → (Fin 13 → Bool) → Bool)
    (hsingle : ∀ w, both w = false → ∀ x,
      f w x = (high (which w) x || Cut.cutVal 13 ∅ gs x (out w)))
    (hdouble : ∀ w, both w = true → ∀ x,
      f w x = (high 0 x || high 1 x))
    (hcorrect : ∀ w x, Support.Band x → f w x = Support.target (lineId w) x) :
    6 ≤ gs.length := by
  have hboth_unique : ∀ a b, both a = true → both b = true → a = b := by
    intro a b ha hb
    by_contra hab
    have hne : lineId a ≠ lineId b := fun h => hab (hinj h)
    let x := Support.row (lineId a)
    have hx : Support.Band x := Or.inr (Support.row_spec (lineId a)).1
    have hae := hcorrect a x hx
    have hbe := hcorrect b x hx
    rw [hdouble a ha] at hae
    rw [hdouble b hb] at hbe
    have he := hae.symm.trans hbe
    rw [(Support.row_spec (lineId a)).2, Bridge.row_targets (lineId a) (lineId b) hne] at he
    cases he
  obtain ⟨a, b, c, d, hab, hac, hbc, ha, hb, hc, habhigh, hdc, hcdhigh⟩ :=
    four_two_ownership which both hboth_unique
  have high_upper (w u : Fin 4)
      (huse : both u = true ∨ which u = which w) :
      ∀ x, Support.Band x → high (which w) x = true →
        Support.target (lineId u) x = true := by
    intro x hxband hx
    rw [← hcorrect u x hxband]
    cases hu : both u with
    | false =>
      have he : which u = which w := huse.resolve_left (by simp [hu])
      rw [hsingle u hu, he, hx]
      simp
    | true =>
      rw [hdouble u hu]
      have he := (which w).isLt
      have hi : which w = 0 ∨ which w = 1 := by omega
      rcases hi with hi | hi
      · simp [← hi, hx]
      · simp [← hi, hx]
  have low_dep (w u : Fin 4) (hwu : w ≠ u) (hw : both w = false)
      (huse : both u = true ∨ which u = which w) :
      ∀ p ∈ Support.line (lineId w) \ Support.line (lineId u),
        Cut.Depends 13 ∅ gs (out w) p := by
    intro p hp
    apply shared_parent_cut_depends_band gs (out w) (fun g hm => (hg g hm).1)
      (lineId w) (lineId u)
      (fun he => hwu (hinj he)) (high (which w))
    · intro x hx
      rw [← hsingle w hw]
      exact hcorrect w x hx
    · exact high_upper w u huse
    · exact hp
  let A := Support.line (lineId a) \ Support.line (lineId b)
  let B := Support.line (lineId b) \ Support.line (lineId a)
  let C := Support.line (lineId c) \ Support.line (lineId d)
  have hline_card (w u : Fin 4) (hwu : w ≠ u) :
      (Support.line (lineId w) \ Support.line (lineId u)).card = 3 := by
    have hne : lineId w ≠ lineId u := fun h => hwu (hinj h)
    have hl := OneAnd.line_card (lineId w)
    have hm := OneAnd.line_meet (lineId w) (lineId u) hne
    change (Support.line (lineId w)).card = 4 at hl
    change (Support.line (lineId w) ∩ Support.line (lineId u)).card = 1 at hm
    rw [Finset.card_sdiff, hl, Finset.inter_comm, hm]
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro p hpA hpB
    exact (Finset.mem_sdiff.mp hpA).2 (Finset.mem_sdiff.mp hpB).1
  have hAC : (A ∩ C).card ≤ 1 := by
    have hsub : A ∩ C ⊆ Support.line (lineId a) ∩ Support.line (lineId c) := by
      intro p hp
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).1).1,
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).2).1⟩
    have hsmall := Global.line_intersection (lineId a) (lineId c)
      (fun he => hac (hinj he))
    exact (Finset.card_le_card hsub).trans hsmall
  have hBC : (B ∩ C).card ≤ 1 := by
    have hsub : B ∩ C ⊆ Support.line (lineId b) ∩ Support.line (lineId c) := by
      intro p hp
      exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).1).1,
        (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).2).1⟩
    have hsmall := Global.line_intersection (lineId b) (lineId c)
      (fun he => hbc (hinj he))
    exact (Finset.card_le_card hsub).trans hsmall
  exact three_triples_lower gs (out a) (out b) (out c) (fun g hm => (hg g hm).2) A B C
    (hline_card a b hab) (hline_card b a hab.symm) (hline_card c d hdc.symm)
    hAB hAC hBC (low_dep a b hab ha (Or.inr habhigh.symm))
    (low_dep b a hab.symm hb (Or.inr habhigh)) (low_dep c d hdc.symm hc hcdhigh)

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

open PEqualNP.CircuitLowerBounds

lemma cut_ge_false (gs : List Gate) (x : Fin 13 → Bool) (i : ℕ)
    (hi : 13 + gs.length ≤ i) : Cut.cutVal 13 ∅ gs x i = false := by
  unfold Cut.cutVal
  apply List.getD_eq_default
  rw [Cut.run_length]
  exact hi

lemma low_prefix_value (gs : List Gate) (hsize : gs.length ≤ 7)
    (i : ℕ) (hi0 : i ≠ 18) (hi1 : i ≠ 19) (x : Fin 13 → Bool) :
    Cut.cutVal 13 ∅ gs x i = Cut.cutVal 13 ∅ (gs.take 5) x i := by
  by_cases hs : 5 ≤ gs.length
  · by_cases hi : i < 18
    · exact Cut.cutVal_take 13 ∅ gs x 5 i hs hi
    · have hi20 : 20 ≤ i := by omega
      rw [cut_ge_false gs x i (by omega),
        cut_ge_false (gs.take 5) x i (by simp only [List.length_take]; omega)]
  · have hs5 : gs.length ≤ 5 := by omega
    rw [List.take_of_length_le hs5]

lemma low_pair_exact (gs : List Gate) (hsize : gs.length ≤ 7)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (i j : ℕ)
    (hi0 : i ≠ 18) (hi1 : i ≠ 19) (hj0 : j ≠ 18) (hj1 : j ≠ 19)
    (hcorrect : ∀ x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x) :
    ∀ x, (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) = Support.target w x := by
  let pre := gs.take 5
  let g : Gate := ⟨GateOp.or, [i, j]⟩
  let code := pre ++ [g]
  let o := 13 + pre.length
  have hval (x : Fin 13 → Bool) :
      Cut.cutVal 13 ∅ code x o =
        (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) := by
    rw [low_prefix_value gs hsize i hi0 hi1 x, low_prefix_value gs hsize j hj0 hj1 x]
    change Cut.cutVal 13 ∅ (pre ++ [g]) x (13 + pre.length) = _
    rw [Cut.cutVal_snoc]
    simp [g, GateOp.eval, pre]
  have hcode : ∀ q ∈ code, (q.op = GateOp.and ∨ q.op = GateOp.or) ∧ q.inputs.length ≤ 2 := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hg q (List.mem_of_mem_take hq)
    · have he : q = g := by simpa using hq
      subst q
      simp [g]
  let E := Cut.essential (M := 13) 13 ∅ code o
  have hE : E.card ≤ 7 := by
    have he := Cut.essential_bound (M := 13) 13 ∅ code o (fun q hq => (hcode q hq).2)
      (Finset.empty_subset _)
    have hlen : code.length ≤ 6 := by
      simp only [code, List.length_append, List.length_singleton, pre, List.length_take]
      omega
    simp only [Finset.card_empty, Nat.sub_zero] at he
    exact he.trans (by omega)
  have hband : ∀ x, Support.Band x → Circuit.eval ⟨code, o⟩ (List.ofFn x) = Support.target w x := by
    intro x hx
    rw [← Cut.cut_empty, hval]
    exact hcorrect x hx
  have hsupp : Support.Supports (fun x => Circuit.eval ⟨code, o⟩ (List.ofFn x)) E := by
    intro x y hxy
    simpa only [Cut.cut_empty] using Cut.essential_supports 13 ∅ code o x y hxy
  have he : ∀ x, Cut.cutVal 13 ∅ code x o = Support.target w x := by
    simpa only [Cut.cut_empty] using Support.circuit_support_exact code o w
      (fun q hq => (hcode q hq).1) hband E hE hsupp
  intro x
  rw [← hval, he]

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

open PEqualNP.CircuitLowerBounds

lemma pair_representation (gs : List Gate) (hsize : gs.length ≤ 7) (i j : ℕ)
    (hhigh : i = 18 ∨ i = 19 ∨ j = 18 ∨ j = 19) :
    ∃ (both : Bool) (which : Fin 2) (o : ℕ),
      (both = false → ∀ x : Fin 13 → Bool,
        (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) =
          (Cut.cutVal 13 ∅ gs x (18 + which.val) || Cut.cutVal 13 ∅ (gs.take 5) x o)) ∧
      (both = true → ∀ x : Fin 13 → Bool,
        (Cut.cutVal 13 ∅ gs x i || Cut.cutVal 13 ∅ gs x j) =
          (Cut.cutVal 13 ∅ gs x 18 || Cut.cutVal 13 ∅ gs x 19)) := by
  have hfalse (x : Fin 13 → Bool) : Cut.cutVal 13 ∅ (gs.take 5) x 20 = false :=
    cut_ge_false (gs.take 5) x 20 (by simp only [List.length_take]; omega)
  by_cases hi0 : i = 18
  · subst i
    by_cases hj1 : j = 19
    · refine ⟨true, 0, 20, by simp, ?_⟩
      intro _ x
      rw [hj1]
    · by_cases hj0 : j = 18
      · refine ⟨false, 0, 20, ?_, by simp⟩
        intro _ x
        simp [hj0, hfalse]
      · refine ⟨false, 0, j, ?_, by simp⟩
        intro _ x
        simpa using congrArg (fun z => Cut.cutVal 13 ∅ gs x 18 || z)
          (low_prefix_value gs hsize j hj0 hj1 x)
  · by_cases hi1 : i = 19
    · subst i
      by_cases hj0 : j = 18
      · refine ⟨true, 0, 20, by simp, ?_⟩
        intro _ x
        simp [hj0, Bool.or_comm]
      · by_cases hj1 : j = 19
        · refine ⟨false, 1, 20, ?_, by simp⟩
          intro _ x
          simp [hj1, hfalse]
        · refine ⟨false, 1, j, ?_, by simp⟩
          intro _ x
          simpa using congrArg (fun z => Cut.cutVal 13 ∅ gs x 19 || z)
            (low_prefix_value gs hsize j hj0 hj1 x)
    · have hj : j = 18 ∨ j = 19 := by tauto
      rcases hj with hj | hj
      · refine ⟨false, 0, i, ?_, by simp⟩
        intro _ x
        rw [hj, low_prefix_value gs hsize i hi0 hi1 x]
        simp [Bool.or_comm]
      · refine ⟨false, 1, i, ?_, by simp⟩
        intro _ x
        rw [hj, low_prefix_value gs hsize i hi0 hi1 x]
        simp [Bool.or_comm]

lemma four_pairs_impossible (gs : List Gate) (hsize : gs.length ≤ 7)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin 4 → Fin 13) (hinj : Function.Injective lineId)
    (left right : Fin 4 → ℕ)
    (hcorrect : ∀ w x, Support.Band x →
      (Cut.cutVal 13 ∅ gs x (left w) || Cut.cutVal 13 ∅ gs x (right w)) =
        Support.target (lineId w) x)
    (hnotexact : ∀ w, ¬ ∀ x : Fin 13 → Bool,
      (Cut.cutVal 13 ∅ gs x (left w) || Cut.cutVal 13 ∅ gs x (right w)) =
        Support.target (lineId w) x) : False := by
  have hhigh (w : Fin 4) : left w = 18 ∨ left w = 19 ∨ right w = 18 ∨ right w = 19 := by
    by_contra h
    push Not at h
    exact hnotexact w (low_pair_exact gs hsize hg (lineId w) (left w) (right w)
      h.1 h.2.1 h.2.2.1 h.2.2.2 (hcorrect w))
  have hrep (w : Fin 4) := pair_representation gs hsize (left w) (right w) (hhigh w)
  choose both which out hsingle hdouble using hrep
  have hcount := high_network_lower_band (gs.take 5) out
    (fun g hgmem => hg g (List.mem_of_mem_take hgmem)) lineId hinj which both
    (fun u x => Cut.cutVal 13 ∅ gs x (18 + u.val))
    (fun w x => Cut.cutVal 13 ∅ gs x (left w) || Cut.cutVal 13 ∅ gs x (right w))
    hsingle hdouble hcorrect
  simp only [List.length_take] at hcount
  omega

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks


namespace PEqualNP.Outside.L_meta_1024_aux.FourReduction
open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 4000000 in
lemma four_or_sink_bound (gs : List Gate) (out : Fin 13 → ℕ)
    (lineId : Fin 4 → Fin 13) (hinj : Function.Injective lineId)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ w (x : Fin 13 → Bool), Support.Band x → Global.val gs x (out w) = Support.target w x)
    (hordinary : ∀ w ∉ Finset.univ.image lineId, ∀ x : Fin 13 → Bool,
      Global.val gs x (out w) = Support.target w x)
    (hsinks : Dead.NoReads 13 (Finset.univ.image (fun u : Fin 4 => out (lineId u))) gs)
    (hor : ∀ u : Fin 4, ∃ j : ℕ, ∃ hj : j < gs.length,
      out (lineId u) = 13 + j ∧ gs[j].op = GateOp.or) : 39 ≤ gs.length := by
  classical
  by_contra! hsmall
  let A : Finset (Fin 13) := Finset.univ.image lineId
  let W := Finset.univ \ A
  let Q : Finset ℕ := Finset.univ.image (fun u : Fin 4 => out (lineId u))
  have houtinj := Bridge.output_distinct gs out hcorrect
  have hindex (w : Fin 13) := Bridge.output_index gs (out w) w (hcorrect w)
  have hA : A.card = 4 := by rw [Finset.card_image_of_injective _ hinj]; decide
  have hW : W.card = 9 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hA]
    decide
  have hQ : Q.card = 4 := by
    have hi : Function.Injective (fun u : Fin 4 => out (lineId u)) := houtinj.comp hinj
    change (Finset.univ.image (fun u : Fin 4 => out (lineId u))).card = 4
    rw [Finset.card_image_of_injective _ hi]
    decide
  have hnotW (u : Fin 4) : lineId u ∉ W := by
    intro hu
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
  have hord : ∀ w ∈ W, ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = decide (∃ p ∈ Global.line w, x p = true) := by
    intro w hw x
    change Global.val gs x (out w) = Support.target w x
    exact hordinary w (Finset.mem_sdiff.mp hw).2 x
  obtain ⟨P, hP, hPcount, hPprops⟩ := Charges.ordinary_charge_family_strong gs out W hg hord
  have hP27 : 27 ≤ P.card := by simpa [hW] using hPcount
  have hPupper : P.card ≤ gs.length := by simpa using Finset.card_le_card hP
  have hPraw : ∀ i ∈ P, 13 ≤ i := fun i hi => (Finset.mem_Ico.mp (hP hi)).1
  have hnotP (u : Fin 4) : out (lineId u) ∉ P := by
    intro hu
    obtain ⟨x, hx, hxt, hxf⟩ := (hPprops (lineId u) (hnotW u) _ hu).2
    have hh := hcorrect (lineId u) x hx
    rw [hxf, hxt] at hh
    exact Bool.noConfusion hh
  have hdisj : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro i hiP hiQ
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hiQ
    exact hnotP u hiP
  have hQsub : Q ⊆ Finset.Ico 13 (13 + gs.length) := by
    intro i hi
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_Ico.mpr (hindex (lineId u))
  let E (u : Fin 4) := Cut.essential (M := 13 + gs.length) 13 P gs (out (lineId u))
  have hE9 (u : Fin 4) : (E u).card ≤ 9 := by
    let R := Q.erase (out (lineId u))
    have hoQ : out (lineId u) ∈ Q := Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    have hR : R.card = 3 := by rw [Finset.card_erase_of_mem hoQ, hQ]
    have hRsub : R ⊆ Q := Finset.erase_subset _ _
    have hPR : Disjoint P R := hdisj.mono_right hRsub
    have hcount : 30 ≤ (P ∪ R).card := by
      rw [Finset.card_union_of_disjoint hPR, hR]
      omega
    have hsub : P ∪ R ⊆ Finset.Ico 13 (13 + gs.length) :=
      Finset.union_subset hP (hRsub.trans hQsub)
    have hupper : (P ∪ R).card ≤ gs.length := by simpa using Finset.card_le_card hsub
    have hreads : Dead.NoReads 13 R gs := by
      intro j hj i hi hn hiR
      exact hsinks j hj i hi hn (hRsub hiR)
    have heq := Cut.essential_add_sinks (M := 13 + gs.length) 13 P R gs hreads
      (out (lineId u)) (by simp [R])
    have hb := Cut.essential_bound (M := 13 + gs.length) 13 (P ∪ R) gs (out (lineId u))
      (fun g hm => (hg g hm).2) hsub
    rw [heq] at hb
    change (E u).card ≤ _ at hb
    omega
  have hraw (u : Fin 4) (p : Fin 13) (hp : p ∈ Global.line (lineId u)) : Bridge.rawIndex gs p ∈ E u := by
    apply Bridge.raw_line_members9 gs (out (lineId u)) (lineId u) (fun g hm => (hg g hm).1)
      (hcorrect (lineId u)) P
      (fun i hi => (hPprops (lineId u) (hnotW u) i hi).1)
      (fun i hi => (hPprops (lineId u) (hnotW u) i hi).2)
      (fun z => Cut.cutVal 13 P gs z (out (lineId u))) (E u) (hE9 u)
    · exact Cut.essential_sources 13 P gs (out (lineId u))
    · intro x y hxy hx
      exact Cut.cutVal_mono 13 P gs (fun g hm => (hg g hm).1) x y hxy (out (lineId u)) hx
    · exact Cut.essential_supports 13 P gs (out (lineId u))
    · intro x
      exact Cut.factor P gs x (out (lineId u))
    · exact hp
  have hclamped (u : Fin 4) : ∀ x : Fin 13 → Bool, Support.Band x →
      Cut.cutVal 13 P gs (Dead.trueSources gs x) (out (lineId u)) = Support.target (lineId u) x := by
    apply (PaidClamp.correct_and_bounded gs (fun g hm => (hg g hm).1) (lineId u) P hPraw
      (fun i hi => (hPprops (lineId u) (hnotW u) i hi).1) (E u) (by have := hE9 u; omega)
      (Cut.essential_sources 13 P gs (out (lineId u))) (hraw u)
      (fun z => Cut.cutVal 13 P gs z (out (lineId u))) ?_ ?_ ?_).2
    · intro x y hxy hx
      exact Cut.cutVal_mono 13 P gs (fun g hm => (hg g hm).1) x y hxy (out (lineId u)) hx
    · exact Cut.essential_supports 13 P gs (out (lineId u))
    · intro x hx
      exact (Cut.factor P gs x (out (lineId u))).trans (hcorrect (lineId u) x hx)
  let C := Sink.transform 13 P gs
  have hCsize : C.length = gs.length := Sink.transform_length 13 P gs
  have hCallowed := Sink.transform_allowed 13 P gs hg
  have hCval (u : Fin 4) (x : Fin 13 → Bool) : Global.val C x (out (lineId u)) =
      Cut.cutVal 13 P gs (Dead.trueSources gs x) (out (lineId u)) :=
    Sink.transform_cut_output P gs (fun g hm => (hg g hm).1) hPraw x (Dead.trueSources gs x)
      (Dead.trueSources_input gs x) (fun i _ hn hi => Dead.trueSources_paid gs x i hn hi) _ (hnotP u)
  have hCcorrect (u : Fin 4) (x : Fin 13 → Bool) (hx : Support.Band x) :
      Global.val C x (out (lineId u)) = Support.target (lineId u) x := (hCval u x).trans (hclamped u x hx)
  have hCreads : Dead.NoReads 13 (P ∪ Q) C := Dead.noReads_union 13 P Q C
    (Dead.transform_noReads 13 P gs) (Sink.preserves_noReads 13 P Q gs hsinks)
  let I := Dead.code 13 (P ∪ Q) C
  have hPQ : P ∪ Q ⊆ Finset.Ico 13 (13 + C.length) := by
    rw [hCsize]
    exact Finset.union_subset hP hQsub
  have hPQcard : 31 ≤ (P ∪ Q).card := by
    rw [Finset.card_union_of_disjoint hdisj, hQ]
    omega
  have hPQupper : (P ∪ Q).card ≤ C.length := by simpa using Finset.card_le_card hPQ
  have hI : I.length ≤ 7 := by
    rw [Dead.code_length, Cut.unpaid_eq_sub 13 (P ∪ Q) C hPQ]
    omega
  have hIallowed := Dead.code_allowed 13 (P ∪ Q) C hCallowed
  have hpair : ∀ u : Fin 4, ∃ a b : ℕ, ∀ x : Fin 13 → Bool, Global.val C x (out (lineId u)) =
      (Global.val I x a || Global.val I x b) := by
    intro u
    obtain ⟨j, hj, hout, hOR⟩ := hor u
    have hjC : j < C.length := by rwa [hCsize]
    have hfalse : Global.val C (Support.row (lineId u)) (13 + j) = false := by
      rw [← hout]
      exact (hCcorrect u _ (Or.inr (Support.row_spec (lineId u)).1)).trans (Support.row_spec (lineId u)).2
    have hORC : C[j].op = GateOp.or := Sink.or_preserved_of_false P gs j hj hOR _ hfalse
    have hfan := (hCallowed C[j] (List.getElem_mem hjC)).2
    have hh := Dead.deleted_or_pair (P ∪ Q) C hCreads hI j hjC hORC hfan
    simpa only [← hout] using hh
  choose left right hpair using hpair
  let U := Dead.paidCode 13 P gs
  let outU : Fin 4 → ℕ := fun u => Dead.paidIndex 13 P gs (out (lineId u))
  have hUsize : U.length ≤ 11 := by
    rw [Dead.paid_length, Cut.unpaid_eq_sub 13 P gs hP]
    omega
  have hUallowed := Dead.paid_allowed 13 P gs hg
  have hUvalid (u : Fin 4) : outU u < 13 + U.length :=
    Dead.mapped_valid 13 P C (out (lineId u)) (by rw [hCsize]; exact (hindex (lineId u)).2) (hnotP u)
  have hUval (u : Fin 4) (x : Fin 13 → Bool) : Global.val U x (outU u) = Global.val C x (out (lineId u)) :=
    Dead.eval P C (Dead.transform_noReads 13 P gs) x (out (lineId u))
      (by rw [hCsize]; exact (hindex (lineId u)).2) (hnotP u)
  have hUnon := small_four_nonordinary U hUsize hUallowed lineId hinj outU hUvalid
    (fun u x hx => (hUval u x).trans (hCcorrect u x hx))
  have hcut (x : Fin 13 → Bool) (i : ℕ) : Cut.cutVal 13 ∅ I x i = Global.val I x i := Cut.cut_empty I x i
  apply FourOrSinks.four_pairs_impossible I hI hIallowed lineId hinj left right
  · intro u x hx
    rw [hcut, hcut, ← hpair u x]
    exact hCcorrect u x hx
  · intro u hexact
    apply hUnon u
    intro x
    rw [hUval, hpair u x, ← hcut, ← hcut]
    exact hexact x

end PEqualNP.Outside.L_meta_1024_aux.FourReduction

namespace PEqualNP.Outside.L_meta_1024_aux.TrueClamp

open PEqualNP.CircuitLowerBounds

noncomputable def constants (n : ℕ) (gs : List Gate) : Finset ℕ :=
  (Finset.Ico n (n + gs.length)).filter
    (fun i => Global.val gs (fun _ : Fin n => false) i = true)

lemma constant_value {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) (i : ℕ) (hi : i ∈ constants n gs) : Global.val gs x i = true := by
  have hz := (Finset.mem_filter.mp hi).2
  change Circuit.eval ⟨gs, i⟩ (List.ofFn (fun _ : Fin n => false)) = true at hz
  change Circuit.eval ⟨gs, i⟩ (List.ofFn x) = true
  rw [← Cut.cut_empty] at hz ⊢
  exact Cut.cutVal_mono n ∅ gs hg (fun _ => false) x (by intro p hp; cases hp) i hz

lemma constant_transform_eq {n : ℕ} (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x : Fin n → Bool) (i : ℕ) :
    Global.val (Sink.transform n (constants n gs) gs) x i = Global.val gs x i := by
  exact Sink.prefix_eq (constants n gs) gs hg x (n + gs.length) (by omega)
    (fun j hj _ _ => constant_value gs hg x j hj) i

lemma and_preserved (n : ℕ) (P : Finset ℕ) (gs : List Gate) (j : ℕ)
    (hj : j < gs.length) (hand : gs[j].op = GateOp.and) :
    ((Sink.transform n P gs)[j]'(by rw [Sink.transform_length]; exact hj)).op = GateOp.and := by
  rw [Sink.transform_get n P gs j hj]
  unfold Sink.gate
  split
  · rename_i h
    have he := h.1
    rw [hand] at he
  · exact hand

noncomputable def intermediate (n : ℕ) (S : Finset ℕ) (gs : List Gate) : List Gate :=
  Sink.transform n S gs

noncomputable def allDeleted (n : ℕ) (S : Finset ℕ) (gs : List Gate) : Finset ℕ :=
  S ∪ constants n (intermediate n S gs)

noncomputable def prepared (n : ℕ) (S : Finset ℕ) (gs : List Gate) : List Gate :=
  Sink.transform n (constants n (intermediate n S gs)) (intermediate n S gs)

noncomputable def clean (n : ℕ) (S : Finset ℕ) (gs : List Gate) : List Gate :=
  Dead.code n (allDeleted n S gs) (prepared n S gs)

noncomputable def cleanIndex (n : ℕ) (S : Finset ℕ) (gs : List Gate) (i : ℕ) : ℕ :=
  (Dead.indices n (allDeleted n S gs) (prepared n S gs)).getD i 0

lemma intermediate_length (n : ℕ) (S : Finset ℕ) (gs : List Gate) :
    (intermediate n S gs).length = gs.length := Sink.transform_length n S gs

lemma prepared_length (n : ℕ) (S : Finset ℕ) (gs : List Gate) :
    (prepared n S gs).length = gs.length := by
  simp only [prepared, intermediate, Sink.transform_length]

lemma prepared_noReads (n : ℕ) (S : Finset ℕ) (gs : List Gate) :
    Dead.NoReads n (allDeleted n S gs) (prepared n S gs) := by
  apply Dead.noReads_union
  · exact Sink.preserves_noReads n (constants n (intermediate n S gs)) S
      (intermediate n S gs) (Dead.transform_noReads n S gs)
  · exact Dead.transform_noReads n (constants n (intermediate n S gs)) _

lemma clean_eval {n : ℕ} (S : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin n → Bool) (i : ℕ) (hi : i < n + gs.length)
    (hkeep : i ∉ allDeleted n S gs) :
    Global.val (clean n S gs) x (cleanIndex n S gs i) =
      Global.val (intermediate n S gs) x i := by
  rw [clean, cleanIndex, Dead.eval (allDeleted n S gs) (prepared n S gs)
    (prepared_noReads n S gs) x i (by rwa [prepared_length]) hkeep]
  exact constant_transform_eq (intermediate n S gs)
    (fun g hm => (Sink.transform_allowed n S gs hg g hm).1) x i

lemma clean_allowed (n : ℕ) (S : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ clean n S gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  exact Dead.code_allowed n (allDeleted n S gs) (prepared n S gs)
    (Sink.transform_allowed n _ _ (Sink.transform_allowed n S gs hg))

lemma clean_length_le (n : ℕ) (S : Finset ℕ) (gs : List Gate)
    (hS : S ⊆ Finset.Ico n (n + gs.length)) :
    (clean n S gs).length ≤ gs.length - S.card := by
  rw [clean, Dead.code_length]
  have hsub : Finset.Ico n (n + gs.length) \ allDeleted n S gs ⊆
      Finset.Ico n (n + gs.length) \ S := by
    intro i hi
    refine Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hi).1, ?_⟩
    intro hiS
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiS)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hS] at hc
  simpa only [Cut.unpaid, prepared_length, Nat.card_Ico, Nat.add_sub_cancel_left] using hc

lemma prepared_op_kept (n : ℕ) (S : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (j : ℕ) (hj : j < gs.length) (hkeep : n + j ∉ allDeleted n S gs) :
    ((prepared n S gs)[j]'(by rw [prepared_length]; exact hj)).op = gs[j].op := by
  have hjt : j < (intermediate n S gs).length := by rwa [intermediate_length]
  have hnotconst : n + j ∉ constants n (intermediate n S gs) :=
    fun h => hkeep (Finset.mem_union_right _ h)
  have hz : Global.val (intermediate n S gs) (fun _ : Fin n => false) (n + j) = false := by
    cases he : Global.val (intermediate n S gs) (fun _ : Fin n => false) (n + j) with
    | false => rfl
    | true =>
      apply False.elim
      apply hnotconst
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, he⟩
  have hmono : ∀ g ∈ intermediate n S gs, g.op = GateOp.and ∨ g.op = GateOp.or :=
    fun g hm => (Sink.transform_allowed n S gs hg g hm).1
  have huz : Global.val (prepared n S gs) (fun _ : Fin n => false) (n + j) = false :=
    (constant_transform_eq (intermediate n S gs) hmono _ _).trans hz
  rcases (hg gs[j] (List.getElem_mem hj)).1 with hand | hor
  · have ht := and_preserved n S gs j hj hand
    have hu := and_preserved n (constants n (intermediate n S gs))
      (intermediate n S gs) j hjt ht
    exact hu.trans hand.symm
  · have ht := Sink.or_preserved_of_false S gs j hj hor (fun _ : Fin n => false) hz
    have hu := Sink.or_preserved_of_false (constants n (intermediate n S gs))
      (intermediate n S gs) j hjt ht (fun _ : Fin n => false) huz
    exact hu.trans hor.symm

end PEqualNP.Outside.L_meta_1024_aux.TrueClamp

namespace PEqualNP.Outside.L_meta_1024_aux.TrueClamp

open PEqualNP.CircuitLowerBounds

def andGate (g : Gate) : Bool := match g.op with
  | GateOp.and => true
  | _ => false

def andCount (gs : List Gate) : ℕ := (gs.filter andGate).length

lemma andCount_snoc (gs : List Gate) (g : Gate) :
    andCount (gs ++ [g]) = andCount gs + if andGate g then 1 else 0 := by
  cases h : andGate g <;> simp [andCount, List.filter_append, h]

lemma code_and_count (n : ℕ) (P : Finset ℕ) (gs hs : List Gate)
    (hlen : hs.length = gs.length)
    (hop : ∀ j (hj : j < gs.length), n + j ∉ P →
      (hs[j]'(by omega)).op = gs[j].op) :
    andCount (Dead.code n P hs) ≤ andCount gs ∧
      (∀ j (hj : j < gs.length), n + j ∈ P → gs[j].op = GateOp.and →
        andCount (Dead.code n P hs) < andCount gs) := by
  induction gs using List.reverseRecOn generalizing hs with
  | nil =>
    have he : hs = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst hs
    simp [andCount, Dead.code, Dead.compile]
  | append_singleton gs g ih =>
    cases hs using List.reverseRecOn with
    | nil => simp at hlen
    | append_singleton hs h ihs =>
      have hlen' : hs.length = gs.length := by
        simp only [List.length_append, List.length_singleton] at hlen
        omega
      have hop' : ∀ j (hj : j < gs.length), n + j ∉ P →
          (hs[j]'(by omega)).op = gs[j].op := by
        intro j hj hjP
        have hh := hop j (by simp; omega) hjP
        simpa only [List.getElem_append_left hj, List.getElem_append_left (show j < hs.length by omega)] using hh
      obtain ⟨hle, hstrict⟩ := ih hs hlen' hop'
      have hsource := andCount_snoc gs g
      by_cases hp : n + gs.length ∈ P
      · have hcode : Dead.code n P (hs ++ [h]) = Dead.code n P hs := by
          rw [Dead.code_snoc, hlen', if_pos hp]
        rw [hcode]
        constructor
        · omega
        · intro j hj hjP hjand
          by_cases hjlast : j = gs.length
          · subst j
            have hga : g.op = GateOp.and := by simpa using hjand
            have hbit : andGate g = true := by simp [andGate, hga]
            have hsource1 : andCount (gs ++ [g]) = andCount gs + 1 := by
              simpa [hbit] using hsource
            omega
          · have hjold : j < gs.length := by
              simp only [List.length_append, List.length_singleton] at hj
              omega
            have hja : gs[j].op = GateOp.and := by
              simpa only [List.getElem_append_left hjold] using hjand
            have hh := hstrict j hjold hjP hja
            omega
      · have hlast : h.op = g.op := by
          have hh := hop gs.length (by simp) hp
          simpa [hlen'] using hh
        have hcode : andCount (Dead.code n P (hs ++ [h])) =
            andCount (Dead.code n P hs) + if andGate g then 1 else 0 := by
          rw [Dead.code_snoc, hlen', if_neg hp, andCount_snoc]
          simp only [Dead.nextGate, andGate, hlast]
          rfl
        rw [hcode]
        constructor
        · omega
        · intro j hj hjP hjand
          have hjold : j < gs.length := by
            simp only [List.length_append, List.length_singleton] at hj
            have hjne : j ≠ gs.length := fun he => hp (he ▸ hjP)
            omega
          have hja : gs[j].op = GateOp.and := by
            simpa only [List.getElem_append_left hjold] using hjand
          have hh := hstrict j hjold hjP hja
          omega

lemma clean_and_count (n : ℕ) (S : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    andCount (clean n S gs) ≤ andCount gs := by
  exact (code_and_count n (allDeleted n S gs) gs (prepared n S gs)
    (prepared_length n S gs) (prepared_op_kept n S gs hg)).1

lemma clean_and_strict (n : ℕ) (S : Finset ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (j : ℕ) (hj : j < gs.length) (hjS : n + j ∈ S) (hand : gs[j].op = GateOp.and) :
    andCount (clean n S gs) < andCount gs := by
  exact (code_and_count n (allDeleted n S gs) gs (prepared n S gs)
    (prepared_length n S gs) (prepared_op_kept n S gs hg)).2 j hj
    (Finset.mem_union_left _ hjS) hand

end PEqualNP.Outside.L_meta_1024_aux.TrueClamp

namespace PEqualNP.Outside.L_meta_1024_aux.TrueClamp

open PEqualNP.CircuitLowerBounds

lemma intermediate_correct_other (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ w x, Support.Band x → Global.val gs x (out w) = Support.target w x)
    (w : Fin 13) (S : Finset ℕ)
    (habove : ∀ i ∈ S, ∀ x, Support.Band x → Support.target w x = true → Global.val gs x i = true)
    (u : Fin 13) (huw : u ≠ w) (x : Fin 13 → Bool) (hx : Support.Band x) :
    Global.val (intermediate 13 S gs) x (out u) = Support.target u x := by
  cases hu : Support.target u x with
  | false =>
    have hw := Sink.other_target_true u w huw x hx hu
    have he := Sink.output_eq S gs (fun g hm => (hg g hm).1) x (out u)
      (Bridge.output_index gs (out u) u (hcorrect u))
      (fun i hi _ => habove i hi x hx hw)
    exact he.trans ((hcorrect u x hx).trans hu)
  | true =>
    apply Sink.val_ge S gs (fun g hm => (hg g hm).1) x (out u)
    exact (hcorrect u x hx).trans hu

lemma output_kept (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ w x, Support.Band x → Global.val gs x (out w) = Support.target w x)
    (w : Fin 13) (S : Finset ℕ)
    (habove : ∀ i ∈ S, ∀ x, Support.Band x → Support.target w x = true → Global.val gs x i = true)
    (u : Fin 13) (huw : u ≠ w) : out u ∉ allDeleted 13 S gs := by
  let x := Support.row u
  have hx : Support.Band x := Or.inr (Support.row_spec u).1
  have hu : Support.target u x = false := (Support.row_spec u).2
  have hw := Sink.other_target_true u w huw x hx hu
  intro hm
  rcases Finset.mem_union.mp hm with hS | hP
  · have ht := habove (out u) hS x hx hw
    rw [hcorrect u x hx, hu] at ht
    cases ht
  · have ht := constant_value (intermediate 13 S gs)
      (fun g hgmem => (Sink.transform_allowed 13 S gs hg g hgmem).1) x (out u) hP
    rw [intermediate_correct_other gs out hg hcorrect w S habove u huw x hx, hu] at ht
    cases ht

lemma clean_correct_other (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ w x, Support.Band x → Global.val gs x (out w) = Support.target w x)
    (w : Fin 13) (S : Finset ℕ)
    (habove : ∀ i ∈ S, ∀ x, Support.Band x → Support.target w x = true → Global.val gs x i = true)
    (u : Fin 13) (huw : u ≠ w) (x : Fin 13 → Bool) (hx : Support.Band x) :
    Global.val (clean 13 S gs) x (cleanIndex 13 S gs (out u)) = Support.target u x := by
  rw [clean_eval S gs hg x (out u) (Bridge.output_index gs (out u) u (hcorrect u)).2
    (output_kept gs out hg hcorrect w S habove u huw)]
  exact intermediate_correct_other gs out hg hcorrect w S habove u huw x hx

end PEqualNP.Outside.L_meta_1024_aux.TrueClamp

namespace PEqualNP.Outside.L_meta_1024_aux.TrueClamp

open PEqualNP.CircuitLowerBounds

lemma seed_extreme_true (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (w u : Fin 13) (huw : u ≠ w) (S : Finset ℕ)
    (habove : ∀ i ∈ S, ∀ x, Support.Band x → Support.target w x = true → Global.val gs x i = true)
    (i : ℕ) (hi : i ∈ S) : Global.val gs (Global.Zof (Global.line u)) i = true := by
  have ht := habove i hi (Support.row u) (Or.inr (Support.row_spec u).1)
    (Bridge.row_targets u w huw)
  apply Bridge.val_mono gs hg (Support.row u) (Global.Zof (Global.line u)) _ i ht
  intro p hp
  have hn : p ∉ Support.line u := by
    intro hm
    rw [Clamp.row_line_false u p hm] at hp
    cases hp
  simpa [Global.Zof, Global.line, Support.line] using hn

lemma intermediate_ordinary (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ v x, Support.Band x → Global.val gs x (out v) = Support.target v x)
    (w : Fin 13) (S : Finset ℕ)
    (habove : ∀ i ∈ S, ∀ x, Support.Band x → Support.target w x = true → Global.val gs x i = true)
    (u : Fin 13) (huw : u ≠ w)
    (hordinary : ∀ x, Global.val gs x (out u) = Support.target u x) :
    ∀ x, Global.val (intermediate 13 S gs) x (out u) = Support.target u x := by
  let Z := Global.Zof (Global.line u)
  have hZtarget : Support.target u Z = false := by
    simp [Support.target, Z, Global.Zof, Global.line, Support.line]
  have hZ : Global.val (intermediate 13 S gs) Z (out u) = false := by
    have he := Sink.output_eq S gs (fun g hm => (hg g hm).1) Z (out u)
      (Bridge.output_index gs (out u) u (hcorrect u))
      (fun i hi _ => seed_extreme_true gs (fun g hm => (hg g hm).1) w u huw S habove i hi)
    exact he.trans ((hordinary Z).trans hZtarget)
  intro x
  cases hx : Support.target u x with
  | true =>
    exact Sink.val_ge S gs (fun g hm => (hg g hm).1) x (out u) ((hordinary x).trans hx)
  | false =>
    have hxZ : ∀ p, x p = true → Z p = true := by
      intro p hp
      have hn : p ∉ Support.line u := by
        intro hm
        have ht : Support.target u x = true := decide_eq_true ⟨p, hm, hp⟩
        rw [hx] at ht
        cases ht
      simpa [Z, Global.Zof, Global.line, Support.line] using hn
    cases he : Global.val (intermediate 13 S gs) x (out u) with
    | false => rfl
    | true =>
      have ht := Bridge.val_mono (intermediate 13 S gs)
        (fun g hm => (Sink.transform_allowed 13 S gs hg g hm).1) x Z hxZ (out u) he
      rw [hZ] at ht
      cases ht

lemma clean_ordinary (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ v x, Support.Band x → Global.val gs x (out v) = Support.target v x)
    (w : Fin 13) (S : Finset ℕ)
    (habove : ∀ i ∈ S, ∀ x, Support.Band x → Support.target w x = true → Global.val gs x i = true)
    (u : Fin 13) (huw : u ≠ w)
    (hordinary : ∀ x, Global.val gs x (out u) = Support.target u x) :
    ∀ x, Global.val (clean 13 S gs) x (cleanIndex 13 S gs (out u)) = Support.target u x := by
  intro x
  rw [clean_eval S gs hg x (out u) (Bridge.output_index gs (out u) u (hcorrect u)).2
    (output_kept gs out hg hcorrect w S habove u huw)]
  exact intermediate_ordinary gs out hg hcorrect w S habove u huw hordinary x

end PEqualNP.Outside.L_meta_1024_aux.TrueClamp

namespace PEqualNP.Outside.L_meta_1024_aux.TrueClamp

open PEqualNP.CircuitLowerBounds

lemma appendLine_andCount (gs : List Gate) (w : Fin 13) :
    andCount (AppendLine.appendLine gs w) = andCount gs := by
  simp [AppendLine.appendLine, andCount, andGate, AppendLine.pairGate, List.filter_append]

lemma seed_surgery (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ w x, Support.Band x → Global.val gs x (out w) = Support.target w x)
    (w : Fin 13) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ico 13 (13 + gs.length)) (hcard : 3 ≤ S.card)
    (habove : ∀ i ∈ S, ∀ x, Support.Band x → Support.target w x = true → Global.val gs x i = true)
    (j : ℕ) (hj : j < gs.length) (hjS : 13 + j ∈ S) (hand : gs[j].op = GateOp.and) :
    ∃ (gs' : List Gate) (out' : Fin 13 → ℕ),
      (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ andCount gs' < andCount gs ∧
      (∀ u x, Support.Band x → Global.val gs' x (out' u) = Support.target u x) ∧
      (∀ x, Global.val gs' x (out' w) = Support.target w x) ∧
      ∀ u, (∀ x, Global.val gs x (out u) = Support.target u x) →
        ∀ x, Global.val gs' x (out' u) = Support.target u x := by
  let cs := clean 13 S gs
  let gs' := AppendLine.appendLine cs w
  let out' : Fin 13 → ℕ := fun u => if u = w then 15 + cs.length else cleanIndex 13 S gs (out u)
  refine ⟨gs', out', AppendLine.allowed cs w (clean_allowed 13 S gs hg), ?_, ?_, ?_, ?_, ?_⟩
  · have hlen := clean_length_le 13 S gs hS
    have hScard := Finset.card_le_card hS
    simp only [Nat.card_Ico, Nat.add_sub_cancel_left] at hScard
    change (AppendLine.appendLine cs w).length ≤ gs.length
    rw [AppendLine.length]
    change (clean 13 S gs).length + 3 ≤ gs.length
    omega
  · change andCount (AppendLine.appendLine cs w) < andCount gs
    rw [appendLine_andCount]
    exact clean_and_strict 13 S gs hg j hj hjS hand
  · intro u x hx
    by_cases huw : u = w
    · subst u
      simp only [out', if_pos rfl]
      exact AppendLine.eval cs w x
    · simp only [out', if_neg huw]
      change Global.val (AppendLine.appendLine cs w) x (cleanIndex 13 S gs (out u)) = _
      rw [AppendLine.old cs w x _ (by
        exact Dead.mapped_valid 13 (allDeleted 13 S gs) (prepared 13 S gs) (out u)
          (by rw [prepared_length]; exact (Bridge.output_index gs (out u) u (hcorrect u)).2)
          (output_kept gs out hg hcorrect w S habove u huw))]
      exact clean_correct_other gs out hg hcorrect w S habove u huw x hx

  · intro x
    simp only [out', if_pos rfl]
    exact AppendLine.eval cs w x
  · intro u hordinary x
    by_cases huw : u = w
    · subst u
      simp only [out', if_pos rfl]
      exact AppendLine.eval cs w x
    · simp only [out', if_neg huw]
      change Global.val (AppendLine.appendLine cs w) x (cleanIndex 13 S gs (out u)) = _
      rw [AppendLine.old cs w x _ (by
        exact Dead.mapped_valid 13 (allDeleted 13 S gs) (prepared 13 S gs) (out u)
          (by rw [prepared_length]; exact (Bridge.output_index gs (out u) u (hcorrect u)).2)
          (output_kept gs out hg hcorrect w S habove u huw))]
      exact clean_ordinary gs out hg hcorrect w S habove u huw hordinary x

end PEqualNP.Outside.L_meta_1024_aux.TrueClamp

namespace PEqualNP.Outside.L_meta_1024_aux.TrueClamp

open PEqualNP.CircuitLowerBounds

lemma first_and_parents (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (k : ℕ) (hk : k < gs.length) (hand : gs[k].op = GateOp.and)
    (hcorrect : ∀ x, Support.Band x → Global.val gs x (13 + k) = Support.target w x)
    (hfirst : ∀ i, i < 13 + k → ¬ ∀ x, Support.Band x → Global.val gs x i = Support.target w x) :
    ∃ i j : ℕ, 13 ≤ i ∧ 13 ≤ j ∧ i < 13 + k ∧ j < 13 + k ∧ i ≠ j ∧
      ∀ x : Fin 13 → Bool, Global.val gs x (13 + k) = (Global.val gs x i && Global.val gs x j) := by
  have hlen := (hg gs[k] (List.getElem_mem hk)).2
  have hformula (x : Fin 13 → Bool) := Dead.wire_eq_gate gs x k hk
  have hnonempty : (Support.line w).Nonempty := Finset.card_pos.mp (by rw [Clamp.line_card]; decide)
  obtain ⟨p, hp⟩ := hnonempty
  let xp := Support.flip w p
  have hxp : Support.Band xp := Or.inl (Support.flip_spec w p hp).1
  have hrootp : Global.val gs xp (13 + k) = true :=
    (hcorrect xp hxp).trans (Support.flip_spec w p hp).2
  cases hins : gs[k].inputs with
  | nil =>
    have he := hformula (Support.row w)
    rw [hand, hins] at he
    simp only [GateOp.eval, List.map_nil, List.all_nil] at he
    rw [hcorrect _ (Or.inr (Support.row_spec w).1), (Support.row_spec w).2] at he
    cases he
  | cons i tail =>
    cases htail : tail with
    | nil =>
      have he (x : Fin 13 → Bool) : Global.val gs x (13 + k) =
          if i < 13 + k then Global.val gs x i else false := by
        simpa [hand, hins, htail, GateOp.eval] using hformula x
      have hi : i < 13 + k := by
        by_contra hn
        have hh := he xp
        rw [hrootp, if_neg hn] at hh
        cases hh
      apply False.elim
      apply hfirst i hi
      intro x hx
      have hh := he x
      rw [if_pos hi] at hh
      exact hh.symm.trans (hcorrect x hx)
    | cons j rest =>
      have hrest : rest = [] := by
        simp only [hins, htail, List.length_cons] at hlen
        exact List.length_eq_zero_iff.mp (by omega)
      have he (x : Fin 13 → Bool) : Global.val gs x (13 + k) =
          ((if i < 13 + k then Global.val gs x i else false) &&
            (if j < 13 + k then Global.val gs x j else false)) := by
        simpa [hand, hins, htail, hrest, GateOp.eval] using hformula x
      have hab := Bool.and_eq_true_iff.mp ((he xp).symm.trans hrootp)
      have hi : i < 13 + k := by
        by_contra hn
        simp [hn] at hab
      have hj : j < 13 + k := by
        by_contra hn
        simp [hn] at hab
      have heq (x : Fin 13 → Bool) : Global.val gs x (13 + k) =
          (Global.val gs x i && Global.val gs x j) := by simpa [hi, hj] using he x
      have habove (x : Fin 13 → Bool) (hx : Support.Band x) (ht : Support.target w x = true) :
          Global.val gs x i = true ∧ Global.val gs x j = true :=
        Bool.and_eq_true_iff.mp ((heq x).symm.trans ((hcorrect x hx).trans ht))
      have higen : 13 ≤ i := by
        by_contra! hn
        let q : Fin 13 := ⟨i, hn⟩
        obtain ⟨r, hrt, hrq⟩ := Charges.raw_not_above w q
        have hv := (habove (Support.row r) (Or.inr (Support.row_spec r).1) hrt).1
        have hf : Global.val gs (Support.row r) i = false :=
          (Bridge.val_input gs (Support.row r) q).trans hrq
        rw [hf] at hv
        cases hv
      have hjgen : 13 ≤ j := by
        by_contra! hn
        let q : Fin 13 := ⟨j, hn⟩
        obtain ⟨r, hrt, hrq⟩ := Charges.raw_not_above w q
        have hv := (habove (Support.row r) (Or.inr (Support.row_spec r).1) hrt).2
        have hf : Global.val gs (Support.row r) j = false :=
          (Bridge.val_input gs (Support.row r) q).trans hrq
        rw [hf] at hv
        cases hv
      have hij : i ≠ j := by
        intro hij
        apply hfirst i hi
        intro x hx
        have hh := heq x
        simpa [hij] using hh.symm.trans (hcorrect x hx)
      exact ⟨i, j, higen, hjgen, hi, hj, hij, heq⟩

end PEqualNP.Outside.L_meta_1024_aux.TrueClamp

namespace PEqualNP.Outside.L_meta_1024_aux.TrueClamp

open PEqualNP.CircuitLowerBounds

lemma first_and_improvement (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ u x, Support.Band x → Global.val gs x (out u) = Support.target u x)
    (w : Fin 13) (k : ℕ) (hk : k < gs.length) (hand : gs[k].op = GateOp.and)
    (hroot : ∀ x, Support.Band x → Global.val gs x (13 + k) = Support.target w x)
    (hfirst : ∀ i, i < 13 + k → ¬ ∀ x, Support.Band x → Global.val gs x i = Support.target w x) :
    ∃ (gs' : List Gate) (out' : Fin 13 → ℕ),
      (∀ g ∈ gs', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs'.length ≤ gs.length ∧ andCount gs' < andCount gs ∧
      (∀ u x, Support.Band x → Global.val gs' x (out' u) = Support.target u x) ∧
      (∀ x, Global.val gs' x (out' w) = Support.target w x) ∧
      ∀ u, (∀ x, Global.val gs x (out u) = Support.target u x) →
        ∀ x, Global.val gs' x (out' u) = Support.target u x := by
  obtain ⟨i, j, higen, hjgen, hi, hj, hij, heq⟩ :=
    first_and_parents gs hg w k hk hand hroot hfirst
  let S : Finset ℕ := {13 + k, i, j}
  have hS : S ⊆ Finset.Ico 13 (13 + gs.length) := by
    intro t ht
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl <;> apply Finset.mem_Ico.mpr <;> constructor <;> omega
  have hScard : S.card = 3 := by
    simp [S, (Nat.ne_of_lt hi).symm, (Nat.ne_of_lt hj).symm, hij]
  have habove : ∀ t ∈ S, ∀ x, Support.Band x → Support.target w x = true → Global.val gs x t = true := by
    intro t ht x hx hw
    have hr := (hroot x hx).trans hw
    have hp := Bool.and_eq_true_iff.mp ((heq x).symm.trans hr)
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact hr
    · exact hp.1
    · exact hp.2
  exact seed_surgery gs out hg hcorrect w S hS (by omega) habove k hk (by simp [S]) hand

end PEqualNP.Outside.L_meta_1024_aux.TrueClamp

namespace PEqualNP.Outside.L_meta_1024_aux.TrueClamp

open PEqualNP.CircuitLowerBounds

lemma normalize_or_sinks (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ u x, Support.Band x → Global.val gs x (out u) = Support.target u x)
    (W : Finset (Fin 13))
    (hW : ∀ u ∈ W, ∀ x, Global.val gs x (out u) = Support.target u x) :
    ∃ (hs : List Gate) (ho : Fin 13 → ℕ),
      (∀ g ∈ hs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      hs.length ≤ gs.length ∧
      (∀ u x, Support.Band x → Global.val hs x (ho u) = Support.target u x) ∧
      (∀ u ∈ W, ∀ x, Global.val hs x (ho u) = Support.target u x) ∧
      Dead.NoReads 13 (Finset.univ.image ho) hs ∧
      ∀ u, u ∉ W → ∃ (k : ℕ) (hk : k < hs.length), ho u = 13 + k ∧ hs[k].op = GateOp.or := by
  classical
  let Candidate (cs : List Gate) (co : Fin 13 → ℕ) : Prop :=
    (∀ g ∈ cs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
    cs.length ≤ gs.length ∧
    (∀ u x, Support.Band x → Global.val cs x (co u) = Support.target u x) ∧
    ∀ u ∈ W, ∀ x, Global.val cs x (co u) = Support.target u x
  have hex : ∃ m : ℕ, ∃ cs co, Candidate cs co ∧ andCount cs = m :=
    ⟨andCount gs, gs, out, ⟨hg, le_rfl, hcorrect, hW⟩, rfl⟩
  obtain ⟨cs, co, hcand, hcount⟩ := Nat.find_spec hex
  obtain ⟨hcg, hclen, hccorrect, hcW⟩ := hcand
  have hminimal (ds : List Gate) (do' : Fin 13 → ℕ) (hd : Candidate ds do') :
      andCount cs ≤ andCount ds := by
    rw [hcount]
    exact Nat.find_min' hex ⟨ds, do', hd, rfl⟩
  have hexout (u : Fin 13) : ∃ i, ∀ x, Support.Band x → Global.val cs x i = Support.target u x :=
    ⟨co u, hccorrect u⟩
  let first : Fin 13 → ℕ := fun u => Nat.find (hexout u)
  have hfirstcorrect (u : Fin 13) : ∀ x, Support.Band x → Global.val cs x (first u) = Support.target u x :=
    Nat.find_spec (hexout u)
  have hfirstmin (u : Fin 13) (i : ℕ) (hi : i < first u) :
      ¬ ∀ x, Support.Band x → Global.val cs x i = Support.target u x := by
    intro he
    have hm := Nat.find_min' (hexout u) he
    change first u ≤ i at hm
    omega
  have hfirstor (u : Fin 13) : ∃ (k : ℕ) (hk : k < cs.length), first u = 13 + k ∧ cs[k].op = GateOp.or := by
    have hv := Bridge.output_index cs (first u) u (hfirstcorrect u)
    let k := first u - 13
    have hk : k < cs.length := by omega
    have he : first u = 13 + k := by omega
    rcases (hcg cs[k] (List.getElem_mem hk)).1 with hand | hor
    · have hr : ∀ x, Support.Band x → Global.val cs x (13 + k) = Support.target u x := by
        simpa only [← he] using hfirstcorrect u
      have hm : ∀ i, i < 13 + k → ¬ ∀ x, Support.Band x → Global.val cs x i = Support.target u x := by
        simpa only [← he] using hfirstmin u
      obtain ⟨ds, do', hdg, hdlen, hdand, hdcorrect, hdselected, hdpreserve⟩ :=
        first_and_improvement cs co hcg hccorrect u k hk hand hr hm
      have hdcand : Candidate ds do' :=
        ⟨hdg, hdlen.trans hclen, hdcorrect, fun v hvW => hdpreserve v (hcW v hvW)⟩
      have hle := hminimal ds do' hdcand
      omega
    · exact ⟨k, hk, he, hor⟩
  let ho : Fin 13 → ℕ := fun u => if u ∈ W then co u else first u
  have hretarget : ∀ u x, Support.Band x → Global.val cs x (ho u) = Support.target u x := by
    intro u x hx
    by_cases hu : u ∈ W
    · simpa [ho, hu] using hccorrect u x hx
    · simpa [ho, hu] using hfirstcorrect u x hx
  let O := Finset.univ.image ho
  let hs := Sink.transform 13 O cs
  have hfinal := Sink.band_correct cs ho (fun g hm => (hcg g hm).1) hretarget
  refine ⟨hs, ho, Sink.transform_allowed 13 O cs hcg, ?_, hfinal, ?_, ?_, ?_⟩
  · simpa only [hs, Sink.transform_length] using hclen
  · intro u hu
    apply Sink.preserves_ordinary cs ho hcg hretarget u
    intro x
    simpa [ho, hu] using hcW u hu x
  · exact Dead.transform_noReads 13 O cs
  · intro u hu
    obtain ⟨k, hk, he, hor⟩ := hfirstor u
    have hout : ho u = 13 + k := by simpa [ho, hu] using he
    have hknew : k < hs.length := by simpa only [hs, Sink.transform_length] using hk
    refine ⟨k, hknew, hout, ?_⟩
    have hf : Global.val hs (Support.row u) (13 + k) = false := by
      rw [← hout, hfinal u _ (Or.inr (Support.row_spec u).1), (Support.row_spec u).2]
    exact Sink.or_preserved_of_false O cs k hk hor (Support.row u) hf

end PEqualNP.Outside.L_meta_1024_aux.TrueClamp


namespace PEqualNP.Outside.L_meta_1024_aux.FourReduction
open PEqualNP.CircuitLowerBounds

lemma nine_ordinary_bound (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ w (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out w) = Support.target w x)
    (W : Finset (Fin 13)) (hW : 9 ≤ W.card)
    (hordinary : ∀ w ∈ W, ∀ x : Fin 13 → Bool,
      Global.val gs x (out w) = Support.target w x) : 39 ≤ gs.length := by
  classical
  obtain ⟨V, hVW, hVcard⟩ := Finset.exists_subset_card_eq hW
  obtain ⟨hs, ho, hhg, hhlen, hhcorrect, hhordinary, hhsinks, hhor⟩ :=
    TrueClamp.normalize_or_sinks gs out hg hcorrect V (fun w hw => hordinary w (hVW hw))
  let C := Finset.univ \ V
  have hC : C.card = 4 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hVcard]
    decide
  let e : Fin 4 ≃ C := (Fintype.equivFinOfCardEq (by simpa using hC)).symm
  let lineId : Fin 4 → Fin 13 := fun u => (e u).val
  have hinj : Function.Injective lineId := Subtype.val_injective.comp e.injective
  have hmem (u : Fin 4) : lineId u ∈ C := (e u).property
  have hrange : Finset.univ.image lineId = C := by
    ext w
    constructor
    · intro hw
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hw
      exact hmem u
    · intro hw
      refine Finset.mem_image.mpr ⟨e.symm ⟨w, hw⟩, Finset.mem_univ _, ?_⟩
      simp [lineId]
  have hbound := four_or_sink_bound hs ho lineId hinj hhg hhcorrect
    (fun w hw => hhordinary w (by simpa [hrange, C] using hw))
    (by
      intro j hj i hi hn hiQ
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hiQ
      exact hhsinks j hj _ hi hn (Finset.mem_image.mpr ⟨lineId u, Finset.mem_univ _, rfl⟩))
    (fun u => hhor (lineId u) (Finset.mem_sdiff.mp (hmem u)).2)
  omega

lemma five_exotic_outputs (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ w (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out w) = Support.target w x)
    (hsmall : gs.length < 39) : 5 ≤ (Bridge.exoticSet gs out).card := by
  classical
  by_contra! hfew
  let W := Finset.univ \ Bridge.exoticSet gs out
  have hW : 9 ≤ W.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hu : (Finset.univ : Finset (Fin 13)).card = 13 := by decide
    rw [hu]
    omega
  have hord : ∀ w ∈ W, ∀ x : Fin 13 → Bool,
      Global.val gs x (out w) = Support.target w x := by
    intro w hw
    have hn := (Finset.mem_sdiff.mp hw).2
    change ∀ x : Fin 13 → Bool, Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x
    simpa [Bridge.exoticSet] using hn
  have hh := nine_ordinary_bound gs out hg hcorrect W hW hord
  omega

end PEqualNP.Outside.L_meta_1024_aux.FourReduction

namespace PEqualNP.Outside.L_meta_1024_aux.FourReduction
open PEqualNP.CircuitLowerBounds

lemma residual_family_nonordinary (k : ℕ) (gs : List Gate) (hsize : gs.length < 3 * k)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin k → Fin 13) (hinj : Function.Injective lineId) (out : Fin k → ℕ)
    (hcorrect : ∀ u (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out u) = Support.target (lineId u) x)
    (hprevious : ∀ (cs : List Gate) (co : Fin 13 → ℕ),
      (∀ g ∈ cs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ w (x : Fin 13 → Bool), Support.Band x → Global.val cs x (co w) = Support.target w x) →
      ∀ W : Finset (Fin 13), 14 - k ≤ W.card →
      (∀ w ∈ W, ∀ x : Fin 13 → Bool, Global.val cs x (co w) = Support.target w x) →
      39 ≤ cs.length) :
    ∀ u, ¬ ∀ x : Fin 13 → Bool, Global.val gs x (out u) = Support.target (lineId u) x := by
  classical
  intro u₀ hexact
  let A : Finset (Fin 13) := Finset.univ.image lineId
  let W := Finset.univ \ A
  have hA : A.card = k := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hk : k ≤ 13 := by
    have hh := Finset.card_le_univ A
    simpa [hA] using hh
  have hkpos : 0 < k := Nat.zero_lt_of_lt u₀.isLt
  have hW : W.card = 13 - k := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hA]
    rfl
  have houtside (u : Fin k) : lineId u ∉ W := by
    intro hu
    exact (Finset.mem_sdiff.mp hu).2 (Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩)
  let cs := AppendLine.appendLines gs W.toList
  have hcs : cs.length < 39 := by
    rw [AppendLine.lines_length, Finset.length_toList, hW]
    omega
  have hallowed := AppendLine.lines_allowed gs W.toList hg
  have hwitness : ∀ w : Fin 13, ∃ i : ℕ,
      (∀ x : Fin 13 → Bool, Support.Band x → Global.val cs x i = Support.target w x) ∧
      ((w ∈ W ∨ w = lineId u₀) → ∀ x : Fin 13 → Bool, Global.val cs x i = Support.target w x) := by
    intro w
    by_cases hw : w ∈ W
    · obtain ⟨i, _, _, hi⟩ := AppendLine.lines_generated gs W.toList w (by simpa using hw)
      exact ⟨i, fun x _ => hi x, fun _ => hi⟩
    · have hwA : w ∈ A := by simpa [W] using hw
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hwA
      have hv := (Bridge.output_index gs (out u) (lineId u) (hcorrect u)).2
      have hold (x : Fin 13 → Bool) : Global.val cs x (out u) = Global.val gs x (out u) :=
        AppendLine.lines_old gs W.toList x (out u) hv
      refine ⟨out u, ?_, ?_⟩
      · intro x hx
        exact (hold x).trans (hcorrect u x hx)
      · rintro (hu | he)
        · exact False.elim (hw hu)
        · have huu : u = u₀ := hinj he
          subst u
          intro x
          exact (hold x).trans (hexact x)
  choose out' hband hord using hwitness
  have hcount : 14 - k ≤ (insert (lineId u₀) W).card := by
    rw [Finset.card_insert_of_notMem (houtside u₀), hW]
    omega
  have hord' : ∀ w ∈ insert (lineId u₀) W, ∀ x : Fin 13 → Bool,
      Global.val cs x (out' w) = Support.target w x := by
    intro w hw
    rcases Finset.mem_insert.mp hw with he | hw
    · exact hord w (Or.inr he)
    · exact hord w (Or.inl hw)
  have hh := hprevious cs out' hallowed hband (insert (lineId u₀) W) hcount hord'
  omega

lemma small_five_nonordinary (gs : List Gate) (hsize : gs.length ≤ 14)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId) (out : Fin 5 → ℕ)
    (hcorrect : ∀ u (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out u) = Support.target (lineId u) x) :
    ∀ u, ¬ ∀ x : Fin 13 → Bool, Global.val gs x (out u) = Support.target (lineId u) x := by
  apply residual_family_nonordinary 5 gs (by omega) hg lineId hinj out hcorrect
  intro cs co hcg hcc W hW hord
  exact nine_ordinary_bound cs co hcg hcc W hW hord

end PEqualNP.Outside.L_meta_1024_aux.FourReduction

namespace PEqualNP.Outside.L_meta_1024_aux.PrivateSurgery
open PEqualNP.CircuitLowerBounds

lemma context_private (gs : List Gate) (o i : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      Global.val gs x o = Support.target w x)
    (C : Finset (Fin 13)) (hC : C ⊆ Global.line w) (hc : C.card ≤ 2)
    (hcontext : ∀ x : Fin 13 → Bool, (∀ p ∈ C, x p = false) →
      Global.val gs x i = false → Global.val gs x o = false) :
    ∀ v : Fin 13, v ≠ w → Global.val gs (Global.Zof (Global.line v)) i = true := by
  classical
  intro v hv
  have hmeet := Global.line_intersection w v hv.symm
  have hcover : ¬ Global.line w ⊆ C ∪ Global.line v := by
    intro hh
    have hs : Global.line w ⊆ C ∪ (Global.line w ∩ Global.line v) := by
      intro p hp
      rcases Finset.mem_union.mp (hh hp) with hpC | hpv
      · exact Finset.mem_union_left _ hpC
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hp, hpv⟩)
    have hcard := (Finset.card_le_card hs).trans (Finset.card_union_le _ _)
    rw [Global.line_card] at hcard
    omega
  obtain ⟨p, hp, hpnot⟩ := Finset.not_subset.mp hcover
  have hsub : C ∪ Global.line v ⊆ Finset.univ.erase p := by
    intro q hq
    exact Finset.mem_erase.mpr ⟨by intro he; subst q; exact hpnot hq, Finset.mem_univ _⟩
  have hsmall : (C ∪ Global.line v).card ≤ 6 := by
    have hh := Finset.card_union_le C (Global.line v)
    rw [Global.line_card] at hh
    omega
  obtain ⟨T, hCT, hT, hTcard⟩ := Finset.exists_subsuperset_card_eq hsub hsmall
    (show 6 ≤ (Finset.univ.erase p : Finset (Fin 13)).card by simp)
  let x := Global.Zof T
  have hxband : Support.Band x := by
    have he : Support.zeroSet x = T := by
      ext q
      simp [Support.zeroSet, x, Global.Zof]
    right
    rw [he]
    exact hTcard
  have hxC : ∀ q ∈ C, x q = false := by
    intro q hq
    simp [x, Global.Zof, hCT (Finset.mem_union_left _ hq)]
  have hxv : ∀ q, x q = true → Global.Zof (Global.line v) q = true := by
    intro q hq
    have hqn : q ∉ T := by simpa [x, Global.Zof] using hq
    simp only [Global.Zof, decide_eq_true_eq]
    exact fun hqv => hqn (hCT (Finset.mem_union_right _ hqv))
  cases hi : Global.val gs (Global.Zof (Global.line v)) i with
  | true => rfl
  | false =>
    have hxi : Global.val gs x i = false := by
      cases he : Global.val gs x i
      · rfl
      · have hh := Bridge.val_mono gs hg x (Global.Zof (Global.line v)) hxv i he
        rw [hi] at hh
        exact Bool.noConfusion hh
    have hxo := hcontext x hxC hxi
    have htarget : Support.target w x = true := by
      apply decide_eq_true_iff.mpr
      refine ⟨p, hp, ?_⟩
      simp only [x, Global.Zof, decide_eq_true_eq]
      exact fun hpt => (Finset.mem_erase.mp (hT hpt)).1 rfl
    rw [hcorrect x hxband, htarget] at hxo
    exact Bool.noConfusion hxo

lemma normal_clamp (gs : List Gate) (o : ℕ) (w : Fin 13) (P : Finset ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      Global.val gs x o = Support.target w x)
    (hnormal : Global.val gs (Global.Zof (Global.line w)) o = false)
    (hprivate : ∀ i ∈ P, Global.val gs (Global.Zof (Global.line w)) i = true) :
    Global.val (Sink.transform 13 P gs) (Global.Zof (Global.line w)) o = false ∧
    ∀ x : Fin 13 → Bool, Support.Band x →
      Global.val (Sink.transform 13 P gs) x o = Support.target w x := by
  have hop := fun g hg' => (hg g hg').1
  have hn := (Sink.output_eq P gs hop (Global.Zof (Global.line w)) o
    (Bridge.output_index gs o w hcorrect) (fun i hi _ => hprivate i hi)).trans hnormal
  refine ⟨hn, ?_⟩
  intro x hx
  cases ht : Support.target w x
  · have hxz : ∀ p, x p = true → Global.Zof (Global.line w) p = true := by
      intro p hp
      simp only [Global.Zof, decide_eq_true_eq]
      intro hpl
      have hh : Support.target w x = true := decide_eq_true_iff.mpr ⟨p, hpl, hp⟩
      rw [ht] at hh
      exact Bool.noConfusion hh
    cases he : Global.val (Sink.transform 13 P gs) x o
    · rfl
    · have hh := Bridge.val_mono (Sink.transform 13 P gs)
        (fun g hm => (Sink.transform_allowed 13 P gs hg g hm).1)
        x (Global.Zof (Global.line w)) hxz o he
      rw [hn] at hh
      exact Bool.noConfusion hh
  · exact Sink.val_ge P gs hop x o ((hcorrect x hx).trans ht)

lemma rebuild (k : ℕ) (gs : List Gate) (out : Fin k → ℕ)
    (lineId : Fin k → Fin 13) (u₀ : Fin k)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ u (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out u) = Support.target (lineId u) x)
    (hnormal : ∀ u, Global.val gs (Global.Zof (Global.line (lineId u))) (out u) = false)
    (P : Finset ℕ) (hP : P ⊆ Finset.Ico 13 (13 + gs.length)) (hcard : 3 ≤ P.card)
    (hprivate : ∀ i ∈ P, ∀ u, u ≠ u₀ →
      Global.val gs (Global.Zof (Global.line (lineId u))) i = true) :
    ∃ (cs : List Gate) (co : Fin k → ℕ),
      cs.length ≤ gs.length ∧
      (∀ g ∈ cs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ u (x : Fin 13 → Bool), Support.Band x →
        Global.val cs x (co u) = Support.target (lineId u) x) ∧
      (∀ x : Fin 13 → Bool, Global.val cs x (co u₀) = Support.target (lineId u₀) x) := by
  classical
  let T := Sink.transform 13 P gs
  let U := Dead.paidCode 13 P gs
  let cs := AppendLine.appendLine U (lineId u₀)
  let co : Fin k → ℕ := fun u => if u = u₀ then 15 + U.length else Dead.paidIndex 13 P gs (out u)
  have hkept (u : Fin k) (hu : u ≠ u₀) : out u ∉ P := by
    intro hp
    have hh := hprivate (out u) hp u hu
    rw [hnormal u] at hh
    exact Bool.noConfusion hh
  have heval (u : Fin k) (hu : u ≠ u₀) (x : Fin 13 → Bool) :
      Global.val U x (Dead.paidIndex 13 P gs (out u)) = Global.val T x (out u) := by
    apply Dead.eval P T (Dead.transform_noReads 13 P gs) x (out u)
      (by simpa [T, Sink.transform_length] using (Bridge.output_index gs (out u) (lineId u) (hcorrect u)).2)
      (hkept u hu)
  have hvalid (u : Fin k) (hu : u ≠ u₀) : Dead.paidIndex 13 P gs (out u) < 13 + U.length :=
    Dead.mapped_valid 13 P T (out u)
      (by simpa [T, Sink.transform_length] using (Bridge.output_index gs (out u) (lineId u) (hcorrect u)).2)
      (hkept u hu)
  refine ⟨cs, co, ?_, AppendLine.allowed U (lineId u₀) (Dead.paid_allowed 13 P gs hg), ?_, ?_⟩
  · have hpbound : P.card ≤ gs.length := by simpa using Finset.card_le_card hP
    change (AppendLine.appendLine U (lineId u₀)).length ≤ gs.length
    rw [AppendLine.length]
    have hu : U.length = gs.length - P.card := by
      exact (Dead.paid_length 13 P gs).trans (Cut.unpaid_eq_sub 13 P gs hP)
    rw [hu]
    omega
  · intro u x hx
    by_cases hu : u = u₀
    · subst u
      simpa only [co, if_pos rfl] using AppendLine.eval U (lineId u₀) x
    · change Global.val cs x (if u = u₀ then _ else _) = _
      rw [if_neg hu, AppendLine.old U (lineId u₀) x _ (hvalid u hu), heval u hu x]
      exact (normal_clamp gs (out u) (lineId u) P hg (hcorrect u) (hnormal u)
        (fun i hi => hprivate i hi u hu)).2 x hx
  · intro x
    simpa only [co, if_pos rfl] using AppendLine.eval U (lineId u₀) x

lemma three_private_impossible (gs : List Gate) (hsize : gs.length ≤ 14)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId) (out : Fin 5 → ℕ)
    (hcorrect : ∀ u (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out u) = Support.target (lineId u) x)
    (hnormal : ∀ u, Global.val gs (Global.Zof (Global.line (lineId u))) (out u) = false)
    (u₀ : Fin 5) (P : Finset ℕ) (hP : P ⊆ Finset.Ico 13 (13 + gs.length)) (hcard : 3 ≤ P.card)
    (hprivate : ∀ i ∈ P, ∀ u, u ≠ u₀ →
      Global.val gs (Global.Zof (Global.line (lineId u))) i = true) : False := by
  obtain ⟨cs, co, hlen, hcg, hcc, he⟩ := rebuild 5 gs out lineId u₀ hg hcorrect hnormal P hP hcard hprivate
  exact FourReduction.small_five_nonordinary cs (by omega) hcg lineId hinj co hcc u₀ he

end PEqualNP.Outside.L_meta_1024_aux.PrivateSurgery

namespace PEqualNP.Outside.L_meta_1024_aux.Minterms
lemma avoid_extension (S : Finset (Fin 13)) (p : Fin 13) (hp : p ∉ S)
    (hs : S.card ≤ 6) :
    ∃ T : Finset (Fin 13), S ⊆ T ∧ T.card = 6 ∧ p ∉ T := by
  have hsub : S ⊆ Finset.univ.erase p := by
    intro q hq
    exact Finset.mem_erase.mpr ⟨fun h => hp (h ▸ hq), Finset.mem_univ q⟩
  have hc : 6 ≤ (Finset.univ.erase p).card := by simp
  obtain ⟨T, hST, hT, hcard⟩ := Finset.exists_subsuperset_card_eq hsub hs hc
  exact ⟨T, hST, hcard, fun h => (Finset.mem_erase.mp (hT h)).1 rfl⟩

end PEqualNP.Outside.L_meta_1024_aux.Minterms

namespace PEqualNP.Outside.L_meta_1024_aux.FalsePruning

open PEqualNP.CircuitLowerBounds

abbrev Entry := ℕ × Finset (Fin 13)

def emptyEntry : Entry := (0, ∅)

def hit (S : Finset (Fin 13)) (x : Fin 13 → Bool) : Bool :=
  decide (∃ p ∈ S, x p = true)

lemma hit_empty (x : Fin 13 → Bool) : hit ∅ x = false := by simp [hit]

lemma hit_union (S T : Finset (Fin 13)) (x : Fin 13 → Bool) :
    hit (S ∪ T) x = (hit S x || hit T x) := by
  apply Bool.eq_iff_iff.mpr
  simp [hit, Finset.mem_union, or_and_right, exists_or]

def readEntry (es : List Entry) (i : ℕ) : Entry := es.getD i emptyEntry

def selected (e : ℕ → Entry) (ins : List ℕ) : List ℕ :=
  match ins with
  | [] => []
  | [a] => [a]
  | a :: b :: _ => if (e a).1 ≤ (e b).1 then [a] else [b]

def profile (e : ℕ → Entry) (g : Gate) : Entry :=
  match g.op with
  | GateOp.and => match g.inputs with
    | [] => (5, ∅)
    | [a] => e a
    | a :: b :: _ => if (e a).1 ≤ (e b).1 then e a else e b
  | _ =>
    (min 5 ((g.inputs.map fun i => (e i).1).sum),
      g.inputs.foldr (fun i S => (e i).2 ∪ S) ∅)

def rewritten (e : ℕ → Entry) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => match g.inputs with
    | [] => g
    | _ :: _ => ⟨GateOp.or, selected e g.inputs⟩
  | _ => g

lemma gate_spec (e : ℕ → Entry) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin 13 → Bool) (old new : ℕ → Bool)
    (hdom : ∀ i, old i = true → new i = true)
    (he : ∀ i, (e i).1 ≤ 4 → (e i).2.card ≤ (e i).1 ∧ new i = hit (e i).2 x) :
    ((rewritten e g).op = GateOp.and ∨ (rewritten e g).op = GateOp.or) ∧
    (rewritten e g).inputs.length ≤ 2 ∧
    (g.op.eval (g.inputs.map old) = true →
      (rewritten e g).op.eval ((rewritten e g).inputs.map new) = true) ∧
    ((profile e g).1 ≤ 4 →
      (profile e g).2.card ≤ (profile e g).1 ∧
      (rewritten e g).op.eval ((rewritten e g).inputs.map new) = hit (profile e g).2 x) := by
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨hop, hlen⟩
  simp only at hop hlen ⊢
  rcases hop with rfl | rfl
  · match ins, hlen with
    | [], _ => simp [rewritten, profile, GateOp.eval]
    | [a], _ =>
      simpa [rewritten, selected, profile, GateOp.eval] using
        (show (GateOp.or = GateOp.and ∨ GateOp.or = GateOp.or) ∧
          1 ≤ 2 ∧ (old a = true → new a = true) ∧
          ((e a).1 ≤ 4 → (e a).2.card ≤ (e a).1 ∧ new a = hit (e a).2 x) from
          ⟨Or.inr rfl, by omega, hdom a, he a⟩)
    | [a, b], _ =>
      by_cases hab : (e a).1 ≤ (e b).1
      · simp only [rewritten, profile, selected, if_pos hab]
        refine ⟨by simp, by simp, ?_, ?_⟩
        · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
          intro hh
          have hboth : old a = true ∧ old b = true := by simpa using hh
          exact hdom a hboth.1
        · simpa [GateOp.eval] using he a
      · simp only [rewritten, profile, selected, if_neg hab]
        refine ⟨by simp, by simp, ?_, ?_⟩
        · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
          intro hh
          have hboth : old a = true ∧ old b = true := by simpa using hh
          exact hdom b hboth.2
        · simpa [GateOp.eval] using he b
    | _ :: _ :: _ :: _, hh => simp at hh
  · match ins, hlen with
    | [], _ => simp [rewritten, profile, GateOp.eval, hit_empty]
    | [a], _ =>
      simp only [rewritten, profile,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        List.foldr_cons, List.foldr_nil, Finset.union_empty]
      refine ⟨by simp, by simp, ?_, ?_⟩
      · simpa [GateOp.eval] using hdom a
      · intro hc
        have ha : (e a).1 ≤ 4 := by omega
        have hm : min 5 (e a).1 = (e a).1 := Nat.min_eq_right (by omega)
        rw [hm]
        simpa [GateOp.eval] using he a ha
    | [a, b], _ =>
      simp only [rewritten, profile,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        List.foldr_cons, List.foldr_nil, Finset.union_empty]
      refine ⟨by simp, by simp, ?_, ?_⟩
      · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
          List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true]
        exact Or.imp (hdom a) (hdom b)
      · intro hc
        have hab : (e a).1 + (e b).1 ≤ 4 := by omega
        have ha := he a (by omega)
        have hb := he b (by omega)
        have hm : min 5 ((e a).1 + (e b).1) = (e a).1 + (e b).1 :=
          Nat.min_eq_right (by omega)
        refine ⟨?_, ?_⟩
        · rw [hm]
          exact (Finset.card_union_le _ _).trans (Nat.add_le_add ha.1 hb.1)
        · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
            List.any_nil, id_eq, Bool.or_false, ha.2, hb.2, hit_union]
    | _ :: _ :: _ :: _, hh => simp at hh

structure State where
  entries : List Entry
  gates : List Gate

def initial : State := ⟨List.ofFn (fun p : Fin 13 => (1, {p})), []⟩

def step (s : State) (g : Gate) : State :=
  ⟨s.entries ++ [profile (readEntry s.entries) g],
    s.gates ++ [rewritten (readEntry s.entries) g]⟩

def build (gs : List Gate) : State := gs.foldl step initial

def cost (gs : List Gate) (o : ℕ) : ℕ := (readEntry (build gs).entries o).1

lemma read_append (es : List Entry) (e : Entry) (i : ℕ) :
    readEntry (es ++ [e]) i = if i = es.length then e else readEntry es i := by
  unfold readEntry
  rcases lt_trichotomy i es.length with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left h]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma build_snoc (gs : List Gate) (g : Gate) : build (gs ++ [g]) = step (build gs) g := by
  simp [build, List.foldl_append]

lemma build_lengths (gs : List Gate) :
    (build gs).entries.length = 13 + gs.length ∧ (build gs).gates.length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [build, initial]
  | append_singleton gs g ih =>
    rw [build_snoc]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma rewritten_allowed (e : ℕ → Entry) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ((rewritten e g).op = GateOp.and ∨ (rewritten e g).op = GateOp.or) ∧
      (rewritten e g).inputs.length ≤ 2 := by
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨hop, hlen⟩
  simp only at hop hlen ⊢
  rcases hop with rfl | rfl
  · match ins, hlen with
    | [], _ => simp [rewritten]
    | [a], _ => simp [rewritten, selected]
    | [a,b], _ =>
      by_cases h : (e a).1 ≤ (e b).1 <;> simp [rewritten, selected, h]
    | _ :: _ :: _ :: _, hh => simp at hh
  · simpa [rewritten] using hlen

lemma build_allowed (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ (build gs).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction gs using List.reverseRecOn with
  | nil => simp [build, initial]
  | append_singleton gs g ih =>
    rw [build_snoc]
    intro a ha
    simp only [step, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact ih (fun b hb => hg b (by simp [hb])) a ha
    · exact rewritten_allowed _ g (hg g (by simp))

lemma wire_spec (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin 13 → Bool) (i : ℕ) :
    (Global.val gs x i = true → Global.val (build gs).gates x i = true) ∧
    ((readEntry (build gs).entries i).1 ≤ 4 →
      (readEntry (build gs).entries i).2.card ≤ (readEntry (build gs).entries i).1 ∧
      Global.val (build gs).gates x i = hit (readEntry (build gs).entries i).2 x) := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    by_cases hi : i < 13
    · have hr : readEntry initial.entries i = (1, {⟨i, hi⟩}) := by
        simp only [readEntry, initial, List.getD_eq_getElem?_getD,
          List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
      change (Global.val [] x i = true → Global.val [] x i = true) ∧ _
      simp only [build, List.foldl_nil, hr]
      simp [initial, Global.val_nil, hi, hit]
    · simp [build, initial, readEntry, emptyEntry, Global.val_nil, hit,
        Nat.le_of_not_lt hi, hi]
  | append_singleton gs g ih =>
    have hgs : ∀ a ∈ gs,
        (a.op = GateOp.and ∨ a.op = GateOp.or) ∧ a.inputs.length ≤ 2 := by
      intro a ha
      exact hg a (by simp [ha])
    have hi := ih hgs
    have hs := gate_spec (readEntry (build gs).entries) g (hg g (by simp)) x
      (Global.val gs x) (Global.val (build gs).gates x)
      (fun j => (hi j).1) (fun j => (hi j).2)
    simp only [build_snoc, step, read_append, Global.val_snoc,
      (build_lengths gs).1, (build_lengths gs).2]
    by_cases he : i = 13 + gs.length
    · simp only [if_pos he]
      exact ⟨hs.2.2.1, hs.2.2.2⟩
    · simp only [if_neg he]
      exact hi i

lemma support_eq_line (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x → f x = Support.target w x)
    (S : Finset (Fin 13)) (hS : S.card ≤ 4)
    (hdom : ∀ x, f x = true → hit S x = true) : S = Support.line w := by
  classical
  have hsub : Support.line w ⊆ S := by
    intro p hp
    by_contra hn
    obtain ⟨T, hST, hT, hpT⟩ := Minterms.avoid_extension S p hn (by omega)
    have hb : Support.Band (Support.fromZeros T) := by
      right
      rw [Support.zeroSet_fromZeros, hT]
    have ht : Support.target w (Support.fromZeros T) = true := by
      simp only [Support.target, decide_eq_true_eq]
      exact ⟨p, hp, by simp [Support.fromZeros, hpT]⟩
    have hh := hdom (Support.fromZeros T) ((hcorrect _ hb).trans ht)
    simp only [hit, decide_eq_true_eq] at hh
    obtain ⟨q, hq, hxq⟩ := hh
    have hqT := hST hq
    simp [Support.fromZeros, hqT] at hxq
  apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [Clamp.line_card]
  exact hS

lemma low_cost_bound (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hcost : ∀ w, cost gs (out w) ≤ 4) : 39 ≤ gs.length := by
  have hglob : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      Circuit.eval ⟨(build gs).gates, out w⟩ (List.ofFn x) =
        decide (∃ p ∈ Global.line w, x p = true) := by
    intro w x
    let S := (readEntry (build gs).entries (out w)).2
    have hc : (readEntry (build gs).entries (out w)).1 ≤ 4 := hcost w
    have hw := wire_spec gs hg x (out w)
    have hcard : S.card ≤ 4 := (hw.2 hc).1.trans hc
    have hdom : ∀ y, Circuit.eval ⟨gs, out w⟩ (List.ofFn y) = true → hit S y = true := by
      intro y hy
      have hh := wire_spec gs hg y (out w)
      exact (hh.2 hc).2.symm.trans (hh.1 hy)
    have hline := support_eq_line w (fun y => Circuit.eval ⟨gs, out w⟩ (List.ofFn y))
      (hcorrect w) S hcard hdom
    change Global.val (build gs).gates x (out w) = Support.target w x
    rw [(hw.2 hc).2]
    change hit S x = Support.target w x
    rw [hline]
    rfl
  have hb := Global.global_bound (build gs).gates out (build_allowed gs hg) hglob
  simpa only [(build_lengths gs).2] using hb

lemma some_large_cost (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hsmall : gs.length < 39) : ∃ w, 5 ≤ cost gs (out w) := by
  by_contra! hn
  have hc : ∀ w, cost gs (out w) ≤ 4 := fun w => by have h := hn w; omega
  have hb := low_cost_bound gs out hg hcorrect hc
  omega

end PEqualNP.Outside.L_meta_1024_aux.FalsePruning

namespace PEqualNP.Outside.L_meta_1024_aux.Certificate

open PEqualNP.CircuitLowerBounds
open FalsePruning

abbrev entry (gs : List Gate) (i : ℕ) : Entry := readEntry (build gs).entries i

lemma entry_snoc (gs : List Gate) (g : Gate) (i : ℕ) :
    entry (gs ++ [g]) i =
      if i = 13 + gs.length then profile (entry gs) g else entry gs i := by
  simp only [entry, build_snoc, FalsePruning.step, read_append, (build_lengths gs).1]

lemma entry_beyond (gs : List Gate) (i : ℕ) (hi : 13 + gs.length ≤ i) :
    entry gs i = emptyEntry := by
  unfold entry readEntry
  apply List.getD_eq_default
  simpa only [(build_lengths gs).1] using hi

lemma positive_valid (gs : List Gate) (i : ℕ) (hi : 0 < (entry gs i).1) :
    i < 13 + gs.length := by
  by_contra hn
  rw [entry_beyond gs i (by omega)] at hi
  simp [emptyEntry] at hi

lemma support_bound (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (i : ℕ) (hc : (entry gs i).1 ≤ 4) : (entry gs i).2.card ≤ (entry gs i).1 :=
  ((wire_spec gs hg (fun _ => false) i).2 hc).1

lemma certificate_false (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (i : ℕ) (hc : (entry gs i).1 ≤ 4) (x : Fin 13 → Bool)
    (hx : ∀ p ∈ (entry gs i).2, x p = false) : Global.val gs x i = false := by
  cases hv : Global.val gs x i
  · rfl
  · have hs := wire_spec gs hg x i
    have ht := (hs.2 hc).2.symm.trans (hs.1 hv)
    simp only [hit, decide_eq_true_eq] at ht
    obtain ⟨p, hp, hpt⟩ := ht
    rw [hx p hp] at hpt
    exact Bool.noConfusion hpt

def Cert (gs : List Gate) (i : ℕ) (Q : Finset ℕ) : Prop :=
  Q ⊆ Finset.Ico 13 (13 + gs.length) ∧
  ∀ q ∈ Q, q ≤ i ∧ (entry gs q).2 ⊆ (entry gs i).2 ∧ 2 ≤ (entry gs q).2.card ∧
    ∀ x : Fin 13 → Bool, Global.val gs x q = false →
      (∀ p ∈ (entry gs i).2 \ (entry gs q).2, x p = false) → Global.val gs x i = false

lemma cert_empty (gs : List Gate) (i : ℕ) : Cert gs i ∅ := by simp [Cert]

lemma cert_old (gs : List Gate) (g : Gate) (i : ℕ) (Q : Finset ℕ)
    (hQ : Cert gs i Q) (hi : i ≠ 13 + gs.length) : Cert (gs ++ [g]) i Q := by
  refine ⟨?_, ?_⟩
  · intro q hq
    have h := hQ.1 hq
    simp only [Finset.mem_Ico, List.length_append, List.length_cons, List.length_nil] at h ⊢
    omega
  · intro q hq
    have hqrange := hQ.1 hq
    have hqn : q ≠ 13 + gs.length := by simp only [Finset.mem_Ico] at hqrange; omega
    have hh := hQ.2 q hq
    simp only [entry_snoc, hi, hqn, ite_false, Global.val_snoc]
    exact hh

lemma cert_inherit (gs : List Gate) (g : Gate) (j : ℕ) (Q : Finset ℕ)
    (hQ : Cert gs j Q) (hj : j < 13 + gs.length)
    (hsub : (entry gs j).2 ⊆ (entry (gs ++ [g]) (13 + gs.length)).2)
    (hstep : ∀ x : Fin 13 → Bool, Global.val gs x j = false →
      (∀ p ∈ (entry (gs ++ [g]) (13 + gs.length)).2 \ (entry gs j).2, x p = false) →
      Global.val (gs ++ [g]) x (13 + gs.length) = false) :
    Cert (gs ++ [g]) (13 + gs.length) Q := by
  refine ⟨?_, ?_⟩
  · intro q hq
    have h := hQ.1 hq
    simp only [Finset.mem_Ico, List.length_append, List.length_cons, List.length_nil] at h ⊢
    omega
  · intro q hq
    obtain ⟨hqi, hqs, hqc, hctx⟩ := hQ.2 q hq
    have hqn : q ≠ 13 + gs.length := by omega
    have heq : entry (gs ++ [g]) q = entry gs q := by simp [entry_snoc, hqn]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · simpa only [heq] using hqs.trans hsub
    · simpa only [heq] using hqc
    · intro x hx hzero
      have hxq : Global.val gs x q = false := by
        simpa only [Global.val_snoc, hqn, ite_false] using hx
      apply hstep x
      · apply hctx x hxq
        intro p hp
        apply hzero p
        rw [heq]
        exact Finset.mem_sdiff.mpr ⟨hsub (Finset.mem_sdiff.mp hp).1,
          (Finset.mem_sdiff.mp hp).2⟩
      · intro p hp
        apply hzero p
        rw [heq]
        obtain ⟨hpin, hpnot⟩ := Finset.mem_sdiff.mp hp
        exact Finset.mem_sdiff.mpr ⟨hpin, fun h => hpnot (hqs h)⟩

lemma cert_union (gs : List Gate) (i : ℕ) (A B : Finset ℕ)
    (hA : Cert gs i A) (hB : Cert gs i B) : Cert gs i (A ∪ B) := by
  refine ⟨Finset.union_subset hA.1 hB.1, ?_⟩
  intro q hq
  rcases Finset.mem_union.mp hq with hq | hq
  · exact hA.2 q hq
  · exact hB.2 q hq

lemma cert_insert (gs : List Gate) (g : Gate) (Q : Finset ℕ)
    (hQ : Cert (gs ++ [g]) (13 + gs.length) Q)
    (hc : 2 ≤ (entry (gs ++ [g]) (13 + gs.length)).2.card) :
    Cert (gs ++ [g]) (13 + gs.length) (insert (13 + gs.length) Q) := by
  refine ⟨?_, ?_⟩
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · simp only [Finset.mem_Ico, List.length_append, List.length_cons, List.length_nil]
      omega
    · exact hQ.1 hq
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact ⟨le_rfl, Finset.Subset.refl _, hc, fun x hx _ => hx⟩
    · exact hQ.2 q hq

lemma cert_disjoint (gs : List Gate) (a b : ℕ) (A B : Finset ℕ)
    (hA : Cert gs a A) (hB : Cert gs b B)
    (hd : Disjoint (entry gs a).2 (entry gs b).2) : Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro q hqa hqb
  have ha := hA.2 q hqa
  have hb := hB.2 q hqb
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (entry gs q).2.card by omega)
  exact Finset.disjoint_left.mp hd (ha.2.1 hp) (hb.2.1 hp)

lemma and_false (g : Gate) (hop : g.op = GateOp.and) (f : ℕ → Bool)
    (j : ℕ) (hj : j ∈ g.inputs) (hf : f j = false) :
    g.op.eval (g.inputs.map f) = false := by
  cases hv : g.op.eval (g.inputs.map f)
  · rfl
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hv
    have ht := hv (f j) (List.mem_map.mpr ⟨j, hj, rfl⟩)
    rw [hf] at ht
    exact Bool.noConfusion ht

lemma inherit_and (gs : List Gate) (g : Gate) (j : ℕ) (Q : Finset ℕ)
    (hop : g.op = GateOp.and) (hj : j ∈ g.inputs)
    (hQ : Cert gs j Q) (hvalid : j < 13 + gs.length)
    (he : entry (gs ++ [g]) (13 + gs.length) = entry gs j) :
    Cert (gs ++ [g]) (13 + gs.length) Q := by
  apply cert_inherit gs g j Q hQ hvalid
  · rw [he]
  · intro x hx _
    simp only [Global.val_snoc, ite_true]
    exact and_false g hop (Global.val gs x) j hj hx

lemma sharp_union (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (a b : ℕ) (hc : (entry gs a).1 + (entry gs b).1 ≤ 4)
    (hs : ((entry gs a).2 ∪ (entry gs b).2).card = (entry gs a).1 + (entry gs b).1) :
    (entry gs a).2.card = (entry gs a).1 ∧ (entry gs b).2.card = (entry gs b).1 ∧
      Disjoint (entry gs a).2 (entry gs b).2 := by
  have ha := support_bound gs hg a (by omega)
  have hb := support_bound gs hg b (by omega)
  have hu := Finset.card_union_le (entry gs a).2 (entry gs b).2
  have he := Finset.card_union_add_card_inter (entry gs a).2 (entry gs b).2
  refine ⟨by omega, by omega, ?_⟩
  apply Finset.disjoint_iff_inter_eq_empty.mpr
  apply Finset.card_eq_zero.mp
  omega

lemma inherit_or_left (gs : List Gate) (a b : ℕ) (Q : Finset ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hQ : Cert gs a Q) (ha : a < 13 + gs.length)
    (hb : (entry gs b).1 ≤ 4)
    (hd : Disjoint (entry gs a).2 (entry gs b).2) :
    Cert (gs ++ [⟨GateOp.or, [a,b]⟩]) (13 + gs.length) Q := by
  have he : (entry (gs ++ [⟨GateOp.or, [a,b]⟩]) (13 + gs.length)).2 =
      (entry gs a).2 ∪ (entry gs b).2 := by simp [entry_snoc, profile]
  apply cert_inherit gs _ a Q hQ ha
  · rw [he]
    exact Finset.subset_union_left
  · intro x hxa hzero
    have hxb : Global.val gs x b = false := by
      apply certificate_false gs hg b hb x
      intro p hp
      apply hzero p
      rw [he]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hp,
        fun h => Finset.disjoint_left.mp hd h hp⟩
    simp [Global.val_snoc, GateOp.eval, hxa, hxb]

lemma inherit_or_right (gs : List Gate) (a b : ℕ) (Q : Finset ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hQ : Cert gs b Q) (hb : b < 13 + gs.length)
    (ha : (entry gs a).1 ≤ 4)
    (hd : Disjoint (entry gs a).2 (entry gs b).2) :
    Cert (gs ++ [⟨GateOp.or, [a,b]⟩]) (13 + gs.length) Q := by
  have he : (entry (gs ++ [⟨GateOp.or, [a,b]⟩]) (13 + gs.length)).2 =
      (entry gs a).2 ∪ (entry gs b).2 := by simp [entry_snoc, profile]
  apply cert_inherit gs _ b Q hQ hb
  · rw [he]
    exact Finset.subset_union_right
  · intro x hxb hzero
    have hxa : Global.val gs x a = false := by
      apply certificate_false gs hg a ha x
      intro p hp
      apply hzero p
      rw [he]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hp,
        fun h => Finset.disjoint_left.mp hd hp h⟩
    simp [Global.val_snoc, GateOp.eval, hxa, hxb]

lemma entry_nil (i : ℕ) : entry [] i =
    if h : i < 13 then (1, {⟨i,h⟩}) else emptyEntry := by
  by_cases hi : i < 13
  · simp only [entry, build, List.foldl_nil, readEntry, initial,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, dite_true, Option.getD_some]
  · simp [entry, build, initial, readEntry, emptyEntry, hi]

lemma extract (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (i : ℕ) (hc : (entry gs i).1 ≤ 4) (hs : (entry gs i).2.card = (entry gs i).1) :
    ∃ Q : Finset ℕ, (entry gs i).1 ≤ Q.card + 1 ∧ Cert gs i Q := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    refine ⟨∅, ?_, cert_empty _ _⟩
    by_cases hi : i < 13 <;> simp [entry_nil, hi, emptyEntry]
  | append_singleton gs g ih =>
    have hgs : ∀ a ∈ gs, (a.op = GateOp.and ∨ a.op = GateOp.or) ∧ a.inputs.length ≤ 2 := by
      intro a ha
      exact hg a (by simp [ha])
    by_cases hsmall : (entry (gs ++ [g]) i).1 ≤ 1
    · exact ⟨∅, by simpa using hsmall, cert_empty _ _⟩
    by_cases hi : i = 13 + gs.length
    · subst i
      have hgate := hg g (by simp)
      rcases g with ⟨op, ins⟩
      rcases hgate with ⟨hop, hlen⟩
      simp only at hop hlen
      rcases hop with rfl | rfl
      · have take_parent (j : ℕ) (hj : j ∈ ins)
            (he : entry (gs ++ [⟨GateOp.and, ins⟩]) (13 + gs.length) = entry gs j) :
            ∃ Q : Finset ℕ,
              (entry (gs ++ [⟨GateOp.and, ins⟩]) (13 + gs.length)).1 ≤ Q.card + 1 ∧
              Cert (gs ++ [⟨GateOp.and, ins⟩]) (13 + gs.length) Q := by
          have hcj : (entry gs j).1 ≤ 4 := he ▸ hc
          have hsj : (entry gs j).2.card = (entry gs j).1 := he ▸ hs
          obtain ⟨Q, hcount, hQ⟩ := ih hgs j hcj hsj
          have hjpos : 0 < (entry gs j).1 := by rw [he] at hsmall; omega
          exact ⟨Q, by simpa only [he] using hcount,
            inherit_and gs _ j Q rfl hj hQ (positive_valid gs j hjpos) he⟩
        rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
        · simp [entry_snoc, profile] at hc
        ·
          apply take_parent a (by simp)
          simp [entry_snoc, profile]
        ·
          by_cases hab : (entry gs a).1 ≤ (entry gs b).1
          · apply take_parent a (by simp)
            simp [entry_snoc, profile, hab]
          · apply take_parent b (by simp)
            simp [entry_snoc, profile, hab]
        · simp at hlen
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
        · simp [entry_snoc, profile] at hsmall
        ·
          have he0 : entry (gs ++ [⟨GateOp.or, [a]⟩]) (13 + gs.length) =
              (min 5 (entry gs a).1, (entry gs a).2) := by simp [entry_snoc, profile]
          rw [he0] at hc hs hsmall
          have ha : (entry gs a).1 ≤ 4 := by omega
          have hm : min 5 (entry gs a).1 = (entry gs a).1 := Nat.min_eq_right (by omega)
          have he : entry (gs ++ [⟨GateOp.or, [a]⟩]) (13 + gs.length) = entry gs a := by
            rw [he0, hm]
          obtain ⟨Q, hcount, hQ⟩ := ih hgs a ha (by simpa only [hm] using hs)
          refine ⟨Q, by simpa only [he] using hcount, ?_⟩
          apply cert_inherit gs _ a Q hQ (positive_valid gs a (by omega))
          · rw [he]
          · intro x hx _
            simp [Global.val_snoc, GateOp.eval, hx]
        ·
          have he : entry (gs ++ [⟨GateOp.or, [a,b]⟩]) (13 + gs.length) =
              (min 5 ((entry gs a).1 + (entry gs b).1), (entry gs a).2 ∪ (entry gs b).2) := by
            simp [entry_snoc, profile]
          rw [he] at hc hs hsmall
          have hab : (entry gs a).1 + (entry gs b).1 ≤ 4 := by omega
          have hm : min 5 ((entry gs a).1 + (entry gs b).1) =
              (entry gs a).1 + (entry gs b).1 := Nat.min_eq_right (by omega)
          have hUnion : ((entry gs a).2 ∪ (entry gs b).2).card =
              (entry gs a).1 + (entry gs b).1 := by simpa only [hm] using hs
          obtain ⟨hsa, hsb, hd⟩ := sharp_union gs hgs a b hab hUnion
          obtain ⟨A, hca, hA⟩ := ih hgs a (by omega) hsa
          obtain ⟨B, hcb, hB⟩ := ih hgs b (by omega) hsb
          by_cases ha0 : (entry gs a).1 = 0
          · refine ⟨B, ?_, inherit_or_right gs a b B hgs hB
                (positive_valid gs b (by omega)) (by omega) hd⟩
            rw [he]
            change min 5 ((entry gs a).1 + (entry gs b).1) ≤ B.card + 1
            rw [hm, ha0, Nat.zero_add]
            exact hcb
          by_cases hb0 : (entry gs b).1 = 0
          · refine ⟨A, ?_, inherit_or_left gs a b A hgs hA
                (positive_valid gs a (by omega)) (by omega) hd⟩
            rw [he]
            change min 5 ((entry gs a).1 + (entry gs b).1) ≤ A.card + 1
            rw [hm, hb0, Nat.add_zero]
            exact hca
          have hIA := inherit_or_left gs a b A hgs hA
            (positive_valid gs a (by omega)) (by omega) hd
          have hIB := inherit_or_right gs a b B hgs hB
            (positive_valid gs b (by omega)) (by omega) hd
          have hdisj := cert_disjoint gs a b A B hA hB hd
          have hn : 13 + gs.length ∉ A ∪ B := by
            intro hh
            rcases Finset.mem_union.mp hh with hh | hh
            · have hr := hA.1 hh
              simp at hr
            · have hr := hB.1 hh
              simp at hr
          refine ⟨insert (13 + gs.length) (A ∪ B), ?_,
            cert_insert gs _ _ (cert_union _ _ _ _ hIA hIB) ?_⟩
          · rw [Finset.card_insert_of_notMem hn, Finset.card_union_of_disjoint hdisj, he]
            simp only [Prod.fst, hm]
            omega
          · rw [he]
            simp only [Prod.snd]
            rw [hUnion]
            omega
        · simp at hlen
    · have he : entry (gs ++ [g]) i = entry gs i := by simp [entry_snoc, hi]
      obtain ⟨Q, hcount, hQ⟩ := ih hgs i (he ▸ hc) (he ▸ hs)
      exact ⟨Q, by simpa only [he] using hcount, cert_old gs g i Q hQ hi⟩

lemma global_line_card (w : Fin 13) : (Global.line w).card = 4 := Clamp.line_card w

lemma line_profile (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (o : ℕ)
    (hcorrect : ∀ x, Support.Band x → Global.val gs x o = Support.target w x)
    (hc : (entry gs o).1 ≤ 4) : (entry gs o).2 = Global.line w ∧ (entry gs o).1 = 4 := by
  have hcard := support_bound gs hg o hc
  have hline : (entry gs o).2 = Global.line w := by
    apply support_eq_line w (fun x => Global.val gs x o) hcorrect _ (hcard.trans hc)
    intro x hx
    have h := wire_spec gs hg x o
    exact (h.2 hc).2.symm.trans (h.1 hx)
  refine ⟨hline, ?_⟩
  rw [hline, global_line_card] at hcard
  omega

lemma three_contexts (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (o : ℕ)
    (hcorrect : ∀ x, Support.Band x → Global.val gs x o = Support.target w x)
    (hc : (entry gs o).1 ≤ 4) :
    ∃ Q : Finset ℕ, 3 ≤ Q.card ∧ Q ⊆ Finset.Ico 13 (13 + gs.length) ∧
      ∀ q ∈ Q, ∃ C : Finset (Fin 13), C ⊆ Global.line w ∧ C.card ≤ 2 ∧
        ∀ x : Fin 13 → Bool, Global.val gs x q = false →
          (∀ p ∈ C, x p = false) → Global.val gs x o = false := by
  obtain ⟨hline, hcost⟩ := line_profile gs hg w o hcorrect hc
  have hsharp : (entry gs o).2.card = (entry gs o).1 := by rw [hline, hcost, global_line_card]
  obtain ⟨Q, hcount, hQ⟩ := extract gs hg o hc hsharp
  refine ⟨Q, by omega, hQ.1, ?_⟩
  intro q hq
  obtain ⟨hqo, hsub, hcard, hctx⟩ := hQ.2 q hq
  refine ⟨(entry gs o).2 \ (entry gs q).2, ?_, ?_, hctx⟩
  · rw [hline]
    exact Finset.sdiff_subset
  · rw [Finset.card_sdiff_of_subset hsub, hline, global_line_card]
    omega

end PEqualNP.Outside.L_meta_1024_aux.Certificate

namespace PEqualNP.Outside.L_meta_1024_aux.PrivateSurgery
open PEqualNP.CircuitLowerBounds

lemma every_cost_large (gs : List Gate) (hsize : gs.length ≤ 14)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (lineId : Fin 5 → Fin 13) (hinj : Function.Injective lineId) (out : Fin 5 → ℕ)
    (hcorrect : ∀ u (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out u) = Support.target (lineId u) x)
    (hnormal : ∀ u, Global.val gs (Global.Zof (Global.line (lineId u))) (out u) = false) :
    ∀ u, 5 ≤ FalsePruning.cost gs (out u) := by
  intro u₀
  by_contra hcost
  have hc : FalsePruning.cost gs (out u₀) ≤ 4 := by omega
  obtain ⟨P, hcard, hP, hcontexts⟩ := Certificate.three_contexts gs hg (lineId u₀)
    (out u₀) (hcorrect u₀) hc
  apply three_private_impossible gs hsize hg lineId hinj out hcorrect hnormal u₀ P hP hcard
  intro i hi u hu
  obtain ⟨C, hC, hc, hcontext⟩ := hcontexts i hi
  apply context_private gs (out u₀) i (lineId u₀) (fun g hm => (hg g hm).1)
    (hcorrect u₀) C hC hc (fun x hx hf => hcontext x hf hx) (lineId u)
  exact fun he => hu (hinj he)

end PEqualNP.Outside.L_meta_1024_aux.PrivateSurgery

namespace PEqualNP.Outside.L_meta_1024_aux.PrivateSurgery
open PEqualNP.CircuitLowerBounds

lemma normal_clamp_ordinary (gs : List Gate) (o : ℕ) (w : Fin 13) (P : Finset ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ x : Fin 13 → Bool, Support.Band x →
      Global.val gs x o = Support.target w x)
    (hordinary : ∀ x : Fin 13 → Bool, Global.val gs x o = Support.target w x)
    (hprivate : ∀ i ∈ P, Global.val gs (Global.Zof (Global.line w)) i = true) :
    ∀ x : Fin 13 → Bool,
      Global.val (Sink.transform 13 P gs) x o = Support.target w x := by
  have hop := fun g hm => (hg g hm).1
  obtain ⟨hz, he⟩ := (Bridge.ordinary_iff_extremes gs o w hop).mp hordinary
  apply (Bridge.ordinary_iff_extremes (Sink.transform 13 P gs) o w
    (fun g hm => (Sink.transform_allowed 13 P gs hg g hm).1)).mpr
  exact ⟨(normal_clamp gs o w P hg hcorrect hz hprivate).1,
    fun p hp => Sink.val_ge P gs hop (Global.eof p) o (he p hp)⟩

lemma rebuild_ordinary (k : ℕ) (gs : List Gate) (out : Fin k → ℕ)
    (lineId : Fin k → Fin 13) (u₀ : Fin k)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ u (x : Fin 13 → Bool), Support.Band x →
      Global.val gs x (out u) = Support.target (lineId u) x)
    (P : Finset ℕ)
    (hprivate : ∀ i ∈ P, ∀ u, u ≠ u₀ →
      Global.val gs (Global.Zof (Global.line (lineId u))) i = true)
    (u : Fin k) (hordinary : ∀ x : Fin 13 → Bool,
      Global.val gs x (out u) = Support.target (lineId u) x) :
    ∀ x : Fin 13 → Bool,
      Global.val (AppendLine.appendLine (Dead.paidCode 13 P gs) (lineId u₀)) x
        (if u = u₀ then 15 + (Dead.paidCode 13 P gs).length else Dead.paidIndex 13 P gs (out u)) =
      Support.target (lineId u) x := by
  classical
  intro x
  by_cases hu : u = u₀
  · subst u
    simpa using AppendLine.eval (Dead.paidCode 13 P gs) (lineId u₀) x
  · rw [if_neg hu]
    have hz := ((Bridge.ordinary_iff_extremes gs (out u) (lineId u)
      (fun g hm => (hg g hm).1)).mp hordinary).1
    have hkeep : out u ∉ P := by
      intro hm
      have hh := hprivate (out u) hm u hu
      rw [hz] at hh
      exact Bool.noConfusion hh
    have hvalid := (Bridge.output_index gs (out u) (lineId u) (hcorrect u)).2
    have hmapped : Dead.paidIndex 13 P gs (out u) < 13 + (Dead.paidCode 13 P gs).length :=
      Dead.mapped_valid 13 P (Sink.transform 13 P gs) (out u)
        (by simpa only [Sink.transform_length] using hvalid) hkeep
    rw [AppendLine.old _ _ x _ hmapped]
    have heq := Dead.eval P (Sink.transform 13 P gs) (Dead.transform_noReads 13 P gs) x
      (out u) (by simpa only [Sink.transform_length] using hvalid) hkeep
    exact heq.trans (normal_clamp_ordinary gs (out u) (lineId u) P hg (hcorrect u)
      hordinary (fun i hi => hprivate i hi u hu) x)

end PEqualNP.Outside.L_meta_1024_aux.PrivateSurgery
