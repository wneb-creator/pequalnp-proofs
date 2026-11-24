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
