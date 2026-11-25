import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_4970.SelectedMerges

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
  (Finset.Ico n (n + gs.length)).filter fun i =>
    Cnt S gs i ∧ (gs[i - n]?.map Gate.op) = some GateOp.or

lemma D_mono {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
    D S gs ⊆ D S (gs ++ [g]) := by
  classical
  intro i hi
  simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append, List.length_cons,
    List.length_nil] at hi ⊢
  refine ⟨⟨hi.1.1, by omega⟩, ?_⟩
  have hne : i ≠ n + gs.length := by omega
  obtain ⟨hz, u, v, huv, hu, hv⟩ := hi.2.1
  refine ⟨⟨?_, u, v, huv, ?_, ?_⟩, ?_⟩
  · rw [val_snoc, if_neg hne]; exact hz
  · rw [val_snoc, if_neg hne]; exact hu
  · rw [val_snoc, if_neg hne]; exact hv
  · rw [List.getElem?_append_left (by omega)]
    exact hi.2.2

lemma and_false_parent {X : Type} (g : Gate) (hop : g.op = GateOp.and)
    (hlen : g.inputs.length ≤ 2) (f : X → ℕ → Bool) (z u v : X)
    (hz : g.op.eval (g.inputs.map (f z)) = false)
    (hu : g.op.eval (g.inputs.map (f u)) = true)
    (hv : g.op.eval (g.inputs.map (f v)) = true) :
    ∃ r, f z r = false ∧ f u r = true ∧ f v r = true := by
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen hz hu hv
  subst op
  match ins, hlen with
  | [], _ => simp [GateOp.eval] at hz
  | [a], _ => exact ⟨a, by simpa [GateOp.eval] using hz,
      by simpa [GateOp.eval] using hu, by simpa [GateOp.eval] using hv⟩
  | [a,b], _ =>
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true, Bool.and_eq_true] at hu hv
    by_cases ha : f z a = false
    · exact ⟨a, ha, hu.1, hv.1⟩
    · refine ⟨b, ?_, hu.2, hv.2⟩
      cases hza : f z a <;> cases hzb : f z b <;> simp_all [GateOp.eval]
  | _ :: _ :: _ :: _, h => simp at h

lemma main_inv {n : ℕ} (S : Finset (Fin n)) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∃ (l : Fin n → Fin n) (M : Finset ℕ),
      Inv S gs l ∧ M ⊆ D S gs ∧ S.card = (S.image l).card + M.card := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    refine ⟨id, ∅, ?_, by simp, by simp⟩
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
    obtain ⟨l, M, hinv, hM, hcard⟩ := ih (fun g' hg' => hg g' (by simp [hg']))
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
      have hop_or : g.op = GateOp.or := by
        rcases hop with hop | hop
        · obtain ⟨r, hrz, hru, hrv⟩ := and_false_parent g hop hlen
            (fun x j => val gs x j) (Zof S) (eof u0) (eof v0) hz hu0 hv0
          exact False.elim (hne (hinv r u0 v0 hrz hru hrv).2)
        · exact hop
      refine ⟨fun w => if l w = l v0 then l u0 else l w, insert N M, ?_, ?_, ?_⟩
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
      · have hNin : N ∈ D S (gs ++ [g]) := by
          simp only [D, Finset.mem_filter, Finset.mem_Ico, List.length_append,
            List.length_cons, List.length_nil]
          refine ⟨⟨by omega, by omega⟩, ⟨?_, u0, v0, ?_, ?_, ?_⟩, ?_⟩
          · rw [hnew]; exact hz
          · intro h; exact hne (by rw [h])
          · rw [hnew]; exact hu0
          · rw [hnew]; exact hv0
          · simp [hN, hop_or]
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hNin
        · exact D_mono S gs g (hM hi)
      · have huS := (key hz u0 hu0).1
        have hvS := (key hz v0 hv0).1
        have herase : (S.image fun w => if l w = l v0 then l u0 else l w) =
            (S.image l).erase (l v0) := by
          ext z
          constructor
          · intro hzmem
            obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hzmem
            by_cases hwv : l w = l v0
            · simp only [hwv, ite_true]
              exact Finset.mem_erase.mpr ⟨hne, Finset.mem_image.mpr ⟨u0, huS, rfl⟩⟩
            · simp only [hwv, ite_false]
              exact Finset.mem_erase.mpr ⟨hwv, Finset.mem_image.mpr ⟨w, hw, rfl⟩⟩
          · intro hzmem
            obtain ⟨hzv, hwmem⟩ := Finset.mem_erase.mp hzmem
            obtain ⟨w, hw, hwz⟩ := Finset.mem_image.mp hwmem
            refine Finset.mem_image.mpr ⟨w, hw, ?_⟩
            have hwv : l w ≠ l v0 := by simpa [hwz] using hzv
            simp [hwz, hzv]
        have hdrop := Finset.card_erase_add_one
          (Finset.mem_image.mpr ⟨v0, hvS, rfl⟩ : l v0 ∈ S.image l)
        rw [← herase] at hdrop
        have hNnot : N ∉ M := by
          intro hmem
          have hin := hM hmem
          simp only [D, Finset.mem_filter, Finset.mem_Ico] at hin
          omega
        rw [Finset.card_insert_of_notMem hNnot]
        omega
    · refine ⟨l, M, ?_, ?_, hcard⟩
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
      · exact hM.trans (D_mono S gs g)


lemma roots_bound {n : ℕ} (gs : List Gate) (T : Finset (Fin n))
    (O : Finset ℕ) (Q : ℕ → Finset (Fin n)) (R : Finset (Fin n))
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hQT : ∀ o ∈ O, Q o ⊆ T)
    (hf : ∀ o ∈ O, ∀ x : Fin n → Bool, val gs x o = decide (∃ q ∈ Q o, x q = true))
    (hR : ∀ u ∈ T, ∃ r ∈ R, Relation.ReflTransGen
      (fun a b : Fin n => ∃ o ∈ O, a ∈ Q o ∧ b ∈ Q o) u r) :
    ∃ M : Finset ℕ, M ⊆ D T gs ∧ T.card ≤ R.card + M.card := by
  classical
  obtain ⟨l, M, hinv, hM, hcard⟩ := main_inv T gs hg
  have hstep {u v : Fin n} (h : ∃ o ∈ O, u ∈ Q o ∧ v ∈ Q o) : l u = l v := by
    obtain ⟨o, ho, hu, hv⟩ := h
    have hz : val gs (Zof T) o = false := by
      rw [hf o ho]
      apply decide_eq_false_iff_not.mpr
      rintro ⟨q, hq, hval⟩
      have hqT := hQT o ho hq
      simp [Zof, hqT] at hval
    have he (w : Fin n) (hw : w ∈ Q o) : val gs (eof w) o = true := by
      rw [hf o ho]
      exact decide_eq_true ⟨w, hw, by simp [eof]⟩
    exact (hinv o u v hz (he u hu) (he v hv)).2
  have hpath {u v : Fin n} (h : Relation.ReflTransGen
      (fun a b : Fin n => ∃ o ∈ O, a ∈ Q o ∧ b ∈ Q o) u v) : l u = l v := by
    induction h with
    | refl => rfl
    | tail _ h ih => exact ih.trans (hstep h)
  have hsub : T.image l ⊆ R.image l := by
    intro a ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨r, hr, hconn⟩ := hR u hu
    exact Finset.mem_image.mpr ⟨r, hr, (hpath hconn).symm⟩
  have hle := (Finset.card_le_card hsub).trans (Finset.card_image_le (s := R) (f := l))
  exact ⟨M, hM, by omega⟩

lemma counted_or_disjoint {n : ℕ} (gs : List Gate) (S T : Finset (Fin n))
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hst : (S ∩ T).card ≤ 1) : Disjoint (D S gs) (D T gs) := by
  classical
  obtain ⟨ls, Ms, hs, -, -⟩ := main_inv S gs hg
  obtain ⟨lt, Mt, ht, -, -⟩ := main_inv T gs hg
  rw [Finset.disjoint_left]
  intro i his hit
  change i ∈ (Finset.Ico n (n + gs.length)).filter
    (fun j => Cnt S gs j ∧ (gs[j - n]?.map Gate.op) = some GateOp.or) at his
  change i ∈ (Finset.Ico n (n + gs.length)).filter
    (fun j => Cnt T gs j ∧ (gs[j - n]?.map Gate.op) = some GateOp.or) at hit
  have hcs : Cnt S gs i := (Finset.mem_filter.mp his).2.1
  have hct : Cnt T gs i := (Finset.mem_filter.mp hit).2.1
  obtain ⟨hza, u, v, huv, hu, hv⟩ := hcs
  obtain ⟨hzb, -⟩ := hct
  have hsub : ({u, v} : Finset (Fin n)) ⊆ S ∩ T := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hwu | hwv
    · rw [hwu]
      exact Finset.mem_inter.mpr ⟨(hs i u u hza hu hu).1, (ht i u u hzb hu hu).1⟩
    · rw [hwv]
      exact Finset.mem_inter.mpr ⟨(hs i v v hza hv hv).1, (ht i v v hzb hv hv).1⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair huv] at hc
  omega

end PEqualNP.Outside.L_meta_4970.SelectedMerges

#print axioms PEqualNP.Outside.L_meta_4970.SelectedMerges.fold_length
#print axioms PEqualNP.Outside.L_meta_4970.SelectedMerges.val_nil
#print axioms PEqualNP.Outside.L_meta_4970.SelectedMerges.val_snoc
#print axioms PEqualNP.Outside.L_meta_4970.SelectedMerges.gate_cases
#print axioms PEqualNP.Outside.L_meta_4970.SelectedMerges.D_mono
#print axioms PEqualNP.Outside.L_meta_4970.SelectedMerges.and_false_parent
#print axioms PEqualNP.Outside.L_meta_4970.SelectedMerges.main_inv
#print axioms PEqualNP.Outside.L_meta_4970.SelectedMerges.roots_bound
#print axioms PEqualNP.Outside.L_meta_4970.SelectedMerges.counted_or_disjoint
