import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1534

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_snoc (A : List Gate) (g : Gate) (x : List Bool) :
    run (A ++ [g]) x
      = run A x ++ [g.op.eval (g.inputs.map fun i => (run A x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

def val (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (Circuit.wires ⟨gs, 0⟩ (List.ofFn x)).getD i false

def sg (n : ℕ) (v : Fin n) : Fin n → Bool := fun vk : Fin n => decide (vk = v)

def ev (n : ℕ) (g : Gate) (G : List Gate) (x : Fin n → Bool) : Bool :=
  g.op.eval (g.inputs.map fun j => val n G x j)

lemma val_input (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (a : Fin n) :
    val n gs x a.val = x a := by
  change (run gs (List.ofFn x)).getD a.val false = x a
  rw [run_getD _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma val_new (n : ℕ) (A : List Gate) (g : Gate) (x : Fin n → Bool) :
    val n (A ++ [g]) x (n + A.length) = ev n g A x := by
  change (run (A ++ [g]) (List.ofFn x)).getD (n + A.length) false = _
  rw [run_snoc]
  have hl : (run A (List.ofFn x)).length = n + A.length := by simp [run_length]
  rw [List.getD_eq_getElem?_getD, ← hl, List.getElem?_concat_length]
  rfl

lemma val_old (n : ℕ) (A : List Gate) (g : Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : i ≠ n + A.length) :
    val n (A ++ [g]) x i = val n A x i := by
  change (run (A ++ [g]) (List.ofFn x)).getD i false = (run A (List.ofFn x)).getD i false
  rw [run_snoc]
  have hl : (run A (List.ofFn x)).length = n + A.length := by simp [run_length]
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · exact List.getD_append _ _ _ _ (by omega)
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma eval_mono (op : GateOp) (h : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f g : ℕ → Bool) (hfg : ∀ j, f j = true → g j = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases h with h | h
  · subst h
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, id]
    intro H j hj
    exact hfg _ (H j hj)
  · subst h
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨b, ⟨j, hj, rfl⟩, hb⟩
    exact ⟨g j, ⟨j, hj, rfl⟩, hfg _ hb⟩

lemma pick (n : ℕ) (G : List Gate) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hmono : ∀ x y : Fin n → Bool, (∀ v, x v = true → y v = true) →
      ∀ i, val n G x i = true → val n G y i = true) :
    ∃ g2 : Gate, ((g2.op = GateOp.and ∨ g2.op = GateOp.or) ∧ g2.inputs.length ≤ 2) ∧
      (∀ x, ev n g2 G x = true → ev n g G x = true) ∧
      (∀ v, ev n g2 G (sg n v) = ev n g G (sg n v)) ∧
      (∀ x y : Fin n → Bool, (∀ v, x v = true → y v = true) →
        ev n g2 G x = true → ev n g2 G y = true) ∧
      ((Finset.univ.filter (fun au : Fin n => ev n g2 G (sg n au) = true)).card ≤ 1 →
        ∀ ax : Fin n → Bool,
          ev n g2 G ax = decide (∃ av : Fin n, ev n g2 G (sg n av) = true ∧ ax av = true)) := by
  have Fm : ∀ x y : Fin n → Bool, (∀ v, x v = true → y v = true) →
      ev n g G x = true → ev n g G y = true :=
    fun x y hxy h => eval_mono _ hg.1 _ _ _ (fun j => hmono x y hxy j) h
  by_cases hc : (Finset.univ.filter (fun au : Fin n => ev n g G (sg n au) = true)).card ≤ 1
  · by_cases hex : ∃ v, ev n g G (sg n v) = true
    · obtain ⟨a, ha⟩ := hex
      have key : ∀ x, ev n ⟨GateOp.or, [a.val]⟩ G x = x a := by
        intro x
        simp [ev, GateOp.eval, val_input]
      have uniq : ∀ v, ev n g G (sg n v) = true → v = a := fun v hv =>
        Finset.card_le_one.mp hc v (by simp [hv]) a (by simp [ha])
      refine ⟨⟨GateOp.or, [a.val]⟩, ⟨Or.inr rfl, by simp⟩, ?_, ?_, ?_, ?_⟩
      · intro x hx
        rw [key] at hx
        refine Fm (sg n a) x ?_ ha
        intro v hv
        have : v = a := by simpa [sg] using hv
        rw [this]; exact hx
      · intro v
        rw [key]
        by_cases hva : v = a
        · subst hva; simp [sg, ha]
        · have h1 : sg n v a = false := by simp [sg]; exact fun h => hva h.symm
          rw [h1]
          cases h2 : ev n g G (sg n v) with
          | false => rfl
          | true => exact absurd (uniq v h2) hva
      · intro x y hxy hx
        rw [key] at *
        exact hxy a hx
      · intro _ ax
        simp only [key]
        cases h3 : ax a with
        | false =>
          symm
          rw [decide_eq_false_iff_not]
          rintro ⟨av, h4, h5⟩
          have : a = av := by simpa [sg] using h4
          rw [← this, h3] at h5
          exact Bool.false_ne_true h5
        | true =>
          symm
          rw [decide_eq_true_iff]
          exact ⟨a, by simp [sg], h3⟩
    · have key : ∀ x, ev n ⟨GateOp.or, []⟩ G x = false := fun x => rfl
      refine ⟨⟨GateOp.or, []⟩, ⟨Or.inr rfl, by simp⟩, ?_, ?_, ?_, ?_⟩
      · intro x hx; rw [key] at hx; exact absurd hx Bool.false_ne_true
      · intro v
        rw [key]
        cases h2 : ev n g G (sg n v) with
        | false => rfl
        | true => exact absurd ⟨v, h2⟩ hex
      · intro x y _ hx; rw [key] at hx; exact absurd hx Bool.false_ne_true
      · intro _ ax
        simp [key]
  · exact ⟨g, hg, fun _ h => h, fun _ => rfl, Fm, fun h => absurd h hc⟩

lemma main (n : ℕ) (gates : List Gate) :
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    ∃ G : List Gate, G.length = gates.length ∧
      (∀ g2 ∈ G, (g2.op = GateOp.and ∨ g2.op = GateOp.or) ∧ g2.inputs.length ≤ 2) ∧
      (∀ (x : Fin n → Bool) (i : ℕ), val n G x i = true → val n gates x i = true) ∧
      (∀ (v : Fin n) (i : ℕ), val n G (sg n v) i = val n gates (sg n v) i) ∧
      (∀ x y : Fin n → Bool, (∀ v, x v = true → y v = true) →
        ∀ i, val n G x i = true → val n G y i = true) ∧
      (∀ ak : ℕ, ak < G.length →
        (Finset.univ.filter (fun au : Fin n => val n G (sg n au) (n + ak) = true)).card ≤ 1 →
        ∀ ax : Fin n → Bool, val n G ax (n + ak)
          = decide (∃ av : Fin n, val n G (sg n av) (n + ak) = true ∧ ax av = true)) := by
  induction gates using List.reverseRecOn with
  | nil =>
    intro _
    exact ⟨[], rfl, by simp, fun _ _ h => h, fun _ _ => rfl, by
      intro x y hxy i hi
      change (List.ofFn x).getD i false = true at hi
      change (List.ofFn y).getD i false = true
      by_cases hin : i < n
      · have hx := val_input n [] x ⟨i, hin⟩
        have hy := val_input n [] y ⟨i, hin⟩
        change (List.ofFn x).getD i false = _ at hx
        change (List.ofFn y).getD i false = _ at hy
        rw [hy]; rw [hx] at hi; exact hxy _ hi
      · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
        exact absurd hi Bool.false_ne_true, by simp⟩
  | append_singleton A g ih =>
    intro hops
    obtain ⟨G, hlen, hG, hb, hc, hd, he⟩ := ih (fun g' hg' => hops g' (by simp [hg']))
    have hgo := hops g (by simp)
    obtain ⟨g2, hg2, pb, pc, pd, pe⟩ := pick n G g hgo hd
    have hgG : ∀ x, ev n g G x = true → ev n g A x = true := fun x h =>
      eval_mono _ hgo.1 _ _ _ (fun j => hb x j) h
    have hgs : ∀ v, ev n g G (sg n v) = ev n g A (sg n v) := by
      intro v
      unfold ev
      congr 2
      funext j
      exact hc v j
    refine ⟨G ++ [g2], by simp [hlen], ?_, ?_, ?_, ?_, ?_⟩
    · intro g' hg'
      rcases List.mem_append.mp hg' with h | h
      · exact hG g' h
      · rw [List.mem_singleton.mp h]; exact hg2
    · intro x i hi
      by_cases hii : i = n + G.length
      · subst hii
        rw [val_new] at hi
        rw [hlen, val_new]
        exact hgG x (pb x hi)
      · rw [val_old _ _ _ _ _ hii] at hi
        rw [val_old _ _ _ _ _ (hlen ▸ hii)]
        exact hb x i hi
    · intro v i
      by_cases hii : i = n + G.length
      · subst hii
        rw [val_new, hlen, val_new, pc, hgs]
      · rw [val_old _ _ _ _ _ hii, val_old _ _ _ _ _ (hlen ▸ hii)]
        exact hc v i
    · intro x y hxy i hi
      by_cases hii : i = n + G.length
      · subst hii
        rw [val_new] at hi ⊢
        exact pd x y hxy hi
      · rw [val_old _ _ _ _ _ hii] at hi ⊢
        exact hd x y hxy i hi
    · intro ak hak hcard ax
      by_cases hk : ak = G.length
      · subst hk
        simp only [val_new] at hcard ⊢
        exact pe hcard ax
      · have hne : n + ak ≠ n + G.length := by omega
        have hak' : ak < G.length := by
          simp at hak; omega
        simp only [val_old _ _ _ _ _ hne] at hcard ⊢
        exact he ak hak' hcard ax

end PEqualNP.Outside.L_meta_1534

theorem PEqualNP.Outside.L_meta_1534 : ∀ (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (S : Fin m → Finset (Fin n)) (D : Set (Fin n → Bool)), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ v : Fin n, (fun vk : Fin n => decide (vk = v)) ∈ D) → (∀ (w : Fin m) (x : Fin n → Bool), x ∈ D → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn x)).getD (out w) false = decide (∃ v0 ∈ S w, x v0 = true)) → ∃ gates2 : List PEqualNP.CircuitLowerBounds.Gate, gates2.length ≤ gates.length ∧ (∀ g2 ∈ gates2, (g2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g2.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g2.inputs.length ≤ 2) ∧ (∀ ak : ℕ, ak < gates2.length → (Finset.univ.filter (fun au : Fin n => (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn (fun auk : Fin n => decide (auk = au)))).getD (n + ak) false = true)).card ≤ 1 → ∀ ax : Fin n → Bool, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn ax)).getD (n + ak) false = decide (∃ av : Fin n, (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn (fun avk : Fin n => decide (avk = av)))).getD (n + ak) false = true ∧ ax av = true)) ∧ ∀ (w2 : Fin m) (x2 : Fin n → Bool), x2 ∈ D → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates2, 0⟩ (List.ofFn x2)).getD (out w2) false = decide (∃ v2 ∈ S w2, x2 v2 = true) := by
  intro n m gates out S D hops hD hout
  obtain ⟨G, hlen, hG, hb, hc, hd, he⟩ := PEqualNP.Outside.L_meta_1534.main n gates hops
  refine ⟨G, le_of_eq hlen, hG, he, ?_⟩
  intro w x hx
  have hox := hout w x hx
  cases hv : (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨G, 0⟩ (List.ofFn x)).getD (out w) false with
  | true =>
    have h1 := hb x (out w) hv
    exact h1.symm.trans hox
  | false =>
    symm
    rw [decide_eq_false_iff_not]
    rintro ⟨v0, hv0, hxv⟩
    have h1 := hout w _ (hD v0)
    have h2 : decide (∃ v ∈ S w, (fun vk : Fin n => decide (vk = v0)) v = true) = true := by
      rw [decide_eq_true_iff]
      exact ⟨v0, hv0, by simp⟩
    rw [h2] at h1
    have h3 := (hc v0 (out w)).trans h1
    have h4 := hd (PEqualNP.Outside.L_meta_1534.sg n v0) x (by
      intro v hv'
      have : v = v0 := by simpa [PEqualNP.Outside.L_meta_1534.sg] using hv'
      rw [this]; exact hxv) (out w) h3
    exact Bool.false_ne_true (hv.symm.trans h4)
