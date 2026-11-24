import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1383
open PEqualNP.CircuitLowerBounds

theorem getD_app_lt {α : Type} (l l' : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_len {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ge {α : Type} (l : List α) (d : α) (i : ℕ) (h : l.length ≤ i) : l.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

def dg (n : ℕ) (M : Finset ℕ) (G : List Gate) (x : ℕ) : ℕ :=
  ((Circuit.mk G 0).lineDegrees n M).getD x 0

def vl (n : ℕ) (G : List Gate) (z : Fin n → Bool) (x : ℕ) : Bool :=
  ((Circuit.mk G 0).wires (List.ofFn z)).getD x false

theorem ld_snoc (n : ℕ) (M : Finset ℕ) (G : List Gate) (g : Gate) :
    (Circuit.mk (G ++ [g]) 0).lineDegrees n M
      = (Circuit.mk G 0).lineDegrees n M ++ [g.lineDegree ((Circuit.mk G 0).lineDegrees n M)] := by
  simp [Circuit.lineDegrees, List.foldl_append]

theorem ld_len (n : ℕ) (M : Finset ℕ) (G : List Gate) :
    ((Circuit.mk G 0).lineDegrees n M).length = n + G.length := by
  induction G using List.reverseRecOn with
  | nil => simp [Circuit.lineDegrees]
  | append_singleton G g ih => rw [ld_snoc]; simp [ih]; omega

theorem wr_snoc (G : List Gate) (g : Gate) (x : List Bool) :
    (Circuit.mk (G ++ [g]) 0).wires x
      = (Circuit.mk G 0).wires x ++ [g.op.eval (g.inputs.map fun i => ((Circuit.mk G 0).wires x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]

theorem wr_len (n : ℕ) (G : List Gate) (z : Fin n → Bool) :
    ((Circuit.mk G 0).wires (List.ofFn z)).length = n + G.length := by
  induction G using List.reverseRecOn with
  | nil => simp [Circuit.wires]
  | append_singleton G g ih => rw [wr_snoc]; simp [ih]; omega

theorem dg_snoc_lt (n : ℕ) (M : Finset ℕ) (G : List Gate) (g : Gate) (x : ℕ) (h : x < n + G.length) :
    dg n M (G ++ [g]) x = dg n M G x := by
  unfold dg; rw [ld_snoc]; exact getD_app_lt _ _ _ _ (by rw [ld_len]; exact h)

theorem vl_snoc_lt (n : ℕ) (G : List Gate) (g : Gate) (z : Fin n → Bool) (x : ℕ) (h : x < n + G.length) :
    vl n (G ++ [g]) z x = vl n G z x := by
  unfold vl; rw [wr_snoc]; exact getD_app_lt _ _ _ _ (by rw [wr_len]; exact h)

theorem dg_app_lt (n : ℕ) (M : Finset ℕ) (G H : List Gate) (x : ℕ) (h : x < n + G.length) :
    dg n M (G ++ H) x = dg n M G x := by
  induction H using List.reverseRecOn with
  | nil => simp
  | append_singleton H g ih =>
    rw [← List.append_assoc, dg_snoc_lt _ _ _ _ _ (by simp; omega), ih]

theorem vl_app_lt (n : ℕ) (G H : List Gate) (z : Fin n → Bool) (x : ℕ) (h : x < n + G.length) :
    vl n (G ++ H) z x = vl n G z x := by
  induction H using List.reverseRecOn with
  | nil => simp
  | append_singleton H g ih =>
    rw [← List.append_assoc, vl_snoc_lt _ _ _ _ _ (by simp; omega), ih]

theorem dg_ge (n : ℕ) (M : Finset ℕ) (G : List Gate) (x : ℕ) (h : n + G.length ≤ x) :
    dg n M G x = 0 := by
  unfold dg; exact getD_ge _ _ _ (by rw [ld_len]; exact h)

theorem vl_ge (n : ℕ) (G : List Gate) (z : Fin n → Bool) (x : ℕ) (h : n + G.length ≤ x) :
    vl n G z x = false := by
  unfold vl; exact getD_ge _ _ _ (by rw [wr_len]; exact h)

theorem dg_new (n : ℕ) (M : Finset ℕ) (G : List Gate) (g : Gate) :
    dg n M (G ++ [g]) (n + G.length) = g.lineDegree ((Circuit.mk G 0).lineDegrees n M) := by
  unfold dg; rw [ld_snoc]
  have h := ld_len n M G
  rw [← h]; exact getD_app_len _ _ _

theorem vl_new (n : ℕ) (G : List Gate) (g : Gate) (z : Fin n → Bool) :
    vl n (G ++ [g]) z (n + G.length)
      = g.op.eval (g.inputs.map fun i => ((Circuit.mk G 0).wires (List.ofFn z)).getD i false) := by
  unfold vl; rw [wr_snoc]
  have h := wr_len n G z
  rw [← h]; exact getD_app_len _ _ _

theorem dg_and (n : ℕ) (M : Finset ℕ) (G : List Gate) (a b : ℕ) :
    dg n M (G ++ [(Gate.mk GateOp.and [a, b])]) (n + G.length) = dg n M G a + dg n M G b := by
  rw [dg_new]; simp [Gate.lineDegree, dg]

theorem dg_or (n : ℕ) (M : Finset ℕ) (G : List Gate) (a b : ℕ) :
    dg n M (G ++ [(Gate.mk GateOp.or [a, b])]) (n + G.length) = max (dg n M G a) (dg n M G b) := by
  rw [dg_new]; simp [Gate.lineDegree, dg]

theorem vl_and (n : ℕ) (G : List Gate) (a b : ℕ) (z : Fin n → Bool) :
    vl n (G ++ [(Gate.mk GateOp.and [a, b])]) z (n + G.length) = (vl n G z a && vl n G z b) := by
  rw [vl_new]; simp [GateOp.eval, vl]

theorem vl_or (n : ℕ) (G : List Gate) (a b : ℕ) (z : Fin n → Bool) :
    vl n (G ++ [(Gate.mk GateOp.or [a, b])]) z (n + G.length) = (vl n G z a || vl n G z b) := by
  rw [vl_new]; simp [GateOp.eval, vl]

theorem dg_input (n : ℕ) (M : Finset ℕ) (G : List Gate) (x : ℕ) (h : x < n) : dg n M G x ≤ 1 := by
  have h1 := dg_app_lt n M [] G x (by simpa using h)
  rw [List.nil_append] at h1
  rw [h1]
  unfold dg
  simp only [Circuit.lineDegrees, List.foldl_nil]
  rw [List.getD_eq_getElem?_getD]
  simp [List.getElem?_range h]
  split <;> omega

def nrm (w : ℕ) (g : Gate) : Bool × ℕ × ℕ :=
  match g.op, g.inputs with
  | GateOp.and, [x, y] => (true, x, y)
  | _, [x, y] => (false, x, y)
  | _, [x] => (false, x, x)
  | _, _ => (false, w, w)

theorem nrm_deg (w : ℕ) (g : Gate) (d : List ℕ) (hd : d.length = w)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    g.lineDegree d = if (nrm w g).1 = true then d.getD (nrm w g).2.1 0 + d.getD (nrm w g).2.2 0
      else max (d.getD (nrm w g).2.1 0) (d.getD (nrm w g).2.2 0) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨h1, h2⟩ := hg
  have hw : d[w]?.getD 0 = 0 := by simp [List.getElem?_eq_none (show d.length ≤ w by omega)]
  rcases ins with _ | ⟨x, _ | ⟨y, _ | ⟨t, l⟩⟩⟩
  · rcases h1 with h1 | h1 <;> simp only at h1 <;> subst h1 <;> simp [nrm, Gate.lineDegree, hw]
  · rcases h1 with h1 | h1 <;> simp only at h1 <;> subst h1 <;> simp [nrm, Gate.lineDegree]
  · rcases h1 with h1 | h1 <;> simp only at h1 <;> subst h1 <;> simp [nrm, Gate.lineDegree]
  · simp at h2

theorem nrm_val (w : ℕ) (g : Gate) (d : List ℕ) (v : List Bool) (hv : v.length = w)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hpos : 0 < g.lineDegree d) :
    g.op.eval (g.inputs.map fun i => v.getD i false)
      = if (nrm w g).1 = true then (v.getD (nrm w g).2.1 false && v.getD (nrm w g).2.2 false)
      else (v.getD (nrm w g).2.1 false || v.getD (nrm w g).2.2 false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨h1, h2⟩ := hg
  have hw : v[w]?.getD false = false := by simp [List.getElem?_eq_none (show v.length ≤ w by omega)]
  rcases ins with _ | ⟨x, _ | ⟨y, _ | ⟨t, l⟩⟩⟩
  · rcases h1 with h1 | h1 <;> simp only at h1 <;> subst h1
    · simp [Gate.lineDegree] at hpos
    · simp [nrm, GateOp.eval, hw]
  · rcases h1 with h1 | h1 <;> simp only at h1 <;> subst h1 <;> simp [nrm, GateOp.eval]
  · rcases h1 with h1 | h1 <;> simp only at h1 <;> subst h1 <;> simp [nrm, GateOp.eval]
  · simp at h2


abbrev St : Type := List Gate × (ℕ → ℕ) × ℕ × List (ℕ × ℕ)

def WF (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St) : Prop :=
  (∃ E, st.1 = Cg ++ E) ∧
  (∀ h ∈ st.1, (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) ∧
  st.1.length ≤ L ∧
  st.2.2.2.length ≤ st.1.length ∧
  (∀ w, st.2.1 w < n + st.1.length) ∧
  (st.2.2.1 < n + st.1.length ∧ dg n M st.1 st.2.2.1 ≤ 4) ∧
  (∀ p ∈ st.2.2.2, (p.1 < n + st.1.length ∧ p.2 < n + st.1.length) ∧
    dg n M st.1 p.1 ≤ 2 ∧ dg n M st.1 p.2 ≤ 2) ∧
  (∀ w, st.2.1 w = n + Cg.length ∨
    (w < n + r ∧ 3 ≤ dg n M Cg w ∧ dg n M st.1 (st.2.1 w) + dg n M Cg w ≤ 4)) ∧
  (n + Cg.length < n + st.1.length ∧ dg n M st.1 (n + Cg.length) = 0 ∧
    ∀ z, vl n st.1 z (n + Cg.length) = false) ∧
  (∀ z, (vl n st.1 z st.2.2.1 = true ↔
    ∃ p ∈ st.2.2.2, vl n st.1 z p.1 = true ∧ vl n st.1 z p.2 = true))

def Sem (n : ℕ) (Cg : List Gate) (st : St) (z : Fin n → Bool) : Prop :=
  vl n st.1 z st.2.2.1 = true ∨
    ∃ w, st.2.1 w ≠ n + Cg.length ∧ vl n st.1 z (st.2.1 w) = true ∧ vl n Cg z w = true

theorem wf_ext (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St)
    (h : WF n M Cg L r st) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    WF n M Cg (L + 1) r (st.1 ++ [g], st.2) := by
  obtain ⟨⟨E, h1⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  unfold WF
  dsimp only
  have hl : (st.1 ++ [g]).length = st.1.length + 1 := by simp
  refine ⟨⟨E ++ [g], by rw [h1, List.append_assoc]⟩, ?_, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    rw [List.mem_append, List.mem_singleton] at hh
    rcases hh with hh | hh
    · exact h2 _ hh
    · rw [hh]; exact hg
  · intro w; have := h5 w; omega
  · exact ⟨by omega, by rw [dg_snoc_lt _ _ _ _ _ h6.1]; exact h6.2⟩
  · intro p hp
    obtain ⟨⟨a, b⟩, c, d⟩ := h7 p hp
    exact ⟨⟨by omega, by omega⟩, by rw [dg_snoc_lt _ _ _ _ _ a]; exact c,
      by rw [dg_snoc_lt _ _ _ _ _ b]; exact d⟩
  · intro w
    rcases h8 w with e | ⟨a, b, c⟩
    · left; exact e
    · right; exact ⟨a, b, by rw [dg_snoc_lt _ _ _ _ _ (h5 w)]; exact c⟩
  · exact ⟨by omega, by rw [dg_snoc_lt _ _ _ _ _ h9.1]; exact h9.2.1,
      fun z => by rw [vl_snoc_lt _ _ _ _ _ h9.1]; exact h9.2.2 z⟩
  · intro z
    rw [vl_snoc_lt _ _ _ _ _ h6.1, h10 z]
    constructor
    · rintro ⟨p, hp, e⟩
      refine ⟨p, hp, ?_⟩
      rw [vl_snoc_lt _ _ _ _ _ (h7 p hp).1.1, vl_snoc_lt _ _ _ _ _ (h7 p hp).1.2]; exact e
    · rintro ⟨p, hp, e⟩
      refine ⟨p, hp, ?_⟩
      rw [vl_snoc_lt _ _ _ _ _ (h7 p hp).1.1, vl_snoc_lt _ _ _ _ _ (h7 p hp).1.2] at e; exact e

theorem sem_ext (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St)
    (h : WF n M Cg L r st) (g : Gate) (z : Fin n → Bool) :
    Sem n Cg (st.1 ++ [g], st.2) z ↔ Sem n Cg st z := by
  obtain ⟨-, -, -, -, h5, h6, -⟩ := h
  unfold Sem
  dsimp only
  rw [vl_snoc_lt _ _ _ _ _ h6.1]
  apply or_congr Iff.rfl
  apply exists_congr
  intro w
  rw [vl_snoc_lt _ _ _ _ _ (h5 w)]

theorem wf_setctx (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St)
    (h : WF n M Cg L r st) (x v : ℕ) (hv : v < n + st.1.length)
    (hd : v = n + Cg.length ∨
      (x < n + r ∧ 3 ≤ dg n M Cg x ∧ dg n M st.1 v + dg n M Cg x ≤ 4)) :
    WF n M Cg L r (st.1, Function.update st.2.1 x v, st.2.2) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  unfold WF
  dsimp only
  refine ⟨h1, h2, h3, h4, ?_, h6, h7, ?_, h9, h10⟩
  · intro w
    by_cases e : w = x
    · subst e; simpa using hv
    · simpa [Function.update, e] using h5 w
  · intro w
    by_cases e : w = x
    · subst e; simpa using hd
    · simpa [Function.update, e] using h8 w

theorem sem_split (n : ℕ) (Cg : List Gate) (st : St) (x : ℕ) (z : Fin n → Bool) :
    Sem n Cg st z ↔ (vl n st.1 z st.2.2.1 = true ∨
      (st.2.1 x ≠ n + Cg.length ∧ vl n st.1 z (st.2.1 x) = true ∧ vl n Cg z x = true) ∨
      ∃ w, w ≠ x ∧ st.2.1 w ≠ n + Cg.length ∧ vl n st.1 z (st.2.1 w) = true ∧ vl n Cg z w = true) := by
  unfold Sem
  constructor
  · rintro (h | ⟨w, a, b, c⟩)
    · left; exact h
    · by_cases e : w = x
      · subst e; right; left; exact ⟨a, b, c⟩
      · right; right; exact ⟨w, e, a, b, c⟩
  · rintro (h | ⟨a, b, c⟩ | ⟨w, e, a, b, c⟩)
    · left; exact h
    · right; exact ⟨x, a, b, c⟩
    · right; exact ⟨w, a, b, c⟩

theorem sem_setctx (n : ℕ) (Cg : List Gate) (st : St) (x v : ℕ) (z : Fin n → Bool) :
    Sem n Cg (st.1, Function.update st.2.1 x v, st.2.2) z ↔ (vl n st.1 z st.2.2.1 = true ∨
      (v ≠ n + Cg.length ∧ vl n st.1 z v = true ∧ vl n Cg z x = true) ∨
      ∃ w, w ≠ x ∧ st.2.1 w ≠ n + Cg.length ∧ vl n st.1 z (st.2.1 w) = true ∧ vl n Cg z w = true) := by
  rw [sem_split n Cg _ x z]
  dsimp only
  apply or_congr Iff.rfl
  apply or_congr
  · simp
  · apply exists_congr
    intro w
    constructor
    · rintro ⟨e, a⟩
      simp only [Function.update, e, dite_false] at a
      exact ⟨e, a⟩
    · rintro ⟨e, a⟩
      simp only [Function.update, e, dite_false]
      exact ⟨e, a⟩

theorem wf_setU (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St)
    (h : WF n M Cg L r st) (v a b : ℕ) (hv : v < n + st.1.length) (hdv : dg n M st.1 v ≤ 4)
    (ha : a < n + st.1.length) (hb : b < n + st.1.length)
    (hda : dg n M st.1 a ≤ 2) (hdb : dg n M st.1 b ≤ 2)
    (hl : st.2.2.2.length + 1 ≤ st.1.length)
    (hval : ∀ z, vl n st.1 z v = (vl n st.1 z st.2.2.1 || (vl n st.1 z a && vl n st.1 z b))) :
    WF n M Cg L r (st.1, st.2.1, v, (a, b) :: st.2.2.2) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  unfold WF
  dsimp only
  refine ⟨h1, h2, h3, by simpa using hl, h5, ⟨hv, hdv⟩, ?_, h8, h9, ?_⟩
  · intro p hp
    rw [List.mem_cons] at hp
    rcases hp with hp | hp
    · rw [hp]; exact ⟨⟨ha, hb⟩, hda, hdb⟩
    · exact h7 p hp
  · intro z
    rw [hval z, Bool.or_eq_true, h10 z, Bool.and_eq_true]
    constructor
    · rintro (⟨p, hp, e⟩ | e)
      · exact ⟨p, List.mem_cons_of_mem _ hp, e⟩
      · exact ⟨(a, b), List.mem_cons_self, e⟩
    · rintro ⟨p, hp, e⟩
      rw [List.mem_cons] at hp
      rcases hp with hp | hp
      · right; rw [hp] at e; exact e
      · left; exact ⟨p, hp, e⟩

theorem sem_setU (n : ℕ) (Cg : List Gate) (st : St) (v a b : ℕ) (z : Fin n → Bool)
    (hval : vl n st.1 z v = (vl n st.1 z st.2.2.1 || (vl n st.1 z a && vl n st.1 z b))) :
    Sem n Cg (st.1, st.2.1, v, (a, b) :: st.2.2.2) z ↔
      (Sem n Cg st z ∨ (vl n st.1 z a = true ∧ vl n st.1 z b = true)) := by
  unfold Sem
  dsimp only
  rw [hval, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  · rintro ((h | h) | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)


def push (n x c : ℕ) (st : St) : St :=
  (st.1 ++ [(Gate.mk GateOp.or [st.2.1 x, c])], Function.update st.2.1 x (n + st.1.length), st.2.2)

theorem wf_push (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St)
    (h : WF n M Cg L r st) (x c : ℕ) (hx : x < n + r)
    (h3 : 3 ≤ dg n M Cg x) (hdc : dg n M st.1 c + dg n M Cg x ≤ 4) :
    WF n M Cg (L + 1) r (push n x c st) := by
  have h' := wf_ext n M Cg L r st h (Gate.mk GateOp.or [st.2.1 x, c]) ⟨Or.inr rfl, by simp⟩
  have h8 := h.2.2.2.2.2.2.2.1 x
  have h9 := h.2.2.2.2.2.2.2.2.1
  unfold push
  refine wf_setctx n M Cg (L + 1) r _ h' x (n + st.1.length) ?_ (Or.inr ⟨hx, h3, ?_⟩)
  · dsimp only; simp
  · dsimp only
    rw [dg_or]
    have hm : max (dg n M st.1 (st.2.1 x)) (dg n M st.1 c) ≤ 4 - dg n M Cg x := by
      apply max_le
      · rcases h8 with e | ⟨-, -, e⟩
        · rw [e, h9.2.1]; omega
        · omega
      · omega
    omega

theorem sem_push (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St)
    (h : WF n M Cg L r st) (x c : ℕ) (z : Fin n → Bool) :
    Sem n Cg (push n x c st) z ↔
      (Sem n Cg st z ∨ (vl n st.1 z c = true ∧ vl n Cg z x = true)) := by
  have h5 := h.2.2.2.2.1 x
  have h9 := h.2.2.2.2.2.2.2.2.1
  have hne : n + st.1.length ≠ n + Cg.length := by omega
  have hZ : st.2.1 x = n + Cg.length → vl n st.1 z (st.2.1 x) = false :=
    fun e => by rw [e]; exact h9.2.2 z
  unfold push
  refine Iff.trans (sem_setctx n Cg (st.1 ++ [(Gate.mk GateOp.or [st.2.1 x, c])], st.2) x _ z) ?_
  rw [← sem_ext n M Cg L r st h (Gate.mk GateOp.or [st.2.1 x, c]) z,
    sem_split n Cg (st.1 ++ [(Gate.mk GateOp.or [st.2.1 x, c])], st.2) x z]
  dsimp only
  rw [vl_or, vl_snoc_lt _ _ _ _ _ h5, Bool.or_eq_true]
  constructor
  · rintro (hu | ⟨-, hv, hc'⟩ | hr)
    · exact Or.inl (Or.inl hu)
    · rcases hv with hv | hv
      · by_cases e : st.2.1 x = n + Cg.length
        · rw [hZ e] at hv; exact absurd hv (by simp)
        · exact Or.inl (Or.inr (Or.inl ⟨e, hv, hc'⟩))
      · exact Or.inr ⟨hv, hc'⟩
    · exact Or.inl (Or.inr (Or.inr hr))
  · rintro ((hu | ⟨-, hv, hc'⟩ | hr) | ⟨hv, hc'⟩)
    · exact Or.inl hu
    · exact Or.inr (Or.inl ⟨hne, Or.inl hv, hc'⟩)
    · exact Or.inr (Or.inr hr)
    · exact Or.inr (Or.inl ⟨hne, Or.inr hv, hc'⟩)

def term (n a b : ℕ) (st : St) : St :=
  (st.1 ++ [(Gate.mk GateOp.and [a, b])] ++ [(Gate.mk GateOp.or [st.2.2.1, n + st.1.length])], st.2.1,
    n + (st.1 ++ [(Gate.mk GateOp.and [a, b])]).length, (a, b) :: st.2.2.2)

theorem term_vals (n : ℕ) (G : List Gate) (U a b : ℕ) (z : Fin n → Bool)
    (hU : U < n + G.length) (ha : a < n + G.length) (hb : b < n + G.length) :
    vl n (G ++ [(Gate.mk GateOp.and [a, b])] ++ [(Gate.mk GateOp.or [U, n + G.length])]) z U = vl n G z U ∧
    vl n (G ++ [(Gate.mk GateOp.and [a, b])] ++ [(Gate.mk GateOp.or [U, n + G.length])]) z a = vl n G z a ∧
    vl n (G ++ [(Gate.mk GateOp.and [a, b])] ++ [(Gate.mk GateOp.or [U, n + G.length])]) z b = vl n G z b ∧
    vl n (G ++ [(Gate.mk GateOp.and [a, b])] ++ [(Gate.mk GateOp.or [U, n + G.length])]) z
      (n + (G ++ [(Gate.mk GateOp.and [a, b])]).length) = (vl n G z U || (vl n G z a && vl n G z b)) := by
  have hl : (G ++ [(Gate.mk GateOp.and [a, b])]).length = G.length + 1 := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [vl_snoc_lt _ _ _ _ _ (by omega), vl_snoc_lt _ _ _ _ _ hU]
  · rw [vl_snoc_lt _ _ _ _ _ (by omega), vl_snoc_lt _ _ _ _ _ ha]
  · rw [vl_snoc_lt _ _ _ _ _ (by omega), vl_snoc_lt _ _ _ _ _ hb]
  · rw [vl_or, vl_and, vl_snoc_lt _ _ _ _ _ hU]

theorem wf_term (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St)
    (h : WF n M Cg L r st) (a b : ℕ) (ha : a < n + st.1.length) (hb : b < n + st.1.length)
    (hda : dg n M st.1 a ≤ 2) (hdb : dg n M st.1 b ≤ 2) :
    WF n M Cg (L + 1 + 1) r (term n a b st) := by
  have h1 := wf_ext n M Cg L r st h (Gate.mk GateOp.and [a, b]) ⟨Or.inl rfl, by simp⟩
  have h2 := wf_ext n M Cg (L + 1) r _ h1 (Gate.mk GateOp.or [st.2.2.1, n + st.1.length])
    ⟨Or.inr rfl, by simp⟩
  have h4 := h.2.2.2.1
  have h6 := h.2.2.2.2.2.1
  have hl : (st.1 ++ [(Gate.mk GateOp.and [a, b])]).length = st.1.length + 1 := by simp
  have hl2 : (st.1 ++ [(Gate.mk GateOp.and [a, b])] ++ [(Gate.mk GateOp.or [st.2.2.1, n + st.1.length])]).length
      = st.1.length + 2 := by simp
  unfold term
  refine wf_setU n M Cg (L + 1 + 1) r _ h2 _ a b ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · dsimp only; omega
  · dsimp only
    rw [dg_or, dg_snoc_lt _ _ _ _ _ h6.1, dg_and]
    exact max_le h6.2 (by omega)
  · dsimp only; omega
  · dsimp only; omega
  · dsimp only
    rw [dg_snoc_lt _ _ _ _ _ (by omega), dg_snoc_lt _ _ _ _ _ ha]; exact hda
  · dsimp only
    rw [dg_snoc_lt _ _ _ _ _ (by omega), dg_snoc_lt _ _ _ _ _ hb]; exact hdb
  · dsimp only; omega
  · intro z
    dsimp only
    obtain ⟨e1, e2, e3, e4⟩ := term_vals n st.1 st.2.2.1 a b z h6.1 ha hb
    rw [e1, e2, e3, e4]

theorem sem_term (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St)
    (h : WF n M Cg L r st) (a b : ℕ) (ha : a < n + st.1.length) (hb : b < n + st.1.length)
    (z : Fin n → Bool) :
    Sem n Cg (term n a b st) z ↔
      (Sem n Cg st z ∨ (vl n st.1 z a = true ∧ vl n st.1 z b = true)) := by
  have h1 := wf_ext n M Cg L r st h (Gate.mk GateOp.and [a, b]) ⟨Or.inl rfl, by simp⟩
  have h6 := h.2.2.2.2.2.1
  obtain ⟨e1, e2, e3, e4⟩ := term_vals n st.1 st.2.2.1 a b z h6.1 ha hb
  unfold term
  refine Iff.trans (sem_setU n Cg
    (st.1 ++ [(Gate.mk GateOp.and [a, b])] ++ [(Gate.mk GateOp.or [st.2.2.1, n + st.1.length])], st.2)
    _ a b z ?_) ?_
  · dsimp only; rw [e1, e2, e3, e4]
  · dsimp only
    rw [e2, e3]
    apply or_congr _ Iff.rfl
    exact Iff.trans (sem_ext n M Cg (L + 1) r (st.1 ++ [(Gate.mk GateOp.and [a, b])], st.2) h1 _ z)
      (sem_ext n M Cg L r st h _ z)


theorem ite_p {α : Type} (c : Prop) [Decidable c] (a b : α) (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_n {α : Type} (c : Prop) [Decidable c] (a b : α) (h : ¬ c) : (if c then a else b) = b := by
  simp [h]

theorem wf_mono (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L L' r : ℕ) (st : St)
    (h : WF n M Cg L r st) (hL : L ≤ L') : WF n M Cg L' r st := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨h1, h2, by omega, h4⟩

theorem wf_shrink (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St)
    (h : WF n M Cg L (r + 1) st) (hz : st.2.1 (n + r) = n + Cg.length) : WF n M Cg L r st := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, ?_, h9⟩
  intro w
  rcases h8 w with e | ⟨a, b, c⟩
  · left; exact e
  · by_cases e : w = n + r
    · left; rw [e]; exact hz
    · right; exact ⟨by omega, b, c⟩

theorem wf_dgC (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St)
    (h : WF n M Cg L r st) (x : ℕ) (hx : x < n + Cg.length) :
    dg n M st.1 x = dg n M Cg x := by
  obtain ⟨⟨E, h1⟩, -⟩ := h
  rw [h1]; exact dg_app_lt n M Cg E x hx

theorem wf_vlC (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St)
    (h : WF n M Cg L r st) (z : Fin n → Bool) (x : ℕ) (hx : x < n + Cg.length) :
    vl n st.1 z x = vl n Cg z x := by
  obtain ⟨⟨E, h1⟩, -⟩ := h
  rw [h1]; exact vl_app_lt n Cg E z x hx

def clr (Z w : ℕ) (st : St) : St := (st.1, Function.update st.2.1 w Z, st.2.2)

theorem wf_clr (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St)
    (h : WF n M Cg L (r + 1) st) : WF n M Cg L r (clr (n + Cg.length) (n + r) st) := by
  have h9 := h.2.2.2.2.2.2.2.2.1
  apply wf_shrink
  · exact wf_setctx n M Cg L (r + 1) st h (n + r) (n + Cg.length) h9.1 (Or.inl rfl)
  · simp [clr]

theorem sem_clr (n : ℕ) (Cg : List Gate) (st : St) (w : ℕ) (z : Fin n → Bool) :
    Sem n Cg st z ↔ (Sem n Cg (clr (n + Cg.length) w st) z ∨
      (st.2.1 w ≠ n + Cg.length ∧ vl n st.1 z (st.2.1 w) = true ∧ vl n Cg z w = true)) := by
  unfold clr
  rw [sem_setctx n Cg st w (n + Cg.length) z, sem_split n Cg st w z]
  constructor
  · rintro (h | h | h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr (Or.inr h))
  · rintro ((h | ⟨h, -⟩ | h) | h)
    · exact Or.inl h
    · exact absurd rfl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

def opnd (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (w c x : ℕ) (st : St) : St :=
  if x < w then (if 3 ≤ dg n M Cg x then push n x c st else term n c x st) else st

theorem opnd_ok (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St)
    (h : WF n M Cg L r st) (hr : r ≤ Cg.length) (c x : ℕ)
    (hc : c < n + st.1.length) (hc1 : dg n M st.1 c ≤ 1)
    (hd : x < n + r → dg n M st.1 c + dg n M Cg x ≤ 4) :
    WF n M Cg (L + 2) r (opnd n M Cg (n + r) c x st) ∧
    (∀ z, Sem n Cg (opnd n M Cg (n + r) c x st) z ↔
      (Sem n Cg st z ∨ (vl n st.1 z c = true ∧ x < n + r ∧ vl n Cg z x = true))) ∧
    ∃ E, (opnd n M Cg (n + r) c x st).1 = st.1 ++ E := by
  have h9 := h.2.2.2.2.2.2.2.2.1
  unfold opnd
  by_cases hx : x < n + r
  · rw [ite_p _ _ _ hx]
    by_cases h3 : 3 ≤ dg n M Cg x
    · rw [ite_p _ _ _ h3]
      refine ⟨wf_mono _ _ _ _ _ _ _ (wf_push n M Cg L r st h x c hx h3 (hd hx)) (by omega), ?_,
        ⟨[Gate.mk GateOp.or [st.2.1 x, c]], rfl⟩⟩
      intro z
      rw [sem_push n M Cg L r st h x c z]
      exact or_congr Iff.rfl ⟨fun ⟨p, q⟩ => ⟨p, hx, q⟩, fun ⟨p, _, q⟩ => ⟨p, q⟩⟩
    · rw [ite_n _ _ _ h3]
      have hxl : x < n + st.1.length := by omega
      have hdx : dg n M st.1 x ≤ 2 := by rw [wf_dgC n M Cg L r st h x (by omega)]; omega
      refine ⟨wf_term n M Cg L r st h c x hc hxl (by omega) hdx, ?_,
        ⟨[Gate.mk GateOp.and [c, x], Gate.mk GateOp.or [st.2.2.1, n + st.1.length]], by simp [term]⟩⟩
      intro z
      rw [sem_term n M Cg L r st h c x hc hxl z, wf_vlC n M Cg L r st h z x (by omega)]
      exact or_congr Iff.rfl ⟨fun ⟨p, q⟩ => ⟨p, hx, q⟩, fun ⟨p, _, q⟩ => ⟨p, q⟩⟩
  · rw [ite_n _ _ _ hx]
    refine ⟨wf_mono _ _ _ _ _ _ _ h (by omega), ?_, ⟨[], by simp⟩⟩
    intro z
    exact ⟨Or.inl, fun q => by
      rcases q with s | ⟨-, q, -⟩
      · exact s
      · exact absurd q hx⟩

theorem andpush (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St)
    (h : WF n M Cg L r st) (hr : r ≤ Cg.length) (c x y : ℕ)
    (hx : x < n + r) (hy : y < n + r) (h3 : 3 ≤ dg n M Cg x)
    (hd : dg n M st.1 c + dg n M Cg y + dg n M Cg x ≤ 4) :
    WF n M Cg (L + 4) r
      (push n x (n + st.1.length) (st.1 ++ [Gate.mk GateOp.and [c, y]], st.2)) ∧
    ∀ z, Sem n Cg (push n x (n + st.1.length) (st.1 ++ [Gate.mk GateOp.and [c, y]], st.2)) z ↔
      (Sem n Cg st z ∨ (vl n st.1 z c = true ∧ vl n Cg z y = true ∧ vl n Cg z x = true)) := by
  have h1 := wf_ext n M Cg L r st h (Gate.mk GateOp.and [c, y]) ⟨Or.inl rfl, by simp⟩
  have hdN : dg n M (st.1 ++ [Gate.mk GateOp.and [c, y]]) (n + st.1.length)
      = dg n M st.1 c + dg n M Cg y := by
    rw [dg_and, wf_dgC n M Cg L r st h y (by omega)]
  constructor
  · exact wf_mono _ _ _ _ _ _ _ (wf_push n M Cg (L + 1) r _ h1 x (n + st.1.length) hx h3
      (by dsimp only; rw [hdN]; exact hd)) (by omega)
  · intro z
    rw [sem_push n M Cg (L + 1) r _ h1 x (n + st.1.length) z, sem_ext n M Cg L r st h _ z]
    dsimp only
    rw [vl_and, wf_vlC n M Cg L r st h z y (by omega), Bool.and_eq_true, and_assoc]

theorem andterm1 (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St)
    (h : WF n M Cg L r st) (hr : r ≤ Cg.length) (c x y : ℕ)
    (hx : x < n + r) (hy : y < n + r) (hdx : dg n M Cg x ≤ 2)
    (hdy : dg n M Cg y + dg n M st.1 c ≤ 2) :
    WF n M Cg (L + 4) r
      (term n x (n + st.1.length) (st.1 ++ [Gate.mk GateOp.and [y, c]], st.2)) ∧
    ∀ z, Sem n Cg (term n x (n + st.1.length) (st.1 ++ [Gate.mk GateOp.and [y, c]], st.2)) z ↔
      (Sem n Cg st z ∨ (vl n Cg z x = true ∧ vl n Cg z y = true ∧ vl n st.1 z c = true)) := by
  have h1 := wf_ext n M Cg L r st h (Gate.mk GateOp.and [y, c]) ⟨Or.inl rfl, by simp⟩
  have h9 := h.2.2.2.2.2.2.2.2.1
  have hl : (st.1 ++ [Gate.mk GateOp.and [y, c]]).length = st.1.length + 1 := by simp
  have hxl : x < n + st.1.length := by omega
  have ha : x < n + (st.1 ++ [Gate.mk GateOp.and [y, c]]).length := by omega
  have hb : n + st.1.length < n + (st.1 ++ [Gate.mk GateOp.and [y, c]]).length := by omega
  constructor
  · refine wf_mono _ _ _ _ _ _ _
      (wf_term n M Cg (L + 1) r _ h1 x (n + st.1.length) ha hb ?_ ?_) (by omega)
    · dsimp only
      rw [dg_snoc_lt _ _ _ _ _ hxl, wf_dgC n M Cg L r st h x (by omega)]; exact hdx
    · dsimp only
      rw [dg_and, wf_dgC n M Cg L r st h y (by omega)]; exact hdy
  · intro z
    rw [sem_term n M Cg (L + 1) r _ h1 x (n + st.1.length) ha hb z, sem_ext n M Cg L r st h _ z]
    dsimp only
    rw [vl_snoc_lt _ _ _ _ _ hxl, vl_and, wf_vlC n M Cg L r st h z x (by omega),
      wf_vlC n M Cg L r st h z y (by omega), Bool.and_eq_true]

theorem andterm2 (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St)
    (h : WF n M Cg L r st) (hr : r ≤ Cg.length) (c x y : ℕ)
    (hx : x < n + r) (hy : y < n + r) (hdy : dg n M Cg y ≤ 2)
    (hdx : dg n M Cg x + dg n M st.1 c ≤ 2) :
    WF n M Cg (L + 4) r
      (term n (n + st.1.length) y (st.1 ++ [Gate.mk GateOp.and [x, c]], st.2)) ∧
    ∀ z, Sem n Cg (term n (n + st.1.length) y (st.1 ++ [Gate.mk GateOp.and [x, c]], st.2)) z ↔
      (Sem n Cg st z ∨ ((vl n Cg z x = true ∧ vl n st.1 z c = true) ∧ vl n Cg z y = true)) := by
  have h1 := wf_ext n M Cg L r st h (Gate.mk GateOp.and [x, c]) ⟨Or.inl rfl, by simp⟩
  have h9 := h.2.2.2.2.2.2.2.2.1
  have hl : (st.1 ++ [Gate.mk GateOp.and [x, c]]).length = st.1.length + 1 := by simp
  have hyl : y < n + st.1.length := by omega
  have ha : y < n + (st.1 ++ [Gate.mk GateOp.and [x, c]]).length := by omega
  have hb : n + st.1.length < n + (st.1 ++ [Gate.mk GateOp.and [x, c]]).length := by omega
  constructor
  · refine wf_mono _ _ _ _ _ _ _
      (wf_term n M Cg (L + 1) r _ h1 (n + st.1.length) y hb ha ?_ ?_) (by omega)
    · dsimp only
      rw [dg_and, wf_dgC n M Cg L r st h x (by omega)]; exact hdx
    · dsimp only
      rw [dg_snoc_lt _ _ _ _ _ hyl, wf_dgC n M Cg L r st h y (by omega)]; exact hdy
  · intro z
    rw [sem_term n M Cg (L + 1) r _ h1 (n + st.1.length) y hb ha z, sem_ext n M Cg L r st h _ z]
    dsimp only
    rw [vl_snoc_lt _ _ _ _ _ hyl, vl_and, wf_vlC n M Cg L r st h z x (by omega),
      wf_vlC n M Cg L r st h z y (by omega), Bool.and_eq_true]

def stepa (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (w c x y : ℕ) (s1 : St) : St :=
  if x < w ∧ y < w then
    (if 3 ≤ dg n M Cg x then
      push n x (n + s1.1.length) (s1.1 ++ [Gate.mk GateOp.and [c, y]], s1.2)
    else if 3 ≤ dg n M Cg y then
      push n y (n + s1.1.length) (s1.1 ++ [Gate.mk GateOp.and [c, x]], s1.2)
    else if dg n M Cg y ≤ 1 then
      term n x (n + s1.1.length) (s1.1 ++ [Gate.mk GateOp.and [y, c]], s1.2)
    else term n (n + s1.1.length) y (s1.1 ++ [Gate.mk GateOp.and [x, c]], s1.2))
  else s1

theorem stepa_ok (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (s1 : St)
    (h : WF n M Cg L r s1) (hr : r ≤ Cg.length) (c x y : ℕ)
    (hsum : x < n + r → y < n + r →
      dg n M s1.1 c + (dg n M Cg x + dg n M Cg y) ≤ 4 ∧ 3 ≤ dg n M Cg x + dg n M Cg y) :
    WF n M Cg (L + 4) r (stepa n M Cg (n + r) c x y s1) ∧
    ∀ z, Sem n Cg (stepa n M Cg (n + r) c x y s1) z ↔
      (Sem n Cg s1 z ∨ (vl n s1.1 z c = true ∧ (x < n + r ∧ y < n + r) ∧
        vl n Cg z x = true ∧ vl n Cg z y = true)) := by
  unfold stepa
  by_cases hxy : x < n + r ∧ y < n + r
  · rw [ite_p _ _ _ hxy]
    obtain ⟨hx, hy⟩ := hxy
    obtain ⟨hs, hs3⟩ := hsum hx hy
    by_cases h3 : 3 ≤ dg n M Cg x
    · rw [ite_p _ _ _ h3]
      obtain ⟨a, b⟩ := andpush n M Cg L r s1 h hr c x y hx hy h3 (by omega)
      refine ⟨a, fun z => ?_⟩
      rw [b z]
      constructor
      · rintro (s | ⟨p, q, t⟩)
        · exact Or.inl s
        · exact Or.inr ⟨p, ⟨hx, hy⟩, t, q⟩
      · rintro (s | ⟨p, -, t, q⟩)
        · exact Or.inl s
        · exact Or.inr ⟨p, q, t⟩
    · rw [ite_n _ _ _ h3]
      by_cases h3y : 3 ≤ dg n M Cg y
      · rw [ite_p _ _ _ h3y]
        obtain ⟨a, b⟩ := andpush n M Cg L r s1 h hr c y x hy hx h3y (by omega)
        refine ⟨a, fun z => ?_⟩
        rw [b z]
        constructor
        · rintro (s | ⟨p, q, t⟩)
          · exact Or.inl s
          · exact Or.inr ⟨p, ⟨hx, hy⟩, q, t⟩
        · rintro (s | ⟨p, -, q, t⟩)
          · exact Or.inl s
          · exact Or.inr ⟨p, q, t⟩
      · rw [ite_n _ _ _ h3y]
        by_cases h1y : dg n M Cg y ≤ 1
        · rw [ite_p _ _ _ h1y]
          obtain ⟨a, b⟩ := andterm1 n M Cg L r s1 h hr c x y hx hy (by omega) (by omega)
          refine ⟨a, fun z => ?_⟩
          rw [b z]
          constructor
          · rintro (s | ⟨p, q, t⟩)
            · exact Or.inl s
            · exact Or.inr ⟨t, ⟨hx, hy⟩, p, q⟩
          · rintro (s | ⟨t, -, p, q⟩)
            · exact Or.inl s
            · exact Or.inr ⟨p, q, t⟩
        · rw [ite_n _ _ _ h1y]
          obtain ⟨a, b⟩ := andterm2 n M Cg L r s1 h hr c x y hx hy (by omega) (by omega)
          refine ⟨a, fun z => ?_⟩
          rw [b z]
          constructor
          · rintro (s | ⟨⟨p, t⟩, q⟩)
            · exact Or.inl s
            · exact Or.inr ⟨t, ⟨hx, hy⟩, p, q⟩
          · rintro (s | ⟨t, -, p, q⟩)
            · exact Or.inl s
            · exact Or.inr ⟨⟨p, t⟩, q⟩
  · rw [ite_n _ _ _ hxy]
    refine ⟨wf_mono _ _ _ _ _ _ _ h (by omega), fun z => ⟨Or.inl, fun q => ?_⟩⟩
    rcases q with s | ⟨-, q, -⟩
    · exact s
    · exact absurd q hxy

theorem stepo_ok (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (s1 : St)
    (h : WF n M Cg L r s1) (hr : r ≤ Cg.length) (c x y : ℕ)
    (hc : c < n + s1.1.length) (hc1 : dg n M s1.1 c ≤ 1)
    (hdx : x < n + r → dg n M s1.1 c + dg n M Cg x ≤ 4)
    (hdy : y < n + r → dg n M s1.1 c + dg n M Cg y ≤ 4) :
    WF n M Cg (L + 4) r (opnd n M Cg (n + r) c y (opnd n M Cg (n + r) c x s1)) ∧
    ∀ z, Sem n Cg (opnd n M Cg (n + r) c y (opnd n M Cg (n + r) c x s1)) z ↔
      (Sem n Cg s1 z ∨ (vl n s1.1 z c = true ∧
        ((x < n + r ∧ vl n Cg z x = true) ∨ (y < n + r ∧ vl n Cg z y = true)))) := by
  obtain ⟨a1, b1, ⟨E, e1⟩⟩ := opnd_ok n M Cg L r s1 h hr c x hc hc1 hdx
  have hc' : c < n + (opnd n M Cg (n + r) c x s1).1.length := by
    rw [e1, List.length_append]; omega
  have hdg : dg n M (opnd n M Cg (n + r) c x s1).1 c = dg n M s1.1 c := by
    rw [e1]; exact dg_app_lt _ _ _ _ _ hc
  have hvl : ∀ z, vl n (opnd n M Cg (n + r) c x s1).1 z c = vl n s1.1 z c := by
    intro z; rw [e1]; exact vl_app_lt _ _ _ _ _ hc
  obtain ⟨a2, b2, -⟩ := opnd_ok n M Cg (L + 2) r _ a1 hr c y hc' (by rw [hdg]; exact hc1)
    (fun hh => by rw [hdg]; exact hdy hh)
  refine ⟨a2, fun z => ?_⟩
  rw [b2 z, b1 z, hvl z]
  constructor
  · rintro ((s | ⟨p, q⟩) | ⟨p, q⟩)
    · exact Or.inl s
    · exact Or.inr ⟨p, Or.inl q⟩
    · exact Or.inr ⟨p, Or.inr q⟩
  · rintro (s | ⟨p, q | q⟩)
    · exact Or.inl (Or.inl s)
    · exact Or.inl (Or.inr ⟨p, q⟩)
    · exact Or.inr ⟨p, q⟩

def stepc (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (w : ℕ) (b : Bool) (x y : ℕ) (st : St) : St :=
  if st.2.1 w = n + Cg.length then st else
  if b = true then stepa n M Cg w (st.2.1 w) x y (clr (n + Cg.length) w st)
  else opnd n M Cg w (st.2.1 w) y (opnd n M Cg w (st.2.1 w) x (clr (n + Cg.length) w st))

theorem stepc_ok (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (L r : ℕ) (st : St)
    (h : WF n M Cg L (r + 1) st) (hr : r < Cg.length) (b : Bool) (x y : ℕ)
    (hD : dg n M Cg (n + r) = if b = true then
        (if x < n + r then dg n M Cg x else 0) + (if y < n + r then dg n M Cg y else 0)
      else max (if x < n + r then dg n M Cg x else 0) (if y < n + r then dg n M Cg y else 0))
    (hV : ∀ z, 0 < dg n M Cg (n + r) → vl n Cg z (n + r) = if b = true then
        ((if x < n + r then vl n Cg z x else false) && (if y < n + r then vl n Cg z y else false))
      else ((if x < n + r then vl n Cg z x else false) || (if y < n + r then vl n Cg z y else false))) :
    WF n M Cg (L + 4) r (stepc n M Cg (n + r) b x y st) ∧
    ∀ z, Sem n Cg (stepc n M Cg (n + r) b x y st) z ↔ Sem n Cg st z := by
  unfold stepc
  by_cases hz : st.2.1 (n + r) = n + Cg.length
  · rw [ite_p _ _ _ hz]
    exact ⟨wf_mono _ _ _ _ _ _ _ (wf_shrink n M Cg L r st h hz) (by omega), fun z => Iff.rfl⟩
  · rw [ite_n _ _ _ hz]
    have h5 : st.2.1 (n + r) < n + st.1.length := h.2.2.2.2.1 (n + r)
    have h8 := h.2.2.2.2.2.2.2.1 (n + r)
    rcases h8 with e | ⟨-, hw3, hw4⟩
    · exact absurd e hz
    have h1 := wf_clr n M Cg L r st h
    have hsc := fun z => sem_clr n Cg st (n + r) z
    cases b with
    | true =>
      rw [ite_p _ _ _ rfl] at hD
      rw [ite_p _ _ _ rfl]
      obtain ⟨a, bb⟩ := stepa_ok n M Cg L r _ h1 (by omega) (st.2.1 (n + r)) x y
        (fun hx hy => by
          rw [ite_p _ _ _ hx, ite_p _ _ _ hy] at hD
          have hw4' : dg n M st.1 (st.2.1 (n + r)) + dg n M Cg (n + r) ≤ 4 := hw4
          constructor
          · show dg n M st.1 (st.2.1 (n + r)) + _ ≤ 4
            omega
          · omega)
      refine ⟨a, fun z => ?_⟩
      rw [bb z, hsc z]
      have hv := hV z (by omega)
      rw [ite_p _ _ _ rfl] at hv
      apply or_congr Iff.rfl
      show (vl n st.1 z (st.2.1 (n + r)) = true ∧ _) ↔ _
      rw [hv]
      by_cases hx : x < n + r <;> by_cases hy : y < n + r <;> simp [hx, hy, hz]
    | false =>
      rw [ite_n _ _ _ (by simp)] at hD
      rw [ite_n _ _ _ (by simp)]
      have hmx : (if x < n + r then dg n M Cg x else 0) ≤ dg n M Cg (n + r) := by
        rw [hD]; exact le_max_left _ _
      have hmy : (if y < n + r then dg n M Cg y else 0) ≤ dg n M Cg (n + r) := by
        rw [hD]; exact le_max_right _ _
      obtain ⟨a, bb⟩ := stepo_ok n M Cg L r _ h1 (by omega) (st.2.1 (n + r)) x y h5
        (by show dg n M st.1 (st.2.1 (n + r)) ≤ 1; omega)
        (fun hx => by
          rw [ite_p _ _ _ hx] at hmx
          show dg n M st.1 (st.2.1 (n + r)) + _ ≤ 4
          omega)
        (fun hy => by
          rw [ite_p _ _ _ hy] at hmy
          show dg n M st.1 (st.2.1 (n + r)) + _ ≤ 4
          omega)
      refine ⟨a, fun z => ?_⟩
      rw [bb z, hsc z]
      have hv := hV z (by omega)
      rw [ite_n _ _ _ (by simp)] at hv
      apply or_congr Iff.rfl
      show (vl n st.1 z (st.2.1 (n + r)) = true ∧ _) ↔ _
      rw [hv]
      by_cases hx : x < n + r <;> by_cases hy : y < n + r <;> simp [hx, hy, hz]


theorem pre_dg (n : ℕ) (M : Finset ℕ) (pre t : List Gate) (x : ℕ) :
    dg n M pre x = if x < n + pre.length then dg n M (pre ++ t) x else 0 := by
  by_cases h : x < n + pre.length
  · rw [ite_p _ _ _ h, dg_app_lt _ _ _ _ _ h]
  · rw [ite_n _ _ _ h, dg_ge _ _ _ _ (by omega)]

theorem pre_vl (n : ℕ) (pre t : List Gate) (z : Fin n → Bool) (x : ℕ) :
    vl n pre z x = if x < n + pre.length then vl n (pre ++ t) z x else false := by
  by_cases h : x < n + pre.length
  · rw [ite_p _ _ _ h, vl_app_lt _ _ _ _ _ h]
  · rw [ite_n _ _ _ h, vl_ge _ _ _ _ (by omega)]

theorem gate_D (n : ℕ) (M : Finset ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    dg n M (pre ++ g :: post) (n + pre.length) =
      if (nrm (n + pre.length) g).1 = true then
        (if (nrm (n + pre.length) g).2.1 < n + pre.length then
          dg n M (pre ++ g :: post) (nrm (n + pre.length) g).2.1 else 0) +
        (if (nrm (n + pre.length) g).2.2 < n + pre.length then
          dg n M (pre ++ g :: post) (nrm (n + pre.length) g).2.2 else 0)
      else max
        (if (nrm (n + pre.length) g).2.1 < n + pre.length then
          dg n M (pre ++ g :: post) (nrm (n + pre.length) g).2.1 else 0)
        (if (nrm (n + pre.length) g).2.2 < n + pre.length then
          dg n M (pre ++ g :: post) (nrm (n + pre.length) g).2.2 else 0) := by
  have e : pre ++ g :: post = (pre ++ [g]) ++ post := by simp
  have hx := pre_dg n M pre (g :: post) (nrm (n + pre.length) g).2.1
  have hy := pre_dg n M pre (g :: post) (nrm (n + pre.length) g).2.2
  have key := nrm_deg (n + pre.length) g _ (ld_len n M pre) hg
  rw [← hx, ← hy, e, dg_app_lt _ _ _ _ _ (by simp), dg_new]
  exact key

theorem gate_V (n : ℕ) (M : Finset ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (z : Fin n → Bool)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hpos : 0 < dg n M (pre ++ g :: post) (n + pre.length)) :
    vl n (pre ++ g :: post) z (n + pre.length) =
      if (nrm (n + pre.length) g).1 = true then
        ((if (nrm (n + pre.length) g).2.1 < n + pre.length then
          vl n (pre ++ g :: post) z (nrm (n + pre.length) g).2.1 else false) &&
        (if (nrm (n + pre.length) g).2.2 < n + pre.length then
          vl n (pre ++ g :: post) z (nrm (n + pre.length) g).2.2 else false))
      else
        ((if (nrm (n + pre.length) g).2.1 < n + pre.length then
          vl n (pre ++ g :: post) z (nrm (n + pre.length) g).2.1 else false) ||
        (if (nrm (n + pre.length) g).2.2 < n + pre.length then
          vl n (pre ++ g :: post) z (nrm (n + pre.length) g).2.2 else false)) := by
  have e : pre ++ g :: post = (pre ++ [g]) ++ post := by simp
  have hx := pre_vl n pre (g :: post) z (nrm (n + pre.length) g).2.1
  have hy := pre_vl n pre (g :: post) z (nrm (n + pre.length) g).2.2
  rw [e, dg_app_lt _ _ _ _ _ (by simp), dg_new] at hpos
  have key := nrm_val (n + pre.length) g _ _ (wr_len n pre z) hg hpos
  rw [← hx, ← hy, e, vl_app_lt _ _ _ _ _ (by simp), vl_new]
  exact key

def run (n : ℕ) (M : Finset ℕ) (Cg : List Gate) : List Gate → St → St
  | [], st => st
  | g :: rest, st => run n M Cg rest (stepc n M Cg (n + rest.length)
      (nrm (n + rest.length) g).1 (nrm (n + rest.length) g).2.1 (nrm (n + rest.length) g).2.2 st)

theorem run_ok (n : ℕ) (M : Finset ℕ) (Cg : List Gate)
    (hCg : ∀ g ∈ Cg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ (rev post : List Gate), Cg = rev.reverse ++ post → ∀ (L : ℕ) (st : St),
      WF n M Cg L rev.length st →
      WF n M Cg (L + 4 * rev.length) 0 (run n M Cg rev st) ∧
      ∀ z, Sem n Cg (run n M Cg rev st) z ↔ Sem n Cg st z := by
  intro rev
  induction rev with
  | nil =>
    intro post _ L st h
    exact ⟨h, fun z => Iff.rfl⟩
  | cons g rest ih =>
    intro post hC L st h
    have hC' : Cg = rest.reverse ++ g :: post := by rw [hC]; simp
    have hlen : rest.reverse.length = rest.length := by simp
    have hg := hCg g (by rw [hC']; simp)
    have hr : rest.length < Cg.length := by rw [hC']; simp
    have hD := gate_D n M rest.reverse g post hg
    have hV := fun z => gate_V n M rest.reverse g post z hg
    rw [hlen, ← hC'] at hD
    simp only [hlen, ← hC'] at hV
    obtain ⟨a, b⟩ := stepc_ok n M Cg L rest.length st h hr _ _ _ hD hV
    obtain ⟨a2, b2⟩ := ih (g :: post) hC' (L + 4) _ a
    have e : L + 4 + 4 * rest.length = L + 4 * (g :: rest).length := by
      rw [List.length_cons]; omega
    refine ⟨?_, fun z => (b2 z).trans (b z)⟩
    rw [← e]; exact a2

theorem init_ok (n : ℕ) (M : Finset ℕ) (Cg : List Gate) (o : ℕ)
    (hCg : ∀ g ∈ Cg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hdo : dg n M Cg o ≤ 4) :
    ∃ st : St, WF n M Cg (Cg.length + 2) Cg.length st ∧
      ∀ z, (Sem n Cg st z ↔ vl n Cg z o = true) := by
  have hl1 : (Cg ++ [Gate.mk GateOp.or []]).length = Cg.length + 1 := by simp
  have hl : (Cg ++ [Gate.mk GateOp.or []] ++ [Gate.mk GateOp.and []]).length = Cg.length + 2 := by
    simp
  have hok : ∀ h ∈ Cg ++ [Gate.mk GateOp.or []] ++ [Gate.mk GateOp.and []],
      (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2 := by
    intro h hh
    rw [List.mem_append, List.mem_append, List.mem_singleton, List.mem_singleton] at hh
    rcases hh with (hh | hh) | hh
    · exact hCg h hh
    · rw [hh]; exact ⟨Or.inr rfl, by simp⟩
    · rw [hh]; exact ⟨Or.inl rfl, by simp⟩
  have hpre : ∃ E, Cg ++ [Gate.mk GateOp.or []] ++ [Gate.mk GateOp.and []] = Cg ++ E :=
    ⟨[Gate.mk GateOp.or [], Gate.mk GateOp.and []], by simp⟩
  have dgZ : dg n M (Cg ++ [Gate.mk GateOp.or []] ++ [Gate.mk GateOp.and []]) (n + Cg.length) = 0 := by
    rw [dg_snoc_lt _ _ _ _ _ (by omega), dg_new]; simp [Gate.lineDegree]
  have vlZ : ∀ z, vl n (Cg ++ [Gate.mk GateOp.or []] ++ [Gate.mk GateOp.and []]) z
      (n + Cg.length) = false := by
    intro z
    rw [vl_snoc_lt _ _ _ _ _ (by omega), vl_new]; simp [GateOp.eval]
  have dgT : dg n M (Cg ++ [Gate.mk GateOp.or []] ++ [Gate.mk GateOp.and []])
      (n + (Cg ++ [Gate.mk GateOp.or []]).length) = 0 := by
    rw [dg_new]; simp [Gate.lineDegree]
  have vlT : ∀ z, vl n (Cg ++ [Gate.mk GateOp.or []] ++ [Gate.mk GateOp.and []]) z
      (n + (Cg ++ [Gate.mk GateOp.or []]).length) = true := by
    intro z
    rw [vl_new]; simp [GateOp.eval]
  have dgC : ∀ x, x < n + Cg.length →
      dg n M (Cg ++ [Gate.mk GateOp.or []] ++ [Gate.mk GateOp.and []]) x = dg n M Cg x := by
    intro x hx
    rw [List.append_assoc]; exact dg_app_lt _ _ _ _ _ hx
  have vlC : ∀ z x, x < n + Cg.length →
      vl n (Cg ++ [Gate.mk GateOp.or []] ++ [Gate.mk GateOp.and []]) z x = vl n Cg z x := by
    intro z x hx
    rw [List.append_assoc]; exact vl_app_lt _ _ _ _ _ hx
  by_cases h3 : 3 ≤ dg n M Cg o
  · have ho : o < n + Cg.length := by
      by_contra hc
      have := dg_ge n M Cg o (by omega)
      omega
    refine ⟨(Cg ++ [Gate.mk GateOp.or []] ++ [Gate.mk GateOp.and []],
      Function.update (fun _ => n + Cg.length) o (n + (Cg ++ [Gate.mk GateOp.or []]).length),
      n + Cg.length, []), ?_, ?_⟩
    · unfold WF
      dsimp only
      refine ⟨hpre, hok, by omega, by simp, ?_, ⟨by omega, by rw [dgZ]; omega⟩, by simp, ?_,
        ⟨by omega, dgZ, vlZ⟩, ?_⟩
      · intro w
        by_cases e : w = o
        · subst e; simp
        · simp [Function.update, e]
      · intro w
        by_cases e : w = o
        · subst e
          right
          refine ⟨ho, h3, ?_⟩
          rw [Function.update_self, dgT]; omega
        · left; simp [Function.update, e]
      · intro z
        rw [vlZ z]; simp
    · intro z
      unfold Sem
      dsimp only
      rw [vlZ z]
      constructor
      · rintro (h | ⟨w, a, b, c⟩)
        · exact absurd h (by simp)
        · by_cases e : w = o
          · subst e; exact c
          · simp [Function.update, e] at a
      · intro h
        refine Or.inr ⟨o, ?_, ?_, h⟩
        · rw [Function.update_self]; omega
        · rw [Function.update_self]; exact vlT z
  · by_cases ho : o < n + Cg.length
    · refine ⟨(Cg ++ [Gate.mk GateOp.or []] ++ [Gate.mk GateOp.and []],
        (fun _ => n + Cg.length), o, [(o, o)]), ?_, ?_⟩
      · unfold WF
        dsimp only
        refine ⟨hpre, hok, by omega, by simp, fun w => by omega,
          ⟨by omega, by rw [dgC o ho]; omega⟩, ?_, fun w => Or.inl rfl,
          ⟨by omega, dgZ, vlZ⟩, ?_⟩
        · intro p hp
          rw [List.mem_singleton] at hp
          rw [hp]
          exact ⟨⟨by omega, by omega⟩, by rw [dgC o ho]; omega, by rw [dgC o ho]; omega⟩
        · intro z; simp
      · intro z
        unfold Sem
        dsimp only
        rw [vlC z o ho]
        constructor
        · rintro (h | ⟨w, a, -⟩)
          · exact h
          · exact absurd rfl a
        · exact Or.inl
    · refine ⟨(Cg ++ [Gate.mk GateOp.or []] ++ [Gate.mk GateOp.and []],
        (fun _ => n + Cg.length), n + Cg.length, []), ?_, ?_⟩
      · unfold WF
        dsimp only
        refine ⟨hpre, hok, by omega, by simp, fun w => by omega,
          ⟨by omega, by rw [dgZ]; omega⟩, by simp, fun w => Or.inl rfl,
          ⟨by omega, dgZ, vlZ⟩, ?_⟩
        intro z
        rw [vlZ z]; simp
      · intro z
        unfold Sem
        dsimp only
        rw [vlZ z, vl_ge n Cg z o (by omega)]
        constructor
        · rintro (h | ⟨w, a, -⟩)
          · exact h
          · exact absurd rfl a
        · exact Or.inl

theorem full : ∀ (Np Nl : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) C 4 → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (J : ℕ) (a b : Fin J → ℕ) (u r : ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ 7 * C.size + 1 ∧ J ≤ D.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) D 4 ∧ D.gates.getLast? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, r] } ∧ D.output + 1 = Np + Nl + D.gates.length ∧ (∀ j : Fin J, (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (a j) 0 ≤ 2 ∧ (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (b j) 0 ≤ 2) ∧ (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (r) 0 ≤ 3 ∧ ∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z ∧ ((D.wires (List.ofFn z)).getD u false = true ↔ ∃ i : Fin J, (D.wires (List.ofFn z)).getD (a i) false = true ∧ (D.wires (List.ofFn z)).getD (b i) false = true) := by
  intro Np Nl C hm hd
  obtain ⟨Cg, o⟩ := C
  have hCg : ∀ g ∈ Cg, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨a, b⟩ := hm g hg
    refine ⟨?_, b⟩
    rcases Set.mem_insert_iff.mp a with a | a
    · exact Or.inl a
    · exact Or.inr (Set.mem_singleton_iff.mp a)
  have hdo : dg (Np + Nl) (Finset.Ico Np (Np + Nl)) Cg o ≤ 4 := hd
  by_cases hs : Cg = []
  · subst hs
    have key : dg (Np + Nl) (Finset.Ico Np (Np + Nl)) [] o ≤ 1 := by
      by_cases ho : o < Np + Nl
      · exact dg_input _ _ _ _ ho
      · rw [dg_ge _ _ _ _ (by simpa using ho)]; omega
    have hdeg : dg (Np + Nl) (Finset.Ico Np (Np + Nl)) ([] ++ [Gate.mk GateOp.or [o, o]]) o ≤ 1 := by
      by_cases ho : o < Np + Nl + ([] : List Gate).length
      · rw [dg_snoc_lt _ _ _ _ _ ho]; exact key
      · by_cases ho2 : o = Np + Nl + ([] : List Gate).length
        · rw [ho2, dg_or, ← ho2]; exact max_le key key
        · rw [dg_ge _ _ _ _ (by simp at ho ho2 ⊢; omega)]; omega
    refine ⟨⟨[Gate.mk GateOp.or [o, o]], Np + Nl⟩, 1, fun _ => o, fun _ => o, o, o,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rw [List.mem_singleton] at hg
      rw [hg]
      exact ⟨by simp, by simp⟩
    · show 1 ≤ 7 * 0 + 1
      omega
    · show 1 ≤ 1
      omega
    · show dg (Np + Nl) (Finset.Ico Np (Np + Nl)) ([] ++ [Gate.mk GateOp.or [o, o]])
        (Np + Nl + ([] : List Gate).length) ≤ 4
      rw [dg_or]
      exact max_le (by omega) (by omega)
    · rfl
    · rfl
    · intro j
      exact ⟨by show dg _ _ ([] ++ [Gate.mk GateOp.or [o, o]]) o ≤ 2; omega,
        by show dg _ _ ([] ++ [Gate.mk GateOp.or [o, o]]) o ≤ 2; omega⟩
    · show dg _ _ ([] ++ [Gate.mk GateOp.or [o, o]]) o ≤ 3
      omega
    · intro z
      constructor
      · show vl (Np + Nl) ([] ++ [Gate.mk GateOp.or [o, o]]) z (Np + Nl + ([] : List Gate).length)
          = vl (Np + Nl) [] z o
        rw [vl_or, Bool.or_self]
      · exact ⟨fun h => ⟨0, h, h⟩, fun ⟨_, h, _⟩ => h⟩
  · have hpos : 0 < Cg.length := by
      rcases Cg with _ | ⟨g0, t⟩
      · exact absurd rfl hs
      · simp
    obtain ⟨st0, w0, s0⟩ := init_ok (Np + Nl) (Finset.Ico Np (Np + Nl)) Cg o hCg hdo
    obtain ⟨wf, sf⟩ := run_ok (Np + Nl) (Finset.Ico Np (Np + Nl)) Cg hCg Cg.reverse [] (by simp)
      (Cg.length + 2) st0 (by rw [List.length_reverse]; exact w0)
    rw [List.length_reverse] at wf
    generalize run (Np + Nl) (Finset.Ico Np (Np + Nl)) Cg Cg.reverse st0 = st at wf sf
    obtain ⟨G, ctx, U, P⟩ := st
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := wf
    dsimp only at h2 h3 h4 h5 h6 h7 h8 h9 h10
    have hlen : (G ++ [Gate.mk GateOp.or [U, Np + Nl + Cg.length]]).length = G.length + 1 := by
      simp
    refine ⟨⟨G ++ [Gate.mk GateOp.or [U, Np + Nl + Cg.length]], Np + Nl + G.length⟩, P.length,
      fun j => (P.get j).1, fun j => (P.get j).2, U, Np + Nl + Cg.length,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rw [List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | hg
      · obtain ⟨a, b⟩ := h2 g hg
        refine ⟨?_, b⟩
        rcases a with a | a
        · rw [a]; simp
        · rw [a]; simp
      · rw [hg]; exact ⟨by simp, by simp⟩
    · show (G ++ [Gate.mk GateOp.or [U, Np + Nl + Cg.length]]).length ≤ 7 * Cg.length + 1
      omega
    · show P.length ≤ (G ++ [Gate.mk GateOp.or [U, Np + Nl + Cg.length]]).length
      omega
    · show dg (Np + Nl) (Finset.Ico Np (Np + Nl))
        (G ++ [Gate.mk GateOp.or [U, Np + Nl + Cg.length]]) (Np + Nl + G.length) ≤ 4
      rw [dg_or]
      exact max_le h6.2 (by rw [h9.2.1]; omega)
    · show (G ++ [Gate.mk GateOp.or [U, Np + Nl + Cg.length]]).getLast? = _
      simp
    · show Np + Nl + G.length + 1
        = Np + Nl + (G ++ [Gate.mk GateOp.or [U, Np + Nl + Cg.length]]).length
      omega
    · intro j
      have hmj := h7 (P.get j) (List.get_mem P j)
      constructor
      · show dg (Np + Nl) (Finset.Ico Np (Np + Nl))
          (G ++ [Gate.mk GateOp.or [U, Np + Nl + Cg.length]]) (P.get j).1 ≤ 2
        rw [dg_snoc_lt _ _ _ _ _ hmj.1.1]; exact hmj.2.1
      · show dg (Np + Nl) (Finset.Ico Np (Np + Nl))
          (G ++ [Gate.mk GateOp.or [U, Np + Nl + Cg.length]]) (P.get j).2 ≤ 2
        rw [dg_snoc_lt _ _ _ _ _ hmj.1.2]; exact hmj.2.2
    · show dg (Np + Nl) (Finset.Ico Np (Np + Nl))
        (G ++ [Gate.mk GateOp.or [U, Np + Nl + Cg.length]]) (Np + Nl + Cg.length) ≤ 3
      rw [dg_snoc_lt _ _ _ _ _ h9.1, h9.2.1]; omega
    · intro z
      constructor
      · show vl (Np + Nl) (G ++ [Gate.mk GateOp.or [U, Np + Nl + Cg.length]]) z (Np + Nl + G.length)
          = vl (Np + Nl) Cg z o
        rw [vl_or, h9.2.2 z, Bool.or_false]
        have hS := (sf z).trans (s0 z)
        have hU : Sem (Np + Nl) Cg (G, ctx, U, P) z ↔ vl (Np + Nl) G z U = true := by
          unfold Sem
          dsimp only
          constructor
          · rintro (a | ⟨w, a, -, -⟩)
            · exact a
            · rcases h8 w with e | ⟨lt, d3, -⟩
              · exact absurd e a
              · have := dg_input (Np + Nl) (Finset.Ico Np (Np + Nl)) Cg w (by omega)
                omega
          · exact Or.inl
        rw [Bool.eq_iff_iff]
        exact hU.symm.trans hS
      · show vl (Np + Nl) (G ++ [Gate.mk GateOp.or [U, Np + Nl + Cg.length]]) z U = true ↔
          ∃ i : Fin P.length,
            vl (Np + Nl) (G ++ [Gate.mk GateOp.or [U, Np + Nl + Cg.length]]) z (P.get i).1 = true ∧
            vl (Np + Nl) (G ++ [Gate.mk GateOp.or [U, Np + Nl + Cg.length]]) z (P.get i).2 = true
        rw [vl_snoc_lt _ _ _ _ _ h6.1, h10 z]
        constructor
        · rintro ⟨p, hp, e⟩
          obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hp
          refine ⟨i, ?_⟩
          rw [vl_snoc_lt _ _ _ _ _ (h7 _ hp).1.1, vl_snoc_lt _ _ _ _ _ (h7 _ hp).1.2]
          exact e
        · rintro ⟨i, e⟩
          have hp := List.get_mem P i
          refine ⟨P.get i, hp, ?_⟩
          rw [vl_snoc_lt _ _ _ _ _ (h7 _ hp).1.1, vl_snoc_lt _ _ _ _ _ (h7 _ hp).1.2] at e
          exact e

end PEqualNP.Outside.L_meta_1383

theorem PEqualNP.Outside.L_meta_1383 : ∀ (Np Nl : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.CircuitLowerBounds.HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) C 4 → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (J : ℕ) (a b : Fin J → ℕ) (u r : ℕ), PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ 7 * C.size + 1 ∧ J ≤ D.size ∧ PEqualNP.CircuitLowerBounds.HasLineDegree (Np + Nl) (Finset.Ico Np (Np + Nl)) D 4 ∧ D.gates.getLast? = some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [u, r] } ∧ D.output + 1 = Np + Nl + D.gates.length ∧ (∀ j : Fin J, (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (a j) 0 ≤ 2 ∧ (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (b j) 0 ≤ 2) ∧ (D.lineDegrees (Np + Nl) (Finset.Ico Np (Np + Nl))).getD (r) 0 ≤ 3 ∧ ∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D z = PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z ∧ ((D.wires (List.ofFn z)).getD u false = true ↔ ∃ i : Fin J, (D.wires (List.ofFn z)).getD (a i) false = true ∧ (D.wires (List.ofFn z)).getD (b i) false = true) :=
  PEqualNP.Outside.L_meta_1383.full
