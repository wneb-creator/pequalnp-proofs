import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2056_aux.RelabelStarExtension

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma wv_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.size) (hback : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hback i hi)]

def addStar (n : ℕ) (C : Circuit) (p a b c d : ℕ) : Circuit :=
  let m := n + C.size
  ⟨C.gates ++ [⟨GateOp.or, [a,b]⟩, ⟨GateOp.or, [m,c]⟩,
    ⟨GateOp.or, [m+1,d]⟩, ⟨GateOp.and, [p,m+2]⟩,
    ⟨GateOp.or, [C.output,m+3]⟩], m+4⟩

lemma addStar_size (n : ℕ) (C : Circuit) (p a b c d : ℕ) :
    (addStar n C p a b c d).size = C.size + 5 := by simp [addStar, Circuit.size]

lemma addStar_valid (n : ℕ) (C : Circuit) (p a b c d : ℕ) :
    (addStar n C p a b c d).output < n + (addStar n C p a b c d).size := by
  rw [addStar_size]
  change n + C.size + 4 < n + (C.size + 5)
  omega

lemma addStar_mono (n : ℕ) (C : Circuit) (p a b c d : ℕ)
    (hc : PEqualNP.MetaComplexity.Monotone2 C) :
    PEqualNP.MetaComplexity.Monotone2 (addStar n C p a b c d) := by
  intro g hg
  change g ∈ C.gates ++ _ at hg
  rcases List.mem_append.mp hg with h | h
  · exact hc g h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> simp

lemma addStar_keep (n : ℕ) (C : Circuit) (p a b c d : ℕ) (x : Fin n → Bool)
    (i : ℕ) (hi : i < n + C.size) :
    wv n (addStar n C p a b c d) x i = wv n C x i := by
  change (((C.gates ++ _).foldl stepW (List.ofFn x)).getD i false) = _
  rw [List.foldl_append]
  apply foldl_getD_lt
  rw [foldl_len]
  simpa [Circuit.size] using hi

lemma addStar_eval {n : ℕ} (C : Circuit) (p a b c d : Fin n)
    (hout : C.output < n + C.size) (x : Fin n → Bool) :
    (addStar n C p.val a.val b.val c.val d.val).eval (List.ofFn x) =
      (C.eval (List.ofFn x) || (x p && (x a || x b || x c || x d))) := by
  let D := addStar n C p.val a.val b.val c.val d.val
  have hsize : D.size = C.size + 5 := addStar_size _ _ _ _ _ _ _
  have g0 : gateAt D C.size = ⟨GateOp.or,[a.val,b.val]⟩ := by
    simp [D, addStar, gateAt, Circuit.size, List.getD_eq_getElem?_getD]
  have g1 : gateAt D (C.size+1) = ⟨GateOp.or,[n+C.size,c.val]⟩ := by
    simp [D, addStar, gateAt, Circuit.size, List.getD_eq_getElem?_getD]
  have g2 : gateAt D (C.size+2) = ⟨GateOp.or,[n+C.size+1,d.val]⟩ := by
    simp [D, addStar, gateAt, Circuit.size, List.getD_eq_getElem?_getD]
  have g3 : gateAt D (C.size+3) = ⟨GateOp.and,[p.val,n+C.size+2]⟩ := by
    simp [D, addStar, gateAt, Circuit.size, List.getD_eq_getElem?_getD]
  have g4 : gateAt D (C.size+4) = ⟨GateOp.or,[C.output,n+C.size+3]⟩ := by
    simp [D, addStar, gateAt, Circuit.size, List.getD_eq_getElem?_getD]
  have v0 : wv n D x (n+C.size) = (x a || x b) := by
    rw [wv_gate n D x C.size (by omega) (by
      rw [g0]
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega), g0]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      Bool.or_false, id_eq]
    rw [wv_input n D x a.val a.isLt, wv_input n D x b.val b.isLt]
  have v1 : wv n D x (n+C.size+1) = (x a || x b || x c) := by
    have hn : n+C.size+1 = n+(C.size+1) := by omega
    rw [hn, wv_gate n D x (C.size+1) (by omega) (by
      rw [g1]
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega), g1]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      Bool.or_false, id_eq]
    rw [v0, wv_input n D x c.val c.isLt]
  have v2 : wv n D x (n+C.size+2) = (x a || x b || x c || x d) := by
    have hn : n+C.size+2 = n+(C.size+2) := by omega
    rw [hn, wv_gate n D x (C.size+2) (by omega) (by
      rw [g2]
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega), g2]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      Bool.or_false, id_eq]
    rw [v1, wv_input n D x d.val d.isLt]
  have v3 : wv n D x (n+C.size+3) = (x p && (x a || x b || x c || x d)) := by
    have hn : n+C.size+3 = n+(C.size+3) := by omega
    rw [hn, wv_gate n D x (C.size+3) (by omega) (by
      rw [g3]
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega), g3]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      Bool.and_true, id_eq]
    rw [v2, wv_input n D x p.val p.isLt]
  change wv n D x (n+C.size+4) = _
  have hn : n+C.size+4 = n+(C.size+4) := by omega
  rw [hn, wv_gate n D x (C.size+4) (by omega) (by
    rw [g4]
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega), g4]
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    Bool.or_false, id_eq]
  rw [v3, addStar_keep n C p.val a.val b.val c.val d.val x C.output hout]
  rfl

def starValue {n : ℕ} (s : Fin 5 → Fin n) (x : Fin n → Bool) : Bool :=
  x (s 0) && (x (s 1) || x (s 2) || x (s 3) || x (s 4))

def extendStars {n : ℕ} (C : Circuit) : List (Fin 5 → Fin n) → Circuit
  | [] => C
  | s :: ss => extendStars
      (addStar n C (s 0).val (s 1).val (s 2).val (s 3).val (s 4).val) ss

lemma extendStars_spec {n : ℕ} (C : Circuit) (ss : List (Fin 5 → Fin n))
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (hout : C.output < n + C.size) :
    PEqualNP.MetaComplexity.Monotone2 (extendStars C ss) ∧
      (extendStars C ss).size = C.size + 5 * ss.length ∧
      (extendStars C ss).output < n + (extendStars C ss).size ∧
      ∀ x : Fin n → Bool, (extendStars C ss).eval (List.ofFn x) =
        (C.eval (List.ofFn x) || ss.any (fun s => starValue s x)) := by
  induction ss generalizing C with
  | nil => exact ⟨hC, by simp [extendStars], hout, by intro x; simp [extendStars]⟩
  | cons s ss ih =>
    let D := addStar n C (s 0).val (s 1).val (s 2).val (s 3).val (s 4).val
    obtain ⟨hm, hs, hv, he⟩ := ih D (addStar_mono _ _ _ _ _ _ _ hC) (addStar_valid _ _ _ _ _ _ _)
    refine ⟨hm, ?_, hv, ?_⟩
    · change (extendStars D ss).size = C.size + 5 * (s :: ss).length
      rw [hs, addStar_size]
      simp [List.length_cons]
      omega
    · intro x
      change (extendStars D ss).eval (List.ofFn x) = _
      rw [he, addStar_eval C (s 0) (s 1) (s 2) (s 3) (s 4) hout]
      simp [starValue, Bool.or_assoc]

lemma patch_budget {k m : ℕ} (hk : k ≤ 13) (hm : m ≤ 5 * k - 2) (hpos : 1 ≤ k) :
    m + 5 * (13 - k) ≤ 63 := by omega

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]


theorem relabel_mono {n m : ℕ} (π : Fin n → Fin m) (C : Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) : PEqualNP.MetaComplexity.Monotone2 (relabel n m π C) := by
  intro g hg
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hg
  exact ⟨(hm h hh).1, by simpa [relGate] using (hm h hh).2⟩

theorem relabel_eval {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) (x : Fin m → Bool) :
    (relabel n m π C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ π)) :=
  (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output


lemma relabel_size {n m : ℕ} (π : Fin n → Fin m) (C : Circuit) :
    (relabel n m π C).size = C.size := by simp [relabel, Circuit.size]

lemma relabel_valid {n m : ℕ} (π : Fin n → Fin m) (C : Circuit)
    (hout : C.output < n + C.size) :
    (relabel n m π C).output < m + (relabel n m π C).size := by
  rw [relabel_size]
  change wmap n m π C.output < m + C.size
  unfold wmap
  split
  · exact lt_of_lt_of_le (π ⟨C.output, by assumption⟩).isLt (by omega)
  · omega

lemma relabel_extend_spec {n m : ℕ} (π : Fin n → Fin m) (C : Circuit)
    (ss : List (Fin 5 → Fin m)) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (hout : C.output < n + C.size) :
    PEqualNP.MetaComplexity.Monotone2 (extendStars (relabel n m π C) ss) ∧
      (extendStars (relabel n m π C) ss).size = C.size + 5 * ss.length ∧
      ∀ x : Fin m → Bool, (extendStars (relabel n m π C) ss).eval (List.ofFn x) =
        (C.eval (List.ofFn (x ∘ π)) || ss.any (fun s => starValue s x)) := by
  obtain ⟨hmono, hsize, _, heval⟩ := extendStars_spec (relabel n m π C) ss
    (relabel_mono π C hC) (relabel_valid π C hout)
  refine ⟨hmono, by simpa only [relabel_size] using hsize, ?_⟩
  intro x
  rw [heval, relabel_eval]

lemma patch_to_full {n k : ℕ} (π : Fin n → Fin 26) (C : Circuit)
    (ss : List (Fin 5 → Fin 26))
    (hC : PEqualNP.MetaComplexity.Monotone2 C) (hout : C.output < n + C.size)
    (hk : 1 ≤ k) (hk' : k ≤ 13) (hsize : C.size ≤ 5 * k - 2)
    (hlen : ss.length = 13 - k) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ D.size ≤ 63 ∧
      ∀ x : Fin 26 → Bool, D.eval (List.ofFn x) =
        (C.eval (List.ofFn (x ∘ π)) || ss.any (fun s => starValue s x)) := by
  obtain ⟨hmono, hsz, heval⟩ := relabel_extend_spec π C ss hC hout
  refine ⟨extendStars (relabel n 26 π C) ss, hmono, ?_, heval⟩
  rw [hsz, hlen]
  exact patch_budget hk' hsize hk

end PEqualNP.Outside.L_meta_2056_aux.RelabelStarExtension
