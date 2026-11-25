import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

lemma ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


lemma mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

lemma cmono (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C) (n : ℕ)
    (x y : Fin n → Bool) (hxy : x ≤ y) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  intro h
  have h' : (wf C.gates (List.ofFn x)).getD C.output false = true := h
  exact mono2 C.gates (fun g hg => ⟨by
      rcases (hC g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr h, (hC g hg).2⟩) (List.ofFn x) (List.ofFn y) (by simp)
    (fun i => ofFn_mono n x y (fun v hv => by
      have := hxy v
      rw [Bool.le_iff_imp] at this
      exact this hv) i) C.output h'

lemma last_not_eval (gs : List Gate) (ins : List ℕ) (n : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs ++ [⟨GateOp.not, ins⟩], n + gs.length⟩ (List.ofFn x) =
      !((ins.map fun i => (wf gs (List.ofFn x)).getD i false).headD false) := by
  rw [eval_eq, wf_snoc]
  have hlen : (wf gs (List.ofFn x)).length = n + gs.length := by
    rw [wf_len, List.length_ofFn]
  rw [← hlen, getD_snoc_eq]
  rfl

lemma last_not_incompatible (gs : List Gate) (ins : List ℕ)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hzero : Circuit.eval ⟨gs ++ [⟨GateOp.not, ins⟩], 10 + gs.length⟩
      (List.ofFn fun _ : Fin 10 => false) = false)
    (hone : Circuit.eval ⟨gs ++ [⟨GateOp.not, ins⟩], 10 + gs.length⟩
      (List.ofFn fun _ : Fin 10 => true) = true) : False := by
  rw [last_not_eval] at hzero hone
  cases ins with
  | nil => simp at hzero
  | cons i is =>
    simp only [List.map_cons, List.headD_cons] at hzero hone
    have hz : (wf gs (List.ofFn fun _ : Fin 10 => false)).getD i false = true := by
      simpa using congrArg Bool.not hzero
    have ho : (wf gs (List.ofFn fun _ : Fin 10 => true)).getD i false = false := by
      simpa using congrArg Bool.not hone
    have hp := mono2 gs hleg (List.ofFn fun _ : Fin 10 => false)
      (List.ofFn fun _ : Fin 10 => true) (by simp)
      (fun w => ofFn_mono 10 (fun _ => false) (fun _ => true) (by simp) w) i hz
    rw [ho] at hp
    contradiction

def petersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

lemma last_not_not_petersen (gs : List Gate) (ins : List ℕ)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ¬ ∀ x : Fin 10 → Bool,
      Circuit.eval ⟨gs ++ [⟨GateOp.not, ins⟩], 10 + gs.length⟩ (List.ofFn x) = petersen x := by
  intro correct
  exact last_not_incompatible gs ins hleg
    (by simpa [petersen] using correct (fun _ => false))
    (by simpa [petersen] using correct (fun _ => true))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma and_primary_witness : ∀ v w : Fin 10, v ≠ w →
    ∃ u : Fin 10, u ≠ v ∧ u ≠ w ∧
      petersen (fun i => decide (i = u)) = false ∧
      petersen (fun i => decide (i = u ∨ i = v)) = true := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma or_primary_witness : ∀ v w : Fin 10, v ≠ w →
    ∃ u : Fin 10, u ≠ v ∧ u ≠ w ∧
      petersen (fun i => decide (i = u ∨ i = w)) = false ∧
      petersen (fun i => decide (i = u ∨ i = w ∨ i = v)) = true := by
  decide

lemma no_primary_and_funnel (v w : Fin 10) (hvw : v ≠ w) :
    ¬ ∀ x y : Fin 10 → Bool, (∀ i : Fin 10, i ≠ v → x i = y i) →
      (x v && x w) = (y v && y w) → petersen x = petersen y := by
  intro hf
  obtain ⟨u, huv, huw, hzero, hone⟩ := and_primary_witness v w hvw
  have hwu := Ne.symm huw
  have hwv := Ne.symm hvw
  have hh := hf (fun i => decide (i = u)) (fun i => decide (i = u ∨ i = v))
    (by intro i hi; simp [hi]) (by simp [hwu, hwv])
  rw [hzero, hone] at hh
  contradiction

lemma no_primary_or_funnel (v w : Fin 10) (hvw : v ≠ w) :
    ¬ ∀ x y : Fin 10 → Bool, (∀ i : Fin 10, i ≠ v → x i = y i) →
      (x v || x w) = (y v || y w) → petersen x = petersen y := by
  intro hf
  obtain ⟨u, huv, huw, hzero, hone⟩ := or_primary_witness v w hvw
  have hh := hf (fun i => decide (i = u ∨ i = w))
    (fun i => decide (i = u ∨ i = w ∨ i = v))
    (by intro i hi; simp [hi]) (by simp)
  rw [hzero, hone] at hh
  contradiction

lemma snoc_except (U V : List Bool) (v : ℕ) (a b : Bool)
    (hlen : U.length = V.length)
    (h : ∀ i : ℕ, i ≠ v → U.getD i false = V.getD i false) (hab : a = b) :
    ∀ i : ℕ, i ≠ v → (U ++ [a]).getD i false = (V ++ [b]).getD i false := by
  intro i hi
  rcases Nat.lt_trichotomy i U.length with hlt | heq | hgt
  · rw [getD_snoc_lt _ _ _ hlt, getD_snoc_lt _ _ _ (by omega)]
    exact h i hi
  · subst i
    rw [getD_snoc_eq, hlen, getD_snoc_eq]
    exact hab
  · rw [getD_snoc_gt _ _ _ hgt, getD_snoc_gt _ _ _ (by omega)]

lemma wf_except (gs : List Gate) (v : ℕ)
    (hread : ∀ g ∈ gs, v ∉ g.inputs) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i : ℕ, i ≠ v → U.getD i false = V.getD i false) →
      ∀ i : ℕ, i ≠ v → (wf gs U).getD i false = (wf gs V).getD i false := by
  induction gs with
  | nil => intro U V _ h i hi; exact h i hi
  | cons g gs ih =>
    intro U V hlen h i hi
    have hgate : g.op.eval (g.inputs.map fun j => U.getD j false) =
        g.op.eval (g.inputs.map fun j => V.getD j false) := by
      congr 1
      apply List.map_congr_left
      intro j hj
      apply h j
      intro hjv
      exact hread g (by simp) (hjv ▸ hj)
    exact ih (fun g' hg' => hread g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun j => U.getD j false)])
      (V ++ [g.op.eval (g.inputs.map fun j => V.getD j false)])
      (by simp [hlen]) (snoc_except U V v _ _ hlen h hgate) i hi

lemma ofFn_except (n : ℕ) (v : Fin n) (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, i ≠ v → x i = y i) :
    ∀ i : ℕ, i ≠ v.val → (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
  intro i hiv
  by_cases hi : i < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, dite_true, Option.getD_some]
    exact hxy ⟨i, hi⟩ (fun h => hiv (congrArg Fin.val h))
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma primary_funnel (n : ℕ) (pre post : List Gate) (op : GateOp) (v w : Fin n)
    (out : ℕ) (hout : out ≠ v.val)
    (hpre : ∀ g ∈ pre, v.val ∉ g.inputs) (hpost : ∀ g ∈ post, v.val ∉ g.inputs)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, i ≠ v → x i = y i)
    (hgate : op.eval [x v, x w] = op.eval [y v, y w]) :
    Circuit.eval ⟨pre ++ [⟨op, [v.val, w.val]⟩] ++ post, out⟩ (List.ofFn x) =
      Circuit.eval ⟨pre ++ [⟨op, [v.val, w.val]⟩] ++ post, out⟩ (List.ofFn y) := by
  have hlen : (wf pre (List.ofFn x)).length = (wf pre (List.ofFn y)).length := by
    simp [wf_len]
  have hbefore := wf_except pre v.val hpre (List.ofFn x) (List.ofFn y)
    (by simp) (ofFn_except n v x y hxy)
  have hg : op.eval ([v.val, w.val].map fun j => (wf pre (List.ofFn x)).getD j false) =
      op.eval ([v.val, w.val].map fun j => (wf pre (List.ofFn y)).getD j false) := by
    simp only [List.map_cons, List.map_nil]
    rw [wf_keep pre _ v.val (by simp),
      wf_keep pre _ w.val (by simp),
      wf_keep pre _ v.val (by simp),
      wf_keep pre _ w.val (by simp)]
    simpa [List.getD_eq_getElem?_getD] using hgate
  have hh := wf_except post v.val hpost
    (wf pre (List.ofFn x) ++ [op.eval ([v.val, w.val].map fun j => (wf pre (List.ofFn x)).getD j false)])
    (wf pre (List.ofFn y) ++ [op.eval ([v.val, w.val].map fun j => (wf pre (List.ofFn y)).getD j false)])
    (by simp [hlen]) (snoc_except _ _ v.val _ _ hlen hbefore hg) out hout
  simpa only [eval_eq, wf, List.foldl_append, List.foldl_cons, List.foldl_nil] using hh

lemma petersen_singleton : ∀ v : Fin 10, petersen (fun i => decide (i = v)) = false := by
  decide

lemma petersen_output_not_primary (C : Circuit)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) (v : Fin 10) :
    C.output ≠ v.val := by
  intro hout
  have hc := correct (fun i => decide (i = v))
  rw [petersen_singleton] at hc
  change (wf C.gates (List.ofFn fun i => decide (i = v))).getD C.output false = false at hc
  rw [hout, wf_keep C.gates _ v.val (by simp)] at hc
  have hget : (List.ofFn fun i : Fin 10 => decide (i = v)).getD v.val false = true := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [v.isLt, dite_true, Option.getD_some]
    rfl
  rw [hget] at hc
  contradiction

lemma petersen_no_primary_and_once (pre post : List Gate) (v w : Fin 10) (out : ℕ)
    (hvw : v ≠ w) (hpre : ∀ g ∈ pre, v.val ∉ g.inputs)
    (hpost : ∀ g ∈ post, v.val ∉ g.inputs) :
    ¬ ∀ x : Fin 10 → Bool,
      Circuit.eval ⟨pre ++ [⟨GateOp.and, [v.val, w.val]⟩] ++ post, out⟩ (List.ofFn x) = petersen x := by
  intro correct
  have hout := petersen_output_not_primary _ correct v
  apply no_primary_and_funnel v w hvw
  intro x y hxy hgate
  have hh := primary_funnel 10 pre post GateOp.and v w out hout hpre hpost x y hxy
    (by simpa [GateOp.eval] using hgate)
  rw [correct x, correct y] at hh
  exact hh

lemma petersen_no_primary_or_once (pre post : List Gate) (v w : Fin 10) (out : ℕ)
    (hvw : v ≠ w) (hpre : ∀ g ∈ pre, v.val ∉ g.inputs)
    (hpost : ∀ g ∈ post, v.val ∉ g.inputs) :
    ¬ ∀ x : Fin 10 → Bool,
      Circuit.eval ⟨pre ++ [⟨GateOp.or, [v.val, w.val]⟩] ++ post, out⟩ (List.ofFn x) = petersen x := by
  intro correct
  have hout := petersen_output_not_primary _ correct v
  apply no_primary_or_funnel v w hvw
  intro x y hxy hgate
  have hh := primary_funnel 10 pre post GateOp.or v w out hout hpre hpost x y hxy
    (by simpa [GateOp.eval] using hgate)
  rw [correct x, correct y] at hh
  exact hh

lemma snoc_mono_except (U V : List Bool) (v : ℕ) (a b : Bool)
    (hlen : U.length = V.length)
    (h : ∀ i : ℕ, i ≠ v → U.getD i false = true → V.getD i false = true)
    (hab : a = true → b = true) :
    ∀ i : ℕ, i ≠ v → (U ++ [a]).getD i false = true → (V ++ [b]).getD i false = true := by
  intro i hi
  rcases Nat.lt_trichotomy i U.length with hlt | heq | hgt
  · rw [getD_snoc_lt _ _ _ hlt, getD_snoc_lt _ _ _ (by omega)]
    exact h i hi
  · subst i
    rw [getD_snoc_eq, hlen, getD_snoc_eq]
    exact hab
  · rw [getD_snoc_gt _ _ _ hgt]
    simp

lemma wf_mono_except (gs : List Gate) (v : ℕ)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hread : ∀ g ∈ gs, v ∉ g.inputs) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i : ℕ, i ≠ v → U.getD i false = true → V.getD i false = true) →
      ∀ i : ℕ, i ≠ v → (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i hi; exact h i hi
  | cons g gs ih =>
    intro U V hlen h i hi
    have hgate : g.op.eval (g.inputs.map fun j => U.getD j false) = true →
        g.op.eval (g.inputs.map fun j => V.getD j false) = true := by
      have hread' : ∀ j ∈ g.inputs, j ≠ v := by
        intro j hj hjv
        exact hread g (by simp) (hjv ▸ hj)
      rcases hops g (by simp) with hop | hop <;> rw [hop]
      · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
        exact fun hall j hj => h j (hread' j hj) (hall j hj)
      · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
        exact fun ⟨j, hj, hv⟩ => ⟨j, hj, h j (hread' j hj) hv⟩
    exact ih (fun g' hg' => hops g' (by simp [hg']))
      (fun g' hg' => hread g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun j => U.getD j false)])
      (V ++ [g.op.eval (g.inputs.map fun j => V.getD j false)])
      (by simp [hlen]) (snoc_mono_except U V v _ _ hlen h hgate) i hi

lemma wf_append (pre post : List Gate) (U : List Bool) :
    wf (pre ++ post) U = wf post (wf pre U) := by
  simp [wf, List.foldl_append]

lemma eval_split_primary_not (n : ℕ) (pre post : List Gate) (v : Fin n)
    (out : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨pre ++ [⟨GateOp.not, [v.val]⟩] ++ post, out⟩ (List.ofFn x) =
      (wf post (wf pre (List.ofFn x) ++ [!x v])).getD out false := by
  rw [eval_eq, wf_append, wf_snoc]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
  rw [wf_keep pre _ v.val (by simp)]
  simp [List.getD_eq_getElem?_getD]

lemma primary_last_not_antitone (n : ℕ) (pre post : List Gate) (v : Fin n)
    (out : ℕ) (hout : out ≠ v.val)
    (hpre : ∀ g ∈ pre, v.val ∉ g.inputs) (hpost : ∀ g ∈ post, v.val ∉ g.inputs)
    (hops : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, i ≠ v → x i = y i) (hxv : x v = false) :
    Circuit.eval ⟨pre ++ [⟨GateOp.not, [v.val]⟩] ++ post, out⟩ (List.ofFn y) = true →
      Circuit.eval ⟨pre ++ [⟨GateOp.not, [v.val]⟩] ++ post, out⟩ (List.ofFn x) = true := by
  rw [eval_split_primary_not, eval_split_primary_not]
  have hlen : (wf pre (List.ofFn y)).length = (wf pre (List.ofFn x)).length := by
    simp [wf_len]
  have hbefore := wf_except pre v.val hpre (List.ofFn x) (List.ofFn y)
    (by simp) (ofFn_except n v x y hxy)
  apply wf_mono_except post v.val hops hpost _ _ (by simp [hlen])
  · apply snoc_mono_except _ _ v.val _ _ hlen
    · intro i hi hb
      rw [hbefore i hi]
      exact hb
    · simp [hxv]
  · exact hout

lemma petersen_neighbor_witness : ∀ v : Fin 10, ∃ u : Fin 10, u ≠ v ∧
    petersen (fun i => decide (i = u)) = false ∧
    petersen (fun i => decide (i = u ∨ i = v)) = true := by
  decide

lemma petersen_no_primary_last_not_once (pre post : List Gate) (v : Fin 10) (out : ℕ)
    (hpre : ∀ g ∈ pre, v.val ∉ g.inputs) (hpost : ∀ g ∈ post, v.val ∉ g.inputs)
    (hops : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ¬ ∀ x : Fin 10 → Bool,
      Circuit.eval ⟨pre ++ [⟨GateOp.not, [v.val]⟩] ++ post, out⟩ (List.ofFn x) = petersen x := by
  intro correct
  have hout := petersen_output_not_primary _ correct v
  obtain ⟨u, huv, hzero, hone⟩ := petersen_neighbor_witness v
  have hdown := primary_last_not_antitone 10 pre post v out hout hpre hpost hops
    (fun i => decide (i = u)) (fun i => decide (i = u ∨ i = v))
    (by intro i hi; simp [hi]) (by simp [Ne.symm huv])
  rw [correct _, correct _, hzero, hone] at hdown
  exact Bool.false_ne_true (hdown rfl)

end PEqualNP.Outside.L_meta_2592_aux

namespace PEqualNP.Outside.L_meta_2592_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma every_primary_read (C : Circuit)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) (v : Fin 10) :
    ∃ g ∈ C.gates, v.val ∈ g.inputs := by
  by_contra! hread
  have hout := petersen_output_not_primary C correct v
  obtain ⟨u, huv, hzero, hone⟩ := petersen_neighbor_witness v
  have hh := wf_except C.gates v.val hread
    (List.ofFn fun i : Fin 10 => decide (i = u))
    (List.ofFn fun i : Fin 10 => decide (i = u ∨ i = v)) (by simp)
    (ofFn_except 10 v _ _ (by intro i hi; simp [hi])) C.output hout
  change C.eval (List.ofFn fun i : Fin 10 => decide (i = u)) =
    C.eval (List.ofFn fun i : Fin 10 => decide (i = u ∨ i = v)) at hh
  rw [correct _, correct _, hzero, hone] at hh
  contradiction

lemma primary_use_positive (C : Circuit)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) (v : Fin 10) :
    1 ≤ ∑ j : Fin C.gates.length, (C.gates.get j).inputs.count v.val := by
  obtain ⟨g, hg, hv⟩ := every_primary_read C correct v
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hg
  have hpos : 1 ≤ (C.gates.get j).inputs.count v.val := by
    rw [hj]
    exact List.count_pos_iff.mpr hv
  exact hpos.trans (Finset.single_le_sum (f := fun k : Fin C.gates.length => (C.gates.get k).inputs.count v.val) (fun i _ => Nat.zero_le _) (Finset.mem_univ j))

lemma count_inputs_eq_sum (gs : List Gate) (v : ℕ) :
    (gs.flatMap Gate.inputs).count v = ∑ j : Fin gs.length, (gs.get j).inputs.count v := by
  induction gs with
  | nil => simp
  | cons g gs ih => simp [Fin.sum_univ_succ, ih]

lemma split_read_once (gs : List Gate) (v : ℕ)
    (once : (gs.flatMap Gate.inputs).count v = 1) :
    ∃ pre g post, gs = pre ++ [g] ++ post ∧ g.inputs.count v = 1 ∧
      (∀ h ∈ pre, v ∉ h.inputs) ∧ (∀ h ∈ post, v ∉ h.inputs) := by
  induction gs with
  | nil => simp at once
  | cons g gs ih =>
    have sum : g.inputs.count v + (gs.flatMap Gate.inputs).count v = 1 := by
      simpa using once
    by_cases hg : v ∈ g.inputs
    · have pos : 0 < g.inputs.count v := List.count_pos_iff.mpr hg
      have gz : (gs.flatMap Gate.inputs).count v = 0 := by omega
      refine ⟨[], g, gs, by simp, by omega, by simp, ?_⟩
      intro h hh hv
      exact (List.count_eq_zero.mp gz) (List.mem_flatMap.mpr ⟨h, hh, hv⟩)
    · have gz : g.inputs.count v = 0 := List.count_eq_zero.mpr hg
      have rest : (gs.flatMap Gate.inputs).count v = 1 := by omega
      obtain ⟨pre, h, post, heq, hc, hp, hs⟩ := ih rest
      refine ⟨g :: pre, h, post, by simp [heq], hc, ?_, hs⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hg
      · exact hp q hq

end PEqualNP.Outside.L_meta_2592_aux


namespace PEqualNP.Outside.L_meta_2592_aux

lemma sum_wire_counts_nat {N : ℕ} (L : List ℕ) :
    (∑ w : Fin N, L.count w.val) ≤ L.length := by
  induction L with
  | nil => simp
  | cons a l ih =>
    have ck (w : Fin N) : (a :: l).count w.val = l.count w.val + if w.val = a then 1 else 0 := by
      by_cases h : w.val = a
      · simp [h]
      · simp [h, Ne.symm h]
    have atmost : (∑ w : Fin N, if w.val = a then (1 : ℕ) else 0) ≤ 1 := by
      by_cases ha : a < N
      · have same (w : Fin N) : (if w.val = a then (1 : ℕ) else 0) =
            (if w = (⟨a, ha⟩ : Fin N) then 1 else 0) := by
          simp [Fin.ext_iff]
        simp_rw [same]
        simp
      · have neq (w : Fin N) : w.val ≠ a := by
          intro e
          apply ha
          exact e ▸ w.isLt
        simp [neq]
    simp only [ck, Finset.sum_add_distrib, List.length_cons]
    omega

lemma single_use_primary_nat {n s : ℕ} (parents : Fin s → List ℕ)
    (binary : ∀ j, (parents j).length ≤ 2)
    (unary : ∃ j, (parents j).length ≤ 1)
    (live : ∀ j : Fin s, j.val + 1 < s →
      1 ≤ ∑ k, (parents k).count (n + j.val))
    (small : s < 2 * n) :
    ∃ i : Fin n, (∑ j, (parents j).count i.val) ≤ 1 := by
  classical
  obtain ⟨u, hu⟩ := unary
  have spos : 0 < s := Nat.zero_lt_of_lt u.isLt
  let uses (w : Fin (n + s)) := ∑ j, (parents j).count w.val
  have slots : (∑ w, uses w) ≤ ∑ j, (parents j).length := by
    simp only [uses]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun j _ => sum_wire_counts_nat (parents j))
  have capacity : (∑ j, (parents j).length) + 1 ≤ 2 * s := by
    have cap : ∀ j : Fin s, (parents j).length + (if j = u then 1 else 0) ≤ 2 := by
      intro j
      by_cases e : j = u
      · subst j
        simp only [ite_true]
        omega
      · simp only [e, ite_false, Nat.add_zero]
        exact binary j
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => cap j)
    simpa [Finset.sum_add_distrib, Nat.mul_comm] using h
  have internal : s ≤ (∑ j : Fin s, uses (Fin.natAdd n j)) + 1 := by
    let last : Fin s := ⟨s - 1, by omega⟩
    have each : ∀ j : Fin s,
        1 ≤ uses (Fin.natAdd n j) + (if j = last then 1 else 0) := by
      intro j
      by_cases e : j = last
      · simp [e]
      · have hlt : j.val + 1 < s := by
          have hj := j.isLt
          have hne : j.val ≠ s - 1 := by
            intro eq
            apply e
            apply Fin.ext
            exact eq
          omega
        simpa [e, uses] using live j hlt
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => each j)
    simpa [Finset.sum_add_distrib] using h
  by_contra! frequent
  have primary : 2 * n ≤ ∑ i : Fin n, uses (Fin.castAdd s i) := by
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun i _ => show 2 ≤ uses (Fin.castAdd s i) by exact frequent i)
    simpa [Nat.mul_comm] using h
  rw [Fin.sum_univ_add] at slots
  omega

end PEqualNP.Outside.L_meta_2592_aux
