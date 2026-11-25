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

namespace PEqualNP.Outside.L_meta_2592_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma petersen_has_read_once (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (small : C.size ≤ 19)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not)
    (unary : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (live : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, 10 + j.val ∈ (C.gates.get k).inputs) :
    ∃ v : Fin 10, (∑ j : Fin C.gates.length, (C.gates.get j).inputs.count v.val) = 1 := by
  have binary : ∀ j : Fin C.gates.length, (C.gates.get j).inputs.length ≤ 2 := by
    intro j
    exact (fan _ (List.get_mem _ _)).2
  have hu : ∃ j : Fin C.gates.length, (C.gates.get j).inputs.length ≤ 1 := by
    obtain ⟨g, hg, hnot⟩ := hasNot
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hg
    exact ⟨j, by rw [hj]; exact unary g hg hnot⟩
  have hl : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      1 ≤ ∑ k : Fin C.gates.length, (C.gates.get k).inputs.count (10 + j.val) := by
    intro j hj
    obtain ⟨k, hk⟩ := live j hj
    have hpos : 1 ≤ (C.gates.get k).inputs.count (10 + j.val) := List.count_pos_iff.mpr hk
    exact hpos.trans (Finset.single_le_sum (f := fun i : Fin C.gates.length => (C.gates.get i).inputs.count (10 + j.val)) (fun i _ => Nat.zero_le _) (Finset.mem_univ k))
  obtain ⟨v, hv⟩ := single_use_primary_nat (n := 10)
    (fun j : Fin C.gates.length => (C.gates.get j).inputs) binary hu hl
    (by change C.gates.length ≤ 19 at small; omega)
  exact ⟨v, Nat.le_antisymm hv (primary_use_positive C correct v)⟩

lemma petersen_single_reader_split (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (small : C.size ≤ 19)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not)
    (unary : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (live : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, 10 + j.val ∈ (C.gates.get k).inputs) :
    ∃ (v : Fin 10) (pre : List Gate) (g : Gate) (post : List Gate),
      C.gates = pre ++ [g] ++ post ∧ g.inputs.count v.val = 1 ∧
      (∀ h ∈ pre, v.val ∉ h.inputs) ∧ (∀ h ∈ post, v.val ∉ h.inputs) := by
  obtain ⟨v, hv⟩ := petersen_has_read_once C fan correct small hasNot unary live
  rw [← count_inputs_eq_sum] at hv
  obtain ⟨pre, g, post, heq, hc, hp, hs⟩ := split_read_once C.gates v.val hv
  exact ⟨v, pre, g, post, heq, hc, hp, hs⟩

lemma singleton_of_count_one (L : List ℕ) (v : ℕ) (hlen : L.length ≤ 1)
    (hcount : L.count v = 1) : L = [v] := by
  have hmem : v ∈ L := List.count_pos_iff.mp (by omega)
  cases L with
  | nil => simp at hmem
  | cons a l =>
    cases l with
    | nil => have ha : v = a := by simpa using hmem
        subst a
        rfl
    | cons b l => simp at hlen

lemma only_not_suffix (C : Circuit) (pre post : List Gate) (g : Gate)
    (heq : C.gates = pre ++ [g] ++ post) (hg : g.op = GateOp.not)
    (one : PEqualNP.NotBracket.notCount C = 1) :
    ∀ h ∈ post, h.op ≠ GateOp.not := by
  letI : DecidableEq GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  have hs : (pre.filter fun g : Gate => decide (g.op = GateOp.not)).length + 1 +
      (post.filter fun g : Gate => decide (g.op = GateOp.not)).length = 1 := by
    simpa [PEqualNP.NotBracket.notCount, heq, hg] using one
  have hz : (post.filter fun g : Gate => decide (g.op = GateOp.not)).length = 0 := by omega
  intro h hh hn
  have hm : h ∈ post.filter (fun g : Gate => decide (g.op = GateOp.not)) := by
    simp [hh, hn]
  rw [List.length_eq_zero_iff.mp hz] at hm
  contradiction

lemma sole_reader_not_impossible (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (one : PEqualNP.NotBracket.notCount C = 1)
    (unary : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (v : Fin 10) (pre post : List Gate) (g : Gate)
    (heq : C.gates = pre ++ [g] ++ post) (hc : g.inputs.count v.val = 1)
    (hp : ∀ h ∈ pre, v.val ∉ h.inputs) (hs : ∀ h ∈ post, v.val ∉ h.inputs) :
    g.op ≠ GateOp.not := by
  intro hnot
  have hgmem : g ∈ C.gates := by rw [heq]; simp
  have hinputs : g.inputs = [v.val] :=
    singleton_of_count_one g.inputs v.val (unary g hgmem hnot) hc
  have ge : g = ⟨GateOp.not, [v.val]⟩ := by cases g; simp_all
  have hpost := only_not_suffix C pre post g heq hnot one
  have hops : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or := by
    intro h hh
    have hf := (fan h (by rw [heq]; simp [hh])).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with ha | ho | hn
    · exact Or.inl ha
    · exact Or.inr ho
    · exact False.elim (hpost h hh hn)
  apply petersen_no_primary_last_not_once pre post v C.output hp hs hops
  intro x
  rw [← ge, ← heq]
  exact correct x

end PEqualNP.Outside.L_meta_2592_aux

namespace PEqualNP.Outside.L_meta_2592_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma gate_swap_eval (pre post : List Gate) (op : GateOp) (a b out : ℕ)
    (hop : op = GateOp.and ∨ op = GateOp.or) (x : List Bool) :
    Circuit.eval ⟨pre ++ [⟨op, [a, b]⟩] ++ post, out⟩ x =
      Circuit.eval ⟨pre ++ [⟨op, [b, a]⟩] ++ post, out⟩ x := by
  have hv : op.eval ([a, b].map fun j => (wf pre x).getD j false) =
      op.eval ([b, a].map fun j => (wf pre x).getD j false) := by
    rcases hop with rfl | rfl <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]
  have hh := congrArg (fun t : Bool => (wf post (wf pre x ++ [t])).getD out false) hv
  simpa only [eval_eq, wf, List.foldl_append, List.foldl_cons, List.foldl_nil] using hh

lemma no_primary_binary_partner (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (v : Fin 10) (pre post : List Gate) (g : Gate) (w : ℕ)
    (heq : C.gates = pre ++ [g] ++ post) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hin : g.inputs = [v.val, w] ∨ g.inputs = [w, v.val])
    (hwv : w ≠ v.val)
    (hp : ∀ h ∈ pre, v.val ∉ h.inputs) (hs : ∀ h ∈ post, v.val ∉ h.inputs) :
    10 ≤ w := by
  by_contra! hw
  let q : Fin 10 := ⟨w, hw⟩
  have hvq : v ≠ q := by
    intro h
    exact hwv (congrArg Fin.val h).symm
  have hcorrect : ∀ x : Fin 10 → Bool,
      Circuit.eval ⟨pre ++ [⟨g.op, [v.val, q.val]⟩] ++ post, C.output⟩ (List.ofFn x) = petersen x := by
    intro x
    rcases hin with hf | hr
    · have ge : g = ⟨g.op, [v.val, q.val]⟩ := by cases g; simp_all [q]
      rw [← ge, ← heq]
      exact correct x
    · rw [gate_swap_eval pre post g.op v.val q.val C.output hop]
      have ge : g = ⟨g.op, [q.val, v.val]⟩ := by cases g; simp_all [q]
      rw [← ge, ← heq]
      exact correct x
  rcases hop with ha | ho
  · rw [ha] at hcorrect
    exact petersen_no_primary_and_once pre post v q C.output hvq hp hs hcorrect
  · rw [ho] at hcorrect
    exact petersen_no_primary_or_once pre post v q C.output hvq hp hs hcorrect

lemma input_shape_of_once (L : List ℕ) (v : ℕ) (hbinary : L.length ≤ 2)
    (hcount : L.count v = 1) :
    L = [v] ∨ ∃ w : ℕ, w ≠ v ∧ (L = [v, w] ∨ L = [w, v]) := by
  have hmem : v ∈ L := List.count_pos_iff.mp (by omega)
  cases L with
  | nil => simp at hmem
  | cons a l =>
    cases l with
    | nil =>
      left
      have ha : v = a := by simpa using hmem
      subst a
      rfl
    | cons b l =>
      cases l with
      | cons c l => simp at hbinary
      | nil =>
        have hmem' : v = a ∨ v = b := by simpa using hmem
        rcases hmem' with rfl | rfl
        · right
          refine ⟨b, ?_, Or.inl rfl⟩
          intro h
          subst b
          simp at hcount
        · right
          refine ⟨a, ?_, Or.inr rfl⟩
          intro h
          subst a
          simp at hcount

end PEqualNP.Outside.L_meta_2592_aux


namespace PEqualNP.Outside.L_meta_2592_aux.Alias

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

private lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

private lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

private lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

private lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

private lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

private lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

private lemma wiresFrom_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (by omega)]
  rw [wiresFrom_getD_lt _ _ _ (by simp [hlen])]
  exact getD_snoc_eq _ _ _ _ hlen.symm

private def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)


private def substWire (k a i : ℕ) : ℕ :=
  if i < k then i else if i = k then a else i - 1

private def substGate (k a : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (substWire k a)⟩

private lemma substGate_ok (k a : ℕ) (g : Gate) (h : OkGate g) : OkGate (substGate k a g) :=
  ⟨h.1, by simp [substGate]; exact h.2⟩

private lemma substGate_nok (k a : ℕ) (g : Gate) (h : NOkGate g) : NOkGate (substGate k a g) :=
  ⟨substGate_ok k a g h.1, fun hop => by simp [substGate]; exact h.2 hop⟩

private def deleteGate (m : ℕ) (C : Circuit) (j a : ℕ) : Circuit :=
  ⟨C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a),
    substWire (m + j) a C.output⟩

private lemma deleteGate_ok (m : ℕ) (C : Circuit) (j a : ℕ)
    (hok : ∀ g ∈ C.gates, OkGate g) : ∀ g ∈ (deleteGate m C j a).gates, OkGate g := by
  intro g hg
  rcases List.mem_append.1 hg with h1 | h1
  · exact hok g (List.mem_of_mem_take h1)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
    exact substGate_ok _ _ g0 (hok g0 (List.mem_of_mem_drop hg0))

private lemma deleteGate_nok (m : ℕ) (C : Circuit) (j a : ℕ)
    (hnok : ∀ g ∈ C.gates, NOkGate g) : ∀ g ∈ (deleteGate m C j a).gates, NOkGate g := by
  intro g hg
  rcases List.mem_append.1 hg with h1 | h1
  · exact hnok g (List.mem_of_mem_take h1)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h1
    exact substGate_nok _ _ g0 (hnok g0 (List.mem_of_mem_drop hg0))

private lemma deleteGate_len (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length) :
    (deleteGate m C j a).gates.length = C.gates.length - 1 := by
  simp only [deleteGate, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega


private lemma wiresFrom_subst_aux (k a : ℕ) (hka : a < k) :
    ∀ (gs : List Gate) (w₁ w₂ : List Bool),
      w₁.length = w₂.length + 1 → k ≤ w₂.length →
      (∀ i < w₁.length, w₂.getD (substWire k a i) false = w₁.getD i false) →
      ∀ i < (wiresFrom gs w₁).length,
        (wiresFrom (gs.map (substGate k a)) w₂).getD (substWire k a i) false =
          (wiresFrom gs w₁).getD i false := by
  intro gs
  induction gs with
  | nil =>
    intro w₁ w₂ _ _ hag i hi
    exact hag i hi
  | cons g rest ih =>
    intro w₁ w₂ hlen hk hag
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons]
    have hmap : ((substGate k a g).inputs.map fun i => w₂.getD i false) =
        (g.inputs.map fun i => w₁.getD i false) := by
      simp only [substGate, List.map_map]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply]
      by_cases hi : i < w₁.length
      · exact hag i hi
      · have hge : w₂.length ≤ substWire k a i := by
          unfold substWire
          split_ifs <;> omega
        rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]
    rw [hmap]
    show ∀ i < (wiresFrom rest _).length,
        (wiresFrom (rest.map (substGate k a)) (w₂ ++ [g.op.eval (g.inputs.map fun i => w₁.getD i false)])).getD
          (substWire k a i) false = _
    apply ih _ _ (by simp [hlen]) (by simp; omega)
    intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < w₁.length
    · have hsublt : substWire k a i < w₂.length := by
        unfold substWire
        split_ifs <;> omega
      rw [getD_snoc_lt _ _ _ _ hsublt, getD_snoc_lt _ _ _ _ hlt]
      exact hag i hlt
    · have hieq : i = w₁.length := by omega
      have hsubeq : substWire k a i = w₂.length := by
        unfold substWire
        split_ifs <;> omega
      rw [getD_snoc_eq _ _ _ _ hsubeq, getD_snoc_eq _ _ _ _ hieq]

private lemma deleteGate_wires_eq (m : ℕ) (C : Circuit) (j a : ℕ) (hj : j < C.gates.length)
    (ha : a < m + j) (x : List Bool) (hx : x.length = m)
    (heq : (C.wires x).getD (m + j) false = (C.wires x).getD a false) :
    ∀ i < m + C.gates.length,
      ((deleteGate m C j a).wires x).getD (substWire (m + j) a i) false =
        (C.wires x).getD i false := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  show ∀ i < m + C.gates.length,
      (wiresFrom (C.gates.take j ++ (C.gates.drop (j + 1)).map (substGate (m + j) a)) x).getD
          (substWire (m + j) a i) false =
        (wiresFrom C.gates x).getD i false
  set w₂ := wiresFrom (C.gates.take j) x with hw₂
  set w₁ := wiresFrom [C.gates[j]] w₂ with hw₁
  have hw₂_len : w₂.length = m + j := by
    rw [hw₂, wiresFrom_length, hx, List.length_take, Nat.min_eq_left (by omega)]
  have hw₁_len : w₁.length = m + j + 1 := by
    rw [hw₁, wiresFrom_length, hw₂_len]; simp
  have hag0 : ∀ i < w₁.length, w₂.getD (substWire (m + j) a i) false = w₁.getD i false := by
    intro i hi
    by_cases hlt : i < m + j
    · simp only [substWire, hlt, ↓reduceIte]
      rw [hw₁, wiresFrom_cons, wiresFrom_nil, getD_snoc_lt _ _ _ _ (by omega)]
    · have hieq : i = m + j := by omega
      subst hieq
      simp only [substWire, lt_irrefl, ↓reduceIte]
      have h1 : (C.wires x).getD (m + j) false = w₁.getD (m + j) false := by
        show (wiresFrom C.gates x).getD (m + j) false = _
        conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
        exact wiresFrom_getD_lt _ _ _ (by omega)
      have h2 : (C.wires x).getD a false = w₂.getD a false := by
        show (wiresFrom C.gates x).getD a false = _
        conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
        rw [wiresFrom_getD_lt _ _ _ (by omega), hw₁, wiresFrom_cons, wiresFrom_nil,
          getD_snoc_lt _ _ _ _ (by omega)]
      rw [← h2, ← heq, h1]
  intro i hi
  rw [wiresFrom_append, ← hw₂]
  conv_rhs => rw [hsplit, wiresFrom_append, wiresFrom_append, ← hw₂, ← hw₁]
  have hlen_rhs : (wiresFrom (C.gates.drop (j + 1)) w₁).length = m + C.gates.length := by
    rw [wiresFrom_length, hw₁_len, List.length_drop]; omega
  exact wiresFrom_subst_aux (m + j) a ha (C.gates.drop (j + 1)) w₁ w₂ (by omega) (by omega) hag0
    i (by omega)


lemma erase_alias {m : ℕ} (C : Circuit) (hok : ∀ g ∈ C.gates, OkGate g)
    (j a : ℕ) (hj : j < C.gates.length) (ha : a < m + j)
    (heq : ∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + j) false =
      (C.wires (List.ofFn x)).getD a false) :
    HasCircuitSize m (circuitFun m C) (C.gates.length - 1) := by
  refine ⟨deleteGate m C j a, deleteGate_ok m C j a hok,
    by show (deleteGate m C j a).gates.length ≤ C.gates.length - 1; rw [deleteGate_len m C j a hj], ?_⟩
  intro x
  show ((deleteGate m C j a).wires (List.ofFn x)).getD (substWire (m + j) a C.output) false =
    (C.wires (List.ofFn x)).getD C.output false
  by_cases hlt : C.output < m + C.gates.length
  · exact deleteGate_wires_eq m C j a hj ha (List.ofFn x) (by simp) (heq x) C.output hlt
  · have hge1 : (deleteGate m C j a).gates.length + m ≤ substWire (m + j) a C.output := by
      rw [deleteGate_len m C j a hj]
      unfold substWire
      split_ifs <;> omega
    have h1 : ((deleteGate m C j a).wires (List.ofFn x)).length =
        m + (deleteGate m C j a).gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    have h2 : (C.wires (List.ofFn x)).length = m + C.gates.length := by
      show (wiresFrom _ _).length = _; rw [wiresFrom_length]; simp
    rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

private lemma wire_eval_gate {m : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin m → Bool) :
    (C.wires (List.ofFn x)).getD (m + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < m + j then (C.wires (List.ofFn x)).getD i false else false) := by
  show (wiresFrom C.gates (List.ofFn x)).getD (m + j) false = _
  have h1 := wiresFrom_getD_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn] at h1
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i _
  have hlen : (wiresFrom (C.gates.take j) (List.ofFn x)).length = m + j := by
    rw [wiresFrom_length, List.length_ofFn, List.length_take, Nat.min_eq_left (by omega)]
  by_cases hi : i < m + j
  · simp only [hi, ↓reduceIte]
    have hsp : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
    conv_rhs => rw [show C.wires (List.ofFn x) = wiresFrom C.gates (List.ofFn x) from rfl, hsp, wiresFrom_append]
    exact (wiresFrom_getD_lt _ _ _ (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact List.getD_eq_default _ _ (by omega)

lemma no_alias {m : ℕ} (C : Circuit) (fan : FanInTwo C)
    (minimal : ∀ E : Circuit, FanInTwo E →
      circuitFun m E = circuitFun m C → C.size ≤ E.size)
    (j a : ℕ) (hj : j < C.gates.length) (ha : a < m + j) :
    ¬ ∀ x : Fin m → Bool, (C.wires (List.ofFn x)).getD (m + j) false =
      (C.wires (List.ofFn x)).getD a false := by
  intro same
  obtain ⟨E, hE, hsize, correct⟩ := erase_alias C fan j a hj ha same
  have lower := minimal E hE (funext correct)
  change E.size ≤ C.size - 1 at hsize
  change j < C.size at hj
  omega

lemma no_unary_copy {m : ℕ} (C : Circuit) (fan : FanInTwo C)
    (minimal : ∀ E : Circuit, FanInTwo E →
      circuitFun m E = circuitFun m C → C.size ≤ E.size)
    (j a : ℕ) (hj : j < C.gates.length) (ha : a < m + j)
    (op : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or) :
    C.gates[j].inputs ≠ [a] := by
  intro inputs
  apply no_alias C fan minimal j a hj ha
  intro x
  rw [wire_eval_gate C j hj x, inputs]
  rcases op with op | op <;> simp [op, ha, GateOp.eval]

lemma no_duplicate_copy {m : ℕ} (C : Circuit) (fan : FanInTwo C)
    (minimal : ∀ E : Circuit, FanInTwo E →
      circuitFun m E = circuitFun m C → C.size ≤ E.size)
    (j a : ℕ) (hj : j < C.gates.length) (ha : a < m + j)
    (op : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or) :
    C.gates[j].inputs ≠ [a, a] := by
  intro inputs
  apply no_alias C fan minimal j a hj ha
  intro x
  rw [wire_eval_gate C j hj x, inputs]
  rcases op with op | op <;> simp [op, ha, GateOp.eval]

end PEqualNP.Outside.L_meta_2592_aux.Alias


namespace PEqualNP.Outside.L_meta_2592_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma not_count_one_has_not (C : Circuit) (one : PEqualNP.NotBracket.notCount C = 1) :
    ∃ g ∈ C.gates, g.op = GateOp.not := by
  letI : DecidableEq GateOp := PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq
  by_contra! hn
  have hf : C.gates.filter (fun g => decide (g.op = GateOp.not)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro g hg
    simp [hn g hg]
  have hz : PEqualNP.NotBracket.notCount C = 0 := by
    simp [PEqualNP.NotBracket.notCount, hf]
  omega

lemma one_not_single_primary_internal (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (small : C.size ≤ 19) (one : PEqualNP.NotBracket.notCount C = 1)
    (unary : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (live : ∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, 10 + j.val ∈ (C.gates.get k).inputs)
    (minimal : ∀ E : Circuit, FanInTwo E →
      circuitFun 10 E = circuitFun 10 C → C.size ≤ E.size) :
    ∃ (v : Fin 10) (pre : List Gate) (g : Gate) (post : List Gate) (w : ℕ),
      C.gates = pre ++ [g] ++ post ∧
      (∀ h ∈ pre, v.val ∉ h.inputs) ∧ (∀ h ∈ post, v.val ∉ h.inputs) ∧
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      (g.inputs = [v.val, w] ∨ g.inputs = [w, v.val]) ∧ 10 ≤ w := by
  obtain ⟨v, pre, g, post, heq, hc, hp, hs⟩ :=
    petersen_single_reader_split C fan correct small (not_count_one_has_not C one) unary live
  have hgmem : g ∈ C.gates := by rw [heq]; simp
  have hgnot := sole_reader_not_impossible C fan correct one unary v pre post g heq hc hp hs
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
    have ho := (fan g hgmem).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    tauto
  have shape := input_shape_of_once g.inputs v.val (fan g hgmem).2 hc
  rcases shape with hsingle | ⟨w, hwv, hin⟩
  · have hj : pre.length < C.gates.length := by rw [heq]; simp; omega
    have hjg : C.gates[pre.length]'hj = g := by rw [heq]; simp
    have bad := Alias.no_unary_copy C fan minimal pre.length v.val hj
      (by have hv := v.isLt; omega) (by simpa [hjg] using hop)
    exact False.elim (bad (by simpa [hjg] using hsingle))
  · exact ⟨v, pre, g, post, w, heq, hp, hs, hop, hin,
      no_primary_binary_partner C fan correct v pre post g w heq hop hin hwv hp hs⟩

end PEqualNP.Outside.L_meta_2592_aux
