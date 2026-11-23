import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_951_small

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_append _ _ _ _ h]

lemma getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ) (hk : k ≤ gs.length) :
    (wiresFrom (gs.take k) w).getD i false =
      if i < w.length + k then (wiresFrom gs w).getD i false else false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit, wiresFrom_append]
    exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm
  · rw [List.getD_eq_default]
    omega

lemma getD_snoc_eq (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp

lemma getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (wiresFrom gs w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (wiresFrom gs w).getD i false else false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  have heq : wiresFrom gs w =
      wiresFrom (gs.drop (k + 1))
        (wiresFrom (gs.take k) w ++
          [(gs[k]).op.eval ((gs[k]).inputs.map fun i => (wiresFrom (gs.take k) w).getD i false)]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt]
  · conv_lhs => rw [← hlen, getD_snoc_eq]
    congr 1
    apply List.map_congr_left
    intro i _
    rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk), heq]
  · rw [List.length_append, hlen]; simp

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

abbrev Input (n : ℕ) := Fin n → Bool
abbrev Wire (n : ℕ) := Input n → Bool
variable {n : ℕ}

def hit (S : Finset (Fin n)) (x : Input n) := ∃ p ∈ S, x p = true
def single (p : Fin n) : Input n := fun k => decide (k = p)
def outside (S : Finset (Fin n)) : Input n := fun k => decide (k ∉ S)

lemma hit_single (S : Finset (Fin n)) (p : Fin n) : hit S (single p) ↔ p ∈ S := by
  simp [hit, single]

lemma hit_point (S : Finset (Fin n)) (p : Fin n) (hp : p ∈ S) : hit S (single p) :=
  (hit_single S p).2 hp

lemma miss (S : Finset (Fin n)) : ¬ hit S (outside S) := by
  simp [hit, outside]

lemma two_points (S : Finset (Fin n)) (hs : 2 ≤ S.card) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b := by
  by_contra! h
  have := Finset.card_le_one.mpr h
  omega

def Low (S : Finset (Fin n)) (f : Wire n) := ∀ x, f x = true → hit S x
def High (S : Finset (Fin n)) (f : Wire n) := ∀ x, hit S x → f x = true
def Exact (S : Finset (Fin n)) (f : Wire n) := ∀ x, f x = true ↔ hit S x

def Good (S : Finset (Fin n)) (f : Wire n) :=
  (Low S f ∨ High S f) ∧
  (∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ f (single a) = true ∧ f (single b) = true) ∧
  f (outside S) = false

lemma exact_good {S : Finset (Fin n)} {f : Wire n} (hs : 2 ≤ S.card)
    (h : Exact S f) : Good S f := by
  obtain ⟨a, ha, b, hb, hn⟩ := two_points S hs
  exact ⟨Or.inl (fun x => (h x).1),
    ⟨a, ha, b, hb, hn, (h _).2 (hit_point _ _ ha), (h _).2 (hit_point _ _ hb)⟩,
    Bool.eq_false_iff.mpr (fun ht => miss S ((h _).1 ht))⟩

lemma incompatible {S T : Finset (Fin n)} {f : Wire n}
    (hST : (S ∩ T).card ≤ 1) (h : Good S f) (h' : Good T f) : False := by
  obtain ⟨_, ⟨a, ha, b, hb, hn, hc, hd⟩, hf⟩ := h
  rcases h'.1 with low | high
  · have hTa : a ∈ T := (hit_single _ _).1 (low _ hc)
    have hTb : b ∈ T := (hit_single _ _).1 (low _ hd)
    exact hn (Finset.card_le_one.mp hST a (Finset.mem_inter.mpr ⟨ha,hTa⟩)
      b (Finset.mem_inter.mpr ⟨hb,hTb⟩))
  · have inc (p : Fin n) (hp : p ∈ T) : p ∈ S := by
      by_contra hh
      have ht := high (outside S) ⟨p, hp, by simpa [outside] using hh⟩
      simp [hf] at ht
    obtain ⟨a',ha',b',hb',hn',_,_⟩ := h'.2.1
    exact hn' (Finset.card_le_one.mp hST a' (Finset.mem_inter.mpr ⟨inc _ ha',ha'⟩)
      b' (Finset.mem_inter.mpr ⟨inc _ hb',hb'⟩))

def Falls (f : Wire n) := ∀ x y : Input n, (∀ k, x k = true → y k = true) →
  f y = true → f x = true

lemma good_rises {S : Finset (Fin n)} {f : Wire n} (h : Good S f) : ¬ Falls f := by
  rintro hf
  obtain ⟨hl | hh, ⟨a, ha, b, hb, hn, hc, hd⟩, ho⟩ := h
  · have h0 := hf (fun _ => false) _ (by simp) hc
    obtain ⟨_, _, ht⟩ := hl _ h0
    contradiction
  · have h1 := hh (fun _ => true) ⟨a, ha, rfl⟩
    have ht := hf (outside S) (fun _ => true) (by simp) h1
    simp [ho] at ht

lemma good_or {S : Finset (Fin n)} {u v : Wire n} (hs : 3 ≤ S.card)
    (he : Exact S (fun x => u x || v x)) : Good S u ∨ Good S v := by
  have lu : Low S u := fun x h => (he x).1 (by simp [h])
  have lv : Low S v := fun x h => (he x).1 (by simp [h])
  have fu : u (outside S) = false := Bool.eq_false_iff.mpr (fun h => miss S (lu _ h))
  have fv : v (outside S) = false := Bool.eq_false_iff.mpr (fun h => miss S (lv _ h))
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp (by omega : 2 < S.card)
  have cov (p : Fin n) (hp : p ∈ S) := (he _).2 (hit_point S p hp)
  simp only [Bool.or_eq_true] at cov
  have gu (a b : Fin n) (ha : a ∈ S) (hb : b ∈ S) (hn : a ≠ b)
      (hc : u (single a) = true) (hd : u (single b) = true) : Good S u ∨ Good S v :=
    Or.inl ⟨Or.inl lu, ⟨a, ha, b, hb, hn, hc, hd⟩, fu⟩
  have gv (a b : Fin n) (ha : a ∈ S) (hb : b ∈ S) (hn : a ≠ b)
      (hc : v (single a) = true) (hd : v (single b) = true) : Good S u ∨ Good S v :=
    Or.inr ⟨Or.inl lv, ⟨a, ha, b, hb, hn, hc, hd⟩, fv⟩
  rcases cov a ha with x | x <;> rcases cov b hb with y | y <;> rcases cov c hc with z | z
  all_goals first
    | exact gu a b ha hb hab x y
    | exact gu a c ha hc hac x z
    | exact gu b c hb hc hbc y z
    | exact gv a b ha hb hab x y
    | exact gv a c ha hc hac x z
    | exact gv b c hb hc hbc y z

lemma good_and {S : Finset (Fin n)} {u v : Wire n} (hs : 2 ≤ S.card)
    (he : Exact S (fun x => u x && v x)) : Good S u ∨ Good S v := by
  have hh (x : Input n) (h : hit S x) : u x = true ∧ v x = true := by
    have ht := (he x).2 h
    simpa only [Bool.and_eq_true] using ht
  have makeGood (f : Wire n) (h : High S f) (hf : f (outside S) = false) : Good S f := by
    obtain ⟨a, ha, b, hb, hn⟩ := two_points S hs
    exact ⟨Or.inr h, ⟨a, ha, b, hb, hn, h _ (hit_point _ _ ha), h _ (hit_point _ _ hb)⟩, hf⟩
  cases hu : u (outside S) with
  | false => exact Or.inl (makeGood _ (fun x h => (hh x h).1) hu)
  | true =>
    apply Or.inr (makeGood _ (fun x h => (hh x h).2) _)
    apply Bool.eq_false_iff.mpr
    intro hv
    exact miss S ((he _).1 (by simp [hu, hv]))

def wire (gs : List Gate) (i : ℕ) (x : Input n) :=
  (wiresFrom gs (List.ofFn x)).getD i false

def prior (gs : List Gate) (k i : ℕ) : Wire n :=
  if i < n + k then wire gs i else fun _ => false

lemma prior_apply (gs : List Gate) (k i : ℕ) (x : Input n) :
    prior gs k i x = if i < n+k then wire gs i x else false := by
  by_cases h : i < n+k <;> simp [prior, h]

lemma wire_gate (gs : List Gate) (k : ℕ) (hk : k < gs.length) (x : Input n) :
    wire gs (n+k) x = gs[k].op.eval (gs[k].inputs.map (fun i => prior gs k i x)) := by
  simpa only [prior_apply, wire, List.length_ofFn] using getD_wiresFrom_gate gs (List.ofFn x) k hk

lemma good_in_range {gs : List Gate} {i : ℕ} {S : Finset (Fin n)} (h : Good S (wire gs i)) :
    n ≤ i ∧ i < n + gs.length := by
  obtain ⟨_, ⟨a, ha, b, hb, hn, hc, hd⟩, _⟩ := h
  constructor
  · by_contra! hi
    have inp (x : Input n) : wire gs i x = x ⟨i, hi⟩ := by
      unfold wire
      rw [getD_wiresFrom_lt _ _ _ (by simpa)]
      rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] : i < (List.ofFn x).length), List.getElem_ofFn]
    rw [inp] at hc hd
    exact hn ((of_decide_eq_true hc).symm.trans (of_decide_eq_true hd))
  · by_contra! hi
    unfold wire at hc
    rw [List.getD_eq_default _ _ (by simpa [length_wiresFrom] using hi)] at hc
    contradiction

lemma from_prior {gs : List Gate} {k i : ℕ} {S : Finset (Fin n)} (h : Good S (prior gs k i)) :
    ∃ j < n+k, Good S (wire gs j) := by
  unfold prior at h
  split at h
  · exact ⟨_, by assumption, h⟩
  · exact False.elim (good_rises h (fun _ _ _ ht => ht))

def OnlyOne (C : Circuit) := ∀ i j : Fin C.gates.length,
  (C.gates.get i).op = GateOp.not → (C.gates.get j).op = GateOp.not → i = j

lemma not_falls (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hu : OnlyOne C)
    (k : ℕ) (hk : k < C.gates.length) (hop : C.gates[k].op = GateOp.not) :
    Falls (n := n) (wire C.gates (n+k)) := by
  have hm : ∀ g ∈ C.gates.take k, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hg
    have hik : i < k := by simp only [List.length_take] at hi; omega
    have hil : i < C.gates.length := by omega
    rw [List.getElem_take]
    have hg' := (hf C.gates[i] (List.getElem_mem hil)).1
    rcases hg' with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · have he := hu ⟨i, hil⟩ ⟨k, hk⟩ h hop
      have he' : i = k := congrArg Fin.val he
      omega
  intro x y hxy
  have hle (i : ℕ) : prior C.gates k i x = true → prior C.gates k i y = true := by
    have hv (z : Input n) : prior C.gates k i z =
        (wiresFrom (C.gates.take k) (List.ofFn z)).getD i false := by
      rw [getD_wiresFrom_take _ _ _ _ (by omega)]
      simp only [prior_apply, wire, List.length_ofFn]
    rw [hv, hv]
    apply wiresFrom_mono _ hm _ _ (by simp)
    intro t ht
    by_cases h : t < n
    · rw [List.getD_eq_getElem _ _ (by simpa using h)] at ht ⊢
      simp only [List.getElem_ofFn] at ht ⊢
      exact hxy ⟨t,h⟩ ht
    · rw [List.getD_eq_default _ _ (by simp; omega)] at ht
      contradiction
  rw [wire_gate _ _ hk, wire_gate _ _ hk, hop]
  cases he : C.gates[k].inputs with
  | nil => simp [GateOp.eval]
  | cons i is =>
    simp only [List.map_cons, GateOp.eval, List.headD_cons, Bool.not_eq_true']
    exact fun hy => Bool.eq_false_iff.mpr (fun hx => by simpa [hy] using hle i hx)

lemma earlier (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hu : OnlyOne C)
    (S : Finset (Fin n)) (hS : 3 ≤ S.card) (k : ℕ) (hk : k < C.gates.length) (he : Exact S (wire C.gates (n+k))) :
    ∃ i < n+k, Good S (wire C.gates i) := by
  let g := C.gates[k]
  have ha := hf g (List.getElem_mem hk)
  have leg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := ha.1
  have len := ha.2
  have eqn (x : Input n) : wire C.gates (n+k) x =
      g.op.eval (g.inputs.map (fun i => prior C.gates k i x)) := wire_gate _ _ _ _
  have bad (b : Bool) (h : ∀ x : Input n, wire C.gates (n+k) x = b) : False := by
    apply good_rises (exact_good (by omega) he)
    intro x y _ ht
    rwa [h x, ← h y]
  rcases leg with ha | ho | hn
  · cases hin : g.inputs with
    | nil => exact (bad true (by simp [eqn, hin, ha, GateOp.eval])).elim
    | cons i rest =>
      cases rest with
      | nil =>
        apply from_prior (i := i)
        apply exact_good (by omega)
        intro x
        simpa [eqn, hin, ha, GateOp.eval] using he x
      | cons j more =>
        have em : more = [] := by rw [hin] at len; simpa using len
        rw [em] at hin
        have h : Exact S (fun x => prior C.gates k i x && prior C.gates k j x) := by
          intro x
          simpa [eqn, hin, ha, GateOp.eval] using he x
        exact (good_and (by omega) h).elim from_prior from_prior
  · cases hin : g.inputs with
    | nil => exact (bad false (by simp [eqn, hin, ho, GateOp.eval])).elim
    | cons i rest =>
      cases rest with
      | nil =>
        apply from_prior (i := i)
        apply exact_good (by omega)
        intro x
        simpa [eqn, hin, ho, GateOp.eval] using he x
      | cons j more =>
        have em : more = [] := by rw [hin] at len; simpa using len
        rw [em] at hin
        have h : Exact S (fun x => prior C.gates k i x || prior C.gates k j x) := by
          intro x
          simpa [eqn, hin, ho, GateOp.eval] using he x
        exact (good_or hS h).elim from_prior from_prior
  · exact (good_rises (exact_good (by omega) he) (not_falls C hf hu k hk hn)).elim


lemma pair_gates (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hu : OnlyOne C)
    (S : Finset (Fin n)) (hS : 3 ≤ S.card) (o : ℕ) (he : Exact S (wire C.gates o)) :
    ∃ i j : Fin C.gates.length, i ≠ j ∧
      Good S (wire C.gates (n+i.val)) ∧ Good S (wire C.gates (n+j.val)) := by
  have hg := exact_good (by omega) he
  obtain ⟨ho, ho'⟩ := good_in_range hg
  let j : Fin C.gates.length := ⟨o-n, by omega⟩
  have hj : n + j.val = o := by dsimp [j]; omega
  obtain ⟨p, hp, hgp⟩ := earlier C hf hu S hS j j.isLt (hj ▸ he)
  obtain ⟨hp0, hp1⟩ := good_in_range hgp
  let i : Fin C.gates.length := ⟨p-n, by omega⟩
  have hi : n + i.val = p := by dsimp [i]; omega
  refine ⟨i, j, ?_, hi ▸ hgp, hj ▸ hg⟩
  intro eqij
  rw [← eqij, hi] at hp
  omega


noncomputable def owned (S : Finset (Fin n)) (gates : List Gate) : Finset ℕ := by
  classical
  exact (Finset.range gates.length).filter (fun k => Good S (wire gates (n+k)))

lemma count_for_set (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hu : OnlyOne C)
    (S : Finset (Fin n)) (h2 : 2 ≤ S.card) (h3 : S.card ≤ 3)
    (o : ℕ) (he : Exact S (wire C.gates o)) :
    S.card - 1 ≤ (owned S C.gates).card := by
  classical
  let A := (Finset.range C.gates.length).filter (fun k => Good S (wire C.gates (n+k)))
  change S.card - 1 ≤ A.card
  by_cases h : 3 ≤ S.card
  · obtain ⟨i,j,hij,hi,hj⟩ := pair_gates C hf hu S h o he
    have hiA : i.val ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt,hi⟩
    have hjA : j.val ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt,hj⟩
    have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hpair : ({i.val,j.val} : Finset ℕ) ⊆ A := by
      intro k hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> assumption
    have hc := Finset.card_le_card hpair
    rw [Finset.card_pair hval] at hc
    omega
  · have hg := exact_good h2 he
    obtain ⟨ho,ho'⟩ := good_in_range hg
    have hmem : o-n ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),by
      simpa only [Nat.add_sub_of_le ho] using hg⟩
    have hc := Finset.card_pos.mpr ⟨o-n,hmem⟩
    omega

lemma sum_card_disjoint_le {ι : Type*} [DecidableEq ι] (R : Finset ι) (A : ι → Finset ℕ)
    (c : ι → ℕ) (B : Finset ℕ)
    (hd : ∀ i ∈ R, ∀ j ∈ R, i ≠ j → Disjoint (A i) (A j))
    (hsub : ∀ i ∈ R, A i ⊆ B)
    (hc : ∀ i ∈ R, c i ≤ (A i).card) :
    ∑ i ∈ R, c i ≤ B.card := by
  have hpd : (R : Set ι).PairwiseDisjoint A := fun i hi j hj hij => hd i hi j hj hij
  calc
    ∑ i ∈ R, c i ≤ ∑ i ∈ R, (A i).card := Finset.sum_le_sum hc
    _ = (R.biUnion A).card := (Finset.card_biUnion hpd).symm
    _ ≤ B.card := Finset.card_le_card fun w hw => by
      obtain ⟨i, hi, hwi⟩ := Finset.mem_biUnion.mp hw
      exact hsub i hi hwi

lemma small_lower (n m : ℕ) (S : Fin m → Finset (Fin n))
    (h2 : ∀ i, 2 ≤ (S i).card) (h3 : ∀ i, (S i).card ≤ 3)
    (hl : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hn : ∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length,
      (gates.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i)
    (he : ∀ (w : Fin m) (x : Fin n → Bool), Circuit.eval ⟨gates,out w⟩ (List.ofFn x) =
      decide (∃ v ∈ S w, x v = true)) :
    (∑ i : Fin m, ((S i).card - 1)) ≤ gates.length := by
  classical
  let C : Circuit := ⟨gates,0⟩
  have hf : PEqualNP.MetaComplexity.FanInTwo C := hg
  have hu : OnlyOne C := by
    obtain ⟨ι,hι⟩ := hn
    intro i j hi hj
    obtain ⟨a,ha⟩ := hι i hi
    obtain ⟨b,hb⟩ := hι j hj
    have hab : a = b := Subsingleton.elim _ _
    exact ha.symm.trans (hab ▸ hb)
  have hex (i : Fin m) : Exact (S i) (wire C.gates (out i)) := by
    intro x
    change Circuit.eval ⟨gates,out i⟩ (List.ofFn x) = true ↔ hit (S i) x
    rw [he]
    exact decide_eq_true_iff
  let A (i : Fin m) := (Finset.range gates.length).filter
    (fun k => Good (S i) (wire gates (n+k)))
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ Finset.univ,
      i ≠ j → Disjoint (A i) (A j) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    exact incompatible (hl i j hij) (Finset.mem_filter.mp hki).2 (Finset.mem_filter.mp hkj).2
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin m)), A i ⊆ Finset.range gates.length :=
    fun _ _ => Finset.filter_subset _ _
  have hc : ∀ i ∈ (Finset.univ : Finset (Fin m)), (S i).card-1 ≤ (A i).card := by
    intro i _
    exact count_for_set C hf hu (S i) (h2 i) (h3 i) (out i) (hex i)
  simpa only [Finset.card_range] using sum_card_disjoint_le Finset.univ A
    (fun i => (S i).card-1) (Finset.range gates.length) hd hsub hc

end PEqualNP.Outside.L_meta_951_small

namespace PEqualNP.Outside.L_meta_951_plus_one_monotone_aux

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
  (Finset.Ico n (n + gs.length)).filter fun i => Cnt S gs i

theorem D_mono {n : ℕ} (S : Finset (Fin n)) (gs : List Gate) (g : Gate) :
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

end PEqualNP.Outside.L_meta_951_plus_one_monotone_aux

open PEqualNP.Outside.L_meta_951_plus_one_monotone_aux in
theorem PEqualNP.Outside.L_meta_951_plus_one_monotone : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), (PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)) = decide (∃ v ∈ S w, x v = true)) → ∑ w, ((S w).card - 1) ≤ gates.length := by
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
namespace PEqualNP.Outside.L_meta_951_plus_one

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_951_small

lemma owned_base {n : ℕ} (C : Circuit)
    (hf : PEqualNP.MetaComplexity.FanInTwo C) (hu : OnlyOne C)
    (S : Finset (Fin n)) (h2 : 2 ≤ S.card)
    (o : ℕ) (he : Exact S (wire C.gates o)) :
    min (S.card-1) 2 ≤ (owned S C.gates).card := by
  classical
  by_cases h3 : 3 ≤ S.card
  · obtain ⟨i,j,hij,hi,hj⟩ := pair_gates C hf hu S h3 o he
    have hs : ({i.val,j.val} : Finset ℕ) ⊆ owned S C.gates := by
      intro k hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, hi⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, hj⟩
    have hc := Finset.card_le_card hs
    have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rw [Finset.card_pair hv] at hc
    omega
  · have h := count_for_set C hf hu S h2 (by omega) o he
    omega

lemma base_plus_not {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h2 : ∀ i, 2 ≤ (S i).card)
    (hl : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (C : Circuit) (hf : PEqualNP.MetaComplexity.FanInTwo C) (hu : OnlyOne C)
    (out : Fin m → ℕ) (he : ∀ i, Exact (S i) (wire C.gates (out i)))
    (k : Fin C.gates.length) (hk : (C.gates.get k).op = GateOp.not) :
    (∑ i : Fin m, min ((S i).card-1) 2) + 1 ≤ C.gates.length := by
  classical
  let A (i : Fin m) := owned (S i) C.gates
  let B := (Finset.range C.gates.length).erase k.val
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin m)), ∀ j ∈ Finset.univ,
      i ≠ j → Disjoint (A i) (A j) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro t hti htj
    exact incompatible (hl i j hij) (Finset.mem_filter.mp hti).2
      (Finset.mem_filter.mp htj).2
  have hsub : ∀ i ∈ (Finset.univ : Finset (Fin m)), A i ⊆ B := by
    intro i _ t ht
    have hmem := Finset.mem_filter.mp ht
    apply Finset.mem_erase.mpr
    refine ⟨?_, hmem.1⟩
    intro htk
    subst t
    exact good_rises hmem.2 (not_falls C hf hu k.val k.isLt hk)
  have hc : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      min ((S i).card-1) 2 ≤ (A i).card :=
    fun i _ => owned_base C hf hu (S i) (h2 i) (out i) (he i)
  have hb := sum_card_disjoint_le Finset.univ A
    (fun i => min ((S i).card-1) 2) B hd hsub hc
  have hcard : B.card + 1 = C.gates.length := by
    dsimp [B]
    have := Finset.card_erase_add_one (Finset.mem_range.mpr k.isLt)
    simpa only [Finset.card_range] using this
  omega

theorem sum_lower_when_excess_le_one (n m : ℕ) (S : Fin m → Finset (Fin n))
    (h2 : ∀ i, 2 ≤ (S i).card)
    (hl : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hexcess : (∑ i : Fin m, ((S i).card-3)) ≤ 1)
    (gates : List Gate) (out : Fin m → ℕ)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2)
    (hn : ∃ ι : Fin 1 → Fin gates.length, ∀ i : Fin gates.length,
      (gates.get i).op = GateOp.not → ∃ j : Fin 1, ι j = i)
    (he : ∀ (w : Fin m) (x : Fin n → Bool), Circuit.eval ⟨gates,out w⟩ (List.ofFn x) =
      decide (∃ v ∈ S w, x v = true)) :
    (∑ i : Fin m, ((S i).card-1)) ≤ gates.length := by
  classical
  by_cases hnot : ∃ k : Fin gates.length, (gates.get k).op = GateOp.not
  · let C : Circuit := ⟨gates,0⟩
    have hf : PEqualNP.MetaComplexity.FanInTwo C := hg
    have hu : OnlyOne C := by
      obtain ⟨ι,hι⟩ := hn
      intro i j hi hj
      obtain ⟨a,ha⟩ := hι i hi
      obtain ⟨b,hb⟩ := hι j hj
      have hab : a = b := Subsingleton.elim _ _
      exact ha.symm.trans (hab ▸ hb)
    have hex (i : Fin m) : Exact (S i) (wire C.gates (out i)) := by
      intro x
      change Circuit.eval ⟨gates,out i⟩ (List.ofFn x) = true ↔ hit (S i) x
      rw [he]
      exact decide_eq_true_iff
    obtain ⟨k,hk⟩ := hnot
    have hb := base_plus_not S h2 hl C hf hu out hex k hk
    have hsplit : (∑ i : Fin m, ((S i).card-1)) =
        (∑ i : Fin m, min ((S i).card-1) 2) + (∑ i : Fin m, ((S i).card-3)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have := h2 i
      omega
    change (∑ i : Fin m, ((S i).card-1)) ≤ C.gates.length
    omega
  · apply PEqualNP.Outside.L_meta_951_plus_one_monotone n m S hl gates out _ he
    intro g hmem
    obtain ⟨hop,hlen⟩ := hg g hmem
    refine ⟨?_,hlen⟩
    rcases hop with ha | ho | ht
    · exact Or.inl ha
    · exact Or.inr ho
    · obtain ⟨i,hi,hiG⟩ := List.getElem_of_mem hmem
      exact False.elim (hnot ⟨⟨i,hi⟩, by simpa only [List.get_eq_getElem,hiG] using ht⟩)

end PEqualNP.Outside.L_meta_951_plus_one

namespace PEqualNP.Outside.L_meta_951_consumer

open PEqualNP.Outside.L_meta_951_small

variable {n : ℕ}

def Rises (f : Wire n) := ∀ x y : Input n, (∀ k, x k = true → y k = true) →
  f x = true → f y = true

lemma low_of_rises_outside {S : Finset (Fin n)} {p : Wire n}
    (hp : Rises p) (hz : p (outside S) = false) : Low S p := by
  intro x hx
  by_contra hmiss
  have hle : ∀ v, x v = true → outside S v = true := by
    intro v hv
    exact decide_eq_true (fun hs => hmiss ⟨v,hs,hv⟩)
  have := hp x (outside S) hle hx
  simp [hz] at this

lemma owned_and_consumer {S T : Finset (Fin n)} {u p : Wire n}
    (hst : S = T ∨ (S ∩ T).card ≤ 1)
    (hmono : Rises p) (hp : Good T p)
    (hq : Good S (fun x => u x && p x)) : Good S p := by
  rcases hst with rfl | hst
  · exact hp
  · have lp := low_of_rises_outside hmono hp.2.2
    obtain ⟨_,⟨a,ha,b,hb,hab,hqa,hqb⟩,_⟩ := hq
    have hpa := (Bool.and_eq_true _ _).mp hqa |>.2
    have hpb := (Bool.and_eq_true _ _).mp hqb |>.2
    have haT := (hit_single T a).mp (lp _ hpa)
    have hbT := (hit_single T b).mp (lp _ hpb)
    exact False.elim (hab (Finset.card_le_one.mp hst a
      (Finset.mem_inter.mpr ⟨ha,haT⟩) b (Finset.mem_inter.mpr ⟨hb,hbT⟩)))

lemma owned_or_consumer {S T : Finset (Fin n)} {u p : Wire n}
    (hmono : Rises p) (hp : Good T p)
    (hq : Good S (fun x => u x || p x)) : Good S p := by
  have hz : p (outside S) = false := by
    have := hq.2.2
    simpa only [Bool.or_eq_false_iff] using (Bool.or_eq_false_iff.mp this).2
  have lp := low_of_rises_outside hmono hz
  obtain ⟨a,ha,b,hb,hab,hpa,hpb⟩ := hp.2.1
  exact ⟨Or.inl lp, ⟨a,(hit_single S a).mp (lp _ hpa),
    b,(hit_single S b).mp (lp _ hpb),hab,hpa,hpb⟩,hz⟩

lemma and_consumer_not_exact {S : Finset (Fin n)} {u p : Wire n}
    (hS : 2 ≤ S.card) (hu : u (fun _ => true) = false) :
    ¬ Exact S (fun x => u x && p x) := by
  intro he
  obtain ⟨a,ha,b,hb,hab⟩ := two_points S hS
  have := (he (fun _ => true)).mpr ⟨a,ha,rfl⟩
  simp [hu] at this

lemma or_consumer_not_exact {S : Finset (Fin n)} {u p : Wire n}
    (hu : u (fun _ => false) = true) :
    ¬ Exact S (fun x => u x || p x) := by
  intro he
  have hh := (he (fun _ => false)).mp (by simp [hu])
  simp [hit] at hh

lemma and_consumer_input_not_good {S : Finset (Fin n)} {u : Wire n} (v : Fin n) :
    ¬ Good S (fun x => u x && x v) := by
  rintro ⟨_,⟨a,ha,b,hb,hab,hqa,hqb⟩,_⟩
  have hpa := (Bool.and_eq_true _ _).mp hqa |>.2
  have hpb := (Bool.and_eq_true _ _).mp hqb |>.2
  exact hab ((of_decide_eq_true hpa).symm.trans (of_decide_eq_true hpb))

lemma or_consumer_input_not_good {S : Finset (Fin n)} {u : Wire n} (v : Fin n)
    (hu : Falls u) (hu0 : u (fun _ => false) = true) :
    ¬ Good S (fun x => u x || x v) := by
  rintro ⟨hl | hh,⟨a,ha,b,hb,hab,hqa,hqb⟩,hz⟩
  · have := hl (fun _ => false) (by simp [hu0])
    simp [hit] at this
  · have hzu : u (outside S) = false := (Bool.or_eq_false_iff.mp hz).1
    have hzv : outside S v = false := (Bool.or_eq_false_iff.mp hz).2
    have hvS : v ∈ S := by simpa only [outside,decide_eq_false_iff_not,not_not] using hzv
    obtain ⟨w,hw,hwv⟩ : ∃ w ∈ S, w ≠ v := by
      by_cases hav : a = v
      · exact ⟨b,hb,fun hbv => hab (hav.trans hbv.symm)⟩
      · exact ⟨a,ha,hav⟩
    let x : Input n := fun t => decide (t ∉ S ∨ t = w)
    have hxw : x w = true := by simp [x]
    have hxv : x v = false := by simp [x,hvS,Ne.symm hwv]
    have hxU : u x = false := by
      apply Bool.eq_false_iff.mpr
      intro hux
      have := hu (outside S) x (fun t ht => by
        exact decide_eq_true (Or.inl (of_decide_eq_true ht))) hux
      simp [hzu] at this
    have hq := hh x ⟨w,hw,hxw⟩
    simp [hxU,hxv] at hq

end PEqualNP.Outside.L_meta_951_consumer
