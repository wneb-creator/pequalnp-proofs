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


def witnessGates : List Gate :=
  [⟨GateOp.or, [4,0]⟩, ⟨GateOp.or, [5,1]⟩, ⟨GateOp.or, [6,2]⟩,
   ⟨GateOp.or, [7,3]⟩, ⟨GateOp.not, [4]⟩, ⟨GateOp.and, [8,9]⟩,
   ⟨GateOp.and, [4,0]⟩, ⟨GateOp.and, [4,1]⟩, ⟨GateOp.and, [4,2]⟩,
   ⟨GateOp.and, [4,3]⟩, ⟨GateOp.or, [11,12]⟩, ⟨GateOp.or, [15,13]⟩,
   ⟨GateOp.or, [16,14]⟩, ⟨GateOp.or, [10,17]⟩]

def witnessS : Finset (Fin 5) := {0,1,2,3}

set_option maxHeartbeats 2000000 in
lemma witness_exact : Exact witnessS (wire witnessGates 18) := by
  unfold Exact hit
  decide

set_option maxHeartbeats 2000000 in
lemma witness_good : ∀ k : Fin 14,
    Good witnessS (wire witnessGates (5+k.val)) ↔ k.val = 5 ∨ k.val = 13 := by
  unfold Good Low High hit
  decide

end PEqualNP.Outside.L_meta_951_small
