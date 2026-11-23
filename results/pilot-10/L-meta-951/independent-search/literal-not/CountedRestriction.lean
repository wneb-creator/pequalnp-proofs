import Mathlib
import PEqualNP.Defs

namespace Pilot10LiteralNot

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, if_neg hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, Or.inl rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [W_val, if_pos rfl]
      show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, Or.inr rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [W_val, if_pos rfl]
      show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    Rep ([] : List Gate) (fun x => (W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (W [] x).getD t false = (W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩

lemma gate_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)) :
    ∃ new', Ext new new' ∧
      Rep new' (fun x => op.eval (l.map fun i => (W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def At {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) (g : Gate)
    (x : Fin n → Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => (W old (ρ x)).getD i false)

def FreeAt {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) (g : Gate) : Prop :=
  (∃ b : Bool, ∀ x, At ρ old g x = b) ∨
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ i ∈ g.inputs, ∃ b : Bool, ∀ x, (W old (ρ x)).getD i false = b)

lemma rep_and_const {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool)
    (hf : Rep new f) (hg : Rep new g)
    (hc : (∃ b, ∀ x, f x = b) ∨ (∃ b, ∀ x, g x = b)) :
    Rep new (fun x => f x && g x) := by
  rcases hc with ⟨b, hb⟩ | ⟨b, hb⟩
  · cases b
    · exact Or.inl ⟨false, fun x => by simp [hb x]⟩
    · exact rep_congr (fun x => by simp [hb x]) hg
  · cases b
    · exact Or.inl ⟨false, fun x => by simp [hb x]⟩
    · exact rep_congr (fun x => by simp [hb x]) hf

lemma rep_or_const {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool)
    (hf : Rep new f) (hg : Rep new g)
    (hc : (∃ b, ∀ x, f x = b) ∨ (∃ b, ∀ x, g x = b)) :
    Rep new (fun x => f x || g x) := by
  rcases hc with ⟨b, hb⟩ | ⟨b, hb⟩
  · cases b
    · exact rep_congr (fun x => by simp [hb x]) hg
    · exact Or.inl ⟨true, fun x => by simp [hb x]⟩
  · cases b
    · exact rep_congr (fun x => by simp [hb x]) hf
    · exact Or.inl ⟨true, fun x => by simp [hb x]⟩

lemma free_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate) (g : Gate)
    (hlen : g.inputs.length ≤ 2) (hf : FreeAt ρ old g)
    (hrep : ∀ t, Rep new (fun x => (W old (ρ x)).getD t false)) :
    Rep new (At ρ old g) := by
  rcases hf with hc | ⟨hop, i, hi, b, hb⟩
  · exact Or.inl hc
  rcases g with ⟨op, ins⟩
  simp only at hlen hop hi ⊢
  rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩
  · simp at hi
  · rcases hop with rfl | rfl
    · exact rep_congr (fun x => by simp [At, GateOp.eval]) (hrep a)
    · exact rep_congr (fun x => by simp [At, GateOp.eval]) (hrep a)
  · have hc : (∃ b, ∀ x, (W old (ρ x)).getD a false = b) ∨
        (∃ b, ∀ x, (W old (ρ x)).getD c false = b) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact Or.inl ⟨b, hb⟩
      · exact Or.inr ⟨b, hb⟩
    rcases hop with rfl | rfl
    · exact rep_congr (fun x => by simp [At, GateOp.eval])
        (rep_and_const new _ _ (hrep a) (hrep c) hc)
    · exact rep_congr (fun x => by simp [At, GateOp.eval])
        (rep_or_const new _ _ (hrep a) (hrep c) hc)
  · simp only [List.length_cons] at hlen
    omega

def credit (j k t : ℕ) : ℕ := (if j < t then 1 else 0) + (if k < t then 1 else 0)

lemma credit_zero (j k : ℕ) : credit j k 0 = 0 := by simp [credit]

lemma credit_succ (j k t : ℕ) (hne : j ≠ k) :
    credit j k (t + 1) = credit j k t + (if t = j ∨ t = k then 1 else 0) := by
  unfold credit
  split_ifs <;> omega

def SavedInv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (j k : ℕ) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧
    new.length + credit j k old.length ≤ old.length ∧
    ∀ t, Rep new (fun x => (W old (ρ x)).getD t false)

lemma saved_step {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (j k : ℕ) (hne : j ≠ k)
    (old : List Gate) (g : Gate) (hlen : g.inputs.length ≤ 2)
    (ha : FreeAt ρ old g ∨ (g.op = GateOp.and ∨ g.op = GateOp.or))
    (hf : old.length = j ∨ old.length = k → FreeAt ρ old g)
    (hinv : SavedInv ρ j k old) : SavedInv ρ j k (old ++ [g]) := by
  obtain ⟨new, hfan, hlennew, hrep⟩ := hinv
  have choice : ∃ new', Ext new new' ∧ Rep new' (At ρ old g) ∧
      (old.length = j ∨ old.length = k → new' = new) := by
    by_cases hevent : old.length = j ∨ old.length = k
    · exact ⟨new, Or.inl rfl, free_rep ρ old new g hlen (hf hevent) hrep, fun _ => rfl⟩
    · rcases ha with hfree | hmono
      · exact ⟨new, Or.inl rfl, free_rep ρ old new g hlen hfree hrep, fun _ => rfl⟩
      · obtain ⟨new', he, hr⟩ := gate_rep ρ old new g.op g.inputs hmono hlen hrep
        exact ⟨new', he, hr, fun h => (hevent h).elim⟩
  obtain ⟨new', he, hr, hsame⟩ := choice
  refine ⟨new', ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨a, rfl, hfa⟩
    · exact hfan
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hfan a ha
      · rw [List.mem_singleton] at ha
        simpa [ha] using hfa
  · rw [List.length_append, List.length_singleton, credit_succ j k old.length hne]
    by_cases hevent : old.length = j ∨ old.length = k
    · rw [if_pos hevent, hsame hevent]
      omega
    · rw [if_neg hevent]
      rcases he with rfl | ⟨a, rfl, _⟩
      · omega
      · simp only [List.length_append, List.length_singleton]
        omega
  · intro t
    by_cases ht : t = n + old.length
    · apply rep_congr (fun x => ?_) hr
      show At ρ old g x = (W (old ++ [g]) (ρ x)).getD t false
      rw [W_val, if_pos ht]
      rfl
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_neg ht]) (rep_mono he _ (hrep t))

theorem counted_restriction {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ b : Bool, ∀ x, ρ x i = b) ∨ (∀ x, ρ x i = x i))
    (gates : List Gate) (j k : ℕ) (hne : j ≠ k) (hj : j < gates.length) (hk : k < gates.length)
    (hlen : ∀ g ∈ gates, g.inputs.length ≤ 2)
    (ha : ∀ pre g post, pre ++ g :: post = gates →
      FreeAt ρ pre g ∨ (g.op = GateOp.and ∨ g.op = GateOp.or))
    (hf : ∀ pre g post, pre ++ g :: post = gates →
      pre.length = j ∨ pre.length = k → FreeAt ρ pre g) :
    ∃ (new : List Gate) (r : ℕ → ℕ),
      (∀ g ∈ new, Fan g) ∧ new.length + 2 ≤ gates.length ∧
      ∀ o, (∃ x y : Fin n → Bool, (W gates (ρ x)).getD o false ≠
        (W gates (ρ y)).getD o false) →
        ∀ x, (W new x).getD (r o) false = (W gates (ρ x)).getD o false := by
  have hall : ∀ post pre : List Gate, pre ++ post = gates →
      SavedInv ρ j k pre → SavedInv ρ j k gates := by
    intro post
    induction post with
    | nil =>
      intro pre hp hi
      rw [List.append_nil] at hp
      rw [← hp]
      exact hi
    | cons g post ih =>
      intro pre hp hi
      have hmem : g ∈ gates := by rw [← hp]; simp
      exact ih (pre ++ [g]) (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hp)
        (saved_step ρ j k hne pre g (hlen g hmem) (ha pre g post hp)
          (hf pre g post hp) hi)
  have hi : SavedInv ρ j k [] :=
    ⟨[], by simp, by simp [credit_zero], rep_input ρ hρ⟩
  obtain ⟨new, hfan, hs, hrep⟩ := hall gates [] (by simp) hi
  have hsel : ∀ o, ∃ r,
      (∃ b : Bool, ∀ x, (W gates (ρ x)).getD o false = b) ∨
      (∀ x, (W new x).getD r false = (W gates (ρ x)).getD o false) := by
    intro o
    rcases hrep o with hc | ⟨r, _, hr⟩
    · exact ⟨0, Or.inl hc⟩
    · exact ⟨r, Or.inr hr⟩
  choose r hr using hsel
  refine ⟨new, r, hfan, ?_, ?_⟩
  · simpa [credit, hj, hk] using hs
  · intro o hnon x
    rcases hr o with ⟨b, hb⟩ | hw
    · obtain ⟨a, b, hab⟩ := hnon
      exact (hab ((hb a).trans (hb b).symm)).elim
    · exact hw x

lemma W_input {n : ℕ} (gates : List Gate) (x : Fin n → Bool) (v : Fin n) :
    (W gates x).getD v.val false = x v := by
  induction gates using List.reverseRecOn with
  | nil =>
    change (List.ofFn x).getD v.val false = x v
    rw [List.getD_eq_getElem _ _ (by simpa using v.isLt)]
    simp
  | append_singleton pre g ih =>
    rw [W_val, if_neg (by have := v.isLt; omega)]
    exact ih

lemma W_prefix {n : ℕ} (pre post : List Gate) (x : Fin n → Bool) (i : ℕ)
    (hi : i < n + pre.length) :
    (W (pre ++ post) x).getD i false = (W pre x).getD i false := by
  induction post using List.reverseRecOn with
  | nil => simp
  | append_singleton post g ih =>
    rw [← List.append_assoc, W_val, if_neg (by simp only [List.length_append]; omega)]
    exact ih

lemma no_consumer_independent {n : ℕ} (gates : List Gate) (x y : Fin n → Bool)
    (v : Fin n) (k : ℕ) (hxy : ∀ i : Fin n, i ≠ v → x i = y i)
    (ha : ∀ pre g post, pre ++ g :: post = gates → pre.length ≠ k →
      ∀ i ∈ g.inputs, i ≠ v.val ∧ i ≠ n + k) :
    ∀ t, t ≠ v.val → t ≠ n + k →
      (W gates x).getD t false = (W gates y).getD t false := by
  have hall : ∀ post pre : List Gate, pre ++ post = gates →
      (∀ t, t ≠ v.val → t ≠ n + k → (W pre x).getD t false = (W pre y).getD t false) →
      ∀ t, t ≠ v.val → t ≠ n + k →
        (W gates x).getD t false = (W gates y).getD t false := by
    intro post
    induction post with
    | nil =>
      intro pre hp heq
      rw [List.append_nil] at hp
      rw [← hp]
      exact heq
    | cons g post ih =>
      intro pre hp heq
      apply ih (pre ++ [g]) (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hp)
      intro t htv htk
      rw [W_val, W_val]
      split_ifs with ht
      · have hpk : pre.length ≠ k := by omega
        apply congrArg g.op.eval
        apply List.map_congr_left
        intro i hi
        exact heq i (ha pre g post hp hpk i hi).1 (ha pre g post hp hpk i hi).2
      · exact heq t htv htk
  apply hall gates [] (by simp)
  intro t htv _
  by_cases ht : t < n
  · have hfin : (⟨t, ht⟩ : Fin n) ≠ v := by
      intro he
      exact htv (congrArg Fin.val he)
    rw [W_input [] x ⟨t, ht⟩, W_input [] y ⟨t, ht⟩]
    exact hxy ⟨t, ht⟩ hfin
  · rw [List.getD_eq_default _ _ (by rw [W_len]; simp; omega),
        List.getD_eq_default _ _ (by rw [W_len]; simp; omega)]

theorem dependent_requires_consumer {n : ℕ} (gates : List Gate) (x y : Fin n → Bool)
    (v : Fin n) (k o : ℕ) (hxy : ∀ i : Fin n, i ≠ v → x i = y i)
    (hov : o ≠ v.val) (hok : o ≠ n + k)
    (hdep : (W gates x).getD o false ≠ (W gates y).getD o false) :
    ∃ pre g post, pre ++ g :: post = gates ∧ pre.length ≠ k ∧
      (v.val ∈ g.inputs ∨ n + k ∈ g.inputs) := by
  classical
  by_contra hn
  have ha : ∀ pre g post, pre ++ g :: post = gates → pre.length ≠ k →
      ∀ i ∈ g.inputs, i ≠ v.val ∧ i ≠ n + k := by
    intro pre g post hp hk i hi
    constructor
    · intro he
      subst i
      exact hn ⟨pre, g, post, hp, hk, Or.inl hi⟩
    · intro he
      subst i
      exact hn ⟨pre, g, post, hp, hk, Or.inr hi⟩
  exact hdep (no_consumer_independent gates x y v k hxy ha o hov hok)

lemma literal_not_value {n : ℕ} (pre post : List Gate) (g : Gate) (v : Fin n)
    (hop : g.op = GateOp.not) (hhead : g.inputs.head? = some v.val) (x : Fin n → Bool) :
    (W (pre ++ g :: post) x).getD (n + pre.length) false = !(x v) := by
  have heq : pre ++ g :: post = (pre ++ [g]) ++ post := by simp
  rw [heq, W_prefix _ _ _ _ (by simp only [List.length_append, List.length_singleton]; omega),
    W_val, if_pos rfl]
  obtain ⟨rest, hr⟩ : ∃ rest, g.inputs = v.val :: rest := by
    cases h : g.inputs with
    | nil => simp [h] at hhead
    | cons a rest =>
      simp [h] at hhead
      exact ⟨rest, by simpa [hhead] using h⟩
  rw [hop, hr]
  change Bool.not ((W pre x).getD v.val false) = Bool.not (x v)
  rw [W_input]

theorem exact_sum_requires_consumer {n : ℕ} (pre post : List Gate) (g : Gate) (v : Fin n)
    (hop : g.op = GateOp.not) (hhead : g.inputs.head? = some v.val)
    (S : Finset (Fin n)) (hv : v ∈ S) (hcard : 2 ≤ S.card) (o : ℕ)
    (hout : ∀ x : Fin n → Bool,
      (W (pre ++ g :: post) x).getD o false = decide (∃ i ∈ S, x i = true)) :
    ∃ pre' g' post', pre' ++ g' :: post' = pre ++ g :: post ∧ pre'.length ≠ pre.length ∧
      (v.val ∈ g'.inputs ∨ n + pre.length ∈ g'.inputs) := by
  classical
  have hov : o ≠ v.val := by
    intro he
    have hex : ∃ u ∈ S, u ≠ v := by
      by_contra hn
      push_neg at hn
      have hsub : S ⊆ {v} := by intro u hu; simpa using hn u hu
      have := Finset.card_le_card hsub
      simp only [Finset.card_singleton] at this
      omega
    obtain ⟨u, hu, huv⟩ := hex
    have hx := hout (fun i => decide (i = u))
    rw [he, W_input] at hx
    have ht : decide (∃ i ∈ S, decide (i = u) = true) = true :=
      decide_eq_true ⟨u, hu, by simp⟩
    have hf : decide (v = u) = false := decide_eq_false (Ne.symm huv)
    rw [hf, ht] at hx
    contradiction
  have hok : o ≠ n + pre.length := by
    intro he
    have hz := hout (fun _ => false)
    rw [he, literal_not_value pre post g v hop hhead] at hz
    simp at hz
  apply dependent_requires_consumer (pre ++ g :: post) (fun _ => false)
    (fun i => decide (i = v)) v pre.length o
  · intro i hi
    simp [hi]
  · exact hov
  · exact hok
  · rw [hout, hout]
    have ht : decide (∃ i ∈ S, decide (i = v) = true) = true :=
      decide_eq_true ⟨v, hv, by simp⟩
    rw [ht]
    simp

lemma head_eq_of_decomp (pre₁ pre₂ post₁ post₂ : List Gate) (g₁ g₂ : Gate)
    (he : pre₁ ++ g₁ :: post₁ = pre₂ ++ g₂ :: post₂) (hl : pre₁.length = pre₂.length) :
    g₁ = g₂ := by
  have h₁ : (pre₁ ++ g₁ :: post₁).drop pre₂.length = g₁ :: post₁ := by rw [← hl]; simp
  have h₂ : (pre₂ ++ g₂ :: post₂).drop pre₂.length = g₂ :: post₂ := by simp
  exact (List.cons.inj (h₁.symm.trans ((congrArg (List.drop pre₂.length) he).trans h₂))).1

theorem literal_not_two_savings {n : ℕ} (pre post : List Gate) (g : Gate) (v : Fin n)
    (hop : g.op = GateOp.not) (hhead : g.inputs.head? = some v.val)
    (hlen : ∀ a ∈ pre ++ g :: post, a.inputs.length ≤ 2)
    (hmono : ∀ p a s, p ++ a :: s = pre ++ g :: post → p.length ≠ pre.length →
      a.op = GateOp.and ∨ a.op = GateOp.or)
    (S : Finset (Fin n)) (hv : v ∈ S) (hcard : 2 ≤ S.card) (o : ℕ)
    (hout : ∀ x : Fin n → Bool,
      (W (pre ++ g :: post) x).getD o false = decide (∃ i ∈ S, x i = true)) :
    ∃ (new : List Gate) (r : ℕ → ℕ), (∀ a ∈ new, Fan a) ∧
      new.length + 2 ≤ (pre ++ g :: post).length ∧
      ∀ o', (∃ x y : Fin n → Bool,
        (W (pre ++ g :: post) (fun i => if i = v then false else x i)).getD o' false ≠
        (W (pre ++ g :: post) (fun i => if i = v then false else y i)).getD o' false) →
        ∀ x, (W new x).getD (r o') false =
          (W (pre ++ g :: post) (fun i => if i = v then false else x i)).getD o' false := by
  classical
  let ρ : (Fin n → Bool) → Fin n → Bool := fun x i => if i = v then false else x i
  obtain ⟨pc, gc, sc, hc, hck, hread⟩ :=
    exact_sum_requires_consumer pre post g v hop hhead S hv hcard o hout
  have free_not : ∀ p a s, p ++ a :: s = pre ++ g :: post → p.length = pre.length →
      FreeAt ρ p a := by
    intro p a s hp hl
    have hag : a = g := head_eq_of_decomp p pre s post a g hp hl
    subst a
    left
    refine ⟨true, ?_⟩
    intro x
    obtain ⟨rest, hr⟩ : ∃ rest, g.inputs = v.val :: rest := by
      cases h : g.inputs with
      | nil => simp [h] at hhead
      | cons a rest =>
        simp [h] at hhead
        exact ⟨rest, by simpa [hhead] using h⟩
    unfold At
    rw [hop, hr]
    change Bool.not ((W p (ρ x)).getD v.val false) = true
    rw [W_input]
    simp [ρ]
  have free_consumer : ∀ p a s, p ++ a :: s = pre ++ g :: post → p.length = pc.length →
      FreeAt ρ p a := by
    intro p a s hp hl
    have hag : a = gc := head_eq_of_decomp p pc s sc a gc (hp.trans hc.symm) hl
    have hpk : p.length ≠ pre.length := by omega
    refine Or.inr ⟨hmono p a s hp hpk, ?_⟩
    rcases hread with hinput | hnotwire
    · refine ⟨v.val, by simpa [hag] using hinput, false, ?_⟩
      intro x
      rw [W_input]
      simp [ρ]
    · refine ⟨n + pre.length, by simpa [hag] using hnotwire, ?_⟩
      by_cases hbefore : p.length < pre.length
      · refine ⟨false, ?_⟩
        intro x
        exact List.getD_eq_default _ _ (by rw [W_len]; omega)
      · refine ⟨true, ?_⟩
        intro x
        have hprior : (W (p ++ a :: s) (ρ x)).getD (n + pre.length) false =
            (W p (ρ x)).getD (n + pre.length) false :=
          W_prefix p (a :: s) (ρ x) _ (by omega)
        rw [hp, literal_not_value pre post g v hop hhead] at hprior
        simpa [ρ] using hprior.symm
  have hρ : ∀ i : Fin n, (∃ b : Bool, ∀ x, ρ x i = b) ∨ (∀ x, ρ x i = x i) := by
    intro i
    by_cases hi : i = v
    · exact Or.inl ⟨false, fun x => by simp [ρ, hi]⟩
    · exact Or.inr (fun x => by simp [ρ, hi])
  apply counted_restriction ρ hρ (pre ++ g :: post) pc.length pre.length hck
  · rw [← hc]
    simp only [List.length_append, List.length_cons]
    omega
  · simp only [List.length_append, List.length_cons]
    omega
  · exact hlen
  · intro p a s hp
    by_cases hl : p.length = pre.length
    · exact Or.inl (free_not p a s hp hl)
    · exact Or.inr (hmono p a s hp hl)
  · intro p a s hp hf
    rcases hf with hf | hf
    · exact free_consumer p a s hp hf
    · exact free_not p a s hp hf
end Pilot10LiteralNot

