import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5160

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wf_append (pre post : List Gate) (w : List Bool) :
    wf (pre ++ post) w = wf post (wf pre w) := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

theorem legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

def sk (N i : ℕ) : ℕ := if i < N then i else i - 1

def rn (N a i : ℕ) : ℕ := if i < N then i else if i = N then a else i - 1

theorem sk_lt (N M i : ℕ) (hN0 : 0 < N) (hM : N ≤ M) (hi : i < M + 1) : sk N i < M := by
  unfold sk
  split_ifs <;> omega

theorem getD_mid (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) :
    (A ++ b :: E).getD N false = b := by
  subst hN
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl A.length),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

theorem getD_sk (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (i : ℕ) (hi : i ≠ N) :
    (A ++ E).getD (sk N i) false = (A ++ b :: E).getD i false := by
  subst hN
  unfold sk
  by_cases h : i < A.length
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [if_neg h]
    have h1 : A.length ≤ i - 1 := by omega
    have h2 : A.length ≤ i := by omega
    have h3 : i - A.length = (i - 1 - A.length) + 1 := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
      List.getElem?_append_right h2]
    rw [h3, List.getElem?_cons_succ]

theorem getD_rn (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (a : ℕ) (ha : a < N)
    (hb : A.getD a false = b) (i : ℕ) :
    (A ++ E).getD (rn N a i) false = (A ++ b :: E).getD i false := by
  by_cases h : i = N
  · have e : rn N a N = a := by
      unfold rn
      rw [if_neg (lt_irrefl _), if_pos rfl]
    have ha' : a < A.length := by omega
    rw [h, getD_mid A E b N hN, e, ← hb]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left ha']
  · have e : rn N a i = sk N i := by
      unfold rn sk
      by_cases h' : i < N
      · rw [if_pos h', if_pos h']
      · rw [if_neg h', if_neg h, if_neg h']
    rw [e]
    exact getD_sk A E b N hN i h

theorem surg (T : Gate → Gate) (A : List Bool) (b : Bool) :
    ∀ (post : List Gate) (E : List Bool),
      (∀ h ∈ post, ∀ E' : List Bool,
        h.op.eval (h.inputs.map fun i => (A ++ b :: E').getD i false)
          = (T h).op.eval ((T h).inputs.map fun i => (A ++ E').getD i false)) →
      ∃ E2 : List Bool, wf post (A ++ b :: E) = A ++ b :: E2 ∧
        wf (post.map T) (A ++ E) = A ++ E2 := by
  intro post
  induction post with
  | nil => intro E _; exact ⟨E, rfl, rfl⟩
  | cons h post ih =>
    intro E hT
    have e := hT h (List.mem_cons.mpr (Or.inl rfl)) E
    obtain ⟨E2, h1, h2⟩ :=
      ih (E ++ [h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)])
        (fun h' hh' E' => hT h' (List.mem_cons.mpr (Or.inr hh')) E')
    refine ⟨E2, ?_, ?_⟩
    · rw [wf_cons, List.append_assoc, List.cons_append]
      exact h1
    · rw [List.map_cons, wf_cons, ← e, List.append_assoc]
      exact h2

theorem ev (pre post : List Gate) (g : Gate) (T : Gate → Gate) (x : List Bool) (b : Bool)
    (hb : g.op.eval (g.inputs.map fun i => (wf pre x).getD i false) = b)
    (hT : ∀ h ∈ post, ∀ E' : List Bool,
        h.op.eval (h.inputs.map fun i => (wf pre x ++ b :: E').getD i false)
          = (T h).op.eval ((T h).inputs.map fun i => (wf pre x ++ E').getD i false)) :
    ∃ E2 : List Bool, wf (pre ++ g :: post) x = wf pre x ++ b :: E2 ∧
      wf (pre ++ post.map T) x = wf pre x ++ E2 := by
  obtain ⟨E2, h1, h2⟩ := surg T (wf pre x) b post [] hT
  rw [List.append_nil] at h2
  refine ⟨E2, ?_, ?_⟩
  · rw [wf_append, wf_cons, hb]
    exact h1
  · rw [wf_append]
    exact h2

def Tc (N a : ℕ) (h : Gate) : Gate := ⟨h.op, h.inputs.map (rn N a)⟩

def Tt (N : ℕ) (h : Gate) : Gate :=
  match h.op with
  | GateOp.and => ⟨GateOp.and, (h.inputs.filter (fun i => decide (i ≠ N))).map (sk N)⟩
  | _ => if N ∈ h.inputs then ⟨GateOp.and, []⟩ else ⟨h.op, h.inputs.map (sk N)⟩

def Tf (N : ℕ) (h : Gate) : Gate :=
  match h.op with
  | GateOp.or => ⟨GateOp.or, (h.inputs.filter (fun i => decide (i ≠ N))).map (sk N)⟩
  | _ => if N ∈ h.inputs then ⟨GateOp.or, []⟩ else ⟨h.op, h.inputs.map (sk N)⟩

theorem Tt_and (N : ℕ) (ins : List ℕ) : Tt N ⟨GateOp.and, ins⟩
    = ⟨GateOp.and, (ins.filter (fun i => decide (i ≠ N))).map (sk N)⟩ := rfl

theorem Tt_or (N : ℕ) (ins : List ℕ) : Tt N ⟨GateOp.or, ins⟩
    = if N ∈ ins then ⟨GateOp.and, []⟩ else ⟨GateOp.or, ins.map (sk N)⟩ := rfl

theorem Tf_or (N : ℕ) (ins : List ℕ) : Tf N ⟨GateOp.or, ins⟩
    = ⟨GateOp.or, (ins.filter (fun i => decide (i ≠ N))).map (sk N)⟩ := rfl

theorem Tf_and (N : ℕ) (ins : List ℕ) : Tf N ⟨GateOp.and, ins⟩
    = if N ∈ ins then ⟨GateOp.or, []⟩ else ⟨GateOp.and, ins.map (sk N)⟩ := rfl

theorem map_sk (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (ins : List ℕ)
    (hni : N ∉ ins) :
    (ins.map (sk N)).map (fun i => (A ++ E).getD i false)
      = ins.map (fun i => (A ++ b :: E).getD i false) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  exact getD_sk A E b N hN i (fun e => hni (by rw [← e]; exact hi))

theorem all_drop (f : ℕ → Bool) (N : ℕ) (hf : f N = true) : ∀ ins : List ℕ,
    (ins.map f).all id = ((ins.filter (fun i => decide (i ≠ N))).map f).all id := by
  intro ins
  induction ins with
  | nil => rfl
  | cons i rest ih =>
    by_cases h : i = N
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_neg (by simp [h])
      rw [e, ← ih, List.map_cons, List.all_cons, h]
      simp [hf]
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = i :: rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_pos (by simpa using h)
      rw [e]
      simp only [List.map_cons, List.all_cons, ih]

theorem any_drop (f : ℕ → Bool) (N : ℕ) (hf : f N = false) : ∀ ins : List ℕ,
    (ins.map f).any id = ((ins.filter (fun i => decide (i ≠ N))).map f).any id := by
  intro ins
  induction ins with
  | nil => rfl
  | cons i rest ih =>
    by_cases h : i = N
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_neg (by simp [h])
      rw [e, ← ih, List.map_cons, List.any_cons, h]
      simp [hf]
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = i :: rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_pos (by simpa using h)
      rw [e]
      simp only [List.map_cons, List.any_cons, ih]

theorem sound_c (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (a : ℕ) (ha : a < N)
    (hb : A.getD a false = b) (h : Gate) :
    h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)
      = (Tc N a h).op.eval ((Tc N a h).inputs.map fun i => (A ++ E).getD i false) := by
  have e : (h.inputs.map (rn N a)).map (fun i => (A ++ E).getD i false)
      = h.inputs.map fun i => (A ++ b :: E).getD i false := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact getD_rn A E b N hN a ha hb i
  show h.op.eval _ = h.op.eval ((h.inputs.map (rn N a)).map fun i => (A ++ E).getD i false)
  rw [e]

theorem sound_t (A E : List Bool) (N : ℕ) (hN : A.length = N) (h : Gate)
    (hop : h.op = GateOp.and ∨ h.op = GateOp.or) :
    h.op.eval (h.inputs.map fun i => (A ++ true :: E).getD i false)
      = (Tt N h).op.eval ((Tt N h).inputs.map fun i => (A ++ E).getD i false) := by
  obtain ⟨op, ins⟩ := h
  have hf : (A ++ true :: E).getD N false = true := getD_mid A E true N hN
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tt_and]
    show (ins.map fun i => (A ++ true :: E).getD i false).all id
      = (((ins.filter (fun i => decide (i ≠ N))).map (sk N)).map
          fun i => (A ++ E).getD i false).all id
    rw [map_sk A E true N hN (ins.filter (fun i => decide (i ≠ N))) (by simp)]
    exact all_drop _ N hf ins
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tt_or]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      show (ins.map fun i => (A ++ true :: E).getD i false).any id = true
      exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨N, hm, rfl⟩, hf⟩
    · rw [if_neg hm]
      show (ins.map fun i => (A ++ true :: E).getD i false).any id
        = ((ins.map (sk N)).map fun i => (A ++ E).getD i false).any id
      rw [map_sk A E true N hN ins hm]

theorem sound_f (A E : List Bool) (N : ℕ) (hN : A.length = N) (h : Gate)
    (hop : h.op = GateOp.and ∨ h.op = GateOp.or) :
    h.op.eval (h.inputs.map fun i => (A ++ false :: E).getD i false)
      = (Tf N h).op.eval ((Tf N h).inputs.map fun i => (A ++ E).getD i false) := by
  obtain ⟨op, ins⟩ := h
  have hf : (A ++ false :: E).getD N false = false := getD_mid A E false N hN
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tf_and]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      show (ins.map fun i => (A ++ false :: E).getD i false).all id = false
      cases hall : (ins.map fun i => (A ++ false :: E).getD i false).all id with
      | false => rfl
      | true =>
        have t := List.all_eq_true.mp hall _ (List.mem_map.mpr ⟨N, hm, rfl⟩)
        have t2 : (A ++ false :: E).getD N false = true := t
        rw [hf] at t2
        exact Bool.noConfusion t2
    · rw [if_neg hm]
      show (ins.map fun i => (A ++ false :: E).getD i false).all id
        = ((ins.map (sk N)).map fun i => (A ++ E).getD i false).all id
      rw [map_sk A E false N hN ins hm]
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tf_or]
    show (ins.map fun i => (A ++ false :: E).getD i false).any id
      = (((ins.filter (fun i => decide (i ≠ N))).map (sk N)).map
          fun i => (A ++ E).getD i false).any id
    rw [map_sk A E false N hN (ins.filter (fun i => decide (i ≠ N))) (by simp)]
    exact any_drop _ N hf ins

theorem Tc_legal (N a : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tc N a h).op = GateOp.and ∨ (Tc N a h).op = GateOp.or) ∧ (Tc N a h).inputs.length ≤ 2 := by
  refine ⟨hl.1, ?_⟩
  show (h.inputs.map (rn N a)).length ≤ 2
  rw [List.length_map]
  exact hl.2

theorem Tc_rb (N a : ℕ) (ha : a < N) (h : Gate) (M : ℕ) (hM : N ≤ M)
    (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tc N a h).inputs, i < M := by
  intro i hi'
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
  have := hi j hj
  unfold rn
  split_ifs <;> omega

theorem Tt_legal (N : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tt N h).op = GateOp.and ∨ (Tt N h).op = GateOp.or) ∧ (Tt N h).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := h
  obtain ⟨hop, hlen⟩ := hl
  have hlen' : ins.length ≤ 2 := hlen
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tt_and]
    refine ⟨Or.inl rfl, ?_⟩
    show ((ins.filter (fun i => decide (i ≠ N))).map (sk N)).length ≤ 2
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) hlen'
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tt_or]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      exact ⟨Or.inl rfl, Nat.zero_le 2⟩
    · rw [if_neg hm]
      refine ⟨Or.inr rfl, ?_⟩
      show (ins.map (sk N)).length ≤ 2
      rw [List.length_map]
      exact hlen'

theorem Tf_legal (N : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tf N h).op = GateOp.and ∨ (Tf N h).op = GateOp.or) ∧ (Tf N h).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := h
  obtain ⟨hop, hlen⟩ := hl
  have hlen' : ins.length ≤ 2 := hlen
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tf_and]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      exact ⟨Or.inr rfl, Nat.zero_le 2⟩
    · rw [if_neg hm]
      refine ⟨Or.inl rfl, ?_⟩
      show (ins.map (sk N)).length ≤ 2
      rw [List.length_map]
      exact hlen'
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tf_or]
    refine ⟨Or.inr rfl, ?_⟩
    show ((ins.filter (fun i => decide (i ≠ N))).map (sk N)).length ≤ 2
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) hlen'

theorem Tt_rb (N : ℕ) (hN0 : 0 < N) (h : Gate) (hop : h.op = GateOp.and ∨ h.op = GateOp.or)
    (M : ℕ) (hM : N ≤ M) (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tt N h).inputs, i < M := by
  obtain ⟨op, ins⟩ := h
  have hi2 : ∀ i ∈ ins, i < M + 1 := hi
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tt_and]
    intro i hi'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
    exact sk_lt N M j hN0 hM (hi2 j (List.mem_filter.mp hj).1)
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tt_or]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      intro i hi'
      exact absurd hi' List.not_mem_nil
    · rw [if_neg hm]
      intro i hi'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
      exact sk_lt N M j hN0 hM (hi2 j hj)

theorem Tf_rb (N : ℕ) (hN0 : 0 < N) (h : Gate) (hop : h.op = GateOp.and ∨ h.op = GateOp.or)
    (M : ℕ) (hM : N ≤ M) (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tf N h).inputs, i < M := by
  obtain ⟨op, ins⟩ := h
  have hi2 : ∀ i ∈ ins, i < M + 1 := hi
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tf_and]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      intro i hi'
      exact absurd hi' List.not_mem_nil
    · rw [if_neg hm]
      intro i hi'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
      exact sk_lt N M j hN0 hM (hi2 j hj)
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tf_or]
    intro i hi'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
    exact sk_lt N M j hN0 hM (hi2 j (List.mem_filter.mp hj).1)

theorem assemble (C : Circuit) (pre post : List Gate) (g : Gate)
    (hC : C.gates = pre ++ g :: post) (T : Gate → Gate) (o' : ℕ)
    (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hTm : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ((T h).op = GateOp.and ∨ (T h).op = GateOp.or) ∧ (T h).inputs.length ≤ 2)
    (hTr : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ∀ M : ℕ, 26 + pre.length ≤ M → (∀ i ∈ h.inputs, i < M + 1) → ∀ i ∈ (T h).inputs, i < M)
    (hev : ∀ x : List Bool, x.length = 26 →
      Circuit.eval ⟨pre ++ post.map T, o'⟩ x = C.eval x) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
  have legal := legal_of C hmono
  refine ⟨⟨pre ++ post.map T, o'⟩, ?_, ?_, hev, ?_⟩
  · intro g' hg'
    have hg2 : g' ∈ pre ∨ g' ∈ post.map T := List.mem_append.mp hg'
    rcases hg2 with hp | hp
    · exact hmono g' (by rw [hC]; exact List.mem_append.mpr (Or.inl hp))
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      have hl := hTm h (legal h (by
        rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hh)))))
      refine ⟨?_, hl.2⟩
      rcases hl.1 with e | e
      · exact Or.inl e
      · exact Or.inr e
  · intro j hj i hi
    have hj' : j < pre.length + post.length := by simpa using hj
    by_cases hjp : j < pre.length
    · have e : gateAt ⟨pre ++ post.map T, o'⟩ j = gateAt C j := by
        simp only [gateAt, hC, List.getD_eq_getElem?_getD, List.getElem?_append_left hjp]
      rw [e] at hi
      exact hrb j (by rw [hC]; simp only [List.length_append, List.length_cons]; omega) i hi
    · have hjk : j - pre.length < post.length := by omega
      have e1 : gateAt ⟨pre ++ post.map T, o'⟩ j = T (post[j - pre.length]) := by
        simp [gateAt, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_of_not_lt hjp), hjk]
      have e2 : gateAt C (j + 1) = post[j - pre.length] := by
        have h3 : j + 1 - pre.length = (j - pre.length) + 1 := by omega
        simp [gateAt, hC, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (show pre.length ≤ j + 1 by omega), h3, hjk]
      rw [e1] at hi
      have hmem : post[j - pre.length] ∈ C.gates := by
        rw [hC]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.getElem_mem hjk))))
      have hold : ∀ i ∈ (post[j - pre.length]).inputs, i < (26 + j) + 1 := by
        intro i hi2
        have := hrb (j + 1) (by rw [hC]; simp only [List.length_append, List.length_cons]; omega)
          i (by rw [e2]; exact hi2)
        omega
      exact hTr _ (legal _ hmem) (26 + j) (by omega) hold i hi
  · show (pre ++ post.map T).length < C.gates.length
    rw [hC]
    simp

theorem copy_case (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (pre post : List Gate) (g : Gate) (hC : C.gates = pre ++ g :: post) (a : ℕ)
    (ha : a < 26 + pre.length)
    (hb : ∀ A : List Bool, g.op.eval (g.inputs.map fun i => A.getD i false) = A.getD a false) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
  apply assemble C pre post g hC (Tc (26 + pre.length) a) (rn (26 + pre.length) a C.output)
    hmono hrb
  · intro h hl
    exact Tc_legal _ _ h hl
  · intro h _ M hM hi
    exact Tc_rb _ _ ha h M hM hi
  · intro x hx
    have hlen : (wf pre x).length = 26 + pre.length := by rw [wf_len, hx]
    obtain ⟨E2, h1, h2⟩ := ev pre post g (Tc (26 + pre.length) a) x _ (hb (wf pre x))
      (fun h _ E' => sound_c (wf pre x) E' _ (26 + pre.length) hlen a ha rfl h)
    show (wf (pre ++ post.map (Tc (26 + pre.length) a)) x).getD
        (rn (26 + pre.length) a C.output) false = (wf C.gates x).getD C.output false
    rw [h2, hC, h1]
    exact getD_rn (wf pre x) E2 _ (26 + pre.length) hlen a ha rfl C.output

theorem const_case (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (pre post : List Gate) (g : Gate) (hC : C.gates = pre ++ g :: post) (T : Gate → Gate)
    (b : Bool)
    (hb : ∀ A : List Bool, g.op.eval (g.inputs.map fun i => A.getD i false) = b)
    (hTm : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ((T h).op = GateOp.and ∨ (T h).op = GateOp.or) ∧ (T h).inputs.length ≤ 2)
    (hTr : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ∀ M : ℕ, 26 + pre.length ≤ M → (∀ i ∈ h.inputs, i < M + 1) → ∀ i ∈ (T h).inputs, i < M)
    (hs : ∀ h : Gate, (h.op = GateOp.and ∨ h.op = GateOp.or) → ∀ (A E : List Bool),
      A.length = 26 + pre.length →
      h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)
        = (T h).op.eval ((T h).inputs.map fun i => (A ++ E).getD i false))
    (hne : ∃ x y : List Bool, x.length = 26 ∧ y.length = 26 ∧ C.eval x = true ∧
      C.eval y = false) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
  have legal := legal_of C hmono
  have key : ∀ x : List Bool, x.length = 26 → ∃ E2 : List Bool,
      wf C.gates x = wf pre x ++ b :: E2 ∧ wf (pre ++ post.map T) x = wf pre x ++ E2 := by
    intro x hx
    have hlen : (wf pre x).length = 26 + pre.length := by rw [wf_len, hx]
    have hpost : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or := by
      intro h hh
      exact (legal h (by
        rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hh))))).1
    rw [hC]
    exact ev pre post g T x b (hb (wf pre x))
      (fun h hh E' => hs h (hpost h hh) (wf pre x) E' hlen)
  have hout : C.output ≠ 26 + pre.length := by
    intro ho
    obtain ⟨x, y, hx, hy, ex, ey⟩ := hne
    obtain ⟨E2, h1, _⟩ := key x hx
    obtain ⟨E3, h3, _⟩ := key y hy
    have vx : C.eval x = b := by
      show (wf C.gates x).getD C.output false = b
      rw [h1, ho]
      exact getD_mid _ _ _ _ (by rw [wf_len, hx])
    have vy : C.eval y = b := by
      show (wf C.gates y).getD C.output false = b
      rw [h3, ho]
      exact getD_mid _ _ _ _ (by rw [wf_len, hy])
    rw [vx] at ex
    rw [vy, ex] at ey
    exact Bool.noConfusion ey
  apply assemble C pre post g hC T (sk (26 + pre.length) C.output) hmono hrb hTm hTr
  intro x hx
  obtain ⟨E2, h1, h2⟩ := key x hx
  show (wf (pre ++ post.map T) x).getD (sk (26 + pre.length) C.output) false
    = (wf C.gates x).getD C.output false
  rw [h2, h1]
  exact getD_sk _ _ _ _ (by rw [wf_len, hx]) _ hout

theorem copy_val (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (v : Bool) :
    op.eval [v] = v ∧ op.eval [v, v] = v := by
  rcases hop with rfl | rfl <;> cases v <;> exact ⟨rfl, rfl⟩

theorem len26 (f g : Fin 13 → Bool) : (List.ofFn f ++ List.ofFn g).length = 26 := by
  simp

theorem short_case (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hne : ∃ x y : List Bool, x.length = 26 ∧ y.length = 26 ∧ C.eval x = true ∧
      C.eval y = false)
    (hdeg : ∃ g ∈ C.gates, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
    obtain ⟨g, hg, hd⟩ := hdeg
    obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
    obtain ⟨pre, post, gj, hC, hpl, hgj⟩ := split_gates C.gates k hk
    have hgg : gj = g := by rw [← hgj, hgk]
    rw [hgg] at hC
    have hl := legal_of C hmono g hg
    have hin : ∀ i ∈ g.inputs, i < 26 + pre.length := by
      intro i hi
      have := hrb k hk i (by rw [gateAt_eq C k hk, hgk]; exact hi)
      omega
    obtain ⟨op, ins⟩ := g
    have hop : op = GateOp.and ∨ op = GateOp.or := hl.1
    have hlen : ins.length ≤ 2 := hl.2
    have hd' : ins.length < 2 ∨ ins.getD 0 0 = ins.getD 1 0 := hd
    have hin' : ∀ i ∈ ins, i < 26 + pre.length := hin
    rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, r⟩⟩⟩
    · rcases hop with hop | hop
      · subst hop
        exact const_case C hmono hrb pre post _ hC (Tt (26 + pre.length)) true (fun _ => rfl)
          (fun h hl => Tt_legal _ h hl)
          (fun h hl M hM hi => Tt_rb _ (by omega) h hl.1 M hM hi)
          (fun h hop A E hA => sound_t A E _ hA h hop) hne
      · subst hop
        exact const_case C hmono hrb pre post _ hC (Tf (26 + pre.length)) false (fun _ => rfl)
          (fun h hl => Tf_legal _ h hl)
          (fun h hl M hM hi => Tf_rb _ (by omega) h hl.1 M hM hi)
          (fun h hop A E hA => sound_f A E _ hA h hop) hne
    · exact copy_case C hmono hrb pre post _ hC a (hin' a (by simp))
        (fun A => (copy_val op hop _).1)
    · have hac : a = c := by simpa using hd'
      subst hac
      exact copy_case C hmono hrb pre post _ hC a (hin' a (by simp))
        (fun A => (copy_val op hop _).2)
    · have h3 : (a :: c :: d :: r).length ≤ 2 := hlen
      simp only [List.length_cons] at h3
      omega

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

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_reader (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → ∃ r, r < C.gates.length ∧ i < r ∧ n + i ∈ (gateAt C r).inputs ∧
      (r = j ∨ InCone n C r j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have h' := h
    rw [inCone_iff] at h'
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h'
    · subst h3
      exact ⟨j, h0, hk, hin, Or.inl rfl⟩
    · obtain ⟨r, hr, hir, hrin, h4⟩ := ih k hk h3
      refine ⟨r, hr, hir, hrin, Or.inr ?_⟩
      rw [inCone_iff]
      refine ⟨h0, k, hk, hin, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C C' : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt C' k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma transfer (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool) (R : Bool → Bool → Prop)
    (hRrefl : ∀ a, R a a) (hRtrans : ∀ a b c, R a b → R b c → R a c)
    (hRand : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.and.eval (l.map f)) (GateOp.and.eval (l.map f')))
    (hRor : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.or.eval (l.map f)) (GateOp.or.eval (l.map f')))
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → R (wv n C x (n + r)) (wv n C x b)) →
      R (wv n C x w) (wv n C' x (tau n r b w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hR0
    by_cases h1 : w < n
    · have ht : tau n r b w = w := by unfold tau; rw [if_pos (by omega)]
      rw [ht, wv_input n C x w h1, wv_input n C' x w h1]
      exact hRrefl _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k = r
      · subst hk
        have ht : tau n k b (n + k) = b := by unfold tau; simp
        have htb : tau n k b b = b := by unfold tau; rw [if_pos hb]
        have h2 := ih b (by omega) (by omega) (fun h => absurd h (by omega))
        rw [htb] at h2
        rw [ht]
        exact hRtrans _ _ _ (hR0 le_rfl) h2
      · have hkm : k < C.gates.length := by omega
        obtain ⟨k', hk'1, hk'2, hk'3⟩ : ∃ k', tau n r b (n + k) = n + k' ∧ rho r k' = k ∧
            k' < C.gates.length - 1 := by
          by_cases hkr : k < r
          · refine ⟨k, ?_, ?_, by omega⟩
            · unfold tau; rw [if_pos (by omega)]
            · unfold rho; rw [if_pos hkr]
          · refine ⟨k - 1, ?_, ?_, by omega⟩
            · unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
            · unfold rho; rw [if_neg (by omega)]; omega
        have hg := hred k' hk'3
        rw [hk'2] at hg
        rw [hk'1, wv_rec n C x hC k hkm, wv_rec n C' x hC' k' (by omega), hg]
        simp only [List.map_map]
        have hin : ∀ w ∈ (gateAt C k).inputs,
            R (wv n C x w) ((wv n C' x ∘ tau n r b) w) := by
          intro w hw'
          have hlt := (hC k hkm).2 w hw'
          exact ih w hlt (by omega) (fun h => hR0 (by omega))
        rcases (hC k hkm).1 with hop | hop
        · rw [hop]; exact hRand _ _ _ hin
        · rw [hop]; exact hRor _ _ _ hin

lemma transfer_eq (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → wv n C x (n + r) = wv n C x b) →
      wv n C x w = wv n C' x (tau n r b w) := by
  refine transfer n C C' r b x (fun a b => a = b) (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2)
    ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h
    rw [List.map_congr_left h]
  · intro l f f' h
    rw [List.map_congr_left h]

lemma transfer_le (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length →
      (n + r ≤ w → (wv n C x (n + r) = true → wv n C x b = true)) →
      (wv n C x w = true → wv n C' x (tau n r b w) = true) := by
  refine transfer n C C' r b x (fun a b => a = true → b = true) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h hall
    simp only [GateOp.eval] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw (hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · intro l f f' h hany
    simp only [GateOp.eval] at hany ⊢
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨v, hv, hv2⟩ := hany
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨f' w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩


def gfun (n : ℕ) (C : Circuit) (r b : ℕ) (top : Gate) (k : ℕ) : Gate :=
  if k < C.gates.length - 1 then
    ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ else top

def V1 (n : ℕ) (C : Circuit) (r b : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (gfun n C r b ⟨GateOp.or, []⟩), tau n r b C.output⟩

def V2 (n : ℕ) (C : Circuit) (r b i : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (gfun n C r b ⟨GateOp.or, [tau n r b C.output, n + i]⟩),
    n + C.gates.length - 1⟩

lemma gateAt_range (m : ℕ) (g : ℕ → Gate) (out k : ℕ) (hk : k < m) :
    gateAt ⟨(List.range m).map g, out⟩ k = g k := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma V1_len (n : ℕ) (C : Circuit) (r b : ℕ) :
    (V1 n C r b).gates.length = C.gates.length - 1 := by simp [V1]

lemma V2_len (n : ℕ) (C : Circuit) (r b i : ℕ) :
    (V2 n C r b i).gates.length = C.gates.length := by simp [V2]

lemma V1_gate (n : ℕ) (C : Circuit) (r b k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V1 n C r b) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V1
  rw [gateAt_range _ _ _ _ hk]
  unfold gfun
  rw [if_pos hk]

lemma V2_gate (n : ℕ) (C : Circuit) (r b i k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V2 n C r b i) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_pos hk]

lemma V2_top (n : ℕ) (C : Circuit) (r b i : ℕ) (hm : 0 < C.gates.length) :
    gateAt (V2 n C r b i) (C.gates.length - 1) =
      ⟨GateOp.or, [tau n r b C.output, n + i]⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_neg (by omega)]

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma aob {n : ℕ} {C : Circuit} (h : AO2 n C) : AOB n C :=
  fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho; split_ifs <;> omega

lemma tau_lt (n r b w k : ℕ) (hb : b < n + r) (hw : w < n + rho r k) :
    tau n r b w < n + k := by
  unfold tau; unfold rho at hw; split_ifs at hw ⊢ <;> omega

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  unfold tau; rw [if_pos hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho; split_ifs <;> omega

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma V1_AO2 (n : ℕ) (C : Circuit) (r b : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) : AO2 n (V1 n C r b) := by
  intro k hk
  rw [V1_len] at hk
  rw [V1_gate n C r b k hk]
  obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk)
  refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  exact tau_lt n r b w0 k hb (h3 w0 hw0)

lemma V2_AO2 (n : ℕ) (C : Circuit) (r b i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) (hi : i < r) (hout : C.output < n + C.gates.length) :
    AO2 n (V2 n C r b i) := by
  intro k hk
  rw [V2_len] at hk
  by_cases hk1 : k < C.gates.length - 1
  · rw [V2_gate n C r b i k hk1]
    obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk1)
    refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact tau_lt n r b w0 k hb (h3 w0 hw0)
  · have hk2 : k = C.gates.length - 1 := by omega
    subst hk2
    rw [V2_top n C r b i (by omega)]
    refine ⟨Or.inr rfl, ⟨_, _, rfl⟩, ?_⟩
    intro w hw
    have hw' : w = tau n r b C.output ∨ w = n + i := by simpa using hw
    rcases hw' with rfl | rfl
    · unfold tau; split_ifs <;> omega
    · omega

lemma V1_red (n : ℕ) (C : Circuit) (r b : ℕ) : IsRedirect n C (V1 n C r b) r b :=
  fun k hk => V1_gate n C r b k hk

lemma V2_red (n : ℕ) (C : Circuit) (r b i : ℕ) : IsRedirect n C (V2 n C r b i) r b :=
  fun k hk => V2_gate n C r b i k hk

lemma V1_fun (n : ℕ) (C : Circuit) (r b : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hout : C.output < n + C.gates.length)
    (h1 : wv n C x b = true → wv n C x C.output = true)
    (h2 : wv n C x b = false → wv n C x (n + r) = false) :
    wv n (V1 n C r b) x (V1 n C r b).output = wv n C x C.output := by
  have hC' := V1_AO2 n C r b hC hr hb
  have hlen : C.gates.length - 1 ≤ (V1 n C r b).gates.length := by rw [V1_len]
  show wv n (V1 n C r b) x (tau n r b C.output) = wv n C x C.output
  cases hbv : wv n C x b with
  | true =>
    rw [h1 hbv]
    exact transfer_le n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ _ => hbv) (h1 hbv)
  | false =>
    exact (transfer_eq n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ => by rw [h2 hbv, hbv])).symm

lemma V2_low (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) :
    ∀ w, w < n + r → wv n (V2 n C r b i) x w = wv n C x w := by
  intro w hw
  have h := transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w (by omega) (fun h => absurd h (by omega))
  rw [tau_low n r b w hw] at h
  exact h.symm

lemma V2_same (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x b) :
    ∀ w, w < n + C.gates.length → wv n (V2 n C r b i) x (tau n r b w) = wv n C x w := by
  intro w hw
  exact (transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w hw (fun _ => h0)).symm

lemma V2_out (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbel : wv n C x (n + i) = true → wv n C x C.output = true)
    (h0 : wv n C x (n + i) = false → wv n C x (n + r) = wv n C x b) :
    wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output := by
  have hC' := V2_AO2 n C r b i hC hr hb hi hout
  have hm : 0 < C.gates.length := by omega
  have e : (V2 n C r b i).output = n + (C.gates.length - 1) := by
    show n + C.gates.length - 1 = _
    omega
  rw [e, wv_rec n _ x (aob hC') (C.gates.length - 1) (by rw [V2_len]; omega),
    V2_top n C r b i hm]
  have hi' := V2_low n C r b i x hC hr hb hi hout (n + i) (by omega)
  dsimp only
  rw [eval_or_pair, hi']
  cases hv : wv n C x (n + i) with
  | true => rw [hbel hv]; simp
  | false =>
    rw [V2_same n C r b i x hC hr hb hi hout (h0 hv) C.output hout]; simp

lemma V1_fun_top (n : ℕ) (D : Circuit) (r c i y : ℕ) (x : Fin n → Bool) (hD : AO2 n D)
    (hr : r < D.gates.length - 1) (hc : c < n + r) (hi : i < r)
    (hout : D.output = n + (D.gates.length - 1))
    (htop : gateAt D (D.gates.length - 1) = ⟨GateOp.or, [y, n + i]⟩)
    (h0 : wv n D x (n + i) = false → wv n D x (n + r) = wv n D x c) :
    wv n (V1 n D r c) x (V1 n D r c).output = wv n D x D.output := by
  have hr' : r < D.gates.length := by omega
  have hE := V1_AO2 n D r c hD hr' hc
  have hlen : D.gates.length - 1 ≤ (V1 n D r c).gates.length := by rw [V1_len]
  have hred := V1_red n D r c
  show wv n (V1 n D r c) x (tau n r c D.output) = wv n D x D.output
  cases hv : wv n D x (n + i) with
  | false =>
    exact (transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred D.output (by omega)
      (fun _ => h0 hv)).symm
  | true =>
    have e1 : wv n D x D.output = true := by
      rw [hout, wv_rec n D x (aob hD) _ (by omega), htop]
      dsimp only
      rw [eval_or_pair, hv]; simp
    have e2 : tau n r c D.output = n + (D.gates.length - 2) := by
      rw [hout]; unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
    have e3 : gateAt (V1 n D r c) (D.gates.length - 2) =
        ⟨GateOp.or, [tau n r c y, n + i]⟩ := by
      rw [V1_gate n D r c _ (by omega)]
      have hrho : rho r (D.gates.length - 2) = D.gates.length - 1 := by
        unfold rho; rw [if_neg (by omega)]; omega
      rw [hrho, htop]
      simp [tau_low n r c (n + i) (by omega)]
    have e4 : wv n (V1 n D r c) x (n + i) = true := by
      have h := transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred (n + i) (by omega)
        (fun h => absurd h (by omega))
      rw [tau_low n r c (n + i) (by omega)] at h
      rw [← h, hv]
    rw [e1, e2, wv_rec n _ x (aob hE) _ (by rw [V1_len]; omega), e3]
    dsimp only
    rw [eval_or_pair, e4]; simp

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma V2_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hc : c < n + r) (hcin : c ∈ (gateAt C r).inputs) (a' : ℕ) :
    ∀ b', b' < C.gates.length - 1 → InCone n (V2 n C r c i) a' b' →
      InCone n C (rho r a') (rho r b') := by
  intro b'
  induction b' using Nat.strong_induction_on with
  | _ b' ih =>
    intro hb' h
    rw [inCone_iff] at h
    obtain ⟨_, k', hk', hin, h3⟩ := h
    rw [V2_gate n C r c i b' hb'] at hin
    simp only [List.mem_map] at hin
    obtain ⟨w, hw, hwk⟩ := hin
    have hbm : rho r b' < C.gates.length := rho_lt r b' _ hr hb'
    have hwlt := (hC (rho r b') hbm).2.2 w hw
    have hrb : rho r b' ≤ b' + 1 := by unfold rho; split_ifs <;> omega
    have hrb2 : b' < r → rho r b' = b' := by intro h; unfold rho; rw [if_pos h]
    have hstep : InCone n C (rho r k') (rho r b') := by
      unfold tau at hwk
      by_cases h1 : w < n + r
      · rw [if_pos h1] at hwk
        have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
        rw [e, inCone_iff]
        refine ⟨hbm, k', by omega, ?_, Or.inl rfl⟩
        rw [← hwk]; exact hw
      · rw [if_neg h1] at hwk
        by_cases h2 : w = n + r
        · rw [if_pos h2] at hwk
          have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
          rw [e]
          have s1 : InCone n C k' r := by
            rw [inCone_iff]
            refine ⟨hr, k', by omega, ?_, Or.inl rfl⟩
            rw [← hwk]; exact hcin
          have s2 : InCone n C r (rho r b') := by
            rw [inCone_iff]
            refine ⟨hbm, r, by omega, ?_, Or.inl rfl⟩
            rw [← h2]; exact hw
          exact inCone_trans n C k' r s1 _ s2
        · rw [if_neg h2] at hwk
          have e : rho r k' = k' + 1 := by unfold rho; rw [if_neg (by omega)]
          rw [e, inCone_iff]
          refine ⟨hbm, k' + 1, by omega, ?_, Or.inl rfl⟩
          have e2 : n + (k' + 1) = w := by omega
          rw [e2]; exact hw
    rcases h3 with h3 | h3
    · rw [h3]; exact hstep
    · exact inCone_trans n C _ _ (ih k' hk' (by omega) h3) _ hstep

lemma V2_no_reader (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ k', k' < C.gates.length - 1 → n + i ∉ (gateAt (V2 n C r c i) k').inputs := by
  intro k' hk' hin
  rw [V2_gate n C r c i k' hk'] at hin
  simp only [List.mem_map] at hin
  obtain ⟨w, hw, hwk⟩ := hin
  have hbm : rho r k' < C.gates.length := rho_lt r k' _ hr hk'
  have hne : rho r k' ≠ r := by unfold rho; split_ifs <;> omega
  unfold tau at hwk
  by_cases h1 : w < n + r
  · rw [if_pos h1] at hwk
    rw [hwk] at hw
    exact hne (huniq _ hbm hw)
  · rw [if_neg h1] at hwk
    by_cases h2 : w = n + r
    · rw [if_pos h2] at hwk
      exact hci hwk
    · rw [if_neg h2] at hwk
      omega

lemma V2_no_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ j', j' < C.gates.length - 1 → ¬ InCone n (V2 n C r c i) i j' := by
  intro j' hj' h
  obtain ⟨r', _, _, hrin, h4⟩ := inCone_reader n _ i j' h
  have hr'j : r' ≤ j' := by
    rcases h4 with h4 | h4
    · omega
    · have := (inCone_lt n _ r' j' h4).1
      omega
  exact V2_no_reader n C r c i hr hi hci huniq r' (by omega) hrin


lemma rho_inj (r : ℕ) : Function.Injective (rho r) := by
  intro a b h
  unfold rho at h
  split_ifs at h <;> omega

lemma rho_ne (r k : ℕ) : rho r k ≠ r := by
  unfold rho; split_ifs <;> omega

lemma rho_surj (r k m : ℕ) (hr : r < m) (hk : k < m) (hne : k ≠ r) : ∃ k', k' < m - 1 ∧ rho r k' = k := by
  by_cases h : k < r
  · exact ⟨k, by omega, by unfold rho; rw [if_pos h]⟩
  · exact ⟨k - 1, by omega, by unfold rho; rw [if_neg (by omega)]; omega⟩

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma out_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : wv n C x C.output = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  unfold wv at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at h
  simp at h

lemma card_pairs_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → ℕ → Prop)
    [DecidablePred (fun p : ℕ × ℕ => P p.1 p.2)] [DecidablePred (fun p : ℕ × ℕ => Q p.1 p.2)]
    (hQP : ∀ a' b', a' < m → b' < m → Q a' b' →
      a' < m - 1 ∧ b' < m - 1 ∧ P (rho r a') (rho r b'))
    (i j : ℕ) (hi : i < m) (hj : j < m) (hP : P i j)
    (hne : ∀ a' b', Q a' b' → ¬ (rho r a' = i ∧ rho r b' = j)) :
    ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => Q p.1 p.2)).card <
      ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => P p.1 p.2)).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (rho r p.1, rho r p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (rho_inj r h.1) (rho_inj r h.2)
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hP⟩
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨a', b'⟩, hab, heq⟩ := hmem
      rw [Finset.mem_filter] at hab
      simp only [Prod.mk.injEq] at heq
      exact hne a' b' hab.2 heq
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨h1, h2, h3⟩ := hQP a' b' hab.1.1 hab.1.2 hab.2
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨rho_lt r a' m hr h1, rho_lt r b' m hr h2⟩, h3⟩

lemma pairs_lt (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
      (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)]
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
      (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)] :
    ((Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)).card <
    ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card := by
  rw [hlen]
  have hjm := (inCone_lt n C i j hij)
  refine card_pairs_rho C.gates.length r hr
    (fun a b => (gateAt C a).op = GateOp.and ∧ (gateAt C b).op = GateOp.and ∧ InCone n C a b)
    (fun a b => (gateAt C' a).op = GateOp.and ∧ (gateAt C' b).op = GateOp.and ∧
      InCone n C' a b) ?_ i j (by omega) hjm.2 ⟨hi, hj, hij⟩ ?_
  · rintro a' b' _ hb' ⟨ha, hb, hab⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have ha' := (inCone_lt n C' a' b' hab).1
    have ha'' : a' < C.gates.length - 1 := by omega
    refine ⟨ha'', hb'', ?_, ?_, hcone a' b' hb'' hab⟩
    · rw [← hops a' ha'']; exact ha
    · rw [← hops b' hb'']; exact hb
  · rintro a' b' ⟨_, hb, hab⟩ ⟨h1, _⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have hb3 := (inCone_lt n C' a' b' hab).2
        have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have e : rho r i = i := by unfold rho; rw [if_pos hir]
    have e2 : a' = i := rho_inj r (h1.trans e.symm)
    rw [e2] at hab
    exact hno b' hb'' hab

lemma pairs_lt2 (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    (T T' : Finset (ℕ × ℕ))
    (hT : ∀ p : ℕ × ℕ, p ∈ T ↔ (p.1 < C.gates.length ∧ p.2 < C.gates.length) ∧
      (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)
    (hT' : ∀ p : ℕ × ℕ, p ∈ T' ↔ (p.1 < C'.gates.length ∧ p.2 < C'.gates.length) ∧
      (gateAt C' p.1).op = GateOp.and ∧ (gateAt C' p.2).op = GateOp.and ∧
        InCone n C' p.1 p.2) :
    T'.card < T.card := by
  classical
  have e : T = (Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2) := by
    ext p
    rw [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  have e' : T' = (Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2) := by
    ext p
    rw [hT', Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  rw [e, e']
  exact pairs_lt n C C' r i j hr hir hlen hops htop hcone hno hi hj hij

lemma reader_or (n : ℕ) (C : Circuit) (hC : AO2 n C) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hC r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hC) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
      wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x hb => V1_fun n C r (n + i) x hC hr hir hout hb (key x)
  have hle := hmin _ (V1_AO2 n C r (n + i) hC hr hir) hfun
  rw [V1_len] at hle
  omega

lemma reader_unique (n : ℕ) (C : Circuit) (hC : AO2 n C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := reader_or n C hC hout i r1 hr1 hmin hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := reader_or n C hC hout i r2 hr2 hmin hin2
  have hir1 : i < r1 := by have := (hC r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hC) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hC) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hC hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
      wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x hb => V2_out n C r2 c2 i x hC hr2 hc2lt hir2 hout hb (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hC hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hC hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hC hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
      wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x hb =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x hb)
  have hle := hmin _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
  rw [V1_len, hDlen] at hle
  omega

lemma step3_core (n : ℕ) (C : Circuit) (hC : AO2 n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := reader_or n C hC hout i r hr hmin hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (reader_unique n C hC hout i k r h hr hmin hkin hrin).elim
    · exact h
    · exact (reader_unique n C hC hout i r k h hk hmin hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hC) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma lift_abs (n : ℕ) (C : Circuit) (hC : AO2 n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hcone : InCone n C i j) :
    ∃ D : Circuit, AO2 n D ∧ D.gates.length = C.gates.length ∧
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) ∧
      PEqualNP.TopForm.andPairs n D < PEqualNP.TopForm.andPairs n C := by
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    step3_core n C hC hout i j hmin hcone
  refine ⟨V2 n C r c i, V2_AO2 n C r c i hC hr hclt hir hout, V2_len n C r c i,
    fun x hb => V2_out n C r c i x hC hr hclt hir hout hb (h0 x), ?_⟩
  unfold PEqualNP.TopForm.andPairs
  refine pairs_lt2 n C (V2 n C r c i) r i j hr hir (V2_len n C r c i) ?_ ?_ ?_ ?_ hi hj hcone
    _ _ ?_ ?_
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro a' b' hb' h
    exact V2_cone n C r c i hC hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq
  · intro p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  · intro p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]

lemma ofFn_of_len (L : List Bool) : ∀ (m : ℕ), L.length = m →
    ∃ x : Fin m → Bool, List.ofFn x = L := by
  intro m hm
  subst hm
  exact ⟨L.get, List.ofFn_get L⟩

lemma AO2_mono {n : ℕ} {C : Circuit} (h : AO2 n C) : Monotone2 C := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have e := gateAt_eq C k hk
  obtain ⟨h1, ⟨a, b, h2⟩, _⟩ := h k hk
  rw [e] at h1 h2
  refine ⟨?_, by rw [h2]; simp⟩
  rcases h1 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

lemma to_AO2 (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (h2 : ∀ g ∈ C.gates, ¬ g.inputs.length < 2) : AO2 26 C := by
  intro k hk
  have e := gateAt_eq C k hk
  have hmem : C.gates[k] ∈ C.gates := List.getElem_mem hk
  have hl := legal_of C hmono _ hmem
  have h3 := h2 _ hmem
  refine ⟨by rw [e]; exact hl.1, ?_, hrb k hk⟩
  rw [e]
  have h4 : (C.gates[k]).inputs.length = 2 := by
    have := hl.2
    omega
  exact List.length_eq_two.mp h4

theorem main26 (A R : List Bool → Prop) (hA : ∀ L, A L → L.length = 26)
    (hR : ∀ L, R L → L.length = 26) (hAne : ∃ L, A L) (hRne : ∃ L, R L)
    (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hacc : ∀ L, A L → C.eval L = true) (hrej : ∀ L, R L → C.eval L = false)
    (i j : ℕ) (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone 26 C i j)
    (hB : ∀ L, R L → (C.wires L).getD (26 + i) false = false) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ ((∀ L, A L → D.eval L = true) ∧
      ∀ L, R L → D.eval L = false) ∧
      (D.size < C.size ∨ D.size = C.size ∧
        PEqualNP.TopForm.andPairs 26 D < PEqualNP.TopForm.andPairs 26 C) := by
  by_cases hsm : ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧
      ((∀ L, A L → D.eval L = true) ∧ ∀ L, R L → D.eval L = false) ∧ D.size < C.size
  · obtain ⟨D, h1, h2, h3, h4⟩ := hsm
    exact ⟨D, h1, h2, h3, Or.inl h4⟩
  · have hne : ∃ x y : List Bool, x.length = 26 ∧ y.length = 26 ∧ C.eval x = true ∧
        C.eval y = false := by
      obtain ⟨La, ha⟩ := hAne
      obtain ⟨Lr, hr⟩ := hRne
      exact ⟨La, Lr, hA _ ha, hR _ hr, hacc _ ha, hrej _ hr⟩
    have hC : AO2 26 C := by
      apply to_AO2 C hmono hrb
      intro g hg hlt
      obtain ⟨C', m1, m2, heq, hsz⟩ := short_case C hmono hrb hne ⟨g, hg, Or.inl hlt⟩
      apply hsm
      refine ⟨C', m1, m2, ⟨?_, ?_⟩, hsz⟩
      · intro L hL
        rw [heq L (hA L hL)]
        exact hacc L hL
      · intro L hL
        rw [heq L (hR L hL)]
        exact hrej L hL
    have hbelA : ∀ x : Fin 26 → Bool, A (List.ofFn x) →
        (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) := by
      intro x hL _
      exact hacc _ hL
    have hbelR : ∀ x : Fin 26 → Bool, R (List.ofFn x) →
        (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) := by
      intro x hL hv
      have h1 : wv 26 C x (26 + i) = false := hB _ hL
      rw [h1] at hv
      exact absurd hv (by simp)
    have tg : ∀ D : Circuit, AO2 26 D →
        (∀ x, (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) →
          wv 26 D x D.output = wv 26 C x C.output) →
        ((∀ L, A L → D.eval L = true) ∧ ∀ L, R L → D.eval L = false) := by
      intro D _ hf
      constructor
      · intro L hL
        obtain ⟨x, hx⟩ := ofFn_of_len L 26 (hA L hL)
        subst hx
        have h1 := hf x (hbelA x hL)
        have h2 : wv 26 C x C.output = true := hacc _ hL
        show wv 26 D x D.output = true
        rw [h1]
        exact h2
      · intro L hL
        obtain ⟨x, hx⟩ := ofFn_of_len L 26 (hR L hL)
        subst hx
        have h1 := hf x (hbelR x hL)
        have h2 : wv 26 C x C.output = false := hrej _ hL
        show wv 26 D x D.output = false
        rw [h1]
        exact h2
    have hmin : ∀ D : Circuit, AO2 26 D →
        (∀ x, (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) →
          wv 26 D x D.output = wv 26 C x C.output) → C.gates.length ≤ D.gates.length := by
      intro D hD hf
      by_contra hlt
      apply hsm
      refine ⟨D, AO2_mono hD, (fun k hk => (hD k hk).2.2), tg D hD hf, ?_⟩
      show D.gates.length < C.gates.length
      omega
    have hout : C.output < 26 + C.gates.length := by
      obtain ⟨La, ha⟩ := hAne
      obtain ⟨x, hx⟩ := ofFn_of_len La 26 (hA La ha)
      subst hx
      exact out_lt 26 C x (hacc _ ha)
    obtain ⟨D, hD, hlen, hf, hp⟩ := lift_abs 26 C hC hout i j hmin hi hj hij
    exact ⟨D, AO2_mono hD, (fun k hk => (hD k hk).2.2), tg D hD hf, Or.inr ⟨hlen, hp⟩⟩

theorem inc00 : (0 : Fin 13) ∈ PEqualNP.HeptadCover.singerLines3 0 := by
  decide

theorem quad : PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3
    ({0, 1, 2, 5} : Finset (Fin 13)) := by
  decide

theorem final (x1 : Finset (Fin 13) → List Bool)
    (hx1 : ∀ S, (x1 S).length = 26)
    (C : Circuit) (hm : Monotone2 C) (hr : ReadsBack 26 C)
    (hacc : ∀ x3 x4 : Fin 13, x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 →
      C.eval ((List.ofFn fun x6 : Fin 13 => decide (x6 = x3)) ++
        List.ofFn fun x6 : Fin 13 => decide (x6 = x4)) = true)
    (hrej : ∀ x3 : Finset (Fin 13),
      PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 →
      C.eval (x1 x3) = false)
    (hex : ∃ x5 x6 : ℕ, (gateAt C x5).op = GateOp.and ∧ (gateAt C x6).op = GateOp.and ∧
      InCone 26 C x5 x6 ∧
      ∀ x7 : Finset (Fin 13),
        PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x7 →
        (C.wires (x1 x7)).getD (26 + x5) false = false) :
    ∃ D : Circuit, (Monotone2 D ∧ ReadsBack 26 D ∧
      (∀ x3 x4 : Fin 13, x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 →
        D.eval ((List.ofFn fun x6 : Fin 13 => decide (x6 = x3)) ++
          List.ofFn fun x6 : Fin 13 => decide (x6 = x4)) = true) ∧
      ∀ x3 : Finset (Fin 13),
        PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 →
        D.eval (x1 x3) = false) ∧
      (D.size < C.size ∨ D.size = C.size ∧
        PEqualNP.TopForm.andPairs 26 D < PEqualNP.TopForm.andPairs 26 C) := by
  obtain ⟨i, j, hi, hj, hij, hB⟩ := hex
  obtain ⟨D, d1, d2, d3, d4⟩ := main26
    (fun L => ∃ a b : Fin 13, a ∈ PEqualNP.HeptadCover.singerLines3 b ∧
      L = (List.ofFn fun k : Fin 13 => decide (k = a)) ++
        List.ofFn fun k : Fin 13 => decide (k = b))
    (fun L => ∃ S : Finset (Fin 13),
      PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 S ∧ L = x1 S)
    (by rintro L ⟨a, b, _, rfl⟩; exact len26 _ _)
    (by rintro L ⟨S, _, rfl⟩; exact hx1 S)
    ⟨_, 0, 0, inc00, rfl⟩
    ⟨_, {0, 1, 2, 5}, quad, rfl⟩
    C hm hr
    (by rintro L ⟨a, b, h, rfl⟩; exact hacc a b h)
    (by rintro L ⟨S, hS, rfl⟩; exact hrej S hS)
    i j hi hj hij
    (by rintro L ⟨S, hS, rfl⟩; exact hB S hS)
  exact ⟨D, ⟨d1, d2, fun a b h => d3.1 _ ⟨a, b, h, rfl⟩, fun S hS => d3.2 _ ⟨S, hS, rfl⟩⟩, d4⟩

end PEqualNP.Outside.L_meta_5160

theorem PEqualNP.Outside.L_meta_5160 : have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) => (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++ List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1); have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.MetaComplexity.Monotone2 x2 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x2 ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 ∈ PEqualNP.HeptadCover.singerLines3 x4 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x3 → x2.eval (x1 x3) = Bool.false; ∀ (x3 : PEqualNP.CircuitLowerBounds.Circuit), x2 x3 → (∃ (x5 : ℕ) (x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x5 x6 ∧ ∀ (x7 : Finset (Fin (13 : ℕ))), PEqualNP.HeptadCover.IsQuadrangle PEqualNP.HeptadCover.singerLines3 x7 → (x3.wires (x1 x7)).getD ((26 : ℕ) + x5) Bool.false = Bool.false) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x2 x6 ∧ (x6.size < x3.size ∨ x6.size = x3.size ∧ PEqualNP.TopForm.andPairs (26 : ℕ) x6 < PEqualNP.TopForm.andPairs (26 : ℕ) x3) := by
  intro x1 x2 C ⟨hm, hr, hacc, hrej⟩ hex
  exact PEqualNP.Outside.L_meta_5160.final x1
    (fun S => PEqualNP.Outside.L_meta_5160.len26 _ _) C hm hr hacc hrej hex
