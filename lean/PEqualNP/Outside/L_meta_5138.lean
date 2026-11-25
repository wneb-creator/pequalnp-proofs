import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5138

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



def u (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del : Finset ℕ) (L : ℕ → List ℕ) (x : List Bool)
    (w : ℕ) : Bool :=
  if w < n then x.getD w false
  else if w - n ∈ Del then false
  else if A (w - n) = true then
    ((if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
      (L (w - n)).any (fun t => x.getD t false)) &&
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
  else
    (if _h : a (w - n) < w then u n A a b Del L x (a (w - n)) else false) ||
    (if _h : b (w - n) < w then u n A a b Del L x (b (w - n)) else false)
termination_by w

section
variable {n : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ} {x : List Bool}

theorem u_in {w : ℕ} (h : w < n) : u n A a b Del L x w = x.getD w false := by
  rw [u, if_pos h]

theorem u_del {j : ℕ} (h : j ∈ Del) : u n A a b Del L x (n + j) = false := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_pos h]

theorem u_and {j : ℕ} (h : j ∉ Del) (hA : A j = true) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = ((u n A a b Del L x (a j) ||
      (L j).any (fun t => x.getD t false)) && u n A a b Del L x (b j)) := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_neg h, if_pos hA, dif_pos ha, dif_pos hb]

theorem u_or {j : ℕ} (h : j ∉ Del) (hA : A j = false) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = (u n A a b Del L x (a j) || u n A a b Del L x (b j)) := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_neg h, if_neg (by simp [hA]), dif_pos ha,
    dif_pos hb]
end

def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

theorem ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

open Classical in
noncomputable def dc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter fun i => (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧
    ∃ x : Fin n → Bool, (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false).card

open Classical in
theorem dc_snoc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) (g : Gate) :
    dc n F (gs ++ [g]) ≤ dc n F gs + if g.op = GateOp.and ∧
      ∃ x : Fin n → Bool, (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧
        F x = false then 1 else 0 := by
  unfold dc
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have e : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
  rw [e]
  have h1 : ((Finset.range gs.length).filter fun i =>
      ((gs ++ [g]).getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + i) false = true ∧ F x = false) =
      (Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false := by
    refine Finset.filter_congr fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [getD_ltz _ _ _ _ hi']
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs [g] _ _ (by simp; omega)]
  rw [h1]
  split_ifs with h
  · exact (Finset.card_insert_le _ _)
  · simp

def ov (gs : List Gate) (x : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => (run gs x).getD w false

theorem ov_ext (gs hs : List Gate) (x : List Bool) (o : Option ℕ)
    (h : ∀ w, o = some w → w < x.length + gs.length) : ov (gs ++ hs) x o = ov gs x o := by
  cases o with
  | none => rfl
  | some w => exact run_prefix gs hs x w (h w rfl)

theorem ov_new (gs : List Gate) (n : ℕ) (x : List Bool) (hx : x.length = n) (o : GateOp) (s t : ℕ)
    (hs : s < n + gs.length) (ht : t < n + gs.length) :
    ov (gs ++ [⟨o, [s, t]⟩]) x (some (n + gs.length)) =
      o.eval [(run gs x).getD s false, (run gs x).getD t false] := by
  unfold ov
  simp only
  rw [run_snoc]
  have : n + gs.length = (run gs x).length := by rw [run_length, hx]
  rw [this, getD_at]
  rfl

theorem chain (n : ℕ) (F : (Fin n → Bool) → Bool) : ∀ (l : List ℕ), (∀ t ∈ l, t < n) →
    ∀ (gs : List Gate), Ok n gs → ∀ o : Option ℕ, (∀ w, o = some w → w < n + gs.length) →
    ∃ (hs : List Gate) (o' : Option ℕ), Ok n (gs ++ hs) ∧ hs.length ≤ l.length ∧
      dc n F (gs ++ hs) ≤ dc n F gs ∧ (∀ w, o' = some w → w < n + (gs ++ hs).length) ∧
      ∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o' =
        (ov gs (List.ofFn x) o || l.any (fun t => (List.ofFn x).getD t false)) := by
  intro l
  induction l with
  | nil =>
    intro _ gs hgs o ho
    exact ⟨[], o, by simpa using hgs, by simp, by simp, by simpa using ho, by simp⟩
  | cons t l ih =>
    intro hl gs hgs o ho
    have ht : t < n := hl t (by simp)
    have hl' : ∀ t ∈ l, t < n := fun s hs => hl s (by simp [hs])
    cases o with
    | none =>
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' gs hgs (some t) (by
        intro w hw; cases hw; omega)
      refine ⟨hs, o', h1, by simp; omega, h3, h4, fun x => ?_⟩
      rw [h5 x]
      have : ov gs (List.ofFn x) (some t) = (List.ofFn x).getD t false :=
        run_input _ _ _ (by simpa using ht)
      rw [this]; simp [ov]
    | some w =>
      have hw := ho w rfl
      obtain ⟨hs, o', h1, h2, h3, h4, h5⟩ := ih hl' (gs ++ [⟨GateOp.or, [w, t]⟩])
        (ok_snoc hgs (Or.inr rfl) hw (by omega)) (some (n + gs.length)) (by
          intro w hw; cases hw; simp)
      refine ⟨⟨GateOp.or, [w, t]⟩ :: hs, o', by simpa using h1, by simp; omega, ?_,
        by simpa using h4, fun x => ?_⟩
      · have := dc_snoc n F gs ⟨GateOp.or, [w, t]⟩
        rw [if_neg (by simp)] at this
        have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e]; omega
      · have e : gs ++ ⟨GateOp.or, [w, t]⟩ :: hs = gs ++ [⟨GateOp.or, [w, t]⟩] ++ hs := by simp
        rw [e, h5 x, ov_new gs n _ (by simp) _ _ _ hw (by omega)]
        rw [run_input gs (List.ofFn x) t (by simpa using ht)]
        simp [ov, GateOp.eval, Bool.or_assoc]

open Classical in
theorem build (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del R : Finset ℕ) (L : ℕ → List ℕ)
    (F : (Fin n → Bool) → Bool) (hL : ∀ j, ∀ t ∈ L j, t < n)
    (hR : ∀ j ∈ R, A j = false ∧ j ∉ Del ∧ ∃ d ∈ Del, d < j ∧ (a j = n + d ∨ b j = n + d)) :
    ∀ p, (∀ j < p, a j < n + j ∧ b j < n + j) →
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n + p, (∀ w', m w = some w' → w' < n + gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) = u n A a b Del L (List.ofFn x) w) ∧
      (∀ d ∈ Del, d < p → m (n + d) = none) ∧
      gs.length + ((Finset.range p).filter (· ∈ Del)).card +
        ((Finset.range p).filter (· ∈ R)).card ≤ p + ∑ j ∈ Finset.range p, (L j).length ∧
      dc n F gs ≤ ((Finset.range p).filter fun j => A j = true ∧ j ∉ Del ∧
        ∃ x : Fin n → Bool, u n A a b Del L (List.ofFn x) (n + j) = true ∧ F x = false).card := by
  intro p
  induction p with
  | zero =>
    intro _
    refine ⟨[], fun w => some w, by intro j hj; simp at hj, ?_, by simp, by simp, by simp [dc]⟩
    intro w hw
    refine ⟨by intro w' h; cases h; simpa using hw, fun x => ?_⟩
    rw [u_in (by omega)]; rfl
  | succ p ih =>
    intro hab
    obtain ⟨gs, m, hok, hm, hd, hc, hj⟩ := ih fun j hj => hab j (by omega)
    obtain ⟨hap, hbp⟩ := hab p (by omega)
    suffices hh : ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧
        (∀ w, o = some w → w < n + (gs ++ hs).length) ∧ (p ∈ Del → o = none) ∧
        (∀ x : Fin n → Bool, ov (gs ++ hs) (List.ofFn x) o =
          u n A a b Del L (List.ofFn x) (n + p)) ∧
        hs.length + (if p ∈ Del then 1 else 0) + (if p ∈ R then 1 else 0) ≤ 1 + (L p).length ∧
        dc n F (gs ++ hs) ≤ dc n F gs + if A p = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
          u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false then 1 else 0 by
      obtain ⟨hs, o, h1, h2, h3, h4, h5, h6⟩ := hh
      refine ⟨gs ++ hs, Function.update m (n + p) o, h1, ?_, ?_, ?_, ?_⟩
      · intro w hw
        by_cases hwp : w = n + p
        · subst hwp; rw [Function.update_self]; exact ⟨h2, h4⟩
        · rw [Function.update_of_ne hwp]
          obtain ⟨q1, q2⟩ := hm w (by omega)
          refine ⟨fun w' hw' => by have := q1 w' hw'; simp; omega, fun x => ?_⟩
          rw [ov_ext gs hs _ _ (by simpa using q1), q2]
      · intro d hdd hdp
        by_cases hdp' : d = p
        · subst hdp'; rw [Function.update_self]; exact h3 hdd
        · rw [Function.update_of_ne (by omega)]; exact hd d hdd (by omega)
      · rw [Finset.range_add_one, Finset.filter_insert, Finset.filter_insert,
          Finset.sum_insert (by simp), List.length_append]
        split_ifs at h5 ⊢ with q1 q2 q2 <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;>
          (try rw [Finset.card_insert_of_notMem (by simp)]) <;> omega
      · rw [Finset.range_add_one, Finset.filter_insert]
        split_ifs at h6 ⊢ with q1
        · rw [Finset.card_insert_of_notMem (by simp)]; omega
        · omega
    by_cases hpd : p ∈ Del
    · have hpR : p ∉ R := fun h => (hR p h).2.1 hpd
      refine ⟨[], none, by simpa using hok, by simp, fun _ => rfl, fun x => ?_, ?_, by simp⟩
      · rw [u_del hpd]; rfl
      · rw [if_pos hpd, if_neg hpR]; simp
    obtain ⟨a1, a2⟩ := hm (a p) hap
    obtain ⟨b1, b2⟩ := hm (b p) hbp
    cases hA : A p with
    | false =>
      have hu := fun x : Fin n → Bool => u_or (L := L) (x := List.ofFn x) hpd hA hap hbp
      rcases ha0 : m (a p) with _ | s
      · refine ⟨[], m (b p), by simpa using hok, by simpa using b1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, ha0]; simp [ov]
        · rw [if_neg hpd]; split_ifs <;> simp
      rcases hb0 : m (b p) with _ | t
      · refine ⟨[], m (a p), by simpa using hok, by simpa using a1, fun h => absurd h hpd,
          fun x => ?_, ?_, by simp⟩
        · rw [hu x, ← a2 x, ← b2 x, hb0]; simp [ov]
        · rw [if_neg hpd]; split_ifs <;> simp
      have hpR : p ∉ R := by
        intro h
        obtain ⟨_, _, d, hd1, hd2, hd3⟩ := hR p h
        have := hd d hd1 hd2
        rcases hd3 with h | h
        · rw [h, this] at ha0; cases ha0
        · rw [h, this] at hb0; cases hb0
      have hs := a1 s ha0
      have ht := b1 t hb0
      refine ⟨[⟨GateOp.or, [s, t]⟩], some (n + gs.length), ok_snoc hok (Or.inr rfl) hs ht,
        by intro w hw; cases hw; simp, fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [ov_new gs n _ (by simp) _ _ _ hs ht, hu x, ← a2 x, ← b2 x, ha0, hb0]
        simp [ov, GateOp.eval]
      · rw [if_neg hpd, if_neg hpR]; simp
      · have := dc_snoc n F gs ⟨GateOp.or, [s, t]⟩
        rw [if_neg (by simp)] at this
        omega
    | true =>
      have hu := fun x : Fin n → Bool => u_and (L := L) (x := List.ofFn x) hpd hA hap hbp
      have hpR : p ∉ R := fun h => by rw [(hR p h).1] at hA; cases hA
      obtain ⟨hs, o', c1, c2, c3, c4, c5⟩ := chain n F (L p) (hL p) gs hok (m (a p)) a1
      rcases ho : o' with _ | s
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := c5 x
          rw [ho, a2 x] at this
          rw [hu x, ← this]; simp [ov]
        · rw [if_neg hpd, if_neg hpR]; omega
      rcases hb0 : m (b p) with _ | t
      · refine ⟨hs, none, c1, by simp, fun _ => rfl, fun x => ?_, ?_, by omega⟩
        · have := b2 x
          rw [hb0] at this
          rw [hu x, ← this]; simp [ov]
        · rw [if_neg hpd, if_neg hpR]; omega
      have hs' := c4 s ho
      have ht : t < n + (gs ++ hs).length := by have := b1 t hb0; simp; omega
      have hval : ∀ x : Fin n → Bool, ov (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)
          (some (n + (gs ++ hs).length)) = u n A a b Del L (List.ofFn x) (n + p) := by
        intro x
        rw [ov_new (gs ++ hs) n _ (by simp) _ _ _ hs' ht, hu x, ← a2 x, ← b2 x, ← c5 x, ho, hb0,
          ← ov_ext gs hs (List.ofFn x) (some t) (by intro w hw; cases hw; simpa using b1 t hb0)]
        simp [ov, GateOp.eval]
      refine ⟨hs ++ [⟨GateOp.and, [s, t]⟩], some (n + (gs ++ hs).length), ?_, ?_,
        fun h => absurd h hpd, fun x => ?_, ?_, ?_⟩
      · rw [← List.append_assoc]; exact ok_snoc c1 (Or.inl rfl) hs' ht
      · intro w hw; cases hw; simp
      · rw [← List.append_assoc]; exact hval x
      · rw [if_neg hpd, if_neg hpR]; simp; omega
      · rw [← List.append_assoc]
        have := dc_snoc n F (gs ++ hs) ⟨GateOp.and, [s, t]⟩
        have e : ((⟨GateOp.and, [s, t]⟩ : Gate).op = GateOp.and ∧ ∃ x : Fin n → Bool,
            (run (gs ++ hs ++ [⟨GateOp.and, [s, t]⟩]) (List.ofFn x)).getD
              (n + (gs ++ hs).length) false = true ∧ F x = false) ↔
            (true = true ∧ p ∉ Del ∧ ∃ x : Fin n → Bool,
              u n A a b Del L (List.ofFn x) (n + p) = true ∧ F x = false) := by
          refine ⟨fun h => ⟨rfl, hpd, ?_⟩, fun h => ⟨rfl, ?_⟩⟩
          · obtain ⟨x, h1, h2⟩ := h.2
            exact ⟨x, by rw [← hval x]; exact h1, h2⟩
          · obtain ⟨x, h1, h2⟩ := h.2.2
            exact ⟨x, by rw [← hval x] at h1; exact h1, h2⟩
        rw [if_congr e rfl rfl] at this
        omega

theorem gf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ p q, G.Adj p q ∧ x p = true ∧ x q = true := by
  simp [graphFun]

theorem gD {n : ℕ} (x : Fin n → Bool) (p : Fin n) : (List.ofFn x).getD p.val false = x p := by
  simp [List.getD_eq_getElem?_getD]

theorem u_mono {n N : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ}
    (hab : ∀ j < N, a j < n + j ∧ b j < n + j) (x y : List Bool)
    (h : ∀ t, x.getD t false = true → y.getD t false = true) :
    ∀ w < n + N, u n A a b Del L x w = true → u n A a b Del L y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx
    by_cases h9 : w < n
    · rw [u_in h9] at hx ⊢; exact h _ hx
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    obtain ⟨ha, hb⟩ := hab j (by omega)
    by_cases hd : j ∈ Del
    · rw [u_del hd] at hx; cases hx
    have ia := ih (a j) ha (by omega)
    have ib := ih (b j) hb (by omega)
    cases hA : A j with
    | true =>
      rw [u_and hd hA ha hb, Bool.and_eq_true, Bool.or_eq_true] at hx ⊢
      refine ⟨?_, ib hx.2⟩
      rcases hx.1 with h1 | h1
      · exact Or.inl (ia h1)
      · right
        rw [List.any_eq_true] at h1 ⊢
        obtain ⟨t, h2, h3⟩ := h1
        exact ⟨t, h2, h t h3⟩
    | false =>
      rw [u_or hd hA ha hb, Bool.or_eq_true] at hx ⊢
      rcases hx with h1 | h1
      · exact Or.inl (ia h1)
      · exact Or.inr (ib h1)

def lo {n : ℕ} (V : (Fin n → Bool) → ℕ → Bool) (F : (Fin n → Bool) → Bool) (w : ℕ) : Prop :=
  ∀ x, V x w = true → F x = true

theorem orS (n : ℕ) (gs : List Gate) :
    (gs.foldl (CleanedNonEdge.orStep n) []).length = gs.length ∧
    ∀ j (hj : j < gs.length) d, d ∈ (gs.foldl (CleanedNonEdge.orStep n) []).getD j [] ↔
      (d = j ∨ (gs[j].op = GateOp.or ∧ ∃ w ∈ gs[j].inputs, n ≤ w ∧ w < n + j ∧
        d ∈ (gs.foldl (CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨rfl, fun j hj => by simp at hj⟩
  | append_singleton gs g ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set r := gs.foldl (CleanedNonEdge.orStep n) [] with hr
    have hold : ∀ i, i < gs.length → (CleanedNonEdge.orStep n r g).getD i [] = r.getD i [] := by
      intro i hi
      exact getD_ltz _ _ _ _ (by omega)
    refine ⟨by simp [CleanedNonEdge.orStep, h1], fun j hj d => ?_⟩
    by_cases hlt : j < gs.length
    · rw [hold j hlt, h2 j hlt d, List.getElem_append_left hlt]
      refine or_congr_right (and_congr_right fun _ => exists_congr fun w =>
        and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun hw => ?_)
      rw [hold _ (by omega)]
    · have hje : j = gs.length := by simp at hj; omega
      subst hje
      have e : (gs ++ [g])[gs.length] = g := by simp
      rw [e]
      have e2 : (CleanedNonEdge.orStep n r g).getD gs.length [] = r.length ::
          (@ite _ (g.op = GateOp.or) (Classical.dec _)
            ((g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + r.length))).flatMap
              (fun w => r.getD (w - n) [])) []) := by
        rw [← h1]
        unfold CleanedNonEdge.orStep
        rw [getD_at']
        congr 1
        split_ifs <;> rfl
      rw [e2, List.mem_cons, h1]
      refine or_congr_right ?_
      split_ifs with ho
      · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, ho, true_and]
        refine exists_congr fun w => ?_
        constructor
        · rintro ⟨⟨q1, q2, q3⟩, q4⟩
          exact ⟨q1, q2, q3, by rw [hold _ (by omega)]; exact q4⟩
        · rintro ⟨q1, q2, q3, q4⟩
          rw [hold _ (by omega)] at q4
          exact ⟨⟨q1, q2, q3⟩, q4⟩
      · simp [ho]

theorem coneS (n : ℕ) (gs : List Gate) :
    (gs.foldl (EdgeOwnership.coneStep n) []).length = gs.length ∧
    ∀ j (hj : j < gs.length) d, d ∈ (gs.foldl (EdgeOwnership.coneStep n) []).getD j [] →
      (∃ w ∈ gs[j].inputs, n ≤ w ∧ w < n + j ∧ (d = w - n ∨
        d ∈ (gs.foldl (EdgeOwnership.coneStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨rfl, fun j hj => by simp at hj⟩
  | append_singleton gs g ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set r := gs.foldl (EdgeOwnership.coneStep n) [] with hr
    have hold : ∀ i, i < gs.length → (EdgeOwnership.coneStep n r g).getD i [] = r.getD i [] := by
      intro i hi
      exact getD_ltz _ _ _ _ (by omega)
    refine ⟨by simp [EdgeOwnership.coneStep, h1], fun j hj d hd => ?_⟩
    by_cases hlt : j < gs.length
    · rw [hold j hlt] at hd
      rw [List.getElem_append_left hlt]
      obtain ⟨w, q1, q2, q3, q4⟩ := h2 j hlt d hd
      exact ⟨w, q1, q2, q3, by rw [hold _ (by omega)]; exact q4⟩
    · have hje : j = gs.length := by simp at hj; omega
      subst hje
      have e : (gs ++ [g])[gs.length] = g := by simp
      rw [e]
      have e2 : (EdgeOwnership.coneStep n r g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + r.length))).flatMap
              (fun w => (w - n) :: r.getD (w - n) []) := by
        rw [← h1]
        exact getD_at' _ _ _
      rw [e2, List.mem_flatMap] at hd
      obtain ⟨w, hw, hd⟩ := hd
      simp only [List.mem_filter, decide_eq_true_eq, h1] at hw
      refine ⟨w, hw.1, hw.2.1, hw.2.2, ?_⟩
      rw [hold _ (by omega)]
      exact List.mem_cons.1 hd

theorem orR_le (n : ℕ) (C : Circuit) : ∀ j d, d ∈ (CleanedNonEdge.orSets n C).getD j [] → d ≤ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro d hd
    obtain ⟨h1, h2⟩ := orS n C.gates
    by_cases hj : j < C.gates.length
    · rcases (h2 j hj d).1 hd with h | ⟨_, w, _, q2, q3, q4⟩
      · omega
      · have := ih (w - n) (by omega) d q4; omega
    · rw [List.getD_eq_default _ _ (by unfold CleanedNonEdge.orSets; omega)] at hd
      simp at hd

theorem cone_rd (n : ℕ) (C : Circuit) : ∀ j d, EdgeOwnership.InCone n C d j →
    j < C.gates.length ∧ d < j ∧ ∃ r < C.gates.length, n + d ∈ (gateAt C r).inputs := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro d hd
    obtain ⟨h1, h2⟩ := coneS n C.gates
    by_cases hj : j < C.gates.length
    · obtain ⟨w, q1, q2, q3, q4⟩ := h2 j hj d hd
      rcases q4 with q4 | q4
      · refine ⟨hj, by omega, j, hj, ?_⟩
        have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
        rw [e, q4, show n + (w - n) = w by omega]; exact q1
      · obtain ⟨_, t1, t2⟩ := ih (w - n) (by omega) d q4
        exact ⟨hj, by omega, t2⟩
    · unfold EdgeOwnership.InCone at hd
      rw [List.getD_eq_default _ _ (by unfold EdgeOwnership.cones; omega)] at hd
      simp at hd

theorem gate2 {n : ℕ} {C : Circuit} (h : TopForm.IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    C.gates[j] = gateAt C j ∧ (gateAt C j).inputs = [TopForm.opnd C j 0, TopForm.opnd C j 1] ∧
    TopForm.opnd C j 0 < n + j ∧ TopForm.opnd C j 1 < n + j ∧
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hm : gateAt C j ∈ C.gates := by rw [e]; exact List.getElem_mem hj
  have hl := h.2.2 _ hm
  obtain ⟨s, t, hst⟩ := List.length_eq_two.1 hl
  have hb := h.2.1 j hj
  rw [hst] at hb
  have e0 : TopForm.opnd C j 0 = s := by unfold TopForm.opnd; rw [hst]; rfl
  have e1 : TopForm.opnd C j 1 = t := by unfold TopForm.opnd; rw [hst]; rfl
  refine ⟨e.symm, by rw [hst, e0, e1], by rw [e0]; exact hb s (by simp),
    by rw [e1]; exact hb t (by simp), h.1 _ hm⟩

theorem veq (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) (o : GateOp)
    (s t : ℕ) (e : gs[j] = ⟨o, [s, t]⟩) (hs : s < n + j) (ht : t < n + j) :
    (run gs (List.ofFn x)).getD (n + j) false = o.eval [(run gs (List.ofFn x)).getD s false,
      (run gs (List.ofFn x)).getD t false] := by
  have := run_gate gs (List.ofFn x) j hj
  rw [List.length_ofFn, e] at this
  rw [this]
  simp [hs, ht]

theorem gate_eta {g : Gate} {o : GateOp} {l : List ℕ} (h1 : g.op = o) (h2 : g.inputs = l) :
    g = ⟨o, l⟩ := by
  cases g; cases h1; cases h2; rfl

theorem gDv {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := gD x ⟨w, hw⟩

set_option maxHeartbeats 2000000 in
theorem core3 (n N o g h : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del R : Finset ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (s : Fin n → Bool)
    (V : (Fin n → Bool) → ℕ → Bool) (Re : ℕ → Prop) (ta tb tw : Fin n)
    (hab : ∀ j < N, a j < n + j ∧ b j < n + j)
    (hVin : ∀ x, ∀ w < n, V x w = (List.ofFn x).getD w false)
    (hVa : ∀ x, ∀ j < N, A j = true → V x (n + j) = (V x (a j) && V x (b j)))
    (hVo : ∀ x, ∀ j < N, A j = false → V x (n + j) = (V x (a j) || V x (b j)))
    (hout : ∀ x, V x (n + o) = graphFun G ∅ x) (hoN : o < N)
    (hin : ∀ w < n, ¬ lo V (graphFun G ∅) w)
    (H3 : ∀ j < N, A j = true → ¬ lo V (graphFun G ∅) (a j) ∧ ¬ lo V (graphFun G ∅) (b j))
    (HL : ∀ j < N, A j = false → ¬ lo V (graphFun G ∅) (n + j) →
      ¬ lo V (graphFun G ∅) (a j) ∧ ¬ lo V (graphFun G ∅) (b j))
    (hread : ∀ j < N, j = o ∨ ∃ r < N, a r = n + j ∨ b r = n + j)
    (hJ : ∀ j < N, A j = true → ¬ lo V (graphFun G ∅) (n + j) → j = g ∨ j = h)
    (hgl : ¬ lo V (graphFun G ∅) (n + g)) (hhl : ¬ lo V (graphFun G ∅) (n + h))
    (hDel : ∀ d ∈ Del, d < N ∧ d ≠ o) (hgD : g ∈ Del) (hhD : h ∈ Del)
    (hDr : ∀ d ∈ Del, ∀ r < N, (a r = n + d ∨ b r = n + d) → r ∈ Del ∨ d = g ∨ d = h)
    (hRe : Re (n + g)) (hReo : ∀ j < N, A j = false → Re (a j) ∨ Re (b j) → Re (n + j))
    (hRm : ∀ w < n + N, Re w → ∀ x, V x (n + g) = true → V x w = true)
    (hs : ∀ p q, G.Adj p q → s p ≠ s q) (hadj : G.Adj ta tb) (hstw : s tw = s tb)
    (hnaw : ¬ G.Adj ta tw)
    (hgaw : V (EdgeOwnership.pairInput ta tw) (n + g) = true)
    (hhab : V (EdgeOwnership.pairInput ta tb) (n + h) = false)
    (hFall : ∃ x, graphFun G ∅ x = true) (hRN : ∀ j ∈ R, j < N)
    (hR : ∀ j ∈ R, A j = false ∧ j ∉ Del ∧ ∃ d ∈ Del, d < j ∧ (a j = n + d ∨ b j = n + d)) :
    ∃ (gs : List Gate) (w' : ℕ), Ok n gs ∧ w' < n + gs.length ∧
      gs.length + Del.card + R.card ≤ N + 1 ∧
      (∀ x : Fin n → Bool, (run gs (List.ofFn x)).getD w' false = true → graphFun G ∅ x = true) ∧
      (∀ x y : Fin n → Bool, (∀ t, x t = true → y t = true) →
        (run gs (List.ofFn x)).getD w' false = true →
        (run gs (List.ofFn y)).getD w' false = true) ∧
      (run gs (List.ofFn (EdgeOwnership.pairInput ta tb))).getD w' false = true ∧
      ∀ p q, G.Adj p q → V (EdgeOwnership.pairInput p q) (n + g) = false →
        V (EdgeOwnership.pairInput p q) (n + h) = false →
        (run gs (List.ofFn (EdgeOwnership.pairInput p q))).getD w' false = true := by
  classical
  have hLa : ∀ j < N, A j = false → lo V (graphFun G ∅) (n + j) →
      lo V (graphFun G ∅) (a j) ∧ lo V (graphFun G ∅) (b j) := by
    intro j hj hA hl
    refine ⟨fun x hx => hl x ?_, fun x hx => hl x ?_⟩ <;> rw [hVo x j hj hA, hx] <;> simp
  have hlo : lo V (graphFun G ∅) (n + o) := fun x hx => by rw [← hout x]; exact hx
  have Dlo : ∀ i d, N - d = i → d ∈ Del → ¬ lo V (graphFun G ∅) (n + d) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro d hi hd hl
      obtain ⟨hdN, hdo⟩ := hDel d hd
      by_cases hdg : d = g
      · exact hgl (hdg ▸ hl)
      by_cases hdh : d = h
      · exact hhl (hdh ▸ hl)
      rcases hread d hdN with h' | ⟨r, hr, hrd⟩
      · exact hdo h'
      rcases hDr d hd r hr hrd with h' | h' | h'
      · have hdr : d < r := by
          obtain ⟨h1, h2⟩ := hab r hr
          rcases hrd with h | h <;> omega
        cases hA : A r with
        | true =>
          obtain ⟨h1, h2⟩ := H3 r hr hA
          rcases hrd with h | h
          · rw [h] at h1; exact h1 hl
          · rw [h] at h2; exact h2 hl
        | false =>
          obtain ⟨h1, h2⟩ := HL r hr hA (ih (N - r) (by omega) r rfl h')
          rcases hrd with h | h
          · rw [h] at h1; exact h1 hl
          · rw [h] at h2; exact h2 hl
      · exact hdg h'
      · exact hdh h'
  -- the circuit with g and h false
  let Z : Finset ℕ := {g, h}
  let c : (Fin n → Bool) → ℕ → Bool := fun x w => u n A a b Z (fun _ => []) (List.ofFn x) w
  have hgZ : g ∈ Z := by simp [Z]
  have hhZ : h ∈ Z := by simp [Z]
  have hZ : ∀ j, j ∈ Z → j = g ∨ j = h := fun j hj => by simpa [Z] using hj
  have hcin : ∀ x, ∀ w < n, c x w = (List.ofFn x).getD w false := fun x w hw => u_in hw
  have hcZ : ∀ x, ∀ j ∈ Z, c x (n + j) = false := fun x j hj => u_del hj
  have hca : ∀ x, ∀ j < N, j ∉ Z → A j = true → c x (n + j) = (c x (a j) && c x (b j)) := by
    intro x j hj hjZ hA
    have := u_and (L := fun _ => []) (x := List.ofFn x) hjZ hA (hab j hj).1 (hab j hj).2
    simpa [c] using this
  have hco : ∀ x, ∀ j < N, j ∉ Z → A j = false → c x (n + j) = (c x (a j) || c x (b j)) := by
    intro x j hj hjZ hA
    exact u_or hjZ hA (hab j hj).1 (hab j hj).2
  have hAZ : ∀ j < N, A j = true → ¬ lo V (graphFun G ∅) (n + j) → j ∈ Z := by
    intro j hj hA hl
    rcases hJ j hj hA hl with rfl | rfl <;> assumption
  have cV : ∀ w < n + N, ∀ x, c x w = true → V x w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw x hx
      by_cases h9 : w < n
      · rw [hVin x w h9, ← hcin x w h9]; exact hx
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < N := by omega
      obtain ⟨ha, hb⟩ := hab j hj
      by_cases hjZ : j ∈ Z
      · rw [hcZ x j hjZ] at hx; cases hx
      cases hA : A j with
      | true =>
        rw [hca x j hj hjZ hA, Bool.and_eq_true] at hx
        rw [hVa x j hj hA, ih _ ha (by omega) x hx.1, ih _ hb (by omega) x hx.2]; rfl
      | false =>
        rw [hco x j hj hjZ hA, Bool.or_eq_true] at hx
        rw [hVo x j hj hA, Bool.or_eq_true]
        exact hx.imp (ih _ ha (by omega) x) (ih _ hb (by omega) x)
  have Lt : ∀ w < n + N, ¬ lo V (graphFun G ∅) w → ∀ x, c x w = true →
      ∃ i : Fin n, x i = true ∧ c (fun t => decide (t = i)) w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hl x hx
      by_cases h9 : w < n
      · rw [hcin x w h9, gDv x w h9] at hx
        refine ⟨⟨w, h9⟩, hx, ?_⟩
        rw [hcin _ w h9, gDv _ w h9]; simp
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < N := by omega
      obtain ⟨ha, hb⟩ := hab j hj
      by_cases hjZ : j ∈ Z
      · rw [hcZ x j hjZ] at hx; cases hx
      cases hA : A j with
      | true => exact absurd (hAZ j hj hA hl) hjZ
      | false =>
        obtain ⟨l1, l2⟩ := HL j hj hA hl
        rw [hco x j hj hjZ hA, Bool.or_eq_true] at hx
        rcases hx with hx | hx
        · obtain ⟨i, h1, h2⟩ := ih _ ha (by omega) l1 x hx
          exact ⟨i, h1, by rw [hco _ j hj hjZ hA, h2]; rfl⟩
        · obtain ⟨i, h1, h2⟩ := ih _ hb (by omega) l2 x hx
          exact ⟨i, h1, by rw [hco _ j hj hjZ hA, h2, Bool.or_true]⟩
  have Ag : ∀ w < n + N, ¬ lo V (graphFun G ∅) w → ¬ Re w → ∀ x, V x (n + h) = false →
      c x w = V x w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hl hr x hx
      by_cases h9 : w < n
      · rw [hVin x w h9, hcin x w h9]
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < N := by omega
      obtain ⟨ha, hb⟩ := hab j hj
      by_cases hjZ : j ∈ Z
      · rcases hZ j hjZ with rfl | rfl
        · exact absurd hRe hr
        · rw [hcZ x j hjZ, hx]
      cases hA : A j with
      | true => exact absurd (hAZ j hj hA hl) hjZ
      | false =>
        obtain ⟨l1, l2⟩ := HL j hj hA hl
        have hn : ¬ (Re (a j) ∨ Re (b j)) := fun h => hr (hReo j hj hA h)
        rw [not_or] at hn
        rw [hco x j hj hjZ hA, hVo x j hj hA, ih _ ha (by omega) l1 hn.1 x hx,
          ih _ hb (by omega) l2 hn.2 x hx]
  have Ag2 : ∀ x, V x (n + g) = false → V x (n + h) = false → ∀ w < n + N, c x w = V x w := by
    intro x hxg hxh w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases h9 : w < n
      · rw [hVin x w h9, hcin x w h9]
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < N := by omega
      obtain ⟨ha, hb⟩ := hab j hj
      by_cases hjZ : j ∈ Z
      · rw [hcZ x j hjZ]
        rcases hZ j hjZ with rfl | rfl
        · exact hxg.symm
        · exact hxh.symm
      cases hA : A j with
      | true => rw [hca x j hj hjZ hA, hVa x j hj hA, ih _ ha (by omega), ih _ hb (by omega)]
      | false => rw [hco x j hj hjZ hA, hVo x j hj hA, ih _ ha (by omega), ih _ hb (by omega)]
  have P5 : ∀ j < N, lo V (graphFun G ∅) (n + j) → ∀ x, V x (n + j) = true →
      c x (n + j) = false → ∃ k < N, A k = true ∧ lo V (graphFun G ∅) (n + k) ∧
        V x (n + k) = true ∧ c x (n + k) = false := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hl x hV hc
      obtain ⟨ha, hb⟩ := hab j hj
      have hjZ : j ∉ Z := by
        intro hjZ
        rcases hZ j hjZ with rfl | rfl
        · exact hgl hl
        · exact hhl hl
      cases hA : A j with
      | true => exact ⟨j, hj, hA, hl, hV, hc⟩
      | false =>
        obtain ⟨l1, l2⟩ := hLa j hj hA hl
        rw [hco x j hj hjZ hA, Bool.or_eq_false_iff] at hc
        rw [hVo x j hj hA, Bool.or_eq_true] at hV
        have go : ∀ w, w < n + j → lo V (graphFun G ∅) w → V x w = true → c x w = false →
            ∃ k < N, A k = true ∧ lo V (graphFun G ∅) (n + k) ∧
              V x (n + k) = true ∧ c x (n + k) = false := by
          intro w hw l hv hcc
          by_cases h9 : w < n
          · exact absurd l (hin w h9)
          obtain ⟨i, rfl⟩ : ∃ i, w = n + i := ⟨w - n, by omega⟩
          exact ih i (by omega) (by omega) l x hv hcc
        rcases hV with h | h
        · exact go _ ha l1 h hc.1
        · exact go _ hb l2 h hc.2
  -- what the rebuilt circuit needs
  have main : ∀ (a' b' : ℕ → ℕ) (L : ℕ → List ℕ) (k0 : ℕ),
      (∀ j < N, a' j < n + j ∧ b' j < n + j) → (∀ j, j ≠ k0 → a' j = a j ∧ b' j = b j) →
      (k0 < N → A k0 = true) →
      (∀ j, ∀ t ∈ L j, t < n) → (∑ j ∈ Finset.range N, (L j).length ≤ 1) →
      (∀ d ∈ Del, ∀ r < N, (a' r = n + d ∨ b' r = n + d) → r ∈ Del ∨ d = g ∨ d = h) →
      (∀ x, k0 < N → k0 ∉ Del → c x (n + k0) = true →
        (∀ w < n + k0, (∀ d ∈ Del, w = n + d → d = g ∨ d = h) → c x w = true →
          u n A a' b' Del L (List.ofFn x) w = true) →
        u n A a' b' Del L (List.ofFn x) (n + k0) = true) →
      (∀ x, k0 < N → k0 ∉ Del →
        (∀ w < n + k0, ¬ lo V (graphFun G ∅) w → u n A a' b' Del L (List.ofFn x) w = true →
          c x w = true) →
        u n A a' b' Del L (List.ofFn x) (n + k0) = true →
          graphFun G ∅ x = true ∧ lo V (graphFun G ∅) (n + k0)) →
      (k0 < N → lo V (graphFun G ∅) (n + k0)) → (∀ j, j ≠ k0 → L j = []) →
      (c (EdgeOwnership.pairInput ta tb) (n + o) = true ∨ (k0 < N ∧ 
        ((∀ w < n + k0, (∀ d ∈ Del, w = n + d → d = g ∨ d = h) →
          c (EdgeOwnership.pairInput ta tb) w = true →
          u n A a' b' Del L (List.ofFn (EdgeOwnership.pairInput ta tb)) w = true) →
        u n A a' b' Del L (List.ofFn (EdgeOwnership.pairInput ta tb)) (n + k0) = true))) →
      ∃ (gs : List Gate) (w' : ℕ), Ok n gs ∧ w' < n + gs.length ∧
        gs.length + Del.card + R.card ≤ N + 1 ∧
        (∀ x : Fin n → Bool, (run gs (List.ofFn x)).getD w' false = true → graphFun G ∅ x = true) ∧
        (∀ x y : Fin n → Bool, (∀ t, x t = true → y t = true) →
          (run gs (List.ofFn x)).getD w' false = true →
          (run gs (List.ofFn y)).getD w' false = true) ∧
        (run gs (List.ofFn (EdgeOwnership.pairInput ta tb))).getD w' false = true ∧
        ∀ p q, G.Adj p q → V (EdgeOwnership.pairInput p q) (n + g) = false →
          V (EdgeOwnership.pairInput p q) (n + h) = false →
          (run gs (List.ofFn (EdgeOwnership.pairInput p q))).getD w' false = true := by
    intro a' b' L k0 hab' hsame hk0A hLn hLs hDr' hk0c hk0u hk0l hL0 hpair
    have hR' : ∀ j ∈ R, A j = false ∧ j ∉ Del ∧ ∃ d ∈ Del, d < j ∧
        (a' j = n + d ∨ b' j = n + d) := by
      intro j hj
      obtain ⟨h1, h2, h3⟩ := hR j hj
      have : j ≠ k0 := by
        rintro rfl
        rw [hk0A (hRN j hj)] at h1; cases h1
      obtain ⟨e1, e2⟩ := hsame j this
      rw [e1, e2]; exact ⟨h1, h2, h3⟩
    obtain ⟨gs, m, hok, hm, _, hcount, _⟩ :=
      build n A a' b' Del R L (graphFun G ∅) hLn hR' N hab'
    have Uc : ∀ w < n + N, ∀ x : Fin n → Bool, u n A a' b' Del L (List.ofFn x) w = true →
        (lo V (graphFun G ∅) w → graphFun G ∅ x = true) ∧
        (¬ lo V (graphFun G ∅) w → c x w = true) := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw x hx
        by_cases h9 : w < n
        · rw [u_in h9] at hx
          exact ⟨fun hl => absurd hl (hin w h9), fun _ => by rw [hcin x w h9]; exact hx⟩
        obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < N := by omega
        obtain ⟨ha', hb'⟩ := hab' j hj
        by_cases hd : j ∈ Del
        · rw [u_del hd] at hx; cases hx
        have hjZ : j ∉ Z := by
          intro hz
          rcases hZ j hz with rfl | rfl
          · exact hd hgD
          · exact hd hhD
        by_cases hjk : j = k0
        · subst hjk
          obtain ⟨q1, q2⟩ := hk0u x hj hd (fun w hw hl hu => (ih w hw (by omega) x hu).2 hl) hx
          exact ⟨fun _ => q1, fun hl => absurd q2 hl⟩
        obtain ⟨e1, e2⟩ := hsame j hjk
        rw [e1] at ha'
        rw [e2] at hb'
        cases hA : A j with
        | true =>
          obtain ⟨l1, l2⟩ := H3 j hj hA
          rw [u_and hd hA (hab' j hj).1 (hab' j hj).2, hL0 j hjk, e1, e2] at hx
          simp only [List.any_nil, Bool.or_false, Bool.and_eq_true] at hx
          have c1 := (ih _ ha' (by omega) x hx.1).2 l1
          have c2 := (ih _ hb' (by omega) x hx.2).2 l2
          have cc : c x (n + j) = true := by rw [hca x j hj hjZ hA, c1, c2]; rfl
          exact ⟨fun hl => hl x (cV _ hw x cc), fun _ => cc⟩
        | false =>
          rw [u_or hd hA (hab' j hj).1 (hab' j hj).2, e1, e2, Bool.or_eq_true] at hx
          refine ⟨fun hl => ?_, fun hl => ?_⟩
          · obtain ⟨l1, l2⟩ := hLa j hj hA hl
            rcases hx with h1 | h1
            · exact (ih _ ha' (by omega) x h1).1 l1
            · exact (ih _ hb' (by omega) x h1).1 l2
          · obtain ⟨l1, l2⟩ := HL j hj hA hl
            rw [hco x j hj hjZ hA, Bool.or_eq_true]
            rcases hx with h1 | h1
            · exact Or.inl ((ih _ ha' (by omega) x h1).2 l1)
            · exact Or.inr ((ih _ hb' (by omega) x h1).2 l2)
    have P2 : ∀ w < n + N, (∀ d ∈ Del, w = n + d → d = g ∨ d = h) → ∀ x : Fin n → Bool,
        c x w = true → u n A a' b' Del L (List.ofFn x) w = true := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw hdl x hx
        by_cases h9 : w < n
        · rw [u_in h9, ← hcin x w h9]; exact hx
        obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < N := by omega
        by_cases hjZ : j ∈ Z
        · rw [hcZ x j hjZ] at hx; cases hx
        have hd : j ∉ Del := by
          intro hd
          rcases hdl j hd rfl with rfl | rfl
          · exact hjZ hgZ
          · exact hjZ hhZ
        by_cases hjk : j = k0
        · subst hjk
          exact hk0c x hj hd hx fun w hw hdw hc => ih w hw (by omega) hdw x hc
        obtain ⟨e1, e2⟩ := hsame j hjk
        obtain ⟨ha, hb⟩ := hab j hj
        have ia := ih (a j) ha (by omega) (fun d hdd h' =>
          (hDr d hdd j hj (Or.inl h')).resolve_left hd) x
        have ib := ih (b j) hb (by omega) (fun d hdd h' =>
          (hDr d hdd j hj (Or.inr h')).resolve_left hd) x
        cases hA : A j with
        | true =>
          rw [hca x j hj hjZ hA, Bool.and_eq_true] at hx
          rw [u_and hd hA (hab' j hj).1 (hab' j hj).2, e1, e2, ia hx.1, ib hx.2]; rfl
        | false =>
          rw [hco x j hj hjZ hA, Bool.or_eq_true] at hx
          rw [u_or hd hA (hab' j hj).1 (hab' j hj).2, e1, e2, Bool.or_eq_true]
          exact hx.imp ia ib
    have P3 : ∀ i j, N - j = i → j < N → lo V (graphFun G ∅) (n + j) → ∀ x : Fin n → Bool,
        u n A a' b' Del L (List.ofFn x) (n + j) = true →
        u n A a' b' Del L (List.ofFn x) (n + o) = true := by
      intro i
      induction i using Nat.strong_induction_on with
      | _ i ih =>
        intro j hi hj hl x hx
        rcases hread j hj with h | ⟨r, hr, hrj⟩
        · rw [← h]; exact hx
        have hjr : j < r := by
          obtain ⟨h1, h2⟩ := hab r hr
          rcases hrj with h | h <;> omega
        cases hA : A r with
        | true =>
          obtain ⟨h1, h2⟩ := H3 r hr hA
          rcases hrj with h | h
          · rw [h] at h1; exact absurd hl h1
          · rw [h] at h2; exact absurd hl h2
        | false =>
          have hrl : lo V (graphFun G ∅) (n + r) := by
            by_contra hh
            obtain ⟨h1, h2⟩ := HL r hr hA hh
            rcases hrj with h | h
            · rw [h] at h1; exact h1 hl
            · rw [h] at h2; exact h2 hl
          have hrd : r ∉ Del := fun h => Dlo _ r rfl h hrl
          have hrk : r ≠ k0 := by
            rintro rfl
            rw [hk0A hr] at hA; cases hA
          obtain ⟨e1, e2⟩ := hsame r hrk
          refine ih (N - r) (by omega) r rfl hr hrl x ?_
          rw [u_or hrd hA (hab' r hr).1 (hab' r hr).2, e1, e2, Bool.or_eq_true]
          rcases hrj with h | h
          · left; rw [h]; exact hx
          · right; rw [h]; exact hx
    have hodl : ∀ d ∈ Del, n + o = n + d → d = g ∨ d = h := fun d hd h' =>
      absurd (by omega : d = o) (hDel d hd).2
    obtain ⟨hm1, hm2⟩ := hm (n + o) (by omega)
    have hp : u n A a' b' Del L (List.ofFn (EdgeOwnership.pairInput ta tb)) (n + o) = true := by
      rcases hpair with hc | ⟨hk, hc⟩
      · exact P2 _ (by omega) hodl _ hc
      · exact P3 _ k0 rfl hk (hk0l hk) _ (hc fun w hw hdw => P2 w (by omega) hdw _)
    rcases hmo : m (n + o) with _ | w'
    · exfalso
      have := hm2 (EdgeOwnership.pairInput ta tb)
      rw [hmo, hp] at this
      cases this
    have hv : ∀ x : Fin n → Bool, (run gs (List.ofFn x)).getD w' false =
        u n A a' b' Del L (List.ofFn x) (n + o) := by
      intro x
      have := hm2 x
      rw [hmo] at this
      exact this
    refine ⟨gs, w', hok, hm1 w' hmo, ?_, fun x hx => ?_, fun x y hxy hx => ?_, ?_, ?_⟩
    · have e1 : (Finset.range N).filter (· ∈ Del) = Del := by
        ext d; simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨fun h => h.2, fun h => ⟨(hDel d h).1, h⟩⟩
      have e2 : (Finset.range N).filter (· ∈ R) = R := by
        ext d; simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨fun h => h.2, fun h => ⟨hRN d h, h⟩⟩
      rw [e1, e2] at hcount
      omega
    · rw [hv x] at hx
      exact (Uc _ (by omega) x hx).1 hlo
    · rw [hv] at hx ⊢
      refine u_mono hab' _ _ ?_ _ (by omega) hx
      intro t ht
      by_cases htn : t < n
      · rw [gDv _ t htn] at ht ⊢; exact hxy _ ht
      · rw [List.getD_eq_default _ _ (by simpa using htn)] at ht; cases ht
    · rw [hv]; exact hp
    · intro p q hpq hg0 hh0
      rw [hv]
      refine P2 _ (by omega) hodl _ ?_
      rw [Ag2 _ hg0 hh0 _ (by omega), hout]
      exact (gf G _).2 ⟨p, q, hpq, by simp [EdgeOwnership.pairInput],
        by simp [EdgeOwnership.pairInput]⟩
  -- the three cases
  by_cases hc0 : c (EdgeOwnership.pairInput ta tb) (n + o) = true
  · exact main a b (fun _ => []) N hab (fun _ _ => ⟨rfl, rfl⟩) (fun h => absurd h (lt_irrefl _))
      (by simp) (by simp) hDr (fun _ h => absurd h (lt_irrefl _))
      (fun _ h => absurd h (lt_irrefl _)) (fun h => absurd h (lt_irrefl _)) (fun _ _ => rfl)
      (Or.inl hc0)
  have hFab : graphFun G ∅ (EdgeOwnership.pairInput ta tb) = true :=
    (gf G _).2 ⟨ta, tb, hadj, by simp [EdgeOwnership.pairInput], by simp [EdgeOwnership.pairInput]⟩
  obtain ⟨k, hkN, hkA, hkl, hkV, hkc⟩ := P5 o hoN hlo (EdgeOwnership.pairInput ta tb)
    (by rw [hout]; exact hFab) (by simpa using hc0)
  have hkZ : k ∉ Z := by
    intro hz
    rcases hZ k hz with rfl | rfl
    · exact hgl hkl
    · exact hhl hkl
  have hkD : k ∉ Del := fun hd => Dlo _ k rfl hd hkl
  -- p: the operand reaching g, q: the other
  obtain ⟨p, q, hpq, hpk, hqk, hRp⟩ : ∃ p q, ((a k = p ∧ b k = q) ∨ (a k = q ∧ b k = p)) ∧
      p < n + k ∧ q < n + k ∧ Re p := by
    obtain ⟨ha, hb⟩ := hab k hkN
    by_contra hcon
    have n1 : ¬ Re (a k) := fun h => hcon ⟨a k, b k, Or.inl ⟨rfl, rfl⟩, ha, hb, h⟩
    have n2 : ¬ Re (b k) := fun h => hcon ⟨b k, a k, Or.inr ⟨rfl, rfl⟩, hb, ha, h⟩
    obtain ⟨l1, l2⟩ := H3 k hkN hkA
    rw [hca _ k hkN hkZ hkA, Ag _ (by omega) l1 n1 _ hhab, Ag _ (by omega) l2 n2 _ hhab,
      ← hVa _ k hkN hkA, hkV] at hkc
    cases hkc
  have Vk : ∀ x, V x (n + k) = (V x p && V x q) := by
    intro x
    rw [hVa x k hkN hkA]
    rcases hpq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    exact Bool.and_comm _ _
  have ck : ∀ x, c x (n + k) = (c x p && c x q) := by
    intro x
    rw [hca x k hkN hkZ hkA]
    rcases hpq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2]
    exact Bool.and_comm _ _
  have lpq : ¬ lo V (graphFun G ∅) p ∧ ¬ lo V (graphFun G ∅) q := by
    obtain ⟨l1, l2⟩ := H3 k hkN hkA
    rcases hpq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1] at l1 <;> rw [e2] at l2
    · exact ⟨l1, l2⟩
    · exact ⟨l2, l1⟩
  have hRq : ¬ Re q := by
    intro hr
    refine hgl fun x hx => hkl x ?_
    rw [Vk, hRm p (by omega) hRp x hx, hRm q (by omega) hr x hx]; rfl
  have hpqD : ∀ w, (w = p ∨ w = q) → ∀ d ∈ Del, w = n + d → d = g ∨ d = h := by
    intro w hw d hd hwd
    refine (hDr d hd k hkN ?_).resolve_left hkD
    rcases hpq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hw with rfl | rfl <;> omega
  -- letters of q
  have cq : c (EdgeOwnership.pairInput ta tb) q = true := by
    rw [Ag q (by omega) lpq.2 hRq _ hhab]
    rw [Vk, Bool.and_eq_true] at hkV
    exact hkV.2
  have key : ∀ i : Fin n, c (fun t => decide (t = i)) q = true →
      i ≠ ta ∧ i ≠ tw ∧ (G.Adj i ta ∨ G.Adj i tw) := by
    intro i hi
    have hx : ∀ x : Fin n → Bool, x ta = true → x tw = true → x i = true →
        graphFun G ∅ x = true := by
      intro x x1 x2 x3
      refine hkl x ?_
      have Vmono : ∀ w < n + N, ∀ x y : Fin n → Bool, (∀ t, x t = true → y t = true) →
          V x w = true → V y w = true := by
        intro w
        induction w using Nat.strong_induction_on with
        | _ w ih =>
          intro hw x y hxy hx
          by_cases h9 : w < n
          · rw [hVin _ w h9, gDv _ w h9] at hx ⊢; exact hxy _ hx
          obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
          have hj : j < N := by omega
          obtain ⟨ha, hb⟩ := hab j hj
          have ia := ih _ ha (by omega) x y hxy
          have ib := ih _ hb (by omega) x y hxy
          cases hA : A j with
          | true =>
            rw [hVa _ j hj hA, Bool.and_eq_true] at hx ⊢
            exact ⟨ia hx.1, ib hx.2⟩
          | false =>
            rw [hVo _ j hj hA, Bool.or_eq_true] at hx ⊢
            exact hx.imp ia ib
      have v1 : V x (n + g) = true := by
        refine Vmono _ ?_ _ x (fun t ht => ?_) hgaw
        · have := (hDel g hgD).1; omega
        · have : t = ta ∨ t = tw := by simpa [EdgeOwnership.pairInput] using ht
          rcases this with rfl | rfl <;> assumption
      have v2 : V x q = true := by
        refine Vmono q (by omega) _ x (fun t ht => ?_) (cV q (by omega) _ hi)
        have : t = i := by simpa using ht
        rw [this]; exact x3
      rw [Vk, hRm p (by omega) hRp x v1, v2]; rfl
    have hne : i ≠ ta ∧ i ≠ tw := by
      rw [← not_or]
      intro hi'
      have := hx (EdgeOwnership.pairInput ta tw) (by simp [EdgeOwnership.pairInput])
        (by simp [EdgeOwnership.pairInput]) (by simpa [EdgeOwnership.pairInput] using hi')
      obtain ⟨p', q', hpq', h1, h2⟩ := (gf G _).1 this
      have h1' : p' = ta ∨ p' = tw := by simpa [EdgeOwnership.pairInput] using h1
      have h2' : q' = ta ∨ q' = tw := by simpa [EdgeOwnership.pairInput] using h2
      rcases h1' with rfl | rfl <;> rcases h2' with rfl | rfl
      · exact G.irrefl hpq'
      · exact hnaw hpq'
      · exact hnaw hpq'.symm
      · exact G.irrefl hpq'
    refine ⟨hne.1, hne.2, ?_⟩
    have := hx (fun t => decide (t = ta ∨ t = tw ∨ t = i)) (by simp) (by simp) (by simp)
    obtain ⟨p', q', hpq', h1, h2⟩ := (gf G _).1 this
    have h1' : p' = ta ∨ p' = tw ∨ p' = i := by simpa using h1
    have h2' : q' = ta ∨ q' = tw ∨ q' = i := by simpa using h2
    rcases h1' with rfl | rfl | rfl <;> rcases h2' with rfl | rfl | rfl
    · exact absurd hpq' G.irrefl
    · exact absurd hpq' hnaw
    · exact Or.inl hpq'.symm
    · exact absurd hpq'.symm hnaw
    · exact absurd hpq' G.irrefl
    · exact Or.inr hpq'.symm
    · exact Or.inl hpq'
    · exact Or.inr hpq'
    · exact absurd hpq' G.irrefl
  have cqb : c (fun t => decide (t = tb)) q = true := by
    obtain ⟨i, h1, h2⟩ := Lt q (by omega) lpq.2 _ cq
    have : i = ta ∨ i = tb := by simpa [EdgeOwnership.pairInput] using h1
    rcases this with rfl | rfl
    · exact absurd rfl (key i h2).1
    · exact h2
  by_cases hp0 : ∃ x, c x p = true
  · -- widen k by the letter ta
    obtain ⟨x0, hx0⟩ := hp0
    obtain ⟨s1, _, hs1⟩ := Lt p (by omega) lpq.1 x0 hx0
    have adj12 : ∀ i : Fin n, c (fun t => decide (t = i)) q = true → G.Adj s1 i := by
      intro i hi
      have hmono : ∀ (j : Fin n) (w : ℕ), w < n + N → c (fun t => decide (t = j)) w = true →
          ∀ y : Fin n → Bool, y j = true → c y w = true := by
        intro j w hw hc y hy
        refine u_mono hab _ _ ?_ w hw hc
        intro t ht
        by_cases htn : t < n
        · rw [gDv _ t htn] at ht ⊢
          have : (⟨t, htn⟩ : Fin n) = j := by simpa using ht
          rw [this]; exact hy
        · rw [List.getD_eq_default _ _ (by simpa using htn)] at ht; cases ht
      have e1 := hmono s1 p (by omega) hs1 (EdgeOwnership.pairInput s1 i)
        (by simp [EdgeOwnership.pairInput])
      have e2 := hmono i q (by omega) hi (EdgeOwnership.pairInput s1 i)
        (by simp [EdgeOwnership.pairInput])
      have : graphFun G ∅ (EdgeOwnership.pairInput s1 i) = true := by
        refine hkl _ (cV _ (by omega) _ ?_)
        rw [ck, e1, e2]; rfl
      obtain ⟨p', q', hpq', h1, h2⟩ := (gf G _).1 this
      have h1' : p' = s1 ∨ p' = i := by simpa [EdgeOwnership.pairInput] using h1
      have h2' : q' = s1 ∨ q' = i := by simpa [EdgeOwnership.pairInput] using h2
      rcases h1' with rfl | rfl <;> rcases h2' with rfl | rfl
      · exact absurd hpq' G.irrefl
      · exact hpq'
      · exact hpq'.symm
      · exact absurd hpq' G.irrefl
    have adja : ∀ i : Fin n, c (fun t => decide (t = i)) q = true → G.Adj i ta := by
      intro i hi
      rcases (key i hi).2.2 with h' | h'
      · exact h'
      · exfalso
        have c1 := hs _ _ (adj12 i hi)
        have c2 := hs _ _ (adj12 tb cqb)
        have c3 := hs _ _ h'
        rw [hstw] at c3
        revert c1 c2 c3
        generalize s s1 = e1
        generalize s i = e2
        generalize s tb = e3
        revert e1 e2 e3
        decide
    let a' : ℕ → ℕ := fun j => if j = k then p else a j
    let b' : ℕ → ℕ := fun j => if j = k then q else b j
    let L : ℕ → List ℕ := fun j => if j = k then [ta.val] else []
    have ea : a' k = p := if_pos rfl
    have eb : b' k = q := if_pos rfl
    have eL : L k = [ta.val] := if_pos rfl
    have hab' : ∀ j < N, a' j < n + j ∧ b' j < n + j := by
      intro j hj
      by_cases hjk : j = k
      · subst hjk; rw [ea, eb]; exact ⟨hpk, hqk⟩
      · simp only [a', b', if_neg hjk]; exact hab j hj
    have uk : ∀ x : Fin n → Bool, u n A a' b' Del L (List.ofFn x) (n + k) =
        ((u n A a' b' Del L (List.ofFn x) p || x ta) && u n A a' b' Del L (List.ofFn x) q) := by
      intro x
      have := u_and (L := L) (x := List.ofFn x) hkD hkA (hab' k hkN).1 (hab' k hkN).2
      rw [ea, eb, eL] at this
      rw [this]
      simp only [List.any_cons, List.any_nil, Bool.or_false, gD]
    refine main a' b' L k hab' ?_ (fun _ => hkA) ?_ ?_ ?_ ?_ ?_ (fun _ => hkl) ?_ (Or.inr ⟨hkN, ?_⟩)
    · intro j hj; simp only [a', b', if_neg hj, and_self]
    · intro j t ht
      by_cases hjk : j = k
      · simp only [L, if_pos hjk, List.mem_singleton] at ht
        rw [ht]; exact ta.isLt
      · simp [L, if_neg hjk] at ht
    · rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.2 hkN)
        (fun j _ hj => by simp [L, if_neg hj]), eL]
      simp
    · intro d hd r hr hrd
      by_cases hrk : r = k
      · subst hrk
        rw [ea, eb] at hrd
        refine hDr d hd r hr ?_
        rcases hpq with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hrd with hrd | hrd <;> omega
      · simp only [a', b', if_neg hrk] at hrd
        exact hDr d hd r hr hrd
    · intro x _ _ hx hall
      rw [ck, Bool.and_eq_true] at hx
      rw [uk, hall p hpk (hpqD p (Or.inl rfl)) hx.1, hall q hqk (hpqD q (Or.inr rfl)) hx.2]; rfl
    · intro x _ _ hall hx
      refine ⟨?_, hkl⟩
      rw [uk, Bool.and_eq_true, Bool.or_eq_true] at hx
      have hq1 := hall q hqk lpq.2 hx.2
      rcases hx.1 with h1 | h1
      · refine hkl x (cV _ (by omega) x ?_)
        rw [ck, hall p hpk lpq.1 h1, hq1]; rfl
      · obtain ⟨i, h2, h3⟩ := Lt q (by omega) lpq.2 x hq1
        exact (gf G x).2 ⟨i, ta, adja i h3, h2, h1⟩
    · intro j hj; simp only [L, if_neg hj]
    · intro hall
      rw [uk, hall q hqk (hpqD q (Or.inr rfl)) cq]
      simp [EdgeOwnership.pairInput]
  · -- k is dead without g and h: make it the AND of ta and tb
    let a' : ℕ → ℕ := fun j => if j = k then ta.val else a j
    let b' : ℕ → ℕ := fun j => if j = k then tb.val else b j
    have ea : a' k = ta.val := if_pos rfl
    have eb : b' k = tb.val := if_pos rfl
    have hab' : ∀ j < N, a' j < n + j ∧ b' j < n + j := by
      intro j hj
      by_cases hjk : j = k
      · subst hjk; rw [ea, eb]; have := ta.isLt; have := tb.isLt; omega
      · simp only [a', b', if_neg hjk]; exact hab j hj
    have uk : ∀ x : Fin n → Bool, u n A a' b' Del (fun _ => []) (List.ofFn x) (n + k) =
        (x ta && x tb) := by
      intro x
      have := u_and (L := fun _ => []) (x := List.ofFn x) hkD hkA (hab' k hkN).1 (hab' k hkN).2
      rw [ea, eb, u_in ta.isLt, u_in tb.isLt, gD, gD] at this
      rw [this]; simp
    refine main a' b' (fun _ => []) k hab' ?_ (fun _ => hkA) (by simp) (by simp) ?_ ?_ ?_
      (fun _ => hkl) (fun _ _ => rfl) (Or.inr ⟨hkN, ?_⟩)
    · intro j hj; simp only [a', b', if_neg hj, and_self]
    · intro d hd r hr hrd
      by_cases hrk : r = k
      · subst hrk
        rw [ea, eb] at hrd
        have := ta.isLt; have := tb.isLt
        omega
      · simp only [a', b', if_neg hrk] at hrd
        exact hDr d hd r hr hrd
    · intro x _ _ hx _
      rw [ck, Bool.and_eq_true] at hx
      exact absurd ⟨x, hx.1⟩ hp0
    · intro x _ _ _ hx
      refine ⟨?_, hkl⟩
      rw [uk, Bool.and_eq_true] at hx
      exact (gf G x).2 ⟨ta, tb, hadj, hx.1, hx.2⟩
    · intro _
      rw [uk]; simp [EdgeOwnership.pairInput]

theorem star1 (n : ℕ) (gs : List Gate) (w : ℕ) (hok : Ok n gs) (hw : w < n + gs.length)
    (p q r : Fin n) : ∃ (hs : List Gate) (w' : ℕ), Ok n hs ∧ hs.length = gs.length + 3 ∧
      w' < n + hs.length ∧ ∀ x : Fin n → Bool, (run hs (List.ofFn x)).getD w' false =
        ((run gs (List.ofFn x)).getD w false || (x r && (x p || x q))) := by
  have hp := p.isLt; have hq := q.isLt; have hr := r.isLt
  have o1 := ok_snoc hok (o := GateOp.or) (s := p.val) (t := q.val) (Or.inr rfl) (by omega) (by omega)
  have l1 : (gs ++ [(⟨GateOp.or, [p.val, q.val]⟩ : Gate)]).length = gs.length + 1 := by simp
  have o2 := ok_snoc o1 (o := GateOp.and) (s := r.val) (t := n + gs.length) (Or.inl rfl)
    (by omega) (by omega)
  have l2 : (gs ++ [(⟨GateOp.or, [p.val, q.val]⟩ : Gate)] ++
    [(⟨GateOp.and, [r.val, n + gs.length]⟩ : Gate)]).length = gs.length + 2 := by simp
  have o3 := ok_snoc o2 (o := GateOp.or) (s := w) (t := n + (gs.length + 1)) (Or.inr rfl)
    (by omega) (by omega)
  refine ⟨_, n + (gs.length + 2), o3, by simp, by simp, fun x => ?_⟩
  have v1 := ov_new gs n (List.ofFn x) (by simp) GateOp.or p.val q.val (by omega) (by omega)
  have v2 := ov_new (gs ++ [(⟨GateOp.or, [p.val, q.val]⟩ : Gate)]) n (List.ofFn x) (by simp)
    GateOp.and r.val (n + gs.length) (by omega) (by omega)
  have v3 := ov_new (gs ++ [(⟨GateOp.or, [p.val, q.val]⟩ : Gate)] ++
    [(⟨GateOp.and, [r.val, n + gs.length]⟩ : Gate)]) n (List.ofFn x) (by simp)
    GateOp.or w (n + (gs.length + 1)) (by omega) (by omega)
  rw [l1] at v2
  rw [l2] at v3
  unfold ov at v1 v2 v3
  simp only at v1 v2 v3
  rw [v3, v2, v1, List.append_assoc, run_prefix gs _ _ w (by simpa using hw),
    run_input _ _ p.val (by simp), run_input _ _ q.val (by simp), run_input _ _ r.val (by simp),
    gD, gD, gD]
  simp [GateOp.eval]

theorem orR_mono {n : ℕ} {C : Circuit} (hC : TopForm.IsAO2 n C) (x : Fin n → Bool) (g : ℕ) :
    ∀ j, j < C.gates.length → g ∈ (CleanedNonEdge.orSets n C).getD j [] →
    (run C.gates (List.ofFn x)).getD (n + g) false = true →
    (run C.gates (List.ofFn x)).getD (n + j) false = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hg hx
    rcases ((orS n C.gates).2 j hj g).1 hg with rfl | ⟨hop, w, hw, q2, q3, q4⟩
    · exact hx
    · have := ih (w - n) (by omega) (by omega) q4 hx
      rw [show n + (w - n) = w by omega] at this
      obtain ⟨g1, g2, g3, g4, _⟩ := gate2 hC hj
      rw [g1] at hop hw
      rw [veq n C.gates x j hj _ _ _ (g1.trans (gate_eta hop g2)) g3 g4]
      rw [g2] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;>
        simp only [GateOp.eval, List.any_cons, id, this, Bool.true_or, Bool.or_true]

theorem orR_reader {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ j, j < C.gates.length → g ∈ (CleanedNonEdge.orSets n C).getD j [] → j ≠ g →
    ∃ r < C.gates.length, (gateAt C r).op = GateOp.or ∧ n + g ∈ (gateAt C r).inputs ∧
      r ∈ (CleanedNonEdge.orSets n C).getD j [] := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hg hne
    have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
    rcases ((orS n C.gates).2 j hj g).1 hg with rfl | ⟨hop, w, hw, q2, q3, q4⟩
    · exact absurd rfl hne
    · by_cases hwg : w - n = g
      · refine ⟨j, hj, by rw [e]; exact hop, ?_, (((orS n C.gates).2 j hj j)).2 (Or.inl rfl)⟩
        rw [e, ← hwg, show n + (w - n) = w by omega]; exact hw
      · obtain ⟨r, h1, h2, h3, h4⟩ := ih (w - n) (by omega) (by omega) q4 hwg
        exact ⟨r, h1, h2, h3, (((orS n C.gates).2 j hj r)).2 (Or.inr ⟨hop, w, hw, q2, q3, h4⟩)⟩


theorem ok_ao {n : ℕ} {gs : List Gate} {w : ℕ} (hok : Ok n gs) : TopForm.IsAO2 n ⟨gs, w⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; exact h2
  · intro j hj i hi
    obtain ⟨o', s', t', h1, h2, h3, h4⟩ := hok j hj
    have e1 : gateAt ⟨gs, w⟩ j = gs[j] := List.getD_eq_getElem _ _ hj
    rw [e1, h1] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; rfl

theorem coneI (n : ℕ) (gs : List Gate) :
    (gs.foldl (EdgeOwnership.coneStep n) []).length = gs.length ∧
    ∀ j (hj : j < gs.length) d, d ∈ (gs.foldl (EdgeOwnership.coneStep n) []).getD j [] ↔
      (∃ w ∈ gs[j].inputs, n ≤ w ∧ w < n + j ∧ (d = w - n ∨
        d ∈ (gs.foldl (EdgeOwnership.coneStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => exact ⟨rfl, fun j hj => by simp at hj⟩
  | append_singleton gs g ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    set r := gs.foldl (EdgeOwnership.coneStep n) [] with hr
    have hold : ∀ i, i < gs.length → (EdgeOwnership.coneStep n r g).getD i [] = r.getD i [] := by
      intro i hi
      exact getD_ltz _ _ _ _ (by omega)
    refine ⟨by simp [EdgeOwnership.coneStep, h1], fun j hj d => ?_⟩
    by_cases hlt : j < gs.length
    · rw [hold j hlt, h2 j hlt d, List.getElem_append_left hlt]
      refine exists_congr fun w => and_congr_right fun _ => and_congr_right fun _ =>
        and_congr_right fun hw => ?_
      rw [hold _ (by omega)]
    · have hje : j = gs.length := by simp at hj; omega
      subst hje
      have e : (gs ++ [g])[gs.length] = g := by simp
      rw [e]
      have e2 : (EdgeOwnership.coneStep n r g).getD gs.length [] =
            (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + r.length))).flatMap
              (fun w => (w - n) :: r.getD (w - n) []) := by
        rw [← h1]
        exact getD_at' _ _ _
      rw [e2, List.mem_flatMap]
      simp only [List.mem_filter, decide_eq_true_eq, h1, List.mem_cons]
      refine exists_congr fun w => ?_
      constructor
      · rintro ⟨⟨q1, q2, q3⟩, q4⟩
        exact ⟨q1, q2, q3, by rw [hold _ (by omega)]; exact q4⟩
      · rintro ⟨q1, q2, q3, q4⟩
        rw [hold _ (by omega)] at q4
        exact ⟨⟨q1, q2, q3⟩, q4⟩

theorem cone_trans (n : ℕ) (C : Circuit) : ∀ j, j < C.gates.length → ∀ r i,
    EdgeOwnership.InCone n C r j → EdgeOwnership.InCone n C i r →
    EdgeOwnership.InCone n C i j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj r i hr hi
    obtain ⟨w, q1, q2, q3, q4⟩ := (((coneI n C.gates).2 j hj r)).1 hr
    refine (((coneI n C.gates).2 j hj i)).2 ⟨w, q1, q2, q3, Or.inr ?_⟩
    rcases q4 with rfl | q4
    · exact hi
    · exact ih (w - n) (by omega) (by omega) r i q4 hi

theorem cone_one (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (d : ℕ) (hd : d < j)
    (h : n + d ∈ (gateAt C j).inputs) : EdgeOwnership.InCone n C d j := by
  have e : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  rw [e] at h
  exact (((coneI n C.gates).2 j hj d)).2 ⟨n + d, h, by omega, by omega, Or.inl (by omega)⟩

theorem pr {n : ℕ} {G : SimpleGraph (Fin n)} {p q i j : Fin n} {x : Fin n → Bool} (hij : i ≠ j)
    (h1 : EdgeOwnership.pairInput p q i = true) (h2 : EdgeOwnership.pairInput p q j = true)
    (hpq : G.Adj p q) (hp : x p = true) (hq : x q = true) :
    G.Adj i j ∧ x i = true ∧ x j = true := by
  have h1' : i = p ∨ i = q := by simpa [EdgeOwnership.pairInput] using h1
  have h2' : j = p ∨ j = q := by simpa [EdgeOwnership.pairInput] using h2
  rcases h1' with rfl | rfl <;> rcases h2' with rfl | rfl
  · exact absurd rfl hij
  · exact ⟨hpq, hp, hq⟩
  · exact ⟨hpq.symm, hq, hp⟩
  · exact absurd rfl hij

def un {n : ℕ} (i : Fin n) : Fin n → Bool := fun t => decide (t = i)

theorem un_self {n : ℕ} (i : Fin n) : un i i = true := by simp [un]
theorem un_ne {n : ℕ} {i t : Fin n} (h : t ≠ i) : un i t = false := by simp [un, h]

end PEqualNP.Outside.L_meta_5138

open PEqualNP.Outside.L_meta_5138 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_5138 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g h : ℕ) (z z0 a d w b : Fin n), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsLeastAO G C → PEqualNP.Core.IsLiftFixedPoint G C → z ≠ z0 → z ≠ a → z0 ≠ a → d ≠ w → d ≠ b → w ≠ b → G.Adj z d → G.Adj z w → G.Adj z0 w → G.Adj z0 b → G.Adj a b → g < C.gates.length → h < C.gates.length → g ≠ h → (∀ k : ℕ, k ∈ PEqualNP.TopForm.junk G C ↔ k = g ∨ k = h) → (∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) x = (x z0 || x a) ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) x = (x w || x b) ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C h 0) x = (x z || x z0) ∧ PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C h 1) x = (x w || x d)) → (∀ i : Fin 2, ∀ k < C.gates.length, (PEqualNP.TopForm.opnd C g i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k = g) ∧ (PEqualNP.TopForm.opnd C h i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k = h)) → (∃ T < C.gates.length, ∃ c : Fin 2, (PEqualNP.MetaComplexity.NestedCover.gateAt C T).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C T c) g ∧ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C T (1 - c)) h) → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → n + g ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs ∧ n + h ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs) → (∀ e ∈ [(z0, w), (z0, b), (a, b)], PEqualNP.MetaComplexity.circuitFun n ⟨C.gates.set g ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, C.output⟩ (PEqualNP.EdgeOwnership.pairInput e.1 e.2) = false) → (∀ e ∈ [(z0, w), (z, w), (z, d)], PEqualNP.MetaComplexity.circuitFun n ⟨C.gates.set h ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, C.output⟩ (PEqualNP.EdgeOwnership.pairInput e.1 e.2) = false) → False := by
  intro n G _ C s g h z z0 a d w b hcol hC4 hLeast hLift hzz0 hza hz0a hdw hdb hwb zd zw z0w z0b ab
    hgN hhN hgh hJ hfac hpriv hT hnoand _ _
  classical
  obtain ⟨hAO, hF, hmin⟩ := hLeast
  let V : (Fin n → Bool) → ℕ → Bool := fun x w => (run C.gates (List.ofFn x)).getD w false
  -- colours
  have sw : s w = !(s z0) := by
    have := hcol _ _ z0w; revert this; cases s z0 <;> cases s w <;> simp
  have sb : s b = !(s z0) := by
    have := hcol _ _ z0b; revert this; cases s z0 <;> cases s b <;> simp
  have sz : s z = s z0 := by
    have := hcol _ _ zw; rw [sw] at this; revert this; cases s z0 <;> cases s z <;> simp
  have sa : s a = s z0 := by
    have := hcol _ _ ab; rw [sb] at this; revert this; cases s z0 <;> cases s a <;> simp
  have sd : s d = !(s z0) := by
    have := hcol _ _ zd; rw [sz] at this; revert this; cases s z0 <;> cases s d <;> simp
  have cn : ∀ p q : Fin n, s p = s z0 → s q = !(s z0) → p ≠ q := by
    rintro p q h1 h2 rfl
    rw [h1] at h2; revert h2; cases s z0 <;> simp
  have zw' := cn z w sz sw
  have zb' := cn z b sz sb
  have zd' := cn z d sz sd
  have z0w' := cn z0 w rfl sw
  have z0b' := cn z0 b rfl sb
  have z0d' := cn z0 d rfl sd
  have aw' := cn a w sa sw
  have ab' := cn a b sa sb
  have ad' := cn a d sa sd
  have four : ∀ p q u v : Fin n, p ≠ q → u ≠ v → G.Adj p u → G.Adj p v → G.Adj q u → G.Adj q v →
      False := by
    intro p q u v hpq huv h1 h2 h3 h4
    have := hC4 p q hpq
    have h2c : ({u, v} : Finset (Fin n)).card ≤
        (Finset.univ.filter fun w => G.Adj p w ∧ G.Adj q w).card := by
      refine Finset.card_le_card fun t ht => ?_
      rw [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · simp [h1, h3]
      · simp [h2, h4]
    rw [Finset.card_pair huv] at h2c
    omega
  have naw : ¬ G.Adj a w := fun h' => four a z0 w b hz0a.symm hwb h' ab z0w z0b
  have nz0d : ¬ G.Adj z0 d := fun h' => four z z0 w d hzz0 hdw.symm zw zd z0w h'
  have hgJ : g ∈ TopForm.junk G C := (hJ g).2 (Or.inl rfl)
  have hhJ : h ∈ TopForm.junk G C := (hJ h).2 (Or.inr rfl)
  have hgg := Finset.mem_filter.1 hgJ
  have hhh := Finset.mem_filter.1 hhJ
  have hgA : (gateAt C g).op = GateOp.and := hgg.2.1
  have hhA : (gateAt C h).op = GateOp.and := hhh.2.1
  let A : ℕ → Bool := fun j => decide ((gateAt C j).op = GateOp.and)
  let p0 : ℕ → ℕ := fun j => TopForm.opnd C j 0
  let p1 : ℕ → ℕ := fun j => TopForm.opnd C j 1
  have hA1 : ∀ j, A j = true ↔ (gateAt C j).op = GateOp.and := fun j => by simp [A]
  have hA0 : ∀ j < C.gates.length, A j = false → (gateAt C j).op = GateOp.or := by
    intro j hj h
    rcases (gate2 hAO hj).2.2.2.2 with h1 | h1
    · rw [(hA1 j).2 h1] at h; cases h
    · exact h1
  have hor0 : ∀ j, (gateAt C j).op = GateOp.or → A j = false := by
    intro j h; simp [A, h]
  have hmemi : ∀ j < C.gates.length, ∀ w, w ∈ (gateAt C j).inputs ↔ (p0 j = w ∨ p1 j = w) := by
    intro j hj w
    rw [(gate2 hAO hj).2.1]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact or_congr eq_comm eq_comm
  have hab : ∀ j < C.gates.length, p0 j < n + j ∧ p1 j < n + j := fun j hj =>
    ⟨(gate2 hAO hj).2.2.1, (gate2 hAO hj).2.2.2.1⟩
  have hVa : ∀ x, ∀ j < C.gates.length, A j = true →
      V x (n + j) = (V x (p0 j) && V x (p1 j)) := by
    intro x j hj hA
    obtain ⟨g1, g2, g3, g4, _⟩ := gate2 hAO hj
    have := veq n C.gates x j hj _ _ _ (g1.trans (gate_eta ((hA1 j).1 hA) g2)) g3 g4
    simpa [V, GateOp.eval] using this
  have hVo : ∀ x, ∀ j < C.gates.length, A j = false →
      V x (n + j) = (V x (p0 j) || V x (p1 j)) := by
    intro x j hj hA
    obtain ⟨g1, g2, g3, g4, _⟩ := gate2 hAO hj
    have := veq n C.gates x j hj _ _ _ (g1.trans (gate_eta (hA0 j hj hA) g2)) g3 g4
    simpa [V, GateOp.eval] using this
  have hVin : ∀ x, ∀ w < n, V x w = (List.ofFn x).getD w false := fun x w hw =>
    run_input _ _ _ (by simpa using hw)
  -- the two dirty ANDs and their factors
  have f1 : ∀ x, V x (p0 g) = (x z0 || x a) := fun x => (hfac x).1
  have f2 : ∀ x, V x (p1 g) = (x w || x b) := fun x => (hfac x).2.1
  have f3 : ∀ x, V x (p0 h) = (x z || x z0) := fun x => (hfac x).2.2.1
  have f4 : ∀ x, V x (p1 h) = (x w || x d) := fun x => (hfac x).2.2.2
  have Vg : ∀ x, V x (n + g) = ((x z0 || x a) && (x w || x b)) := fun x => by
    rw [hVa x g hgN ((hA1 g).2 hgA), f1, f2]
  have Vh : ∀ x, V x (n + h) = ((x z || x z0) && (x w || x d)) := fun x => by
    rw [hVa x h hhN ((hA1 h).2 hhA), f3, f4]
  have isg : ∀ (W : ℕ) (p q : Fin n), p ≠ q → (∀ x, V x W = (x p || x q)) → n ≤ W := by
    intro W p q hpq hW
    by_contra hlt
    have hlt' : W < n := by omega
    have e1 := hW (un p)
    have e2 := hW (un q)
    rw [hVin _ _ hlt', gDv _ _ hlt', un_self, Bool.true_or] at e1
    rw [hVin _ _ hlt', gDv _ _ hlt', un_self, Bool.or_true] at e2
    simp only [un, decide_eq_true_eq] at e1 e2
    exact hpq (e1.symm.trans e2)
  obtain ⟨F1, e1⟩ : ∃ F1, p0 g = n + F1 := ⟨p0 g - n, by have := isg _ _ _ hz0a f1; omega⟩
  obtain ⟨F2, e2⟩ : ∃ F2, p1 g = n + F2 := ⟨p1 g - n, by have := isg _ _ _ hwb f2; omega⟩
  obtain ⟨F3, e3⟩ : ∃ F3, p0 h = n + F3 := ⟨p0 h - n, by have := isg _ _ _ hzz0 f3; omega⟩
  obtain ⟨F4, e4⟩ : ∃ F4, p1 h = n + F4 := ⟨p1 h - n, by have := isg _ _ _ hdw.symm f4; omega⟩
  rw [e1] at f1
  rw [e2] at f2
  rw [e3] at f3
  rw [e4] at f4
  have lt1 : F1 < g := by have := (hab g hgN).1; omega
  have lt2 : F2 < g := by have := (hab g hgN).2; omega
  have lt3 : F3 < h := by have := (hab h hhN).1; omega
  have lt4 : F4 < h := by have := (hab h hhN).2; omega
  have dif : ∀ (p q : ℕ) (x : Fin n → Bool), V x (n + p) = true → V x (n + q) = false → p ≠ q := by
    rintro p q x h1 h2 rfl
    rw [h1] at h2; cases h2
  have uz0 : V (un z0) (n + F1) = true ∧ V (un z0) (n + F2) = false ∧ V (un z0) (n + F3) = true ∧
      V (un z0) (n + F4) = false ∧ V (un z0) (n + g) = false ∧ V (un z0) (n + h) = false := by
    rw [f1, f2, f3, f4, Vg, Vh]
    simp [un_self, un_ne hzz0, un_ne hz0a.symm, un_ne z0w'.symm, un_ne z0b'.symm, un_ne z0d'.symm]
  have ua : V (un a) (n + F1) = true ∧ V (un a) (n + F3) = false := by
    rw [f1, f3]
    simp [un_self, un_ne hza, un_ne hz0a]
  have uw : V (un w) (n + F1) = false ∧ V (un w) (n + F2) = true ∧ V (un w) (n + F3) = false ∧
      V (un w) (n + F4) = true ∧ V (un w) (n + g) = false ∧ V (un w) (n + h) = false := by
    rw [f1, f2, f3, f4, Vg, Vh]
    simp [un_self, un_ne zw', un_ne z0w', un_ne aw', un_ne hwb.symm, un_ne hdw]
  have ub : V (un b) (n + F2) = true ∧ V (un b) (n + F4) = false := by
    rw [f2, f4]
    simp [un_self, un_ne hwb, un_ne hdb]
  let Del : Finset ℕ := {g, h, F1, F2, F3, F4}
  have hDm : ∀ j, j ∈ Del ↔ j = g ∨ j = h ∨ j = F1 ∨ j = F2 ∨ j = F3 ∨ j = F4 := fun j => by
    simp [Del]
  have hDc : Del.card = 6 := by
    have n12 := dif F1 F2 _ uz0.1 uz0.2.1
    have n13 := dif F1 F3 _ ua.1 ua.2
    have n14 := dif F1 F4 _ uz0.1 uz0.2.2.2.1
    have n23 := dif F2 F3 _ uw.2.1 uw.2.2.1
    have n24 := dif F2 F4 _ ub.1 ub.2
    have n34 := dif F3 F4 _ uz0.2.2.1 uz0.2.2.2.1
    have g1 := dif F1 g _ uz0.1 uz0.2.2.2.2.1
    have g2 := dif F2 g _ uw.2.1 uw.2.2.2.2.1
    have g3 := dif F3 g _ uz0.2.2.1 uz0.2.2.2.2.1
    have g4 := dif F4 g _ uw.2.2.2.1 uw.2.2.2.2.1
    have h1 := dif F1 h _ uz0.1 uz0.2.2.2.2.2
    have h2 := dif F2 h _ uw.2.1 uw.2.2.2.2.2
    have h3 := dif F3 h _ uz0.2.2.1 uz0.2.2.2.2.2
    have h4 := dif F4 h _ uw.2.2.2.1 uw.2.2.2.2.2
    simp only [Del]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    all_goals simp [*, Ne.symm g1, Ne.symm g2, Ne.symm g3, Ne.symm g4, Ne.symm h1, Ne.symm h2,
      Ne.symm h3, Ne.symm h4]
  -- output
  have hdirty : ∀ j, j ∈ TopForm.junk G C → ¬ lo V (graphFun G ∅) (n + j) := by
    intro j hj hl
    obtain ⟨_, _, _, x, h1, h2⟩ := Finset.mem_filter.1 hj
    have := hl x h1
    rw [this] at h2; cases h2
  have hFall0 : graphFun G ∅ (EdgeOwnership.pairInput a b) = true :=
    (gf G _).2 ⟨a, b, ab, by simp [EdgeOwnership.pairInput], by simp [EdgeOwnership.pairInput]⟩
  have hoV : ∀ x, V x C.output = graphFun G ∅ x := fun x => by
    have := congrFun hF x
    rw [← this]; rfl
  have hlin : ∀ w < n, ¬ lo V (graphFun G ∅) w := by
    intro w hw hl
    have := hl (fun q => decide (q.val = w)) (by
      rw [hVin _ w hw, gD _ ⟨w, hw⟩]; simp)
    obtain ⟨p, q, hpq, h1, h2⟩ := (gf G _).1 this
    simp only [decide_eq_true_eq] at h1 h2
    have : p = q := Fin.ext (h1.trans h2.symm)
    rw [this] at hpq
    exact G.irrefl hpq
  -- in a least circuit every gate but the output is read
  have hread' : ∀ k < C.gates.length, C.output = n + k ∨
      ∃ r < C.gates.length, p0 r = n + k ∨ p1 r = n + k := by
    intro k hk
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hko, hkr⟩ := hcon
    have hkr' : ∀ r < C.gates.length, p0 r ≠ n + k ∧ p1 r ≠ n + k := by
      intro r hr
      rw [← not_or]
      exact fun h => hkr ⟨r, hr, h⟩
    obtain ⟨gs, m, hok, hm, _, hcount, _⟩ := build n A p0 p1 {k} ∅ (fun _ => []) (graphFun G ∅)
      (by simp) (by simp) C.gates.length hab
    have hu : ∀ W < n + C.gates.length, W ≠ n + k → ∀ x : Fin n → Bool,
        u n A p0 p1 {k} (fun _ => []) (List.ofFn x) W = V x W := by
      intro W
      induction W using Nat.strong_induction_on with
      | _ W ih =>
        intro hW hWk x
        by_cases h9 : W < n
        · rw [u_in h9, hVin _ _ h9]
        obtain ⟨j, rfl⟩ : ∃ j, W = n + j := ⟨W - n, by omega⟩
        have hj : j < C.gates.length := by omega
        obtain ⟨h1, h2⟩ := hab j hj
        have hjk : j ∉ ({k} : Finset ℕ) := by
          rw [Finset.mem_singleton]; omega
        have i1 := ih _ h1 (by omega) (hkr' j hj).1 x
        have i2 := ih _ h2 (by omega) (hkr' j hj).2 x
        cases hA : A j with
        | true => rw [u_and hjk hA h1 h2, hVa _ j hj hA, i1, i2]; simp
        | false => rw [u_or hjk hA h1 h2, hVo _ j hj hA, i1, i2]
    have hol : C.output < n + C.gates.length := by
      by_contra hge
      have := hoV (EdgeOwnership.pairInput a b)
      rw [hFall0] at this
      simp only [V] at this
      rw [List.getD_eq_default _ _ (by rw [run_length]; simp; omega)] at this
      cases this
    obtain ⟨hm1, hm2⟩ := hm C.output hol
    rcases hmo : m C.output with _ | w'
    · have := hm2 (EdgeOwnership.pairInput a b)
      rw [hmo, hu _ hol hko, hoV, hFall0] at this
      cases this
    have hle := hmin ⟨gs, w'⟩ (ok_ao hok) (by
      funext x
      have := hm2 x
      rw [hmo, hu _ hol hko, hoV] at this
      exact this)
    have hc1 : ((Finset.range C.gates.length).filter (· ∈ ({k} : Finset ℕ))).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨k, ?_⟩
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
    rw [hc1] at hcount
    simp at hcount
    change C.gates.length ≤ gs.length at hle
    omega
  obtain ⟨o, hoN, hoo⟩ : ∃ o < C.gates.length, C.output = n + o := by
    have hol : C.output < n + C.gates.length := by
      by_contra hge
      have := hoV (EdgeOwnership.pairInput a b)
      rw [hFall0] at this
      simp only [V] at this
      rw [List.getD_eq_default _ _ (by rw [run_length]; simp; omega)] at this
      cases this
    have hon : n ≤ C.output := by
      by_contra hlt
      exact hlin C.output (by omega) fun x hx => by rw [← hoV x]; exact hx
    exact ⟨C.output - n, by omega, by omega⟩
  have hmax : ∀ j < C.gates.length, j ≤ o := by
    intro j hj
    rcases hread' (C.gates.length - 1) (by omega) with h | ⟨r, hr, hrd⟩
    · omega
    · obtain ⟨h1, h2⟩ := hab r hr
      rcases hrd with h | h <;> omega
  have hcone : ∀ i k, C.gates.length - k = i → k < C.gates.length → Core.InOutputCone n C k := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro k hi hk
      rcases hread' k hk with h | ⟨r, hr, hrd⟩
      · exact ⟨hk, Or.inl h⟩
      · have hkr : k < r := by
          obtain ⟨h1, h2⟩ := hab r hr
          rcases hrd with h | h <;> omega
        have h1 := cone_one n C r hr k hkr ((hmemi r hr _).2 hrd)
        refine ⟨hk, Or.inr ⟨by omega, ?_⟩⟩
        have hon : C.output - n = o := by omega
        rw [hon]
        rcases (ih (C.gates.length - r) (by omega) r rfl hr).2 with h2 | ⟨_, h2⟩
        · have : r = o := by omega
          rw [← this]; exact h1
        · rw [hon] at h2
          exact cone_trans n C o hoN r k h2 h1
  have hout : ∀ x, V x (n + o) = graphFun G ∅ x := by
    intro x
    have := congrFun hF x
    rw [← this]
    change _ = (run C.gates (List.ofFn x)).getD C.output false
    rw [hoo]
  have hlout : lo V (graphFun G ∅) (n + o) := fun x hx => by rw [← hout x]; exact hx
  have ones : ∀ w < n + C.gates.length, V (fun _ => true) w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases h9 : w < n
      · rw [hVin _ w h9, gDv _ w h9]
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨h1, h2⟩ := hab j hj
      have i1 := ih _ h1 (by omega)
      have i2 := ih _ h2 (by omega)
      cases hA : A j with
      | true => rw [hVa _ j hj hA, i1, i2]; rfl
      | false => rw [hVo _ j hj hA, i1, i2]; rfl
  have hread : ∀ j < C.gates.length, j = o ∨ ∃ r < C.gates.length, p0 r = n + j ∨ p1 r = n + j := by
    intro j hj
    rcases hread' j hj with h | h
    · left; omega
    · exact Or.inr h
  have hJc : ∀ j < C.gates.length, A j = true → ¬ lo V (graphFun G ∅) (n + j) →
      j = g ∨ j = h := by
    intro j hj hA hl
    refine (hJ j).1 (Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, (hA1 j).1 hA, hj, ?_⟩)
    by_contra hcon
    refine hl fun x hx => ?_
    by_contra hf
    exact hcon ⟨x, hx, by simpa using hf⟩
  have hgl := hdirty g hgJ
  have hhl := hdirty h hhJ
  have HL : ∀ j < C.gates.length, A j = false → ¬ lo V (graphFun G ∅) (n + j) →
      ¬ lo V (graphFun G ∅) (p0 j) ∧ ¬ lo V (graphFun G ∅) (p1 j) := by
    intro j hj hA hl
    have key : ∀ i : Fin 2, ¬ lo V (graphFun G ∅) (TopForm.opnd C j i) := by
      intro i hlw
      refine hLift ⟨j, hj, i, hcone _ j rfl hj, hA0 j hj hA, hl, hlw, fun _ => true, ?_⟩
      have hi : i = 0 ∨ i = 1 := by omega
      have : TopForm.opnd C j i < n + C.gates.length := by
        rcases hi with rfl | rfl
        · have := (gate2 hAO hj).2.2.1; omega
        · have := (gate2 hAO hj).2.2.2.1; omega
      exact ones _ this
    exact ⟨key 0, key 1⟩
  -- no AND has an operand below F: otherwise that AND could be the operand
  have H3 : ∀ j < C.gates.length, A j = true →
      ¬ lo V (graphFun G ∅) (p0 j) ∧ ¬ lo V (graphFun G ∅) (p1 j) := by
    intro t ht hAt
    have goal : ∀ w1, w1 < n + t → (∀ x, V x (n + t) = true → V x w1 = true) →
        ¬ lo V (graphFun G ∅) w1 := by
      intro w1 hw1 hVw hl1
      have htl : lo V (graphFun G ∅) (n + t) := fun x hx => hl1 x (hVw x hx)
      let ρ : ℕ → ℕ := fun W => if W = n + t then w1 else W
      have ρt : ρ (n + t) = w1 := if_pos rfl
      have ρn : ∀ W, W ≠ n + t → ρ W = W := fun W hW => if_neg hW
      have ρle : ∀ W, ρ W ≤ W := by
        intro W
        by_cases hW : W = n + t
        · rw [hW, ρt]; omega
        · rw [ρn W hW]
      have hab' : ∀ j < C.gates.length, ρ (p0 j) < n + j ∧ ρ (p1 j) < n + j := fun j hj => by
        have h1 := ρle (p0 j)
        have h2 := ρle (p1 j)
        obtain ⟨h3, h4⟩ := hab j hj
        omega
      have ρne : ∀ W, ρ W ≠ n + t := by
        intro W
        by_cases hW : W = n + t
        · rw [hW, ρt]; omega
        · rw [ρn W hW]; exact hW
      obtain ⟨gs, m, hok, hm, _, hcount, _⟩ := build n A (fun j => ρ (p0 j)) (fun j => ρ (p1 j))
        {t} ∅ (fun _ => []) (graphFun G ∅) (by simp) (by simp) C.gates.length hab'
      let U : (Fin n → Bool) → ℕ → Bool := fun x W =>
        u n A (fun j => ρ (p0 j)) (fun j => ρ (p1 j)) {t} (fun _ => []) (List.ofFn x) W
      have hU : ∀ W < n + C.gates.length, W ≠ n + t → ∀ x,
          (lo V (graphFun G ∅) W → U x W = true → graphFun G ∅ x = true) ∧
          (¬ lo V (graphFun G ∅) W → U x W = V x W) ∧ (V x W = true → U x W = true) := by
        intro W
        induction W using Nat.strong_induction_on with
        | _ W ih =>
          intro hW hWt x
          by_cases h9 : W < n
          · have : U x W = V x W := by
              rw [hVin _ _ h9]; exact u_in h9
            rw [this]
            exact ⟨fun h => h x, fun _ => rfl, id⟩
          obtain ⟨j, rfl⟩ : ∃ j, W = n + j := ⟨W - n, by omega⟩
          have hj : j < C.gates.length := by omega
          obtain ⟨h1, h2⟩ := hab j hj
          have hjt : j ∉ ({t} : Finset ℕ) := by
            rw [Finset.mem_singleton]; omega
          -- what an operand gives
          have op : ∀ q, q < n + j → (lo V (graphFun G ∅) q → U x (ρ q) = true →
              graphFun G ∅ x = true) ∧ (¬ lo V (graphFun G ∅) q → U x (ρ q) = V x q) ∧
              (V x q = true → U x (ρ q) = true) := by
            intro q hq
            by_cases hqt : q = n + t
            · subst hqt
              rw [ρt]
              obtain ⟨i1, _, i3⟩ := ih w1 (by omega) (by omega) (by omega) x
              exact ⟨fun _ => i1 hl1, fun h => absurd htl h, fun h => i3 (hVw x h)⟩
            · rw [ρn q hqt]
              exact ih q hq (by omega) hqt x
          obtain ⟨a1, a2, a3⟩ := op _ h1
          obtain ⟨b1, b2, b3⟩ := op _ h2
          cases hA : A j with
          | true =>
            have e : U x (n + j) = (U x (ρ (p0 j)) && U x (ρ (p1 j))) := by
              have := u_and (a := fun j => ρ (p0 j)) (b := fun j => ρ (p1 j)) (L := fun _ => [])
                (x := List.ofFn x) hjt hA (hab' j hj).1 (hab' j hj).2
              simpa [U] using this
            have hn : ¬ lo V (graphFun G ∅) (n + j) →
                ¬ lo V (graphFun G ∅) (p0 j) ∧ ¬ lo V (graphFun G ∅) (p1 j) := by
              intro hl
              refine ⟨fun h => hl fun y hy => h y ?_, fun h => hl fun y hy => h y ?_⟩ <;>
                rw [hVa y j hj hA, Bool.and_eq_true] at hy
              · exact hy.1
              · exact hy.2
            refine ⟨fun hl hx => ?_, fun hl => ?_, fun hx => ?_⟩
            · rw [e, Bool.and_eq_true] at hx
              by_cases l1 : lo V (graphFun G ∅) (p0 j)
              · exact a1 l1 hx.1
              by_cases l2 : lo V (graphFun G ∅) (p1 j)
              · exact b1 l2 hx.2
              refine hl x ?_
              rw [hVa x j hj hA, ← a2 l1, ← b2 l2, hx.1, hx.2]; rfl
            · obtain ⟨l1, l2⟩ := hn hl
              rw [e, hVa x j hj hA, a2 l1, b2 l2]
            · rw [hVa x j hj hA, Bool.and_eq_true] at hx
              rw [e, a3 hx.1, b3 hx.2]; rfl
          | false =>
            have e : U x (n + j) = (U x (ρ (p0 j)) || U x (ρ (p1 j))) :=
              u_or hjt hA (hab' j hj).1 (hab' j hj).2
            refine ⟨fun hl hx => ?_, fun hl => ?_, fun hx => ?_⟩
            · have l1 : lo V (graphFun G ∅) (p0 j) := fun y hy => hl y (by
                rw [hVo y j hj hA, hy]; rfl)
              have l2 : lo V (graphFun G ∅) (p1 j) := fun y hy => hl y (by
                rw [hVo y j hj hA, hy, Bool.or_true])
              rw [e, Bool.or_eq_true] at hx
              exact hx.elim (a1 l1) (b1 l2)
            · obtain ⟨l1, l2⟩ := HL j hj hA hl
              rw [e, hVo x j hj hA, a2 l1, b2 l2]
            · rw [hVo x j hj hA, Bool.or_eq_true] at hx
              rw [e, Bool.or_eq_true]
              exact hx.imp a3 b3
      have hUo : ∀ x, U x (ρ C.output) = graphFun G ∅ x := by
        intro x
        rw [Bool.eq_iff_iff]
        by_cases hot : C.output = n + t
        · rw [hot, ρt]
          obtain ⟨i1, _, i3⟩ := hU w1 (by omega) (by omega) x
          refine ⟨i1 hl1, fun hx => i3 (hVw x ?_)⟩
          rw [← hot, hoV]; exact hx
        · rw [ρn _ hot]
          obtain ⟨i1, _, i3⟩ := hU C.output (by omega) hot x
          exact ⟨i1 (fun y hy => by rw [← hoV y]; exact hy), fun hx => i3 (by rw [hoV]; exact hx)⟩
      obtain ⟨hm1, hm2⟩ := hm (ρ C.output) (by have := ρle C.output; omega)
      rcases hmo : m (ρ C.output) with _ | w'
      · have := hm2 (EdgeOwnership.pairInput a b)
        rw [hmo] at this
        have h2 := hUo (EdgeOwnership.pairInput a b)
        rw [hFall0] at h2
        have h3 : (false : Bool) = true := this.trans h2
        cases h3
      have hle := hmin ⟨gs, w'⟩ (ok_ao hok) (by
        funext x
        have := hm2 x
        rw [hmo] at this
        exact this.trans (hUo x))
      have hc1 : ((Finset.range C.gates.length).filter (· ∈ ({t} : Finset ℕ))).card = 1 := by
        rw [Finset.card_eq_one]
        refine ⟨t, ?_⟩
        ext j
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
      rw [hc1] at hcount
      simp at hcount
      change C.gates.length ≤ gs.length at hle
      omega
    refine ⟨goal _ (hab t ht).1 fun x hx => ?_, goal _ (hab t ht).2 fun x hx => ?_⟩ <;>
      rw [hVa x t ht hAt, Bool.and_eq_true] at hx
    · exact hx.1
    · exact hx.2
  -- the two ORs reading g and h on the way to T
  obtain ⟨T, hTN, tc, hTop, hTg, hTh⟩ := hT
  have hTA : A T = true := (hA1 T).2 hTop
  have orl : ∀ (q : ℕ) (i : Fin 2), q = g ∨ q = h → q < C.gates.length →
      CleanedNonEdge.OrReaches n C (TopForm.opnd C T i) q →
      q < T ∧ (∀ x, V x (n + q) = true → V x (TopForm.opnd C T i) = true) ∧
      ∃ r < C.gates.length, (gateAt C r).op = GateOp.or ∧ n + q ∈ (gateAt C r).inputs ∧
        (∀ x, V x (n + r) = true → V x (TopForm.opnd C T i) = true) := by
    intro q i hq hqN hr
    have hi : i = 0 ∨ i = 1 := by omega
    have hlt : TopForm.opnd C T i < n + T := by
      rcases hi with rfl | rfl
      · exact (hab T hTN).1
      · exact (hab T hTN).2
    have hin : TopForm.opnd C T i ∈ (gateAt C T).inputs := by
      rw [(gate2 hAO hTN).2.1]
      rcases hi with rfl | rfl <;> simp
    have hqle := orR_le n C _ _ hr.2
    have hne : TopForm.opnd C T i - n ≠ q := by
      intro e
      have e' : TopForm.opnd C T i = n + q := by have := hr.1; omega
      rw [e'] at hin
      rcases hq with rfl | rfl
      · exact (hnoand T hTN hTop).1 hin
      · exact (hnoand T hTN hTop).2 hin
    have back : ∀ q', q' ∈ (CleanedNonEdge.orSets n C).getD (TopForm.opnd C T i - n) [] →
        ∀ x, V x (n + q') = true → V x (TopForm.opnd C T i) = true := by
      intro q' hq' x hx
      have := orR_mono hAO x q' _ (by omega) hq' hx
      rw [show n + (TopForm.opnd C T i - n) = TopForm.opnd C T i by have := hr.1; omega] at this
      exact this
    obtain ⟨r, h1, h2, h3, h4⟩ := orR_reader q _ (by omega) hr.2 hne
    exact ⟨by omega, back q hr.2, r, h1, h2, h3, back r h4⟩
  obtain ⟨hgT, gT, r1, r1N, r1o, r1g, r1b⟩ := orl g tc (Or.inl rfl) hgN hTg
  obtain ⟨hhT, hTh', r2, r2N, r2o, r2h, r2b⟩ := orl h (1 - tc) (Or.inr rfl) hhN hTh
  have hTl : lo V (graphFun G ∅) (n + T) := by
    by_contra hl
    rcases hJc T hTN hTA hl with e | e <;> omega
  have VT : ∀ x, V x (n + T) =
      (V x (TopForm.opnd C T tc) && V x (TopForm.opnd C T (1 - tc))) := by
    intro x
    rw [hVa x T hTN hTA]
    have hi : tc = 0 ∨ tc = 1 := by omega
    rcases hi with rfl | rfl
    · rfl
    · exact Bool.and_comm _ _
  have rmono : ∀ r q, r < C.gates.length → (gateAt C r).op = GateOp.or →
      n + q ∈ (gateAt C r).inputs → ∀ x, V x (n + q) = true → V x (n + r) = true := by
    intro r q hr hop hin x hx
    rw [hVo x r hr (hor0 r hop), Bool.or_eq_true]
    rcases (hmemi r hr _).1 hin with e | e
    · left; rw [e]; exact hx
    · right; rw [e]; exact hx
  have hr12 : r1 ≠ r2 := by
    intro e
    refine hgl fun x hx => hTl x ?_
    have h1 := rmono r1 g r1N r1o r1g x hx
    rw [VT, r1b x h1, r2b x (by rw [← e]; exact h1)]; rfl
  have hr1g : g < r1 := by have := hAO.2.1 r1 r1N _ r1g; omega
  have hr2h : h < r2 := by have := hAO.2.1 r2 r2N _ r2h; omega
  have pab : V (EdgeOwnership.pairInput a b) (n + g) = true ∧
      V (EdgeOwnership.pairInput a b) (n + h) = false ∧
      V (EdgeOwnership.pairInput a b) (n + F3) = false ∧
      V (EdgeOwnership.pairInput a b) (n + F4) = false := by
    rw [Vg, Vh, f3, f4]
    simp [EdgeOwnership.pairInput, hza, zb', hz0a, z0b', aw'.symm, hwb, ad'.symm, hdb]
  have pzd : V (EdgeOwnership.pairInput z d) (n + h) = true ∧
      V (EdgeOwnership.pairInput z d) (n + F1) = false ∧
      V (EdgeOwnership.pairInput z d) (n + F2) = false := by
    rw [Vh, f1, f2]
    simp [EdgeOwnership.pairInput, hzz0.symm, z0d', hza.symm, ad', zw'.symm, hdw.symm, zb'.symm,
      hdb.symm]
  have hr1D : r1 ∉ Del := by
    rw [hDm]
    have v := rmono r1 g r1N r1o r1g _ pab.1
    rintro (e | e | e | e | e | e)
    · omega
    · rw [e, hhA] at r1o; cases r1o
    · omega
    · omega
    · rw [e, pab.2.2.1] at v; cases v
    · rw [e, pab.2.2.2] at v; cases v
  have hr2D : r2 ∉ Del := by
    rw [hDm]
    have v := rmono r2 h r2N r2o r2h _ pzd.1
    rintro (e | e | e | e | e | e)
    · rw [e, hgA] at r2o; cases r2o
    · omega
    · rw [e, pzd.2.1] at v; cases v
    · rw [e, pzd.2.2] at v; cases v
    · omega
    · omega
  have hgo : g < o := by
    rcases Nat.lt_or_ge g o with h' | h'
    · exact h'
    · have := hmax g hgN
      exact absurd hlout (by rw [show o = g by omega]; exact hgl)
  have hho : h < o := by
    rcases Nat.lt_or_ge h o with h' | h'
    · exact h'
    · have := hmax h hhN
      exact absurd hlout (by rw [show o = h by omega]; exact hhl)
  obtain ⟨gs, w', hok, hw', hlen, hleF, hmono, hpab, hpq⟩ := core3 n C.gates.length o g h A p0 p1
    Del {r1, r2} G s V (fun W => CleanedNonEdge.OrReaches n C W g) a b w hab hVin hVa hVo hout hoN
    hlin H3 HL hread hJc hgl hhl
    (by
      intro q hq
      rcases (hDm q).1 hq with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
    (by simp [Del]) (by simp [Del])
    (by
      intro q hq r hr hrd
      have hin := (hmemi r hr _).2 hrd
      rcases (hDm q).1 hq with rfl | rfl | rfl | rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
      · left
        have := (hpriv 0 r hr).1 (by change p0 g ∈ _; rw [e1]; exact hin)
        rw [this]; simp [Del]
      · left
        have := (hpriv 1 r hr).1 (by change p1 g ∈ _; rw [e2]; exact hin)
        rw [this]; simp [Del]
      · left
        have := (hpriv 0 r hr).2 (by change p0 h ∈ _; rw [e3]; exact hin)
        rw [this]; simp [Del]
      · left
        have := (hpriv 1 r hr).2 (by change p1 h ∈ _; rw [e4]; exact hin)
        rw [this]; simp [Del])
    (by
      refine ⟨by omega, ?_⟩
      rw [Nat.add_sub_cancel_left]
      exact (((orS n C.gates).2 g hgN g)).2 (Or.inl rfl))
    (by
      intro j hj hA hr
      have hop := hA0 j hj hA
      obtain ⟨W, hW, hWr⟩ : ∃ W ∈ (gateAt C j).inputs, CleanedNonEdge.OrReaches n C W g := by
        rcases hr with hr | hr
        · exact ⟨_, (hmemi j hj _).2 (Or.inl rfl), hr⟩
        · exact ⟨_, (hmemi j hj _).2 (Or.inr rfl), hr⟩
      refine ⟨by omega, ?_⟩
      rw [Nat.add_sub_cancel_left]
      refine (((orS n C.gates).2 j hj g)).2 (Or.inr ?_)
      rw [(gate2 hAO hj).1]
      exact ⟨hop, W, hW, hWr.1, hAO.2.1 j hj W hW, hWr.2⟩)
    (by
      intro W hW hr x hx
      have := orR_mono hAO x g (W - n) (by have := hr.1; omega) hr.2 hx
      rw [show n + (W - n) = W by have := hr.1; omega] at this
      exact this)
    hcol ab (by rw [sw, sb]) naw
    (by rw [Vg]; simp [EdgeOwnership.pairInput])
    pab.2.1 ⟨_, hFall0⟩
    (by
      intro j hj
      have : j = r1 ∨ j = r2 := by simpa using hj
      rcases this with rfl | rfl <;> assumption)
    (by
      intro j hj
      have : j = r1 ∨ j = r2 := by simpa using hj
      rcases this with rfl | rfl
      · exact ⟨hor0 _ r1o, hr1D, g, by simp [Del], hr1g, (hmemi _ r1N _).1 r1g⟩
      · exact ⟨hor0 _ r2o, hr2D, h, by simp [Del], hr2h, (hmemi _ r2N _).1 r2h⟩)
  obtain ⟨g2, w2, ok2, len2, hw2, val2⟩ := star1 n gs w' hok hw' d w z
  obtain ⟨g3, w3, ok3, len3, hw3, val3⟩ := star1 n g2 w2 ok2 hw2 w b z0
  have hle := hmin ⟨g3, w3⟩ (ok_ao ok3) (by
    funext x
    change (run g3 (List.ofFn x)).getD w3 false = _
    rw [val3, val2, Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true]
    constructor
    · rintro ((h1 | ⟨h1, h2 | h2⟩) | ⟨h1, h2 | h2⟩)
      · exact hleF x h1
      · exact (gf G x).2 ⟨z, d, zd, h1, h2⟩
      · exact (gf G x).2 ⟨z, w, zw, h1, h2⟩
      · exact (gf G x).2 ⟨z0, w, z0w, h1, h2⟩
      · exact (gf G x).2 ⟨z0, b, z0b, h1, h2⟩
    · intro hx
      obtain ⟨p, q, hpq', hp, hq⟩ := (gf G x).1 hx
      have up : ∀ i j : Fin n, x i = true → x j = true →
          (run gs (List.ofFn (EdgeOwnership.pairInput i j))).getD w' false = true →
          (run gs (List.ofFn x)).getD w' false = true := by
        intro i j hi hj hv
        refine hmono _ x (fun t ht => ?_) hv
        have : t = i ∨ t = j := by simpa [EdgeOwnership.pairInput] using ht
        rcases this with rfl | rfl <;> assumption
      cases hg0 : V (EdgeOwnership.pairInput p q) (n + g) with
      | true =>
        rw [Vg, Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true] at hg0
        rcases hg0 with ⟨h1 | h1, h2 | h2⟩
        · obtain ⟨_, t2, t3⟩ := pr z0w' h1 h2 hpq' hp hq
          exact Or.inr ⟨t2, Or.inl t3⟩
        · obtain ⟨_, t2, t3⟩ := pr z0b' h1 h2 hpq' hp hq
          exact Or.inr ⟨t2, Or.inr t3⟩
        · exact absurd (pr aw' h1 h2 hpq' hp hq).1 naw
        · obtain ⟨_, t2, t3⟩ := pr ab' h1 h2 hpq' hp hq
          exact Or.inl (Or.inl (up a b t2 t3 hpab))
      | false =>
        cases hh0 : V (EdgeOwnership.pairInput p q) (n + h) with
        | true =>
          rw [Vh, Bool.and_eq_true, Bool.or_eq_true, Bool.or_eq_true] at hh0
          rcases hh0 with ⟨h1 | h1, h2 | h2⟩
          · obtain ⟨_, t2, t3⟩ := pr zw' h1 h2 hpq' hp hq
            exact Or.inl (Or.inr ⟨t2, Or.inr t3⟩)
          · obtain ⟨_, t2, t3⟩ := pr zd' h1 h2 hpq' hp hq
            exact Or.inl (Or.inr ⟨t2, Or.inl t3⟩)
          · obtain ⟨_, t2, t3⟩ := pr z0w' h1 h2 hpq' hp hq
            exact Or.inr ⟨t2, Or.inl t3⟩
          · exact absurd (pr z0d' h1 h2 hpq' hp hq).1 nz0d
        | false => exact Or.inl (Or.inl (up p q hp hq (hpq p q hpq' hg0 hh0))))
  change C.gates.length ≤ g3.length at hle
  rw [hDc, Finset.card_pair hr12] at hlen
  omega
