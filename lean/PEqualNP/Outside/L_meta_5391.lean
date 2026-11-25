import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5391

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

open Classical in
theorem core (n N o T : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del R : Finset ℕ)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (V c : (Fin n → Bool) → ℕ → Bool) (K Re : ℕ → Prop) (S : Finset (Sym2 (Fin n)))
    (hab : ∀ j < N, a j < n + j ∧ b j < n + j)
    (hVin : ∀ x, ∀ w < n, V x w = (List.ofFn x).getD w false)
    (hcin : ∀ x, ∀ w < n, c x w = (List.ofFn x).getD w false)
    (hVa : ∀ x, ∀ j < N, A j = true → V x (n + j) = (V x (a j) && V x (b j)))
    (hVo : ∀ x, ∀ j < N, A j = false → V x (n + j) = (V x (a j) || V x (b j)))
    (hca : ∀ x, ∀ j < N, j ≠ T → A j = true → c x (n + j) = (c x (a j) && c x (b j)))
    (hco : ∀ x, ∀ j < N, j ≠ T → A j = false → c x (n + j) = (c x (a j) || c x (b j)))
    (hcT : ∀ x, c x (n + T) = false)
    (hout : ∀ x, V x (n + o) = graphFun G ∅ x) (hoN : o < N) (hTN : T < N) (hAT : A T = true)
    (hin : ∀ w < n, ¬ lo V (graphFun G ∅) w)
    (H3 : ∀ j < N, A j = true → ¬ lo V (graphFun G ∅) (a j) ∧ ¬ lo V (graphFun G ∅) (b j))
    (HL : ∀ j < N, A j = false → ¬ lo V (graphFun G ∅) (n + j) →
      ¬ lo V (graphFun G ∅) (a j) ∧ ¬ lo V (graphFun G ∅) (b j))
    (hread : ∀ j < N, j = o ∨ ∃ r < N, a r = n + j ∨ b r = n + j)
    (hTl : ¬ lo V (graphFun G ∅) (n + T))
    (hDel : ∀ d ∈ Del, d < N ∧ d ≠ o) (hTD : T ∈ Del)
    (hDr : ∀ d ∈ Del, ∀ r < N, (a r = n + d ∨ b r = n + d) → r ∈ Del ∨ d = T)
    (hK : ∀ k < N, A k = true → k ≠ T → Re (a k) ∨ Re (b k) → K k)
    (hK2 : ∀ k < N, K k → lo V (graphFun G ∅) (n + k) ∧ b k < n ∧ A k = true)
    (hRe : Re (n + T)) (hRo : ∀ j < N, A j = false → Re (a j) ∨ Re (b j) → Re (n + j))
    (hS : ∀ p q, G.Adj p q → c (EdgeOwnership.pairInput p q) (n + o) = false → s(p, q) ∈ S)
    (hS' : ∀ ed ∈ S, ∃ p q, ed = s(p, q) ∧ G.Adj p q ∧
      c (EdgeOwnership.pairInput p q) (n + o) = false)
    (hFall : ∃ x, graphFun G ∅ x = true) (hRN : ∀ j ∈ R, j < N)
    (hR : ∀ j ∈ R, A j = false ∧ j ∉ Del ∧ ∃ d ∈ Del, d < j ∧ (a j = n + d ∨ b j = n + d)) :
    ∃ (gs : List Gate) (w' : ℕ), Ok n gs ∧ w' < n + gs.length ∧
      (∀ x : Fin n → Bool, (run gs (List.ofFn x)).getD w' false = graphFun G ∅ x) ∧
      gs.length + Del.card + R.card ≤ N + S.card ∧
      dc n (graphFun G ∅) gs ≤ ((Finset.range N).filter fun j => A j = true ∧ j ∉ Del ∧
        ∃ x : Fin n → Bool, V x (n + j) = true ∧ graphFun G ∅ x = false).card := by
  have hLa : ∀ j < N, A j = false → lo V (graphFun G ∅) (n + j) →
      lo V (graphFun G ∅) (a j) ∧ lo V (graphFun G ∅) (b j) := by
    intro j hj hA h
    refine ⟨fun x hx => h x ?_, fun x hx => h x ?_⟩ <;> rw [hVo x j hj hA, hx] <;> simp
  have hlo : lo V (graphFun G ∅) (n + o) := fun x hx => by rw [← hout x]; exact hx
  -- nothing deleted is below F
  have Dlo : ∀ i d, N - d = i → d ∈ Del → ¬ lo V (graphFun G ∅) (n + d) := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro d hi hd hl
      obtain ⟨hdN, hdo⟩ := hDel d hd
      by_cases hdT : d = T
      · exact hTl (hdT ▸ hl)
      rcases hread d hdN with h | ⟨r, hr, hrd⟩
      · exact hdo h
      rcases hDr d hd r hr hrd with h | h
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
          obtain ⟨h1, h2⟩ := HL r hr hA (ih (N - r) (by omega) r rfl h)
          rcases hrd with h | h
          · rw [h] at h1; exact h1 hl
          · rw [h] at h2; exact h2 hl
      · exact hdT h
  -- wires not below F that do not reach T are unchanged
  have P4 : ∀ w < n + N, ¬ lo V (graphFun G ∅) w → ¬ Re w → ∀ x, c x w = V x w := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hl hr x
      by_cases h9 : w < n
      · rw [hVin x w h9, hcin x w h9]
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < N := by omega
      obtain ⟨ha, hb⟩ := hab j hj
      have hjT : j ≠ T := fun h => hr (h ▸ hRe)
      cases hA : A j with
      | true =>
        obtain ⟨l1, l2⟩ := H3 j hj hA
        have hn : ¬ (Re (a j) ∨ Re (b j)) := fun h => hl (hK2 j hj (hK j hj hA hjT h)).1
        rw [not_or] at hn
        rw [hca x j hj hjT hA, hVa x j hj hA, ih _ ha (by omega) l1 hn.1, ih _ hb (by omega) l2 hn.2]
      | false =>
        obtain ⟨l1, l2⟩ := HL j hj hA hl
        have hn : ¬ (Re (a j) ∨ Re (b j)) := fun h => hr (hRo j hj hA h)
        rw [not_or] at hn
        rw [hco x j hj hjT hA, hVo x j hj hA, ih _ ha (by omega) l1 hn.1, ih _ hb (by omega) l2 hn.2]
  -- a changed wire below F has a changed AND under it
  have P5 : ∀ j < N, lo V (graphFun G ∅) (n + j) → ∀ x, V x (n + j) = true →
      c x (n + j) = false → ∃ k < N, K k ∧ V x (n + k) = true := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hl x hV hc
      obtain ⟨ha, hb⟩ := hab j hj
      have hjT : j ≠ T := fun h => hTl (h ▸ hl)
      cases hA : A j with
      | true =>
        by_cases hk : K j
        · exact ⟨j, hj, hk, hV⟩
        · exfalso
          have hn : ¬ (Re (a j) ∨ Re (b j)) := fun h => hk (hK j hj hA hjT h)
          rw [not_or] at hn
          obtain ⟨l1, l2⟩ := H3 j hj hA
          rw [hca x j hj hjT hA, P4 _ (by omega) l1 hn.1, P4 _ (by omega) l2 hn.2,
            ← hVa x j hj hA, hV] at hc
          cases hc
      | false =>
        obtain ⟨l1, l2⟩ := hLa j hj hA hl
        rw [hco x j hj hjT hA, Bool.or_eq_false_iff] at hc
        rw [hVo x j hj hA, Bool.or_eq_true] at hV
        have go : ∀ w, w < n + j → lo V (graphFun G ∅) w → V x w = true → c x w = false →
            ∃ k < N, K k ∧ V x (n + k) = true := by
          intro w hw l hv hcc
          by_cases h9 : w < n
          · exact absurd l (hin w h9)
          obtain ⟨i, rfl⟩ : ∃ i, w = n + i := ⟨w - n, by omega⟩
          exact ih i (by omega) (by omega) l x hv hcc
        rcases hV with h | h
        · exact go _ ha l1 h hc.1
        · exact go _ hb l2 h hc.2
  -- the letters handed to the widened ANDs
  have hch : ∀ ed ∈ S, ∃ k t, k < N ∧ K k ∧ t < n ∧
      (∀ p q, ed = s(p, q) → (List.ofFn (EdgeOwnership.pairInput p q)).getD t false = true ∧
        (List.ofFn (EdgeOwnership.pairInput p q)).getD (b k) false = true) ∧
      ∀ x : Fin n → Bool, (List.ofFn x).getD t false = true →
        (List.ofFn x).getD (b k) false = true → graphFun G ∅ x = true := by
    intro ed hed
    obtain ⟨p, q, rfl, hpq, hc⟩ := hS' ed hed
    have hF : graphFun G ∅ (EdgeOwnership.pairInput p q) = true :=
      (gf G _).2 ⟨p, q, hpq, by simp [EdgeOwnership.pairInput], by simp [EdgeOwnership.pairInput]⟩
    obtain ⟨k, hkN, hk, hkv⟩ := P5 o hoN hlo _ (by rw [hout]; exact hF) hc
    obtain ⟨_, hbn, hAk⟩ := hK2 k hkN hk
    rw [hVa _ k hkN hAk, Bool.and_eq_true] at hkv
    have hbv := hkv.2
    rw [hVin _ _ hbn] at hbv
    have e1 : (⟨b k, hbn⟩ : Fin n) = p ∨ (⟨b k, hbn⟩ : Fin n) = q := by
      have := gD (EdgeOwnership.pairInput p q) ⟨b k, hbn⟩
      rw [hbv] at this
      simpa [EdgeOwnership.pairInput] using this.symm
    have sym : ∀ p' q' : Fin n, s(p, q) = s(p', q') →
        EdgeOwnership.pairInput p q = EdgeOwnership.pairInput p' q' := by
      intro p' q' h
      rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · funext w; simp [EdgeOwnership.pairInput, or_comm]
    rcases e1 with e1 | e1
    · refine ⟨k, q.val, hkN, hk, q.isLt, fun p' q' h => ?_, fun x h1 h2 => ?_⟩
      · rw [← sym p' q' h]
        exact ⟨by rw [gD]; simp [EdgeOwnership.pairInput], hbv⟩
      · refine (gf G x).2 ⟨p, q, hpq, ?_, by rw [← gD x]; exact h1⟩
        rw [← gD x, ← e1]; exact h2
    · refine ⟨k, p.val, hkN, hk, p.isLt, fun p' q' h => ?_, fun x h1 h2 => ?_⟩
      · rw [← sym p' q' h]
        exact ⟨by rw [gD]; simp [EdgeOwnership.pairInput], hbv⟩
      · refine (gf G x).2 ⟨p, q, hpq, by rw [← gD x]; exact h1, ?_⟩
        rw [← gD x, ← e1]; exact h2
  choose! κ τ hκ1 hκ2 hκ3 hκ4 hκ5 using hch
  let L : ℕ → List ℕ := fun j => ((S.filter fun ed => κ ed = j).toList.map τ)
  have hLm : ∀ j t, t ∈ L j → ∃ ed ∈ S, κ ed = j ∧ τ ed = t := by
    intro j t ht
    simp only [L, List.mem_map, Finset.mem_toList, Finset.mem_filter] at ht
    obtain ⟨ed, ⟨h1, h2⟩, h3⟩ := ht
    exact ⟨ed, h1, h2, h3⟩
  have hLn : ∀ j, ∀ t ∈ L j, t < n := by
    intro j t ht
    obtain ⟨ed, h1, _, rfl⟩ := hLm j t ht
    exact hκ3 ed h1
  have hsum : ∑ j ∈ Finset.range N, (L j).length = S.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := κ) (s := S) (t := Finset.range N)
      (fun ed h => by simpa using hκ1 ed h)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [L]
  obtain ⟨gs, m, hok, hm, hdn, hcount, hj⟩ :=
    build n A a b Del R L (graphFun G ∅) hLn hR N hab
  have uin : ∀ (x : Fin n → Bool) (w : ℕ), w < n →
      u n A a b Del L (List.ofFn x) w = V x w := fun x w hw => by rw [u_in hw, hVin x w hw]
  -- upper bound
  have P1 : ∀ w < n + N, ∀ x : Fin n → Bool, u n A a b Del L (List.ofFn x) w = true →
      (lo V (graphFun G ∅) w → graphFun G ∅ x = true) ∧
      (¬ lo V (graphFun G ∅) w → V x w = true) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw x hx
      by_cases h9 : w < n
      · rw [uin x w h9] at hx
        exact ⟨fun h => h x hx, fun _ => hx⟩
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < N := by omega
      obtain ⟨ha, hb⟩ := hab j hj
      by_cases hd : j ∈ Del
      · rw [u_del hd] at hx; cases hx
      cases hA : A j with
      | true =>
        obtain ⟨l1, l2⟩ := H3 j hj hA
        rw [u_and hd hA ha hb, Bool.and_eq_true, Bool.or_eq_true] at hx
        have hbV := (ih _ hb (by omega) x hx.2).2 l2
        rcases hx.1 with h1 | h1
        · have haV := (ih _ ha (by omega) x h1).2 l1
          have : V x (n + j) = true := by rw [hVa x j hj hA, haV, hbV]; rfl
          exact ⟨fun h => h x this, fun _ => this⟩
        · rw [List.any_eq_true] at h1
          obtain ⟨t, ht, htx⟩ := h1
          obtain ⟨ed, hed, hk, rfl⟩ := hLm j t ht
          subst hk
          obtain ⟨k1, k2, _⟩ := hK2 _ hj (hκ2 ed hed)
          rw [hVin x _ k2] at hbV
          exact ⟨fun _ => hκ5 ed hed x htx hbV, fun h => absurd k1 h⟩
      | false =>
        rw [u_or hd hA ha hb, Bool.or_eq_true] at hx
        refine ⟨fun h => ?_, fun h => ?_⟩
        · obtain ⟨l1, l2⟩ := hLa j hj hA h
          rcases hx with h1 | h1
          · exact (ih _ ha (by omega) x h1).1 l1
          · exact (ih _ hb (by omega) x h1).1 l2
        · obtain ⟨l1, l2⟩ := HL j hj hA h
          rw [hVo x j hj hA, Bool.or_eq_true]
          rcases hx with h1 | h1
          · exact Or.inl ((ih _ ha (by omega) x h1).2 l1)
          · exact Or.inr ((ih _ hb (by omega) x h1).2 l2)
  -- lower bound
  have P2 : ∀ w < n + N, (∀ d ∈ Del, w = n + d → d = T) → ∀ x : Fin n → Bool,
      c x w = true → u n A a b Del L (List.ofFn x) w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw hdl x hx
      by_cases h9 : w < n
      · rw [u_in h9, ← hcin x w h9]; exact hx
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < N := by omega
      obtain ⟨ha, hb⟩ := hab j hj
      by_cases hjT : j = T
      · rw [hjT, hcT] at hx; cases hx
      have hd : j ∉ Del := fun h => hjT (hdl j h rfl)
      have ia := ih (a j) ha (by omega) (fun d hdd h =>
        (hDr d hdd j hj (Or.inl h)).resolve_left hd) x
      have ib := ih (b j) hb (by omega) (fun d hdd h =>
        (hDr d hdd j hj (Or.inr h)).resolve_left hd) x
      cases hA : A j with
      | true =>
        rw [hca x j hj hjT hA, Bool.and_eq_true] at hx
        rw [u_and hd hA ha hb, ia hx.1, ib hx.2]; rfl
      | false =>
        rw [hco x j hj hjT hA, Bool.or_eq_true] at hx
        rw [u_or hd hA ha hb, Bool.or_eq_true]
        exact hx.imp ia ib
  -- wires below F pass to the output
  have P3 : ∀ i j, N - j = i → j < N → lo V (graphFun G ∅) (n + j) → ∀ x : Fin n → Bool,
      u n A a b Del L (List.ofFn x) (n + j) = true →
      u n A a b Del L (List.ofFn x) (n + o) = true := by
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
        refine ih (N - r) (by omega) r rfl hr hrl x ?_
        rw [u_or hrd hA (hab r hr).1 (hab r hr).2, Bool.or_eq_true]
        rcases hrj with h | h
        · left; rw [h]; exact hx
        · right; rw [h]; exact hx
  have hod : o ∉ Del := fun h => (hDel o h).2 rfl
  have hu : ∀ x : Fin n → Bool, u n A a b Del L (List.ofFn x) (n + o) = graphFun G ∅ x := by
    intro x
    rw [Bool.eq_iff_iff]
    refine ⟨fun h => (P1 _ (by omega) x h).1 hlo, fun h => ?_⟩
    obtain ⟨p, q, hpq, hp, hq⟩ := (gf G x).1 h
    refine u_mono hab (List.ofFn (EdgeOwnership.pairInput p q)) _ ?_ (n + o) (by omega) ?_
    · intro t ht
      by_cases htn : t < n
      · have e := gD (EdgeOwnership.pairInput p q) ⟨t, htn⟩
        have e' := gD x ⟨t, htn⟩
        simp only at e e'
        rw [e] at ht
        rw [e']
        have : (⟨t, htn⟩ : Fin n) = p ∨ (⟨t, htn⟩ : Fin n) = q := by
          simpa [EdgeOwnership.pairInput] using ht
        rcases this with h | h <;> rw [h] <;> assumption
      · rw [List.getD_eq_default _ _ (by simpa using htn)] at ht; cases ht
    · by_cases hc : c (EdgeOwnership.pairInput p q) (n + o) = true
      · exact P2 _ (by omega) (fun d hd h => absurd (by omega : d = o) (hDel d hd).2) _ hc
      · have hed := hS p q hpq (by simpa using hc)
        have hk := hκ2 _ hed
        have hkN := hκ1 _ hed
        obtain ⟨k1, k2, k3⟩ := hK2 _ hkN hk
        have hkd : κ s(p, q) ∉ Del := fun h => Dlo _ _ rfl h k1
        refine P3 _ (κ s(p, q)) rfl hkN k1 _ ?_
        obtain ⟨t1, t2⟩ := hκ4 _ hed p q rfl
        rw [u_and hkd k3 (hab _ hkN).1 (hab _ hkN).2, Bool.and_eq_true, Bool.or_eq_true]
        refine ⟨Or.inr ?_, by rw [u_in k2]; exact t2⟩
        rw [List.any_eq_true]
        refine ⟨τ s(p, q), ?_, t1⟩
        simp only [L, List.mem_map, Finset.mem_toList, Finset.mem_filter]
        exact ⟨s(p, q), ⟨hed, rfl⟩, rfl⟩
  obtain ⟨hm1, hm2⟩ := hm (n + o) (by omega)
  rcases hmo : m (n + o) with _ | w'
  · exfalso
    obtain ⟨x, hx⟩ := hFall
    have := hm2 x
    rw [hmo, hu x, hx] at this
    cases this
  refine ⟨gs, w', hok, hm1 w' hmo, fun x => ?_, ?_, ?_⟩
  · have := hm2 x
    rw [hmo, hu x] at this
    exact this
  · have e1 : (Finset.range N).filter (· ∈ Del) = Del := by
      ext d; simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨(hDel d h).1, h⟩⟩
    have e2 : (Finset.range N).filter (· ∈ R) = R := by
      ext d; simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨fun h => h.2, fun h => ⟨hRN d h, h⟩⟩
    rw [e1, e2, hsum] at hcount
    exact hcount
  · refine hj.trans (Finset.card_le_card fun j hj' => ?_)
    simp only [Finset.mem_filter, Finset.mem_range] at hj' ⊢
    obtain ⟨h1, h2, h3, x, h4, h5⟩ := hj'
    refine ⟨h1, h2, h3, x, (P1 _ (by omega) x h4).2 fun hl => ?_, h5⟩
    rw [(P1 _ (by omega) x h4).1 hl] at h5; cases h5

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

end PEqualNP.Outside.L_meta_5391

open PEqualNP.Outside.L_meta_5391 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_5391 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool)
    (g T : ℕ) (e : Fin 2) (A B Cs : Finset (Fin n)) (R Dd : Finset ℕ),
  (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G →
  PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C →
  (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs,
      ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) →
  (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) →
  g ∈ PEqualNP.TopForm.junk G C → T ∈ PEqualNP.TopForm.junk G C → g ≠ T →
  A.Nonempty → B.Nonempty → Cs.Nonempty → Disjoint A B →
  (∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) x = decide (∃ t ∈ A, x t = true)) → (∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) x = decide (∃ t ∈ B, x t = true)) →
  PEqualNP.TopForm.opnd C T e = n + g → (∀ x : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C T (1 - e)) x = decide (∃ t ∈ Cs, x t = true)) →
  (∀ k < C.gates.length, n + g ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k = T) →
  (∀ k < C.gates.length, k ≠ T → (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ i : Fin 2, PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C k i) T →
      PEqualNP.TopForm.BelowF G C k ∧ PEqualNP.TopForm.opnd C k (1 - i) < n) →
  (∀ j ∈ R, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ n + T ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs) →
  (∀ j ∈ Dd, j < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      (PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C g 0) j ∨ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C g 1) j ∨ PEqualNP.CleanedNonEdge.OrReaches n C (PEqualNP.TopForm.opnd C T (1 - e)) j) ∧
      ∀ k < C.gates.length, n + j ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs → k = g ∨ k = T ∨ k ∈ Dd) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
    D.size + 2 + R.card + Dd.card ≤ C.size +
      (G.edgeFinset.filter (fun ed => ∃ u v : Fin n, ed = s(u, v) ∧
        PEqualNP.MetaComplexity.circuitFun n ⟨C.gates.set T ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩, C.output⟩ (PEqualNP.EdgeOwnership.pairInput u v) = false)).card ∧
    (PEqualNP.TopForm.junk G D).card + 2 ≤ (PEqualNP.TopForm.junk G C).card := by
  intro n G _ C s g T e AA BB Cs R Dd _ _ hAO hF hLift hH3 hcone hg hT hgT _ _ _ _ _ _ hTe _ hgr hKr
    hRR hDd
  classical
  let V : (Fin n → Bool) → ℕ → Bool := fun x w => (run C.gates (List.ofFn x)).getD w false
  let c : (Fin n → Bool) → ℕ → Bool := fun x w =>
    (run (C.gates.set T ⟨GateOp.or, []⟩) (List.ofFn x)).getD w false
  have hgg := Finset.mem_filter.1 hg
  have hTT := Finset.mem_filter.1 hT
  have hgN : g < C.gates.length := Finset.mem_range.1 hgg.1
  have hTN : T < C.gates.length := Finset.mem_range.1 hTT.1
  have hgA : (gateAt C g).op = GateOp.and := hgg.2.1
  have hTA : (gateAt C T).op = GateOp.and := hTT.2.1
  -- operands, the OR-reaching one first
  let Re : ℕ → Prop := fun w => CleanedNonEdge.OrReaches n C w T
  let sw : ℕ → Prop := fun j => (gateAt C j).op = GateOp.and ∧ ¬ Re (TopForm.opnd C j 0) ∧
    Re (TopForm.opnd C j 1)
  let A : ℕ → Bool := fun j => decide ((gateAt C j).op = GateOp.and)
  let a : ℕ → ℕ := fun j => if sw j then TopForm.opnd C j 1 else TopForm.opnd C j 0
  let b : ℕ → ℕ := fun j => if sw j then TopForm.opnd C j 0 else TopForm.opnd C j 1
  let K : ℕ → Prop := fun k => (gateAt C k).op = GateOp.and ∧ k ≠ T ∧
    (Re (TopForm.opnd C k 0) ∨ Re (TopForm.opnd C k 1))
  let Del : Finset ℕ := insert g (insert T Dd)
  have hA1 : ∀ j, A j = true ↔ (gateAt C j).op = GateOp.and := fun j => by simp [A]
  have hA0 : ∀ j < C.gates.length, A j = false → (gateAt C j).op = GateOp.or := by
    intro j hj h
    rcases (gate2 hAO hj).2.2.2.2 with h1 | h1
    · rw [(hA1 j).2 h1] at h; cases h
    · exact h1
  have hor0 : ∀ j, (gateAt C j).op = GateOp.or → A j = false := by
    intro j h; simp [A, h]
  -- every fact about both operands passes to a, b
  have both : ∀ (Q : ℕ → Prop) j, Q (TopForm.opnd C j 0) → Q (TopForm.opnd C j 1) →
      Q (a j) ∧ Q (b j) := by
    intro Q j h0 h1
    by_cases h : sw j
    · simp only [a, b, if_pos h]; exact ⟨h1, h0⟩
    · simp only [a, b, if_neg h]; exact ⟨h0, h1⟩
  have orb : ∀ (Q : ℕ → Prop) j, (Q (a j) ∨ Q (b j)) ↔
      (Q (TopForm.opnd C j 0) ∨ Q (TopForm.opnd C j 1)) := by
    intro Q j
    by_cases h : sw j
    · simp only [a, b, if_pos h]; exact or_comm
    · simp only [a, b, if_neg h]
  have hmemi : ∀ j < C.gates.length, ∀ w, w ∈ (gateAt C j).inputs ↔ (a j = w ∨ b j = w) := by
    intro j hj w
    rw [(gate2 hAO hj).2.1, orb (fun q => q = w) j]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact or_congr eq_comm eq_comm
  have hab : ∀ j < C.gates.length, a j < n + j ∧ b j < n + j := fun j hj =>
    both (fun w => w < n + j) j (gate2 hAO hj).2.2.1 (gate2 hAO hj).2.2.2.1
  have sym : ∀ (y : ℕ → Bool) j, (y (TopForm.opnd C j 0) && y (TopForm.opnd C j 1)) =
      (y (a j) && y (b j)) ∧ (y (TopForm.opnd C j 0) || y (TopForm.opnd C j 1)) =
      (y (a j) || y (b j)) := by
    intro y j
    by_cases h : sw j
    · simp only [a, b, if_pos h]; exact ⟨Bool.and_comm _ _, Bool.or_comm _ _⟩
    · simp only [a, b, if_neg h, and_self]
  have hVa : ∀ x, ∀ j < C.gates.length, A j = true → V x (n + j) = (V x (a j) && V x (b j)) := by
    intro x j hj hA
    obtain ⟨g1, g2, g3, g4, _⟩ := gate2 hAO hj
    have := veq n C.gates x j hj _ _ _ (g1.trans (gate_eta ((hA1 j).1 hA) g2)) g3 g4
    rw [← (sym (V x) j).1]
    simpa [V, GateOp.eval] using this
  have hVo : ∀ x, ∀ j < C.gates.length, A j = false →
      V x (n + j) = (V x (a j) || V x (b j)) := by
    intro x j hj hA
    obtain ⟨g1, g2, g3, g4, _⟩ := gate2 hAO hj
    have := veq n C.gates x j hj _ _ _ (g1.trans (gate_eta (hA0 j hj hA) g2)) g3 g4
    rw [← (sym (V x) j).2]
    simpa [V, GateOp.eval] using this
  have hset : ∀ j (hj : j < C.gates.length), j ≠ T →
      (C.gates.set T ⟨GateOp.or, []⟩)[j]'(by simpa using hj) = C.gates[j] := by
    intro j hj h
    rw [List.getElem_set_ne (fun h' => h h'.symm)]
  have hca : ∀ x, ∀ j < C.gates.length, j ≠ T → A j = true →
      c x (n + j) = (c x (a j) && c x (b j)) := by
    intro x j hj hjT hA
    obtain ⟨g1, g2, g3, g4, _⟩ := gate2 hAO hj
    have := veq n (C.gates.set T ⟨GateOp.or, []⟩) x j (by simpa using hj) _ _ _
      ((hset j hj hjT).trans (g1.trans (gate_eta ((hA1 j).1 hA) g2))) g3 g4
    rw [← (sym (c x) j).1]
    simpa [c, GateOp.eval] using this
  have hco : ∀ x, ∀ j < C.gates.length, j ≠ T → A j = false →
      c x (n + j) = (c x (a j) || c x (b j)) := by
    intro x j hj hjT hA
    obtain ⟨g1, g2, g3, g4, _⟩ := gate2 hAO hj
    have := veq n (C.gates.set T ⟨GateOp.or, []⟩) x j (by simpa using hj) _ _ _
      ((hset j hj hjT).trans (g1.trans (gate_eta (hA0 j hj hA) g2))) g3 g4
    rw [← (sym (c x) j).2]
    simpa [c, GateOp.eval] using this
  have hcT : ∀ x, c x (n + T) = false := by
    intro x
    have := run_gate (C.gates.set T ⟨GateOp.or, []⟩) (List.ofFn x) T (by simpa using hTN)
    rw [List.length_ofFn] at this
    have e2 : (C.gates.set T ⟨GateOp.or, []⟩)[T]'(by simpa using hTN) = ⟨GateOp.or, []⟩ := by simp
    rw [e2] at this
    exact this
  have hVin : ∀ x, ∀ w < n, V x w = (List.ofFn x).getD w false := fun x w hw =>
    run_input _ _ _ (by simpa using hw)
  have hcin : ∀ x, ∀ w < n, c x w = (List.ofFn x).getD w false := fun x w hw =>
    run_input _ _ _ (by simpa using hw)
  -- the output gate
  obtain ⟨o, hoN, hoo, hmax⟩ : ∃ o < C.gates.length, C.output = n + o ∧
      ∀ j < C.gates.length, j ≤ o := by
    obtain ⟨o, ho, hoo⟩ : ∃ o < C.gates.length, C.output = n + o := by
      rcases (hcone g hgN).2 with h | ⟨h1, h2⟩
      · exact ⟨g, hgN, h⟩
      · exact ⟨C.output - n, (cone_rd n C _ _ h2).1, by omega⟩
    refine ⟨o, ho, hoo, fun j hj => ?_⟩
    rcases (hcone j hj).2 with h | ⟨h1, h2⟩
    · omega
    · have := (cone_rd n C _ _ h2).2.1; omega
  have hout : ∀ x, V x (n + o) = graphFun G ∅ x := by
    intro x
    have := congrFun hF x
    rw [← this]
    change _ = (run C.gates (List.ofFn x)).getD C.output false
    rw [hoo]
  have ones : ∀ w < n + C.gates.length, V (fun _ => true) w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases h9 : w < n
      · rw [hVin _ w h9, gD (fun _ => true) ⟨w, h9⟩]
      obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨h1, h2⟩ := hab j hj
      have i1 := ih _ h1 (by omega)
      have i2 := ih _ h2 (by omega)
      cases hA : A j with
      | true => rw [hVa _ j hj hA, i1, i2]; rfl
      | false => rw [hVo _ j hj hA, i1, i2]; rfl
  have hread : ∀ j < C.gates.length, j = o ∨ ∃ r < C.gates.length, a r = n + j ∨ b r = n + j := by
    intro j hj
    rcases (hcone j hj).2 with h | ⟨h1, h2⟩
    · left; omega
    · obtain ⟨_, _, r, hr, hrj⟩ := cone_rd n C _ _ h2
      exact Or.inr ⟨r, hr, (hmemi r hr _).1 hrj⟩
  have hdirty : ∀ j, CleanedNonEdge.IsDirtyAnd n G C j → ¬ lo V (graphFun G ∅) (n + j) := by
    rintro j ⟨_, _, x, h1, h2⟩ hl
    have := hl x h1
    rw [this] at h2; cases h2
  have hlout : lo V (graphFun G ∅) (n + o) := fun x hx => by rw [← hout x]; exact hx
  have hgo : g ≠ o := fun h => hdirty g hgg.2 (h ▸ hlout)
  have hTo : T ≠ o := fun h => hdirty T hTT.2 (h ▸ hlout)
  have hTin : n + g ∈ (gateAt C T).inputs := by
    rw [(gate2 hAO hTN).2.1]
    have he : e = 0 ∨ e = 1 := by omega
    rcases he with rfl | rfl <;> simp [hTe]
  have hgltT : g < T := by
    have := hAO.2.1 T hTN _ hTin; omega
  have hDlt : ∀ d ∈ Dd, d < T := by
    intro d hd
    obtain ⟨hdN, _, hr, _⟩ := hDd d hd
    have key : ∀ q w, w < n + q → CleanedNonEdge.OrReaches n C w d → d < q := by
      intro q w hw h
      have := orR_le n C _ _ h.2
      have := h.1
      omega
    rcases hr with h | h | h
    · have := key g _ (gate2 hAO hgN).2.2.1 h; omega
    · have := key g _ (gate2 hAO hgN).2.2.2.1 h; omega
    · refine key T _ ?_ h
      have he : e = 0 ∨ e = 1 := by omega
      rcases he with rfl | rfl
      · exact (gate2 hAO hTN).2.2.2.1
      · exact (gate2 hAO hTN).2.2.1
  have hgD : g ∉ insert T Dd := by
    rw [Finset.mem_insert, not_or]
    refine ⟨hgT, fun h => ?_⟩
    have := (hDd g h).2.1
    rw [hgA] at this; cases this
  have hTD : T ∉ Dd := fun h => absurd (hDlt T h) (lt_irrefl _)
  have hDc : Del.card = 2 + Dd.card := by
    simp only [Del]
    rw [Finset.card_insert_of_notMem hgD, Finset.card_insert_of_notMem hTD]; omega
  have hnolo : ∀ j < C.gates.length, ∀ w ∈ (gateAt C j).inputs, (gateAt C j).op = GateOp.and →
      ¬ lo V (graphFun G ∅) w := fun j hj w hw hop => hH3 j hj hop w hw
  have hlift : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or →
      ¬ lo V (graphFun G ∅) (n + j) → ∀ i : Fin 2, ¬ lo V (graphFun G ∅) (TopForm.opnd C j i) := by
    intro j hj hop hl i hlw
    refine hLift ⟨j, hj, i, hcone j hj, hop, hl, hlw, fun _ => true, ?_⟩
    have hi : i = 0 ∨ i = 1 := by omega
    have : TopForm.opnd C j i < n + C.gates.length := by
      rcases hi with rfl | rfl
      · have := (gate2 hAO hj).2.2.1; omega
      · have := (gate2 hAO hj).2.2.2.1; omega
    exact ones _ this
  have hReT : Re (n + T) := by
    refine ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    exact (((orS n C.gates).2 T hTN T)).2 (Or.inl rfl)
  have hReo : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or → ∀ w ∈ (gateAt C j).inputs,
      Re w → Re (n + j) := by
    intro j hj hop w hw hr
    refine ⟨by omega, ?_⟩
    rw [Nat.add_sub_cancel_left]
    refine (((orS n C.gates).2 j hj T)).2 (Or.inr ?_)
    rw [(gate2 hAO hj).1]
    exact ⟨hop, w, hw, hr.1, hAO.2.1 j hj w hw, hr.2⟩
  obtain ⟨gs, w', hok, hw', hval, hcnt, hjk⟩ := core n C.gates.length o T A a b Del R G V c K Re
    (G.edgeFinset.filter (fun ed => ∃ u v : Fin n, ed = s(u, v) ∧
      circuitFun n ⟨C.gates.set T ⟨GateOp.or, []⟩, C.output⟩ (EdgeOwnership.pairInput u v) = false))
    hab hVin hcin hVa hVo hca hco hcT hout hoN hTN ((hA1 T).2 hTA)
    (by
      intro w hw hl
      have := hl (fun q => decide (q.val = w)) (by
        rw [hVin _ w hw, gD _ ⟨w, hw⟩]; simp)
      obtain ⟨p, q, hpq, h1, h2⟩ := (gf G _).1 this
      simp only [decide_eq_true_eq] at h1 h2
      have : p = q := Fin.ext (h1.trans h2.symm)
      rw [this] at hpq
      exact G.loopless.irrefl _ hpq)
    (by
      intro j hj hA
      have h := hnolo j hj
      exact ⟨h _ ((hmemi j hj _).2 (Or.inl rfl)) ((hA1 j).1 hA),
        h _ ((hmemi j hj _).2 (Or.inr rfl)) ((hA1 j).1 hA)⟩)
    (by
      intro j hj hA hl
      exact both (fun w => ¬ lo V (graphFun G ∅) w) j (hlift j hj (hA0 j hj hA) hl 0)
        (hlift j hj (hA0 j hj hA) hl 1))
    hread (hdirty T hTT.2)
    (by
      intro d hd
      simp only [Del, Finset.mem_insert] at hd
      rcases hd with rfl | rfl | hd
      · exact ⟨hgN, hgo⟩
      · exact ⟨hTN, hTo⟩
      · have h1 := hDlt d hd
        have h2 := hmax T hTN
        exact ⟨by omega, by omega⟩)
    (by simp [Del])
    (by
      intro d hd r hr hrd
      have hm := (hmemi r hr _).2 hrd
      simp only [Del, Finset.mem_insert] at hd ⊢
      rcases hd with rfl | rfl | hd
      · exact Or.inl (Or.inr (Or.inl (hgr r hr hm)))
      · exact Or.inr rfl
      · exact Or.inl ((hDd d hd).2.2.2 r hr hm))
    (by
      intro k hk hA hkT h
      exact ⟨(hA1 k).1 hA, hkT, (orb Re k).1 h⟩)
    (by
      rintro k hk ⟨hop, hkT, hr⟩
      have hbl : b k < n ∧ lo V (graphFun G ∅) (n + k) := by
        by_cases h0 : Re (TopForm.opnd C k 0)
        · have hns : ¬ sw k := fun h => h.2.1 h0
          obtain ⟨q1, q2⟩ := hKr k hk hkT hop 0 h0
          exact ⟨by simp only [b, if_neg hns]; exact q2, q1⟩
        · have h1 := hr.resolve_left h0
          have hs : sw k := ⟨hop, h0, h1⟩
          obtain ⟨q1, q2⟩ := hKr k hk hkT hop 1 h1
          exact ⟨by simp only [b, if_pos hs]; exact q2, q1⟩
      exact ⟨hbl.2, hbl.1, (hA1 k).2 hop⟩)
    hReT
    (by
      intro j hj hA h
      have hop := hA0 j hj hA
      rcases h with h | h
      · exact hReo j hj hop _ ((hmemi j hj _).2 (Or.inl rfl)) h
      · exact hReo j hj hop _ ((hmemi j hj _).2 (Or.inr rfl)) h)
    (by
      intro p q hpq hc
      refine Finset.mem_filter.2 ⟨SimpleGraph.mem_edgeFinset.2 hpq, p, q, rfl, ?_⟩
      change (run (C.gates.set T ⟨GateOp.or, []⟩) (List.ofFn _)).getD C.output false = false
      rw [hoo]; exact hc)
    (by
      intro ed hed
      obtain ⟨h1, p, q, rfl, h2⟩ := Finset.mem_filter.1 hed
      refine ⟨p, q, rfl, SimpleGraph.mem_edgeFinset.1 h1, ?_⟩
      change (run (C.gates.set T ⟨GateOp.or, []⟩) (List.ofFn _)).getD C.output false = false at h2
      rw [hoo] at h2; exact h2)
    ⟨fun _ => true, by rw [← hout]; exact ones _ (by omega)⟩
    (fun j hj => (hRR j hj).1)
    (by
      intro j hj
      obtain ⟨hjN, hop, hin⟩ := hRR j hj
      have hTj : T < j := by have := hAO.2.1 j hjN _ hin; omega
      refine ⟨hor0 j hop, ?_, T, by simp [Del], hTj, (hmemi j hjN _).1 hin⟩
      simp only [Del, Finset.mem_insert, not_or]
      refine ⟨by omega, by omega, fun h => ?_⟩
      have := hDlt j h; omega)
  refine ⟨⟨gs, w'⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; exact h2
  · intro j hj i hi
    obtain ⟨o', s', t', h1, h2, h3, h4⟩ := hok j hj
    have e1 : gateAt ⟨gs, w'⟩ j = gs[j] := List.getD_eq_getElem _ _ hj
    rw [e1, h1] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; rfl
  · funext x; exact hval x
  · change gs.length + 2 + R.card + Dd.card ≤ C.gates.length + _
    rw [hDc] at hcnt
    omega
  · have h1 : (TopForm.junk G ⟨gs, w'⟩).card ≤ dc n (graphFun G ∅) gs := by
      refine Finset.card_le_card fun j hj => ?_
      obtain ⟨q1, q2, _, q3⟩ := Finset.mem_filter.1 hj
      exact Finset.mem_filter.2 ⟨q1, q2, q3⟩
    have h2 : ((Finset.range C.gates.length).filter fun j => A j = true ∧ j ∉ Del ∧
        ∃ x : Fin n → Bool, V x (n + j) = true ∧ graphFun G ∅ x = false).card + 2 ≤
        (TopForm.junk G C).card := by
      set X := (Finset.range C.gates.length).filter fun j => A j = true ∧ j ∉ Del ∧
        ∃ x : Fin n → Bool, V x (n + j) = true ∧ graphFun G ∅ x = false with hX
      have hXd : ∀ j ∈ X, j ∉ Del := fun j hj => (Finset.mem_filter.1 hj).2.2.1
      have n1 : T ∉ X := fun h => hXd T h (by simp [Del])
      have n2 : g ∉ insert T X := by
        rw [Finset.mem_insert, not_or]
        exact ⟨hgT, fun h => hXd g h (by simp [Del])⟩
      have : (insert g (insert T X)).card ≤ (TopForm.junk G C).card := by
        refine Finset.card_le_card fun j hj => ?_
        rw [Finset.mem_insert, Finset.mem_insert] at hj
        rcases hj with rfl | rfl | hj
        · exact hg
        · exact hT
        · obtain ⟨q1, q2, _, q3⟩ := Finset.mem_filter.1 hj
          exact Finset.mem_filter.2 ⟨q1, (hA1 j).1 q2, Finset.mem_range.1 q1, q3⟩
      rw [Finset.card_insert_of_notMem n2, Finset.card_insert_of_notMem n1] at this
      omega
    omega
