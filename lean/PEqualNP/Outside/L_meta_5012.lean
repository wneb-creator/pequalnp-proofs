import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic

namespace PEqualNP.Outside.L_meta_5012

namespace CriticalEdge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

lemma run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
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

section LocalScope1
variable {n : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ} {x : List Bool}

lemma u_in {w : ℕ} (h : w < n) : u n A a b Del L x w = x.getD w false := by
  rw [u, if_pos h]

lemma u_del {j : ℕ} (h : j ∈ Del) : u n A a b Del L x (n + j) = false := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_pos h]

lemma u_and {j : ℕ} (h : j ∉ Del) (hA : A j = true) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = ((u n A a b Del L x (a j) ||
      (L j).any (fun t => x.getD t false)) && u n A a b Del L x (b j)) := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_neg h, if_pos hA, dif_pos ha, dif_pos hb]

lemma u_or {j : ℕ} (h : j ∉ Del) (hA : A j = false) (ha : a j < n + j) (hb : b j < n + j) :
    u n A a b Del L x (n + j) = (u n A a b Del L x (a j) || u n A a b Del L x (b j)) := by
  rw [u, if_neg (by omega), Nat.add_sub_cancel_left, if_neg h, if_neg (by simp [hA]), dif_pos ha,
    dif_pos hb]
end LocalScope1

def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

lemma ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
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
lemma dc_snoc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) (g : Gate) :
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

lemma ov_ext (gs hs : List Gate) (x : List Bool) (o : Option ℕ)
    (h : ∀ w, o = some w → w < x.length + gs.length) : ov (gs ++ hs) x o = ov gs x o := by
  cases o with
  | none => rfl
  | some w => exact run_prefix gs hs x w (h w rfl)

lemma ov_new (gs : List Gate) (n : ℕ) (x : List Bool) (hx : x.length = n) (o : GateOp) (s t : ℕ)
    (hs : s < n + gs.length) (ht : t < n + gs.length) :
    ov (gs ++ [⟨o, [s, t]⟩]) x (some (n + gs.length)) =
      o.eval [(run gs x).getD s false, (run gs x).getD t false] := by
  unfold ov
  simp only
  rw [run_snoc]
  have : n + gs.length = (run gs x).length := by rw [run_length, hx]
  rw [this, getD_at]
  rfl

lemma chain (n : ℕ) (F : (Fin n → Bool) → Bool) : ∀ (l : List ℕ), (∀ t ∈ l, t < n) →
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
lemma build (n : ℕ) (A : ℕ → Bool) (a b : ℕ → ℕ) (Del R : Finset ℕ) (L : ℕ → List ℕ)
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

lemma gf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ p q, G.Adj p q ∧ x p = true ∧ x q = true := by
  simp [graphFun]

lemma gD {n : ℕ} (x : Fin n → Bool) (p : Fin n) : (List.ofFn x).getD p.val false = x p := by
  simp [List.getD_eq_getElem?_getD]

lemma u_mono {n N : ℕ} {A : ℕ → Bool} {a b : ℕ → ℕ} {Del : Finset ℕ} {L : ℕ → List ℕ}
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

lemma gate2 {n : ℕ} {C : Circuit} (h : TopForm.IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
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

lemma veq (n : ℕ) (gs : List Gate) (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) (o : GateOp)
    (s t : ℕ) (e : gs[j] = ⟨o, [s, t]⟩) (hs : s < n + j) (ht : t < n + j) :
    (run gs (List.ofFn x)).getD (n + j) false = o.eval [(run gs (List.ofFn x)).getD s false,
      (run gs (List.ofFn x)).getD t false] := by
  have := run_gate gs (List.ofFn x) j hj
  rw [List.length_ofFn, e] at this
  rw [this]
  simp [hs, ht]

lemma gate_eta {g : Gate} {o : GateOp} {l : List ℕ} (h1 : g.op = o) (h2 : g.inputs = l) :
    g = ⟨o, l⟩ := by
  cases g; cases h1; cases h2; rfl

lemma gDv {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := gD x ⟨w, hw⟩
lemma ok_ao {n : ℕ} {gs : List Gate} {w : ℕ} (hok : Ok n gs) : TopForm.IsAO2 n ⟨gs, w⟩ := by
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

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def isAnd (C : Circuit) (j : ℕ) : Bool :=
  match (gateAt C j).op with
  | .and => true
  | _ => false

def val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run C.gates (List.ofFn x)).getD w false

def cutVal (n : ℕ) (C : Circuit) (Del : Finset ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  u n (isAnd C) (fun j => opnd C j 0) (fun j => opnd C j 1) Del (fun _ => []) (List.ofFn x) w

lemma val_in {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val n C x w = (List.ofFn x).getD w false := by
  exact run_input C.gates (List.ofFn x) w (by simpa using hw)

lemma val_rec {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) (j : ℕ)
    (hj : j < C.gates.length) :
    val n C x (n + j) = if isAnd C j = true then
      val n C x (opnd C j 0) && val n C x (opnd C j 1)
    else val n C x (opnd C j 0) || val n C x (opnd C j 1) := by
  obtain ⟨heq, hin, ha, hb, hop⟩ := gate2 hC hj
  have hr := run_gate C.gates (List.ofFn x) j hj
  rw [List.length_ofFn, heq, hin] at hr
  rcases hop with hop | hop
  · simp only [val, hr, hop, List.map_cons, List.map_nil, if_pos ha, if_pos hb]
    simp [isAnd, hop, GateOp.eval]
  · simp only [val, hr, hop, List.map_cons, List.map_nil, if_pos ha, if_pos hb]
    simp [isAnd, hop, GateOp.eval]

lemma cutVal_le {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (Del : Finset ℕ)
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length, cutVal n C Del x w = true → val n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw h
    by_cases hin : w < n
    · simpa only [cutVal, u_in hin, val_in C x w hin] using h
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    obtain ⟨_, _, ha, hb, _⟩ := gate2 hC hj
    by_cases hd : j ∈ Del
    · simp only [cutVal, u_del hd] at h
      cases h
    rw [val_rec C hC x j hj]
    cases hA : isAnd C j with
    | false =>
      simp only [hA, Bool.false_eq_true, ↓reduceIte]
      rw [cutVal, u_or hd hA ha hb, Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Bool.or_eq_true]; exact Or.inl (ih _ ha (by omega) h)
      · rw [Bool.or_eq_true]; exact Or.inr (ih _ hb (by omega) h)
    | true =>
      simp only [hA, ↓reduceIte]
      rw [cutVal, u_and hd hA ha hb] at h
      simp only [List.any_nil, Bool.or_false, Bool.and_eq_true] at h
      rw [Bool.and_eq_true]; exact ⟨ih _ ha (by omega) h.1, ih _ hb (by omega) h.2⟩

lemma cutVal_eq_of_zero {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (x : Fin n → Bool) (hz : val n C x (n + j) = false) :
    ∀ w < n + C.gates.length, cutVal n C {j} x w = val n C x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · simp only [cutVal, u_in hin, val_in C x w hin]
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    obtain ⟨_, _, ha, hb, _⟩ := gate2 hC hk
    by_cases hd : k ∈ ({j} : Finset ℕ)
    · have hkj : k = j := Finset.mem_singleton.mp hd
      subst k
      rw [cutVal, u_del (Finset.mem_singleton_self j), hz]
    rw [val_rec C hC x k hk]
    have ia := ih (opnd C k 0) ha (by omega)
    have ib := ih (opnd C k 1) hb (by omega)
    cases hA : isAnd C k with
    | false =>
      simp only [hA, Bool.false_eq_true, ↓reduceIte]
      rw [cutVal, u_or hd hA ha hb]
      exact congrArg₂ Bool.or ia ib
    | true =>
      simp only [hA, ↓reduceIte]
      rw [cutVal, u_and hd hA ha hb]
      simp only [List.any_nil, Bool.or_false]
      exact congrArg₂ Bool.and ia ib

lemma cutVal_mono {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (Del : Finset ℕ)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) (hw : w < n + C.gates.length) :
    cutVal n C Del x w = true → cutVal n C Del y w = true := by
  have hab : ∀ j < C.gates.length, opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
    intro j hj
    exact ⟨(gate2 hC hj).2.2.1, (gate2 hC hj).2.2.2.1⟩
  have hget : ∀ t, (List.ofFn x).getD t false = true → (List.ofFn y).getD t false = true := by
    intro t ht
    by_cases ht' : t < n
    · rw [gDv y t ht']
      exact hxy ⟨t, ht'⟩ (by simpa only [gDv x t ht'] using ht)
    · have : (List.ofFn x).getD t false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [this] at ht
      cases ht
  exact u_mono hab (List.ofFn x) (List.ofFn y) hget w hw

lemma val_out {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    val n C x C.output = circuitFun n C x := rfl

lemma output_lt {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hF : circuitFun n C = graphFun G ∅) (hE : G.edgeFinset.Nonempty) :
    C.output < n + C.gates.length := by
  have hE' : ∃ p q, G.Adj p q := by
    obtain ⟨e, he⟩ := hE
    induction e using Sym2.ind with
    | _ p q => exact ⟨p, q, by simpa using he⟩
  obtain ⟨p, q, hpq⟩ := hE'
  have htrue : val n C (fun _ => true) C.output = true := by
    rw [val_out, hF]
    exact (gf G _).mpr ⟨p, q, hpq, rfl, rfl⟩
  by_contra h
  have hfalse : val n C (fun _ => true) C.output = false :=
    List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn]; omega)
  rw [hfalse] at htrue
  cases htrue

lemma compile_cut {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (hout : C.output < n + C.gates.length) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
      ∀ x : Fin n → Bool, circuitFun n D x = cutVal n C {j} x C.output := by
  obtain ⟨gs, m, hok, hm, _, hsize, _⟩ := build n (isAnd C)
    (fun k => opnd C k 0) (fun k => opnd C k 1) {j} ∅ (fun _ => [])
    (fun _ => false) (by simp) (by simp) C.gates.length
    (fun k hk => ⟨(gate2 hC hk).2.2.1, (gate2 hC hk).2.2.2.1⟩)
  have hcard : ((Finset.range C.gates.length).filter (· ∈ ({j} : Finset ℕ))).card = 1 := by
    have : (Finset.range C.gates.length).filter (· ∈ ({j} : Finset ℕ)) = {j} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      omega
    rw [this]
    simp
  simp only [hcard, Finset.notMem_empty, Finset.filter_false, Finset.card_empty,
    Nat.add_zero, List.length_nil, Finset.sum_const_zero] at hsize
  rcases hm C.output hout with ⟨hbound, heq⟩
  cases ho : m C.output with
  | none =>
    refine ⟨⟨gs, n + gs.length⟩, ok_ao hok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    have hfalse : (run gs (List.ofFn x)).getD (n + gs.length) false = false :=
      List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn])
    change (run gs (List.ofFn x)).getD (n + gs.length) false = _
    rw [hfalse]
    have hh := heq x
    simpa only [ho, ov, cutVal] using hh
  | some w =>
    refine ⟨⟨gs, w⟩, ok_ao hok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    change (run gs (List.ofFn x)).getD w false = _
    have hh := heq x
    simpa only [ho, ov, cutVal] using hh

lemma least_gate_critical {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hE : G.edgeFinset.Nonempty) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ cutVal n C {j} (pairInput p q) C.output = false := by
  have hout := output_lt G C hL.2.1 hE
  by_contra h
  push Not at h
  have hF : ∀ x : Fin n → Bool, cutVal n C {j} x C.output = graphFun G ∅ x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      have hval := cutVal_le C hL.1 {j} x C.output hout hx
      rwa [val_out, hL.2.1] at hval
    · intro hx
      obtain ⟨p, q, hpq, hp, hq⟩ := (gf G x).mp hx
      have hedge : cutVal n C {j} (pairInput p q) C.output = true := by
        cases ht : cutVal n C {j} (pairInput p q) C.output
        · exact (h p q hpq ht).elim
        · rfl
      apply cutVal_mono C hL.1 {j} (pairInput p q) x ?_ C.output hout hedge
      intro i hi
      have : i = p ∨ i = q := by simpa [pairInput] using hi
      rcases this with rfl | rfl <;> assumption
  obtain ⟨D, hAO, hsize, heq⟩ := compile_cut C hL.1 j hj hout
  have hDF : circuitFun n D = graphFun G ∅ := funext fun x => (heq x).trans (hF x)
  have hmin := hL.2.2 D hAO hDF
  omega

lemma least_gate_hits_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hE : G.edgeFinset.Nonempty) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ gateVal n C j (pairInput p q) = true := by
  obtain ⟨p, q, hpq, hcut⟩ := least_gate_critical G C hL hE j hj
  refine ⟨p, q, hpq, ?_⟩
  cases hz : gateVal n C j (pairInput p q) with
  | true => rfl
  | false =>
    have heq := cutVal_eq_of_zero C hL.1 j (pairInput p q) hz C.output
      (output_lt G C hL.2.1 hE)
    rw [hcut, val_out, hL.2.1] at heq
    have hf : graphFun G ∅ (pairInput p q) = true :=
      (gf G _).mpr ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
    rw [hf] at heq
    cases heq

lemma least_gammaE_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hE : G.edgeFinset.Nonempty) (j : ℕ)
    (hj : j < C.gates.length) : (gammaE G C j).Nonempty := by
  obtain ⟨p, q, hpq, hjpq⟩ := least_gate_hits_edge G C hL hE j hj
  exact ⟨s(p, q), Finset.mem_filter.mpr ⟨by simpa using hpq, p, q, rfl, hjpq⟩⟩

lemma cutVal_eq_set {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j : ℕ)
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length,
      cutVal n C {j} x w =
        (run (C.gates.set j ⟨GateOp.or, []⟩) (List.ofFn x)).getD w false := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · rw [cutVal, u_in hin, run_input _ _ w (by simpa using hin)]
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have hk' : k < (C.gates.set j ⟨GateOp.or, []⟩).length := by simpa using hk
    have hrec := run_gate (C.gates.set j ⟨GateOp.or, []⟩) (List.ofFn x) k hk'
    rw [List.length_ofFn] at hrec
    by_cases hkj : k = j
    · subst k
      rw [cutVal, u_del (Finset.mem_singleton_self j), hrec]
      simp [GateOp.eval]
    have hnot : k ∉ ({j} : Finset ℕ) := by simpa using hkj
    have hgt : (C.gates.set j ⟨GateOp.or, []⟩)[k] = C.gates[k] := by
      simp [List.getElem_set, hkj, Ne.symm hkj]
    obtain ⟨heq, hinp, ha, hb, hop⟩ := gate2 hC hk
    rw [hgt, heq, hinp] at hrec
    simp only [List.map_cons, List.map_nil, if_pos ha, if_pos hb] at hrec
    have ia := ih (opnd C k 0) ha (by omega)
    have ib := ih (opnd C k 1) hb (by omega)
    rcases hop with hop | hop
    · have hA : isAnd C k = true := by simp [isAnd, hop]
      rw [cutVal, u_and hnot hA ha hb, hrec, hop]
      simp only [List.any_nil, Bool.or_false, GateOp.eval, List.all_cons, List.all_nil,
        Bool.and_true, id_eq]
      exact congrArg₂ Bool.and ia ib
    · have hA : isAnd C k = false := by simp [isAnd, hop]
      rw [cutVal, u_or hnot hA ha hb, hrec, hop]
      simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id_eq]
      exact congrArg₂ Bool.or ia ib

lemma least_gate_critical_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hE : G.edgeFinset.Nonempty) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ gateVal n C j (pairInput p q) = true ∧
      circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput p q) = false := by
  obtain ⟨p, q, hpq, hcut⟩ := least_gate_critical G C hL hE j hj
  have hkill : circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput p q) = false := by
    change (run (C.gates.set j ⟨GateOp.or, []⟩) (List.ofFn (pairInput p q))).getD C.output false = false
    rw [← cutVal_eq_set C hL.1 j (pairInput p q) C.output (output_lt G C hL.2.1 hE)]
    exact hcut
  refine ⟨p, q, hpq, ?_, hkill⟩
  cases hz : gateVal n C j (pairInput p q) with
  | true => rfl
  | false =>
    have heq := cutVal_eq_of_zero C hL.1 j (pairInput p q) hz C.output
      (output_lt G C hL.2.1 hE)
    rw [hcut, val_out, hL.2.1] at heq
    have hf : graphFun G ∅ (pairInput p q) = true :=
      (gf G _).mpr ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
    rw [hf] at heq
    cases heq

lemma least_nonempty_of_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length) :
    G.edgeFinset.Nonempty := by
  by_contra hempty
  have hempty : G.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
  have hadj : ∀ p q : Fin n, ¬ G.Adj p q := by
    intro p q hpq
    have he : s(p, q) ∈ G.edgeFinset := by simpa using hpq
    rw [hempty] at he
    exact Finset.notMem_empty _ he
  let D : Circuit := ⟨[], n⟩
  have hAO : IsAO2 n D := by
    simp [IsAO2, AndOrOnly, ReadsBack, D]
  have hF : circuitFun n D = graphFun G ∅ := by
    funext x
    have hfalse : graphFun G ∅ x = false := by
      cases hx : graphFun G ∅ x with
      | false => rfl
      | true =>
        obtain ⟨p, q, hpq, _, _⟩ := (gf G x).mp hx
        exact (hadj p q hpq).elim
    rw [hfalse]
    simp [circuitFun, D, Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
  have hsize := hL.2.2 D hAO hF
  simp only [Circuit.size, D, List.length_nil] at hsize
  omega

lemma least_gate_critical_edge_of_least {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (j : ℕ)
    (hj : j < C.gates.length) :
    ∃ p q : Fin n, G.Adj p q ∧ gateVal n C j (pairInput p q) = true ∧
      circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput p q) = false := by
  exact least_gate_critical_edge G C hL (least_nonempty_of_gate G C hL j hj) j hj

lemma least_gammaE_nonempty_of_least {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (j : ℕ)
    (hj : j < C.gates.length) : (gammaE G C j).Nonempty := by
  exact least_gammaE_nonempty G C hL (least_nonempty_of_gate G C hL j hj) j hj

end CriticalEdge

namespace CriticalEdge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def aliasWire (n j b w : ℕ) : ℕ := if w = n + j then b else w

def aliasVal (n : ℕ) (C : Circuit) (j b : ℕ) (x : Fin n → Bool) (w : ℕ) : Bool :=
  u n (isAnd C) (fun k => aliasWire n j b (opnd C k 0))
    (fun k => aliasWire n j b (opnd C k 1)) {j} (fun _ => []) (List.ofFn x) (aliasWire n j b w)

lemma alias_le {n j b w : ℕ} (hb : b < n + j) : aliasWire n j b w ≤ w := by
  unfold aliasWire
  split_ifs with h <;> omega

lemma aliasVal_in {n : ℕ} (C : Circuit) (j b : ℕ) (x : Fin n → Bool)
    (w : ℕ) (hw : w < n) : aliasVal n C j b x w = (List.ofFn x).getD w false := by
  have h : w ≠ n + j := by omega
  simp only [aliasVal, aliasWire, if_neg h, u_in hw]

lemma aliasVal_here {n : ℕ} (C : Circuit) (j b : ℕ) (hb : b < n + j)
    (x : Fin n → Bool) : aliasVal n C j b x (n + j) = aliasVal n C j b x b := by
  simp [aliasVal, aliasWire, Nat.ne_of_lt hb]

lemma aliasVal_rec {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j b : ℕ)
    (hb : b < n + j) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hkj : k ≠ j) :
    aliasVal n C j b x (n + k) = if isAnd C k = true then
      aliasVal n C j b x (opnd C k 0) && aliasVal n C j b x (opnd C k 1)
    else aliasVal n C j b x (opnd C k 0) || aliasVal n C j b x (opnd C k 1) := by
  obtain ⟨_, _, ha, hc, _⟩ := gate2 hC hk
  have hnkj : n + k ≠ n + j := by omega
  have hnot : k ∉ ({j} : Finset ℕ) := by simpa using hkj
  have ha' : aliasWire n j b (opnd C k 0) < n + k := lt_of_le_of_lt (alias_le hb) ha
  have hc' : aliasWire n j b (opnd C k 1) < n + k := lt_of_le_of_lt (alias_le hb) hc
  unfold aliasVal
  rw [show aliasWire n j b (n + k) = n + k by unfold aliasWire; exact if_neg hnkj]
  cases hA : isAnd C k with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact u_or hnot hA ha' hc'
  | true =>
    simp only [↓reduceIte]
    simpa only [List.any_nil, Bool.or_false] using u_and (L := fun _ => []) hnot hA ha' hc'

lemma aliasVal_le {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j b : ℕ)
    (hb : b < n + j) (x : Fin n → Bool)
    (hsmall : val n C x b = true → val n C x (n + j) = true) :
    ∀ w < n + C.gates.length, aliasVal n C j b x w = true → val n C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx
    by_cases hin : w < n
    · simpa only [aliasVal_in C j b x w hin, val_in C x w hin] using hx
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    by_cases hkj : k = j
    · subst k
      rw [aliasVal_here C j b hb x] at hx
      exact hsmall (ih b hb (by omega) hx)
    obtain ⟨_, _, ha, hc, _⟩ := gate2 hC hk
    rw [aliasVal_rec C hC j b hb x k hk hkj] at hx
    rw [val_rec C hC x k hk]
    cases hA : isAnd C k with
    | false =>
      simp only [hA, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true] at hx ⊢
      rcases hx with h | h
      · exact Or.inl (ih _ ha (by omega) h)
      · exact Or.inr (ih _ hc (by omega) h)
    | true =>
      simp only [hA, ↓reduceIte, Bool.and_eq_true] at hx ⊢
      exact ⟨ih _ ha (by omega) hx.1, ih _ hc (by omega) hx.2⟩

lemma aliasVal_eq {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j b : ℕ)
    (hb : b < n + j) (x : Fin n → Bool) (heq : val n C x b = val n C x (n + j)) :
    ∀ w < n + C.gates.length, aliasVal n C j b x w = val n C x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hin : w < n
    · simp only [aliasVal_in C j b x w hin, val_in C x w hin]
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    by_cases hkj : k = j
    · subst k
      rw [aliasVal_here C j b hb x, ih b hb (by omega), heq]
    obtain ⟨_, _, ha, hc, _⟩ := gate2 hC hk
    rw [aliasVal_rec C hC j b hb x k hk hkj, val_rec C hC x k hk,
      ih _ ha (by omega), ih _ hc (by omega)]

lemma aliasVal_mono {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j b : ℕ)
    (hb : b < n + j) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) (hw : w < n + C.gates.length) :
    aliasVal n C j b x w = true → aliasVal n C j b y w = true := by
  have hab : ∀ k < C.gates.length,
      aliasWire n j b (opnd C k 0) < n + k ∧ aliasWire n j b (opnd C k 1) < n + k := by
    intro k hk
    exact ⟨lt_of_le_of_lt (alias_le hb) (gate2 hC hk).2.2.1,
      lt_of_le_of_lt (alias_le hb) (gate2 hC hk).2.2.2.1⟩
  have hget : ∀ t, (List.ofFn x).getD t false = true → (List.ofFn y).getD t false = true := by
    intro t ht
    by_cases ht' : t < n
    · rw [gDv y t ht']
      exact hxy ⟨t, ht'⟩ (by simpa only [gDv x t ht'] using ht)
    · have : (List.ofFn x).getD t false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [this] at ht
      cases ht
  exact u_mono hab (List.ofFn x) (List.ofFn y) hget _ (lt_of_le_of_lt (alias_le hb) hw)

lemma compile_alias {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j b : ℕ)
    (hb : b < n + j) (hj : j < C.gates.length) (hout : C.output < n + C.gates.length) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧
      ∀ x : Fin n → Bool, circuitFun n D x = aliasVal n C j b x C.output := by
  have hab : ∀ k < C.gates.length,
      aliasWire n j b (opnd C k 0) < n + k ∧ aliasWire n j b (opnd C k 1) < n + k := by
    intro k hk
    exact ⟨lt_of_le_of_lt (alias_le hb) (gate2 hC hk).2.2.1,
      lt_of_le_of_lt (alias_le hb) (gate2 hC hk).2.2.2.1⟩
  obtain ⟨gs, m, hok, hm, _, hsize, _⟩ := build n (isAnd C)
    (fun k => aliasWire n j b (opnd C k 0)) (fun k => aliasWire n j b (opnd C k 1))
    {j} ∅ (fun _ => []) (fun _ => false) (by simp) (by simp) C.gates.length hab
  have hcard : ((Finset.range C.gates.length).filter (· ∈ ({j} : Finset ℕ))).card = 1 := by
    have : (Finset.range C.gates.length).filter (· ∈ ({j} : Finset ℕ)) = {j} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      omega
    rw [this]
    simp
  simp only [hcard, Finset.notMem_empty, Finset.filter_false, Finset.card_empty,
    Nat.add_zero, List.length_nil, Finset.sum_const_zero] at hsize
  rcases hm (aliasWire n j b C.output) (lt_of_le_of_lt (alias_le hb) hout) with ⟨hbound, heq⟩
  cases ho : m (aliasWire n j b C.output) with
  | none =>
    refine ⟨⟨gs, n + gs.length⟩, ok_ao hok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    have hfalse : (run gs (List.ofFn x)).getD (n + gs.length) false = false :=
      List.getD_eq_default _ _ (by rw [run_length, List.length_ofFn])
    change (run gs (List.ofFn x)).getD (n + gs.length) false = _
    rw [hfalse]
    have hh := heq x
    simpa only [ho, ov, aliasVal] using hh
  | some w =>
    refine ⟨⟨gs, w⟩, ok_ao hok, by simp only [Circuit.size]; omega, ?_⟩
    intro x
    change (run gs (List.ofFn x)).getD w false = _
    have hh := heq x
    simpa only [ho, ov, aliasVal] using hh

lemma least_alias_impossible {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j b : ℕ) (hb : b < n + j)
    (hj : j < C.gates.length)
    (hsmall : ∀ x : Fin n → Bool, val n C x b = true → val n C x (n + j) = true)
    (hedge : ∀ p q : Fin n, G.Adj p q → val n C (pairInput p q) b = val n C (pairInput p q) (n + j)) :
    False := by
  have hE := least_nonempty_of_gate G C hL j hj
  have hout := output_lt G C hL.2.1 hE
  have hF : ∀ x : Fin n → Bool, aliasVal n C j b x C.output = graphFun G ∅ x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      have hval := aliasVal_le C hL.1 j b hb x (hsmall x) C.output hout hx
      rwa [val_out, hL.2.1] at hval
    · intro hx
      obtain ⟨p, q, hpq, hp, hq⟩ := (gf G x).mp hx
      have hpair : aliasVal n C j b (pairInput p q) C.output = true := by
        rw [aliasVal_eq C hL.1 j b hb (pairInput p q) (hedge p q hpq) C.output hout,
          val_out, hL.2.1]
        exact (gf G _).mpr ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
      apply aliasVal_mono C hL.1 j b hb (pairInput p q) x ?_ C.output hout hpair
      intro i hi
      have : i = p ∨ i = q := by simpa [pairInput] using hi
      rcases this with rfl | rfl <;> assumption
  obtain ⟨D, hAO, hsize, heq⟩ := compile_alias C hL.1 j b hb hj hout
  have hDF : circuitFun n D = graphFun G ∅ := funext fun x => (heq x).trans (hF x)
  have hmin := hL.2.2 D hAO hDF
  omega

lemma least_read_input_incident {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length)
    (z : Fin n) (hread : z.val ∈ (gateAt C j).inputs) : ∃ v : Fin n, G.Adj z v := by
  by_contra hiso
  push Not at hiso
  have hzpair : ∀ p q : Fin n, G.Adj p q → val n C (pairInput p q) z.val = false := by
    intro p q hpq
    rw [val_in C _ z.val z.isLt, gD]
    cases hz : pairInput p q z with
    | false => rfl
    | true =>
      have : z = p ∨ z = q := by simpa [pairInput] using hz
      rcases this with rfl | rfl
      · exact (hiso q hpq).elim
      · exact (hiso p hpq.symm).elim
  obtain ⟨_, hinp, ha, hb, hop⟩ := gate2 hL.1 hj
  rw [hinp] at hread
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hread
  rcases hop with hop | hop
  · obtain ⟨p, q, hpq, hgate, _⟩ := least_gate_critical_edge_of_least G C hL j hj
    have hval : val n C (pairInput p q) (n + j) = true := hgate
    rw [val_rec C hL.1 _ j hj] at hval
    have hA : isAnd C j = true := by simp [isAnd, hop]
    simp only [hA, ↓reduceIte, Bool.and_eq_true] at hval
    rcases hread with h | h
    · have := hval.1
      rw [← h, hzpair p q hpq] at this
      cases this
    · have := hval.2
      rw [← h, hzpair p q hpq] at this
      cases this
  · have hA : isAnd C j = false := by simp [isAnd, hop]
    rcases hread with h | h
    · apply least_alias_impossible G C hL j (opnd C j 1) hb hj
      · intro x hx
        rw [val_rec C hL.1 x j hj]
        simp [hA, hx]
      · intro p q hpq
        rw [val_rec C hL.1 _ j hj]
        simp [hA, ← h, hzpair p q hpq]
    · apply least_alias_impossible G C hL j (opnd C j 0) ha hj
      · intro x hx
        rw [val_rec C hL.1 x j hj]
        simp [hA, hx]
      · intro p q hpq
        rw [val_rec C hL.1 _ j hj]
        simp [hA, ← h, hzpair p q hpq]

lemma least_no_edge_equivalent_earlier_wire {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (j b : ℕ)
    (hb : b < n + j) (hj : j < C.gates.length)
    (hsmall : ∀ x : Fin n → Bool, wireVal n C b x = true → gateVal n C j x = true)
    (hedge : ∀ p q : Fin n, G.Adj p q →
      wireVal n C b (pairInput p q) = gateVal n C j (pairInput p q)) : False := by
  exact least_alias_impossible G C hL j b hb hj hsmall hedge

lemma least_edge_separates_earlier_wire {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (j b : ℕ)
    (hb : b < n + j) (hj : j < C.gates.length)
    (hsmall : ∀ x : Fin n → Bool, wireVal n C b x = true → gateVal n C j x = true) :
    ∃ p q : Fin n, G.Adj p q ∧ gateVal n C j (pairInput p q) = true ∧
      wireVal n C b (pairInput p q) = false := by
  by_contra h
  push Not at h
  apply least_no_edge_equivalent_earlier_wire G C hL j b hb hj hsmall
  intro p q hpq
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact hsmall (pairInput p q)
  · intro hjtrue
    have hbnot := h p q hpq hjtrue
    cases heq : wireVal n C b (pairInput p q) with
    | false => exact (hbnot heq).elim
    | true => rfl

end CriticalEdge

namespace CriticalEdge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma aliasVal_ge {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j b : ℕ)
    (hb : b < n + j) (x : Fin n → Bool)
    (hlarge : val n C x (n + j) = true → val n C x b = true) :
    ∀ w < n + C.gates.length, val n C x w = true → aliasVal n C j b x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hx
    by_cases hin : w < n
    · simpa only [aliasVal_in C j b x w hin, val_in C x w hin] using hx
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    by_cases hkj : k = j
    · subst k
      rw [aliasVal_here C j b hb x]
      exact ih b hb (by omega) (hlarge hx)
    obtain ⟨_, _, ha, hc, _⟩ := gate2 hC hk
    rw [val_rec C hC x k hk] at hx
    rw [aliasVal_rec C hC j b hb x k hk hkj]
    cases hA : isAnd C k with
    | false =>
      simp only [hA, Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true] at hx ⊢
      rcases hx with h | h
      · exact Or.inl (ih _ ha (by omega) h)
      · exact Or.inr (ih _ hc (by omega) h)
    | true =>
      simp only [hA, ↓reduceIte, Bool.and_eq_true] at hx ⊢
      exact ⟨ih _ ha (by omega) hx.1, ih _ hc (by omega) hx.2⟩

lemma least_boundary_alias_impossible {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (j b : ℕ)
    (hb : b < n + j) (hj : j < C.gates.length)
    (hnegative : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      wireVal n C b x = true → gateVal n C j x = true)
    (hedge : ∀ p q : Fin n, G.Adj p q →
      gateVal n C j (pairInput p q) = true → wireVal n C b (pairInput p q) = true) :
    False := by
  have hE := least_nonempty_of_gate G C hL j hj
  have hout := output_lt G C hL.2.1 hE
  have hF : ∀ x : Fin n → Bool, aliasVal n C j b x C.output = graphFun G ∅ x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      cases hg : graphFun G ∅ x with
      | true => rfl
      | false =>
        have hval := aliasVal_le C hL.1 j b hb x (hnegative x hg) C.output hout hx
        rw [val_out, hL.2.1, hg] at hval
        cases hval
    · intro hx
      obtain ⟨p, q, hpq, hp, hq⟩ := (gf G x).mp hx
      have hpair : aliasVal n C j b (pairInput p q) C.output = true := by
        apply aliasVal_ge C hL.1 j b hb (pairInput p q) (hedge p q hpq) C.output hout
        rw [val_out, hL.2.1]
        exact (gf G _).mpr ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
      apply aliasVal_mono C hL.1 j b hb (pairInput p q) x ?_ C.output hout hpair
      intro i hi
      have : i = p ∨ i = q := by simpa [pairInput] using hi
      rcases this with rfl | rfl <;> assumption
  obtain ⟨D, hAO, hsize, heq⟩ := compile_alias C hL.1 j b hb hj hout
  have hDF : circuitFun n D = graphFun G ∅ := funext fun x => (heq x).trans (hF x)
  have hmin := hL.2.2 D hAO hDF
  omega

end CriticalEdge

namespace SmallBase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma graphFun_three (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj]
    (x : Fin 3 → Bool) :
    graphFun G ∅ x =
      ((decide (G.Adj 0 1) && x 0 && x 1) ||
       (decide (G.Adj 0 2) && x 0 && x 2) ||
       (decide (G.Adj 1 2) && x 1 && x 2)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  simp [Fin.exists_fin_succ, SimpleGraph.adj_comm]
  tauto

lemma bipartite_not_triangle (G : SimpleGraph (Fin 3)) (s : Fin 3 → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) :
    ¬ (G.Adj 0 1 ∧ G.Adj 0 2 ∧ G.Adj 1 2) := by
  rintro ⟨h01, h02, h12⟩
  have a := hbip 0 1 h01
  have b := hbip 0 2 h02
  have c := hbip 1 2 h12
  cases hs0 : s 0 <;> cases hs1 : s 1 <;> cases hs2 : s 2 <;>
    simp_all

def emptyC : Circuit := ⟨[], 3⟩

def edgeC (a b : ℕ) : Circuit := ⟨[⟨GateOp.and, [a, b]⟩], 3⟩

def starC (a b c : ℕ) : Circuit :=
  ⟨[⟨GateOp.or, [b, c]⟩, ⟨GateOp.and, [a, 3]⟩], 4⟩

lemma least_three_size (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin 3 → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) : C.size ≤ 2 := by
  have hnot := bipartite_not_triangle G s hbip
  have hcalc := graphFun_three G
  by_cases h01 : G.Adj 0 1 <;> by_cases h02 : G.Adj 0 2 <;>
      by_cases h12 : G.Adj 1 2
  · exact (hnot ⟨h01, h02, h12⟩).elim
  · apply (hL.2.2 (starC 0 1 2) (by decide) ?_).trans (by decide)
    funext x
    rw [hcalc]
    simp [starC, circuitFun, Circuit.eval, Circuit.wires, GateOp.eval,
      List.ofFn_succ, h01, h02, h12]
    cases x 0 <;> cases x 1 <;> cases x 2 <;> decide
  · apply (hL.2.2 (starC 1 0 2) (by decide) ?_).trans (by decide)
    funext x
    rw [hcalc]
    simp [starC, circuitFun, Circuit.eval, Circuit.wires, GateOp.eval,
      List.ofFn_succ, h01, h02, h12, Bool.and_comm]
    cases x 0 <;> cases x 1 <;> cases x 2 <;> decide
  · apply (hL.2.2 (edgeC 0 1) (by decide) ?_).trans (by decide)
    funext x
    rw [hcalc]
    simp [edgeC, circuitFun, Circuit.eval, Circuit.wires, GateOp.eval,
      List.ofFn_succ, h01, h02, h12]
  · apply (hL.2.2 (starC 2 0 1) (by decide) ?_).trans (by decide)
    funext x
    rw [hcalc]
    simp [starC, circuitFun, Circuit.eval, Circuit.wires, GateOp.eval,
      List.ofFn_succ, h01, h02, h12, Bool.and_comm]
    cases x 0 <;> cases x 1 <;> cases x 2 <;> decide
  · apply (hL.2.2 (edgeC 0 2) (by decide) ?_).trans (by decide)
    funext x
    rw [hcalc]
    simp [edgeC, circuitFun, Circuit.eval, Circuit.wires, GateOp.eval,
      List.ofFn_succ, h01, h02, h12]
  · apply (hL.2.2 (edgeC 1 2) (by decide) ?_).trans (by decide)
    funext x
    rw [hcalc]
    simp [edgeC, circuitFun, Circuit.eval, Circuit.wires, GateOp.eval,
      List.ofFn_succ, h01, h02, h12]
  · apply (hL.2.2 emptyC (by decide) ?_).trans (by decide)
    funext x
    rw [hcalc]
    simp [emptyC, circuitFun, Circuit.eval, Circuit.wires,
      List.ofFn_succ, h01, h02, h12]

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

lemma graphFun_singleton {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) : graphFun G ∅ (fun v => decide (v = u)) = false := by
  simp [graphFun]

lemma positive_least_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hpos : 0 < C.size) :
    n ≤ C.output ∧ C.output < n + C.size := by
  constructor
  · by_contra h
    have hlt : C.output < n := by omega
    let u : Fin n := ⟨C.output, hlt⟩
    let x : Fin n → Bool := fun v => decide (v = u)
    have hf := congrFun hL.2.1 x
    have hg := graphFun_singleton G u
    change (C.gates.foldl stepW (List.ofFn x)).getD C.output false = _ at hf
    rw [foldl_getD_lt _ _ _ (by simpa using hlt)] at hf
    simp [List.getD_eq_getElem?_getD, hlt, x, u, hg] at hf
  · by_contra h
    have hge : n + C.size ≤ C.output := by omega
    have hf : circuitFun n C = (fun _ => false) := by
      funext x
      change (C.gates.foldl stepW (List.ofFn x)).getD C.output false = false
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by simp [foldl_len]; exact hge)]
      rfl
    have hzero := hL.2.2 (⟨[], n⟩ : Circuit) (by
      simp [IsAO2, AndOrOnly, ReadsBack, gateAt]) (by
      rw [← hL.2.1, hf]
      funext x
      simp [circuitFun, Circuit.eval, Circuit.wires,
        List.getD_eq_getElem?_getD])
    change C.size ≤ 0 at hzero
    omega

lemma junk_card_lt_size {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (hpos : 0 < C.size) :
    (junk G C).card < C.size := by
  obtain ⟨hlo, hhi⟩ := positive_least_output G C hL hpos
  have hi : C.output - n ∈ Finset.range C.size := by
    simp only [Finset.mem_range]
    omega
  have hnot : C.output - n ∉ junk G C := by
    intro hmem
    obtain ⟨_, _, x, hx, hxF⟩ := (Finset.mem_filter.mp hmem).2
    have houtput : n + (C.output - n) = C.output := by omega
    have he := congrFun hL.2.1 x
    change (C.wires (List.ofFn x)).getD C.output false = _ at he
    unfold gateVal at hx
    rw [houtput, he, hxF] at hx
    contradiction
  have hsub : junk G C ⊂ Finset.range C.size :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, by
      intro h
      exact hnot (h.symm ▸ hi)⟩
  have hc := Finset.card_lt_card hsub
  simpa using hc

lemma no_two_junk_three (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin 3 → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) : (junk G C).card ≠ 2 := by
  intro hj
  have hbound := least_three_size G C s hbip hL
  have hsub : (junk G C).card ≤ C.size :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range _)
  have hstrict := junk_card_lt_size G C hL (by omega)
  omega

end SmallBase

namespace ColorCount

lemma pair_signatures_le_outputs (E : Finset (Fin 2 × Fin 2)) :
    E.card ≤ (E.image Prod.fst).card + (E.image Prod.snd).card := by
  revert E
  decide

lemma mixed_pair_signatures_le_outputs (E : Finset (Fin 2 × Fin 2))
    (L R : Finset (Fin 2))
    (hL : E.image Prod.fst ⊆ L) (hR : E.image Prod.snd ⊆ R) :
    E.card ≤ L.card + R.card :=
  (pair_signatures_le_outputs E).trans
    (Nat.add_le_add (Finset.card_le_card hL) (Finset.card_le_card hR))

lemma split_pair_cost (E₀ E₁ : Finset (Fin 2 × Fin 2))
    (L R : Finset (Fin 2))
    (hL : (E₀ ∩ E₁).image Prod.fst ⊆ L)
    (hR : (E₀ ∩ E₁).image Prod.snd ⊆ R) :
    E₀.card + E₁.card ≤ (E₀ ∪ E₁).card + L.card + R.card := by
  have hm := mixed_pair_signatures_le_outputs (E₀ ∩ E₁) L R hL hR
  have hc := Finset.card_union_add_card_inter E₀ E₁
  omega

end ColorCount

namespace ColorProjection

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

def setOr {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

def project {n : ℕ} (A : Finset (Fin n)) (s : Fin n → Bool) (c : Bool) : Finset (Fin n) :=
  A.filter (fun a => s a = c)

def mono {n : ℕ} (s : Fin n → Bool) (c : Bool) : Fin n → Bool :=
  fun v => decide (s v = c)

lemma project_le {n : ℕ} (A : Finset (Fin n)) (s : Fin n → Bool) (c : Bool)
    (x : Fin n → Bool) : setOr (project A s c) x = true → setOr A x = true := by
  simp only [setOr, decide_eq_true_eq, project, Finset.mem_filter]
  rintro ⟨a, ⟨ha, _⟩, hx⟩
  exact ⟨a, ha, hx⟩

lemma graphFun_mono {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (c : Bool) :
    graphFun G ∅ (mono s c) = false := by
  simp only [graphFun, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  constructor
  · simp
  · rintro ⟨u, v, huv, hu, hv⟩
    have hu' : s u = c := by simpa [mono] using hu
    have hv' : s v = c := by simpa [mono] using hv
    exact hbip u v huv (hu'.trans hv'.symm)

lemma product_project_pair {n : ℕ} (A B : Finset (Fin n))
    (s : Fin n → Bool) (c : Bool) (hA : ∀ a ∈ A, s a = c)
    (hdis : Disjoint A B) (u v : Fin n) (huv : s u ≠ s v) :
    (setOr A (pairInput u v) && setOr (project B s (!c)) (pairInput u v)) =
      (setOr A (pairInput u v) && setOr B (pairInput u v)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨ha, project_le B s (!c) _ hb⟩
  · rintro ⟨ha, hb⟩
    refine ⟨ha, ?_⟩
    obtain ⟨a, haA, haUV⟩ := (of_decide_eq_true ha)
    obtain ⟨b, hbB, hbUV⟩ := (of_decide_eq_true hb)
    have haPair : a = u ∨ a = v := by simpa [pairInput] using haUV
    have hbPair : b = u ∨ b = v := by simpa [pairInput] using hbUV
    have hab : a ≠ b := fun h => Finset.disjoint_left.mp hdis haA (h ▸ hbB)
    have hbc : s b ≠ c := by
      rw [← hA a haA]
      rcases haPair with rfl | rfl <;> rcases hbPair with rfl | rfl
      · exact (hab rfl).elim
      · exact Ne.symm huv
      · exact huv
      · exact (hab rfl).elim
    have hbcolor : s b = !c := by
      cases hs : s b <;> cases hc : c <;> simp_all
    apply decide_eq_true
    exact ⟨b, Finset.mem_filter.mpr ⟨hbB, hbcolor⟩, hbUV⟩

lemma product_active_on_mono {n : ℕ} (A B : Finset (Fin n))
    (s : Fin n → Bool) (c : Bool) (hA : A.Nonempty)
    (hpure : ∀ a ∈ A, s a = c) (hB : ∃ b ∈ B, s b = c) :
    (setOr A (mono s c) && setOr B (mono s c)) = true := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb, hbc⟩ := hB
  simp only [Bool.and_eq_true, setOr, decide_eq_true_eq]
  exact ⟨⟨a, ha, by simp [mono, hpure a ha]⟩,
    ⟨b, hb, by simp [mono, hbc]⟩⟩

lemma biUnion_project {n : ℕ} (S : Finset ℕ) (A : ℕ → Finset (Fin n))
    (color : ℕ → Bool) (s : Fin n → Bool) (c : Bool)
    (hcolor : ∀ w ∈ S, ∀ i ∈ A w, s i = color w) :
    (S.filter (fun w => color w = c)).biUnion A = project (S.biUnion A) s c := by
  ext i
  simp only [Finset.mem_biUnion, Finset.mem_filter, project]
  constructor
  · rintro ⟨w, ⟨hw, hc⟩, hi⟩
    exact ⟨⟨w, hw, hi⟩, (hcolor w hw i hi).trans hc⟩
  · rintro ⟨⟨w, hw, hi⟩, hc⟩
    exact ⟨w, ⟨hw, (hcolor w hw i hi).symm.trans hc⟩, hi⟩

lemma source_projection_eq {n : ℕ} (S : Finset ℕ) (A : ℕ → Finset (Fin n))
    (color : ℕ → Bool) (s : Fin n → Bool) (c : Bool) (x : Fin n → Bool)
    (V : ℕ → Bool) (hV : ∀ w ∈ S, V w = setOr (A w) x)
    (hcolor : ∀ w ∈ S, ∀ i ∈ A w, s i = color w) :
    decide (∃ w ∈ S.filter (fun w => color w = c), V w = true) =
      setOr (project (S.biUnion A) s c) x := by
  rw [← biUnion_project S A color s c hcolor]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, setOr, Finset.mem_biUnion]
  constructor
  · rintro ⟨w, hw, hv⟩
    rw [hV w (Finset.mem_filter.mp hw).1] at hv
    obtain ⟨i, hi, hx⟩ := of_decide_eq_true hv
    exact ⟨i, ⟨w, hw, hi⟩, hx⟩
  · rintro ⟨i, ⟨w, hw, hi⟩, hx⟩
    refine ⟨w, hw, ?_⟩
    rw [hV w (Finset.mem_filter.mp hw).1]
    exact decide_eq_true ⟨i, hi, hx⟩

end ColorProjection

namespace CriticalEdge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma least_cover_boundary_alias_impossible {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hL : IsLeastAO G C) (j b : ℕ)
    (hb : b < n + j) (hj : j < C.gates.length)
    (N : Set (Fin n → Bool))
    (hcover : ∀ x : Fin n → Bool, graphFun G ∅ x = false →
      ∃ y ∈ N, graphFun G ∅ y = false ∧ ∀ i, x i = true → y i = true)
    (hnegative : ∀ x ∈ N, graphFun G ∅ x = false →
      wireVal n C b x = true → gateVal n C j x = true)
    (hedge : ∀ p q : Fin n, G.Adj p q →
      gateVal n C j (pairInput p q) = true → wireVal n C b (pairInput p q) = true) :
    False := by
  have hE := least_nonempty_of_gate G C hL j hj
  have hout := output_lt G C hL.2.1 hE
  have hF : ∀ x : Fin n → Bool, aliasVal n C j b x C.output = graphFun G ∅ x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      cases hg : graphFun G ∅ x with
      | true => rfl
      | false =>
        obtain ⟨y, hyN, hyF, hxy⟩ := hcover x hg
        have hy := aliasVal_mono C hL.1 j b hb x y hxy C.output hout hx
        have hval := aliasVal_le C hL.1 j b hb y (hnegative y hyN hyF) C.output hout hy
        rw [val_out, hL.2.1, hyF] at hval
        cases hval
    · intro hx
      obtain ⟨p, q, hpq, hp, hq⟩ := (gf G x).mp hx
      have hpair : aliasVal n C j b (pairInput p q) C.output = true := by
        apply aliasVal_ge C hL.1 j b hb (pairInput p q) (hedge p q hpq) C.output hout
        rw [val_out, hL.2.1]
        exact (gf G _).mpr ⟨p, q, hpq, by simp [pairInput], by simp [pairInput]⟩
      apply aliasVal_mono C hL.1 j b hb (pairInput p q) x ?_ C.output hout hpair
      intro i hi
      have : i = p ∨ i = q := by simpa [pairInput] using hi
      rcases this with rfl | rfl <;> assumption
  obtain ⟨D, hAO, hsize, heq⟩ := compile_alias C hL.1 j b hb hj hout
  have hDF : circuitFun n D = graphFun G ∅ := funext fun x => (heq x).trans (hF x)
  have hmin := hL.2.2 D hAO hDF
  omega

end CriticalEdge

namespace MixedFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
    (hlt : i < n + r) (hv : W n C x i = true) : W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨i, hi, by rw [if_pos hlt]; exact hv⟩

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and)
    (h : ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ W n C x i = true) :
    W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  intro i hi
  rw [if_pos (h i hi).1]; exact (h i hi).2

open PEqualNP.CleanedNonEdge in
lemma reach_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : W n C x (n + g) = true) :
    ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] → W n C x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    rcases (orSets_mem_iff n C k g hk).mp hmem with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← h]; exact hv
    · have h3 := ih (w - n) (by omega) (by omega) hx
      have e : n + (w - n) = w := by omega
      rw [e] at h3
      exact W_or n C x k hk hop w hw hlt h3

open PEqualNP.CleanedNonEdge in
lemma reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w g : ℕ)
    (h : OrReaches n C w g) (hv : W n C x (n + g) = true) : W n C x w = true := by
  obtain ⟨hn, hmem⟩ := h
  by_cases hk : w - n < C.gates.length
  · have h3 := reach_val n C x g hv (w - n) hk hmem
    have e : n + (w - n) = w := by omega
    rw [e] at h3
    exact h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma mem_filter_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α)
    (h : a ∈ @Finset.filter α p d s) : p a :=
  ((@Finset.mem_filter α p d s a).mp h).2

lemma side_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (b : Fin 2) (i : Fin n)
    (hi : i ∈ PEqualNP.TopForm.side (n := n) C j b) (hx : x i = true) :
    W n C x (PEqualNP.TopForm.opnd C j b) = true := by
  unfold PEqualNP.TopForm.side PEqualNP.TopForm.orIn at hi
  have hi2 := mem_filter_gen _ _ _ _ hi
  rcases hi2 with h | ⟨k, hk, hreach, hop, hin⟩
  · rw [← h, W_input n C x i.val i.isLt]; exact hx
  · have hk1 : W n C x (n + k) = true := by
      apply W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
      rw [W_input n C x i.val i.isLt]; exact hx
    exact reach_up n C x _ k hreach hk1

open PEqualNP.EdgeOwnership in
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
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

open PEqualNP.EdgeOwnership in
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


lemma gateAt_mem' (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]; exact List.getElem_mem hj

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ j i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i h
    obtain ⟨_, k, hk, _, h3⟩ := (inCone_iff n C i j).mp h
    rcases h3 with h3 | h3
    · omega
    · have := ih k hk i h3; omega

open PEqualNP.CleanedNonEdge in
lemma orReach_trans (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (w : ℕ) (hw : w ∈ (gateAt C k).inputs)
    (hlt : w < n + k) (g : ℕ) (h : OrReaches n C w g) : OrReaches n C (n + k) g := by
  obtain ⟨hn, hmem⟩ := h
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k g hk).mpr (Or.inr ⟨hop, w, hw, hn, hlt, hmem⟩)

open PEqualNP.CleanedNonEdge in
lemma orReach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := by
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k k hk).mpr (Or.inl rfl)

lemma orIn_mem (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open PEqualNP.CleanedNonEdge in
lemma down (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ w, W n C x w = true → (∃ i : Fin n, i ∈ PEqualNP.TopForm.orIn n C w ∧ x i = true) ∨
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.and ∧
        W n C x (n + k) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hwn : w < n
    · left
      refine ⟨⟨w, hwn⟩, (orIn_mem n C w _).mpr (Or.inl rfl), ?_⟩
      rw [← W_input n C x w hwn]; exact hv
    · by_cases hk : w - n < C.gates.length
      · have hw : w = n + (w - n) := by omega
        set k := w - n with hkdef
        rcases hAO k hk with hop | hop
        · right
          refine ⟨k, hk, ?_, hop, ?_⟩
          · rw [hw]; exact orReach_self n C k hk
          · rw [← hw]; exact hv
        · have hv2 := hv
          rw [hw, W_gate n C x k hk, hop] at hv2
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv2
          obtain ⟨i, hi, hiv⟩ := hv2
          split_ifs at hiv with hlt
          rcases ih i (by omega) hiv with ⟨j, hj, hxj⟩ | ⟨k', hk', hr, hop', hv'⟩
          · left
            refine ⟨j, ?_, hxj⟩
            rw [orIn_mem] at hj ⊢
            right
            rcases hj with hj | ⟨k'', hk'', hr, hop'', hin⟩
            · refine ⟨k, hk, ?_, hop, ?_⟩
              · rw [hw]; exact orReach_self n C k hk
              · rw [hj]; exact hi
            · refine ⟨k'', hk'', ?_, hop'', hin⟩
              rw [hw]; exact orReach_trans n C k hk hop i hi hlt k'' hr
          · right
            refine ⟨k', hk', ?_, hop', hv'⟩
            rw [hw]; exact orReach_trans n C k hk hop i hi hlt k' hr
      · exfalso
        have hl := wires_length n C x
        have : W n C x w = false := getD_ge_length _ w (by omega)
        rw [this] at hv; exact Bool.false_ne_true hv

open PEqualNP.EdgeOwnership in
lemma orSets_cone (n : ℕ) (C : Circuit) : ∀ m, m < C.gates.length → ∀ k,
    k ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD m [] → k = m ∨ InCone n C k m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm k hk
    rcases (orSets_mem_iff n C m k hm).mp hk with h | ⟨_, w, hw, hn, hlt, hx⟩
    · exact Or.inl h
    · right
      have h2 := ih (w - n) (by omega) (by omega) k hx
      have e : n + (w - n) = w := by omega
      exact (inCone_iff n C k m).mpr ⟨hm, w - n, by omega, by rw [e]; exact hw, h2⟩

open PEqualNP.EdgeOwnership in
lemma reach_cone (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (o : ℕ)
    (ho : o ∈ (gateAt C j).inputs) (hlt : o < n + j) (k : ℕ)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C o k) : InCone n C k j := by
  obtain ⟨hn, hmem⟩ := h
  have h2 := orSets_cone n C (o - n) (by omega) k hmem
  have e : n + (o - n) = o := by omega
  exact (inCone_iff n C k j).mpr ⟨hj, o - n, by omega, by rw [e]; exact ho, h2⟩

end MixedFrontier

namespace MixedFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def mono {n : ℕ} (s : Fin n → Bool) (b : Bool) : Fin n → Bool :=
  fun v => decide (s v = b)

lemma graphFun_mono_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (b : Bool) :
    graphFun G ∅ (mono s b) = false := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or]
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨u, v, huv, hu, hv⟩ := of_decide_eq_true h
  have hu' : s u = b := by simpa [mono] using hu
  have hv' : s v = b := by simpa [mono] using hv
  exact hbip u v huv (hu'.trans hv'.symm)

lemma product_active_mono_of_common_color {n : ℕ} (C : Circuit) (s : Fin n → Bool)
    (j : ℕ) (A B : Finset (Fin n))
    (heval : ∀ x : Fin n → Bool, gateVal n C j x =
      (decide (∃ u ∈ A, x u = true) && decide (∃ v ∈ B, x v = true)))
    (u v : Fin n) (hu : u ∈ A) (hv : v ∈ B) (hcolor : s u = s v) :
    ∃ c : Bool, gateVal n C j (mono s c) = true := by
  refine ⟨s u, ?_⟩
  rw [heval]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨u, hu, by simp [mono]⟩, ⟨v, hv, by simp [mono, hcolor]⟩⟩

lemma product_active_mono_of_mixed_factor {n : ℕ} (C : Circuit) (s : Fin n → Bool)
    (j : ℕ) (A B : Finset (Fin n))
    (heval : ∀ x : Fin n → Bool, gateVal n C j x =
      (decide (∃ u ∈ A, x u = true) && decide (∃ v ∈ B, x v = true)))
    (hmixed : ∀ c : Bool, ∃ u ∈ A, s u = c) (hne : B.Nonempty) :
    ∃ c : Bool, gateVal n C j (mono s c) = true := by
  obtain ⟨v, hv⟩ := hne
  obtain ⟨u, hu, hc⟩ := hmixed (s v)
  exact product_active_mono_of_common_color C s j A B heval u v hu hv hc

lemma W_all_true {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, W n C (fun _ => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hraw : w < n
    · rw [W_input n C (fun _ => true) w hraw]
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have hmem := gateAt_mem' C k hk
    have hinputs : ∀ z ∈ (gateAt C k).inputs,
        z < n + k ∧ W n C (fun _ => true) z = true := by
      intro z hz
      have hzlt := hAO.2.1 k hk z hz
      exact ⟨hzlt, ih z hzlt (by omega)⟩
    rcases hAO.1 (gateAt C k) hmem with hop | hop
    · exact W_and n C (fun _ => true) k hk hop hinputs
    · have hne : (gateAt C k).inputs ≠ [] := by
        have hlen := hAO.2.2 (gateAt C k) hmem
        intro he
        simp [he] at hlen
      obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil _ hne
      exact W_or n C (fun _ => true) k hk hop z hz (hinputs z hz).1 (hinputs z hz).2

lemma operand_mono_activity {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hAO : IsAO2 n C) (hT : TopForm G C)
    (hJ : ∀ j ∈ junk G C, ∃ c : Bool, gateVal n C j (mono s c) = true)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (b : Fin 2) : ∃ c : Bool, W n C (mono s c) (opnd C a b) = true := by
  have hga := gateAt_mem' C a ha
  have hlen := hAO.2.2 (gateAt C a) hga
  have hob : opnd C a b ∈ (gateAt C a).inputs := by
    unfold opnd
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  have hlt := hAO.2.1 a ha _ hob
  have hv := W_all_true C hAO (opnd C a b) (by omega)
  have hops : ∀ k < C.gates.length,
      (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or :=
    fun k hk => hAO.1 _ (gateAt_mem' C k hk)
  rcases down n C (fun _ => true) hops _ hv with ⟨i, hi, _⟩ | ⟨k, hk, hr, hkop, _⟩
  · refine ⟨s i, ?_⟩
    exact side_val n C (mono s (s i)) a b i hi (by simp [mono])
  · have hcone := reach_cone n C a ha _ hob hlt k hr
    have hnb : ¬ BelowF G C k := fun hbelow => hT k hk a ha hkop hbelow hop hcone
    have hex : ∃ x : Fin n → Bool, gateVal n C k x = true ∧ graphFun G ∅ x = false := by
      by_contra h
      apply hnb
      intro x hx
      by_contra hf
      exact h ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
    have hjunk : k ∈ junk G C := by
      obtain ⟨x, hx, hf⟩ := hex
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hkop, hk, x, hx, hf⟩
    obtain ⟨c, hc⟩ := hJ k hjunk
    exact ⟨c, reach_up n C (mono s c) _ k hr hc⟩

lemma top_side_monochromatic {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hT : TopForm G C)
    (hJ : ∀ j ∈ junk G C, ∃ c : Bool, gateVal n C j (mono s c) = true)
    (a : ℕ) (ha : a ∈ tops G C) (b : Fin 2) :
    ∃ c : Bool, ∀ i ∈ side (n := n) C a b, s i = c := by
  classical
  have hdata : a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
    simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
  obtain ⟨halt, hop, hbelow⟩ := hdata
  obtain ⟨c, hc⟩ := operand_mono_activity G C s hAO hT hJ a halt hop (1 - b)
  refine ⟨!c, ?_⟩
  intro i hi
  have hne : s i ≠ c := by
    intro heq
    have hib := side_val n C (mono s c) a b i hi (by simp [mono, heq])
    have hval : W n C (mono s c) (n + a) = true := by
      apply W_and n C (mono s c) a halt hop
      intro z hz
      have hlen := hAO.2.2 _ (gateAt_mem' C a halt)
      obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hz
      have hp' : p < 2 := by omega
      have hinput : (gateAt C a).inputs[p] = opnd C a ⟨p, hp'⟩ := by
        unfold opnd
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
        rfl
      refine ⟨hAO.2.1 a halt _ (List.getElem_mem hp), ?_⟩
      rw [hinput]
      have he : (⟨p, hp'⟩ : Fin 2) = b ∨ (⟨p, hp'⟩ : Fin 2) = 1 - b := by
        fin_cases b <;> omega
      rcases he with he | he
      · simpa [he] using hib
      · simpa [he] using hc
    have hf := hbelow (mono s c) hval
    rw [graphFun_mono_false G s hbip c] at hf
    cases hf
  cases hs : s i <;> cases hc : c <;> simp_all

end MixedFrontier

namespace MixedReach

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.CriticalEdge
open PEqualNP.Outside.L_meta_5012.MixedFrontier

lemma aliasVal_eq_of_unread {n : ℕ} (C : Circuit) (hC : IsAO2 n C) (j b : ℕ)
    (hb : b < n + j)
    (hunread : ∀ k < C.gates.length, n + j ∉ (gateAt C k).inputs)
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length, w ≠ n + j → aliasVal n C j b x w = val n C x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hne
    by_cases hraw : w < n
    · simp only [aliasVal_in C j b x w hraw, val_in C x w hraw]
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have hkj : k ≠ j := by omega
    obtain ⟨_, hin, ha, hc, _⟩ := gate2 hC hk
    have hna : opnd C k 0 ≠ n + j := by
      intro he
      apply hunread k hk
      rw [hin, ← he]
      simp
    have hnc : opnd C k 1 ≠ n + j := by
      intro he
      apply hunread k hk
      rw [hin, ← he]
      simp
    rw [aliasVal_rec C hC j b hb x k hk hkj, val_rec C hC x k hk,
      ih _ ha (by omega) hna, ih _ hc (by omega) hnc]

lemma least_has_reader {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j < C.gates.length)
    (hne : n + j ≠ C.output) :
    ∃ k, k < C.gates.length ∧ n + j ∈ (gateAt C k).inputs := by
  by_contra h
  push Not at h
  have hb := (gate2 hL.1 hj).2.2.1
  have hE := least_nonempty_of_gate G C hL j hj
  have hout := output_lt G C hL.2.1 hE
  obtain ⟨D, hAO, hsize, heval⟩ := compile_alias C hL.1 j (opnd C j 0) hb hj hout
  have hDF : circuitFun n D = graphFun G ∅ := by
    funext x
    rw [heval x, aliasVal_eq_of_unread C hL.1 j (opnd C j 0) hb h x C.output hout
      (Ne.symm hne), val_out, hL.2.1]
  have hmin := hL.2.2 D hAO hDF
  omega

lemma orIn_val {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (i : Fin n)
    (hi : i ∈ orIn n C w) (hx : x i = true) : W n C x w = true := by
  rcases (orIn_mem n C w i).mp hi with heq | ⟨k, hk, hr, hop, hin⟩
  · rw [← heq, W_input n C x i.val i.isLt]
    exact hx
  · have hv := W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
      (by rw [W_input n C x i.val i.isLt]; exact hx)
    exact reach_up n C x w k hr hv

lemma mixed_gate_mono {n : ℕ} (C : Circuit) (s : Fin n → Bool) (j : ℕ)
    (hmixed : ∀ c : Bool, ∃ i ∈ orIn n C (n + j), s i = c) (c : Bool) :
    W n C (mono s c) (n + j) = true := by
  obtain ⟨i, hi, hc⟩ := hmixed c
  exact orIn_val C (mono s c) (n + j) i hi (by simp [mono, hc])

lemma mixed_not_or_output {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hfun : circuitFun n C = graphFun G ∅) (j : ℕ)
    (hmixed : ∀ c : Bool, ∃ i ∈ orIn n C (n + j), s i = c) :
    ¬ OrReaches n C C.output j := by
  intro hr
  have hv := reach_up n C (mono s false) C.output j hr (mixed_gate_mono C s j hmixed false)
  change circuitFun n C (mono s false) = true at hv
  rw [hfun, graphFun_mono_false G s hbip false] at hv
  cases hv

lemma mixed_and_frontier_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (j : ℕ) (hmixed : ∀ c : Bool, ∃ i ∈ orIn n C (n + j), s i = c)
    (a : ℕ) (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    (b : Fin 2) (hr : OrReaches n C (opnd C a b) j) : a ∈ junk G C := by
  obtain ⟨c, hc⟩ := operand_mono_activity G C s hAO hT hJ a ha hop (1 - b)
  have hb := reach_up n C (mono s c) _ j hr (mixed_gate_mono C s j hmixed c)
  have hv : W n C (mono s c) (n + a) = true := by
    apply W_and n C (mono s c) a ha hop
    intro z hz
    obtain ⟨_, hin, h0, h1, _⟩ := gate2 hAO ha
    rw [hin] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    have hboth : ∀ d : Fin 2, W n C (mono s c) (opnd C a d) = true := by
      intro d
      have hd : d = b ∨ d = 1 - b := by fin_cases b <;> fin_cases d <;> simp
      rcases hd with rfl | rfl <;> assumption
    rcases hz with rfl | rfl
    · exact ⟨h0, hboth 0⟩
    · exact ⟨h1, hboth 1⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha, hop, ha, mono s c, hv,
    graphFun_mono_false G s hbip c⟩

lemma and_frontier_of_live {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (hlive : ∀ k < C.gates.length, n + k ≠ C.output →
      ∃ r, r < C.gates.length ∧ n + k ∈ (gateAt C r).inputs)
    (j : ℕ) (hj : j < C.gates.length) (hout : ¬ OrReaches n C C.output j) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ b : Fin 2, OrReaches n C (opnd C a b) j := by
  classical
  let S := (Finset.range C.gates.length).filter fun k => OrReaches n C (n + k) j
  have hmem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, orReach_self n C j hj⟩
  have hne : S.Nonempty := ⟨j, hmem⟩
  let k := S.max' hne
  have hkS : k ∈ S := Finset.max'_mem S hne
  obtain ⟨hk, hkj⟩ := Finset.mem_filter.mp hkS
  have hklt : k < C.gates.length := Finset.mem_range.mp hk
  have hkout : n + k ≠ C.output := by
    intro he
    rw [he] at hkj
    exact hout hkj
  obtain ⟨a, ha, hread⟩ := hlive k hklt hkout
  have hka : k < a := by have := hAO.2.1 a ha (n + k) hread; omega
  rcases hAO.1 _ (gateAt_mem' C a ha) with hop | hop
  · refine ⟨a, ha, hop, ?_⟩
    have hlen := hAO.2.2 _ (gateAt_mem' C a ha)
    obtain ⟨p, hp, heq⟩ := List.getElem_of_mem hread
    have hp' : p < 2 := by omega
    refine ⟨⟨p, hp'⟩, ?_⟩
    have hb : opnd C a ⟨p, hp'⟩ = n + k := by
      unfold opnd
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
      exact heq
    rw [hb]
    exact hkj
  · have haS : a ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ha,
      orReach_trans n C a ha hop (n + k) hread (by omega) j hkj⟩
    have hmax := Finset.le_max' S a haS
    change a ≤ k at hmax
    omega

lemma least_mixed_reaches_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (j : ℕ) (hj : j < C.gates.length)
    (hmixed : ∀ c : Bool, ∃ i ∈ orIn n C (n + j), s i = c) :
    ∃ a ∈ junk G C, ∃ b : Fin 2, OrReaches n C (opnd C a b) j := by
  obtain ⟨a, ha, hop, b, hr⟩ := and_frontier_of_live C hL.1
    (fun k hk hne => least_has_reader G C hL k hk hne) j hj
    (mixed_not_or_output G C s hbip hL.2.1 j hmixed)
  exact ⟨a, mixed_and_frontier_junk G C s hbip hL.1 hT hJ j hmixed a ha hop b hr, b, hr⟩

end MixedReach

namespace MixedReach

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
open PEqualNP.Outside.L_meta_5012.CriticalEdge
open PEqualNP.Outside.L_meta_5012.MixedFrontier

lemma orIn_or_step {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (w : ℕ)
    (hw : w ∈ (gateAt C k).inputs) (hlt : w < n + k) :
    orIn n C w ⊆ orIn n C (n + k) := by
  intro i hi
  rw [orIn_mem] at hi ⊢
  right
  rcases hi with hi | ⟨r, hr, hreach, hrop, hir⟩
  · exact ⟨k, hk, orReach_self n C k hk, hop, hi ▸ hw⟩
  · exact ⟨r, hr, orReach_trans n C k hk hop w hw hlt r hreach, hrop, hir⟩

lemma orSets_orIn_subset {n : ℕ} (C : Circuit) :
    ∀ k < C.gates.length, ∀ j, j ∈ (orSets n C).getD k [] →
      orIn n C (n + j) ⊆ orIn n C (n + k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk j hj
    rcases (orSets_mem_iff n C k j hk).mp hj with heq | ⟨hop, w, hw, hn, hlt, hmem⟩
    · subst j
      exact Finset.Subset.refl _
    · have hsub := ih (w - n) (by omega) (by omega) j hmem
      have heq : n + (w - n) = w := by omega
      rw [heq] at hsub
      exact hsub.trans (orIn_or_step C k hk hop w hw hlt)

lemma orIn_subset_of_orReaches {n : ℕ} (C : Circuit) (w j : ℕ)
    (hw : w < n + C.gates.length) (hr : OrReaches n C w j) :
    orIn n C (n + j) ⊆ orIn n C w := by
  obtain ⟨hn, hmem⟩ := hr
  have hsub := orSets_orIn_subset C (w - n) (by omega) j hmem
  have heq : n + (w - n) = w := by omega
  rwa [heq] at hsub

lemma least_mixed_reaches_mixed_junk_operand {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (j : ℕ) (hj : j < C.gates.length)
    (hmixed : ∀ c : Bool, ∃ i ∈ orIn n C (n + j), s i = c) :
    ∃ a ∈ junk G C, ∃ b : Fin 2, OrReaches n C (opnd C a b) j ∧
      ∀ c : Bool, ∃ i ∈ side (n := n) C a b, s i = c := by
  obtain ⟨a, ha, b, hr⟩ := least_mixed_reaches_junk G C s hbip hL hT hJ j hj hmixed
  have halt : a < C.gates.length := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  have hlen := hL.1.2.2 _ (gateAt_mem' C a halt)
  have hmem : opnd C a b ∈ (gateAt C a).inputs := by
    unfold opnd
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  have hlt := hL.1.2.1 a halt _ hmem
  have hsub := orIn_subset_of_orReaches C (opnd C a b) j (by omega) hr
  refine ⟨a, ha, b, hr, ?_⟩
  intro c
  obtain ⟨i, hi, hc⟩ := hmixed c
  exact ⟨i, hsub hi, hc⟩

lemma mixed_not_monochromatic {n : ℕ} (s : Fin n → Bool) (S : Finset (Fin n))
    (hmixed : ∀ c : Bool, ∃ i ∈ S, s i = c) :
    ¬ ∃ c : Bool, ∀ i ∈ S, s i = c := by
  rintro ⟨c, hc⟩
  obtain ⟨i, hi, hcolor⟩ := hmixed (!c)
  have heq := (hc i hi).symm.trans hcolor
  cases c <;> cases heq

lemma mixed_slot_unique {n : ℕ} (C : Circuit) (s : Fin n → Bool) (a : ℕ)
    (b d : Fin 2)
    (hpure : ∃ c : Bool, ∀ i ∈ side (n := n) C a (1 - d), s i = c)
    (hmixed : ∀ c : Bool, ∃ i ∈ side (n := n) C a b, s i = c) : b = d := by
  by_contra hne
  have hb : b = 1 - d := by
    fin_cases b <;> fin_cases d
    · exact (hne rfl).elim
    · decide
    · decide
    · exact (hne rfl).elim
  rw [hb] at hmixed
  exact mixed_not_monochromatic s _ hmixed hpure

lemma least_mixed_two_operand_coverage {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hJ : ∀ k ∈ junk G C, ∃ c : Bool, gateVal n C k (mono s c) = true)
    (g h : ℕ) (bg bh : Fin 2) (hpair : junk G C = {g, h})
    (hpureg : ∃ c : Bool, ∀ i ∈ side (n := n) C g (1 - bg), s i = c)
    (hpureh : ∃ c : Bool, ∀ i ∈ side (n := n) C h (1 - bh), s i = c)
    (j : ℕ) (hj : j < C.gates.length)
    (hmixed : ∀ c : Bool, ∃ i ∈ orIn n C (n + j), s i = c) :
    OrReaches n C (opnd C g bg) j ∨ OrReaches n C (opnd C h bh) j := by
  obtain ⟨a, ha, b, hr, hm⟩ := least_mixed_reaches_mixed_junk_operand G C s hbip hL hT hJ
    j hj hmixed
  rw [hpair] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with hag | hah
  · subst a
    have he := mixed_slot_unique C s g b bg hpureg hm
    exact Or.inl (he ▸ hr)
  · subst a
    have he := mixed_slot_unique C s h b bh hpureh hm
    exact Or.inr (he ▸ hr)

end MixedReach

namespace CountDAG

lemma vertices_le_edges_add_components {V : Type} [Finite V] (G : SimpleGraph V) :
    Nat.card V ≤ G.edgeSet.ncard + Nat.card G.ConnectedComponent := by
  classical
  let := Fintype.ofFinite G.ConnectedComponent
  have h : ∀ c : G.ConnectedComponent, c.supp.ncard ≤ c.toSimpleGraph.edgeSet.ncard + 1 := by
    intro c
    have hc := c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
    simpa only [← c.ncard_supp, Nat.card_coe_set_eq] using hc
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun c _ => h c)
  simpa only [Finset.sum_add_distrib, G.sum_connectedComponent_ncard_supp,
    G.sum_connectedComponent_ncard_edgeSet, Finset.sum_const, Finset.card_univ,
    Nat.card_eq_fintype_card, smul_eq_mul, mul_one] using hs

def gateNode (N k : ℕ) (j : Fin k) : Fin (N + k) := ⟨N + j, by omega⟩

def wireEdges (N k : ℕ) (a b : Fin k → Fin (N + k)) : Finset (Sym2 (Fin (N + k))) :=
  Finset.univ.image (fun j => s(a j, gateNode N k j)) ∪
  Finset.univ.image (fun j => s(b j, gateNode N k j))

def cutGraph (N k : ℕ) (a b : Fin k → Fin (N + k)) : SimpleGraph (Fin (N + k)) :=
  SimpleGraph.fromEdgeSet (wireEdges N k a b)

lemma cutGraph_edges_le (N k : ℕ) (a b : Fin k → Fin (N + k)) :
    (cutGraph N k a b).edgeSet.ncard ≤ 2 * k := by
  classical
  unfold cutGraph
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  calc
    _ ≤ (↑(wireEdges N k a b) : Set (Sym2 (Fin (N + k)))).ncard :=
      Set.ncard_le_ncard Set.sdiff_subset
    _ = (wireEdges N k a b).card := Set.ncard_coe_finset _
    _ ≤ (Finset.univ.image (fun j => s(a j, gateNode N k j))).card +
        (Finset.univ.image (fun j => s(b j, gateNode N k j))).card := Finset.card_union_le _ _
    _ ≤ k + k := Nat.add_le_add
      (by simpa using Finset.card_image_le (s := Finset.univ) (f := fun j => s(a j, gateNode N k j)))
      (by simpa using Finset.card_image_le (s := Finset.univ) (f := fun j => s(b j, gateNode N k j)))
    _ = 2 * k := by omega

lemma boundary_le_gates_add_components (N k : ℕ) (a b : Fin k → Fin (N + k)) :
    N ≤ k + Nat.card (cutGraph N k a b).ConnectedComponent := by
  have hv := vertices_le_edges_add_components (cutGraph N k a b)
  have he := cutGraph_edges_le N k a b
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hv
  rw [Nat.card_eq_fintype_card]
  omega

lemma components_le_roots {V : Type} [Finite V] (G : SimpleGraph V)
    (roots : Finset V) (hroot : ∀ v, ∃ r ∈ roots, G.Reachable v r) :
    Nat.card G.ConnectedComponent ≤ roots.card := by
  classical
  have hs : Function.Surjective (fun r : {v // v ∈ roots} => G.connectedComponentMk r.val) := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      obtain ⟨r, hr, hvr⟩ := hroot v
      exact ⟨⟨r, hr⟩, (SimpleGraph.ConnectedComponent.sound hvr).symm⟩
  have hc := Nat.card_le_card_of_surjective _ hs
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc

def wireStep (N k : ℕ) (a b : Fin k → Fin (N + k))
    (v w : Fin (N + k)) : Prop :=
  ∃ j, w = gateNode N k j ∧ (v = a j ∨ v = b j)

lemma step_reachable (N k : ℕ) (a b : Fin k → Fin (N + k))
    {v w : Fin (N + k)} (h : wireStep N k a b v w) :
    (cutGraph N k a b).Reachable v w := by
  classical
  by_cases hvw : v = w
  · subst w
    exact SimpleGraph.Reachable.refl v
  apply SimpleGraph.Adj.reachable
  rw [cutGraph, SimpleGraph.fromEdgeSet_adj]
  refine ⟨?_, hvw⟩
  obtain ⟨j, rfl, h⟩ := h
  rcases h with rfl | rfl
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

lemma path_reachable (N k : ℕ) (a b : Fin k → Fin (N + k))
    {v w : Fin (N + k)} (h : Relation.ReflTransGen (wireStep N k a b) v w) :
    (cutGraph N k a b).Reachable v w := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hstep ih => exact ih.trans (step_reachable N k a b hstep)

def inputNode (N k : ℕ) (i : Fin N) : Fin (N + k) := ⟨i, by omega⟩

lemma cut_vertices_reach_roots (N k : ℕ) (a b : Fin k → Fin (N + k))
    (roots : Finset (Fin (N + k)))
    (hused : ∀ i : Fin N, ∃ j : Fin k, inputNode N k i = a j ∨ inputNode N k i = b j)
    (hroot : ∀ j : Fin k, ∃ r ∈ roots,
      Relation.ReflTransGen (wireStep N k a b) (gateNode N k j) r) :
    ∀ v, ∃ r ∈ roots, (cutGraph N k a b).Reachable v r := by
  intro v
  by_cases hv : v.val < N
  · obtain ⟨j, hj⟩ := hused ⟨v, hv⟩
    obtain ⟨r, hr, hpath⟩ := hroot j
    refine ⟨r, hr, ?_⟩
    have hstep : wireStep N k a b v (gateNode N k j) := by
      exact ⟨j, rfl, hj⟩
    exact (step_reachable N k a b hstep).trans (path_reachable N k a b hpath)
  · have hj : v.val - N < k := by omega
    obtain ⟨r, hr, hpath⟩ := hroot ⟨v.val - N, hj⟩
    refine ⟨r, hr, ?_⟩
    have heq : gateNode N k ⟨v.val - N, hj⟩ = v := by
      apply Fin.ext
      simp only [gateNode]
      omega
    rw [heq] at hpath
    exact path_reachable N k a b hpath

lemma cut_components_le_roots (N k : ℕ) (a b : Fin k → Fin (N + k))
    (roots : Finset (Fin (N + k)))
    (hused : ∀ i : Fin N, ∃ j : Fin k, inputNode N k i = a j ∨ inputNode N k i = b j)
    (hroot : ∀ j : Fin k, ∃ r ∈ roots,
      Relation.ReflTransGen (wireStep N k a b) (gateNode N k j) r) :
    Nat.card (cutGraph N k a b).ConnectedComponent ≤ roots.card :=
  components_le_roots _ roots (cut_vertices_reach_roots N k a b roots hused hroot)

lemma boundary_le_gates_add_roots (N k : ℕ) (a b : Fin k → Fin (N + k))
    (roots : Finset (Fin (N + k)))
    (hused : ∀ i : Fin N, ∃ j : Fin k, inputNode N k i = a j ∨ inputNode N k i = b j)
    (hroot : ∀ j : Fin k, ∃ r ∈ roots,
      Relation.ReflTransGen (wireStep N k a b) (gateNode N k j) r) :
    N ≤ k + roots.card :=
  (boundary_le_gates_add_components N k a b).trans
    (Nat.add_le_add_left (cut_components_le_roots N k a b roots hused hroot) k)

lemma two_roots_boundary_le_gates_add_two (N k : ℕ) (a b : Fin k → Fin (N + k))
    (roots : Finset (Fin (N + k))) (hcard : roots.card ≤ 2)
    (hused : ∀ i : Fin N, ∃ j : Fin k, inputNode N k i = a j ∨ inputNode N k i = b j)
    (hroot : ∀ j : Fin k, ∃ r ∈ roots,
      Relation.ReflTransGen (wireStep N k a b) (gateNode N k j) r) :
    N ≤ k + 2 := by
  have h := boundary_le_gates_add_roots N k a b roots hused hroot
  omega

lemma components_le_one_of_roots_connected {V : Type} [Finite V] (G : SimpleGraph V)
    (roots : Finset V) (hroot : ∀ v, ∃ r ∈ roots, G.Reachable v r)
    (hjoin : ∀ r ∈ roots, ∀ s ∈ roots, G.Reachable r s) :
    Nat.card G.ConnectedComponent ≤ 1 := by
  classical
  by_cases hn : roots.Nonempty
  · obtain ⟨r, hr⟩ := hn
    have h := components_le_roots G {r} (by
      intro v
      obtain ⟨s, hs, hvs⟩ := hroot v
      exact ⟨r, by simp, hvs.trans (hjoin s hs r hr)⟩)
    simpa using h
  · have he : roots = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have h := components_le_roots G roots hroot
    simp only [he, Finset.card_empty] at h
    omega

lemma connected_roots_boundary_le_gates_add_one (N k : ℕ) (a b : Fin k → Fin (N + k))
    (roots : Finset (Fin (N + k)))
    (hused : ∀ i : Fin N, ∃ j : Fin k, inputNode N k i = a j ∨ inputNode N k i = b j)
    (hroot : ∀ j : Fin k, ∃ r ∈ roots,
      Relation.ReflTransGen (wireStep N k a b) (gateNode N k j) r)
    (hjoin : ∀ r ∈ roots, ∀ s ∈ roots, (cutGraph N k a b).Reachable r s) :
    N ≤ k + 1 := by
  have hc := components_le_one_of_roots_connected (cutGraph N k a b) roots
    (cut_vertices_reach_roots N k a b roots hused hroot) hjoin
  have h := boundary_le_gates_add_components N k a b
  omega

lemma two_roots_shared_ancestor_boundary_le_gates_add_one (N k : ℕ)
    (a b : Fin k → Fin (N + k)) (u r s : Fin (N + k))
    (hur : Relation.ReflTransGen (wireStep N k a b) u r)
    (hus : Relation.ReflTransGen (wireStep N k a b) u s)
    (hused : ∀ i : Fin N, ∃ j : Fin k, inputNode N k i = a j ∨ inputNode N k i = b j)
    (hroot : ∀ j : Fin k, ∃ t ∈ ({r, s} : Finset (Fin (N + k))),
      Relation.ReflTransGen (wireStep N k a b) (gateNode N k j) t) :
    N ≤ k + 1 := by
  apply connected_roots_boundary_le_gates_add_one N k a b {r, s} hused hroot
  intro x hx y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  have hrs := (path_reachable N k a b hur).symm.trans (path_reachable N k a b hus)
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact SimpleGraph.Reachable.refl _
  · exact hrs
  · exact hrs.symm
  · exact SimpleGraph.Reachable.refl _

end CountDAG

namespace CountCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def oldWireEdges (W J : Finset ℕ) (a b : ℕ → ℕ) (hJ : J ⊆ W)
    (ha : ∀ j ∈ J, a j ∈ W) (hb : ∀ j ∈ J, b j ∈ W) :
    Finset (Sym2 {w // w ∈ W}) :=
  J.attach.image (fun j : {j // j ∈ J} => s(⟨a j, ha j j.property⟩, ⟨j, hJ j.property⟩)) ∪
  J.attach.image (fun j : {j // j ∈ J} => s(⟨b j, hb j j.property⟩, ⟨j, hJ j.property⟩))

def oldWireGraph (W J : Finset ℕ) (a b : ℕ → ℕ) (hJ : J ⊆ W)
    (ha : ∀ j ∈ J, a j ∈ W) (hb : ∀ j ∈ J, b j ∈ W) :
    SimpleGraph {w // w ∈ W} :=
  SimpleGraph.fromEdgeSet (oldWireEdges W J a b hJ ha hb)

lemma oldWireGraph_edges_le (W J : Finset ℕ) (a b : ℕ → ℕ) (hJ : J ⊆ W)
    (ha : ∀ j ∈ J, a j ∈ W) (hb : ∀ j ∈ J, b j ∈ W) :
    (oldWireGraph W J a b hJ ha hb).edgeSet.ncard ≤ 2 * J.card := by
  classical
  unfold oldWireGraph
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  calc
    _ ≤ (↑(oldWireEdges W J a b hJ ha hb) : Set (Sym2 {w // w ∈ W})).ncard :=
      Set.ncard_le_ncard Set.sdiff_subset
    _ = (oldWireEdges W J a b hJ ha hb).card := Set.ncard_coe_finset _
    _ ≤ (J.attach.image (fun j : {j // j ∈ J} => s(⟨a j, ha j j.property⟩, ⟨j, hJ j.property⟩)) :
          Finset (Sym2 {w // w ∈ W})).card +
        (J.attach.image (fun j : {j // j ∈ J} => s(⟨b j, hb j j.property⟩, ⟨j, hJ j.property⟩)) :
          Finset (Sym2 {w // w ∈ W})).card := Finset.card_union_le _ _
    _ ≤ J.card + J.card := by
      apply Nat.add_le_add
      · exact Finset.card_image_le.trans_eq Finset.card_attach
      · exact Finset.card_image_le.trans_eq Finset.card_attach
    _ = 2 * J.card := by omega

lemma old_boundary_le_gates_add_components (B J : Finset ℕ) (hdis : Disjoint B J)
    (a b : ℕ → ℕ) (ha : ∀ j ∈ J, a j ∈ B ∪ J) (hb : ∀ j ∈ J, b j ∈ B ∪ J) :
    B.card ≤ J.card + Nat.card (oldWireGraph (B ∪ J) J a b
      Finset.subset_union_right ha hb).ConnectedComponent := by
  have hv := CountDAG.vertices_le_edges_add_components
    (oldWireGraph (B ∪ J) J a b Finset.subset_union_right ha hb)
  have he := oldWireGraph_edges_le (B ∪ J) J a b Finset.subset_union_right ha hb
  have hu : (B ∪ J).card = B.card + J.card := Finset.card_union_of_disjoint hdis
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe] at hv ⊢
  omega

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


def orWireStep (n : ℕ) (C : Circuit) (u v : ℕ) : Prop :=
  ∃ j < C.gates.length, v = n + j ∧ (gateAt C j).op = GateOp.or ∧
    u ∈ (gateAt C j).inputs ∧ u < n + j

lemma orSets_path (n : ℕ) (C : Circuit) : ∀ k,
    k < C.gates.length → ∀ g, g ∈ (orSets n C).getD k [] →
      Relation.ReflTransGen (orWireStep n C) (n + g) (n + k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk g hg
    rcases (orSets_mem_iff n C k g hk).mp hg with heq | ⟨hop, w, hw, hn, hlt, hmem⟩
    · subst g
      exact Relation.ReflTransGen.refl
    · have hp := ih (w - n) (by omega) (by omega) g hmem
      have heq : n + (w - n) = w := by omega
      rw [heq] at hp
      exact hp.tail ⟨k, hk, rfl, hop, hw, hlt⟩

lemma orReaches_path (n : ℕ) (C : Circuit) (w g : ℕ) (h : OrReaches n C w g) :
    Relation.ReflTransGen (orWireStep n C) (n + g) w := by
  obtain ⟨hn, hmem⟩ := h
  have hlen : (orSets n C).length = C.gates.length := by
    simp [orSets, orFold_length]
  have hk : w - n < C.gates.length := by
    by_contra hnot
    have he : (orSets n C).getD (w - n) [] = [] :=
      List.getD_eq_default _ _ (by rw [hlen]; omega)
    rw [he] at hmem
    exact List.not_mem_nil hmem
  have hp := orSets_path n C (w - n) hk g hmem
  have heq : n + (w - n) = w := by omega
  rwa [heq] at hp

lemma orIn_path (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n)
    (h : i ∈ orIn n C w) :
    Relation.ReflTransGen (orWireStep n C) i.val w := by
  classical
  have hi : i.val = w ∨ ∃ j < C.gates.length, OrReaches n C w j ∧
      (gateAt C j).op = GateOp.or ∧ i.val ∈ (gateAt C j).inputs := by
    simpa only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] using h
  rcases hi with heq | ⟨j, hj, hreach, hop, hread⟩
  · subst w
    exact Relation.ReflTransGen.refl
  · exact (Relation.ReflTransGen.single ⟨j, hj, rfl, hop, hread, by omega⟩).trans
      (orReaches_path n C w j hreach)

lemma common_orIn_has_shared_ancestor (n : ℕ) (C : Circuit) (r s : ℕ)
    (h : (orIn n C r ∩ orIn n C s).Nonempty) :
    ∃ i : Fin n, Relation.ReflTransGen (orWireStep n C) i.val r ∧
      Relation.ReflTransGen (orWireStep n C) i.val s := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨hir, his⟩ := Finset.mem_inter.mp hi
  exact ⟨i, orIn_path n C r i hir, orIn_path n C s i his⟩

lemma old_operand_reachable (W J : Finset ℕ) (a b : ℕ → ℕ) (hJ : J ⊆ W)
    (ha : ∀ j ∈ J, a j ∈ W) (hb : ∀ j ∈ J, b j ∈ W)
    (u j : ℕ) (hu : u ∈ W) (hj : j ∈ J) (hoperand : u = a j ∨ u = b j) :
    (oldWireGraph W J a b hJ ha hb).Reachable ⟨u, hu⟩ ⟨j, hJ hj⟩ := by
  classical
  by_cases heq : u = j
  · have hsub : (⟨u, hu⟩ : {w // w ∈ W}) = ⟨j, hJ hj⟩ := Subtype.ext heq
    rw [hsub]
  apply SimpleGraph.Adj.reachable
  rw [oldWireGraph, SimpleGraph.fromEdgeSet_adj]
  refine ⟨?_, fun h => heq (congrArg Subtype.val h)⟩
  rcases hoperand with rfl | rfl
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨j, hj⟩, by simp, rfl⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨j, hj⟩, by simp, rfl⟩)

lemma two_inputs (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hm : gateAt C j ∈ C.gates := by
    rw [gateAt_eq C j hj]
    exact List.getElem_mem hj
  have hl := hAO.2.2 _ hm
  obtain ⟨a, b, heq⟩ := List.length_eq_two.mp hl
  simp [opnd, heq]

lemma orStep_operand_eq (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (u v : ℕ) (h : orWireStep n C u v) :
    u = opnd C (v - n) 0 ∨ u = opnd C (v - n) 1 := by
  obtain ⟨j, hj, rfl, _, hread, _⟩ := h
  rw [two_inputs n C hAO j hj] at hread
  simpa using hread

def cutOrStep (n : ℕ) (C : Circuit) (J : Finset ℕ) (u v : ℕ) : Prop :=
  orWireStep n C u v ∧ v ∈ J

lemma closed_path_is_cutPath (n : ℕ) (C : Circuit) (J : Finset ℕ)
    (hclosed : ∀ u ∈ J, ∀ v, orWireStep n C u v → v ∈ J)
    {u v : ℕ} (hu : u ∈ J) (h : Relation.ReflTransGen (orWireStep n C) u v) :
    v ∈ J ∧ Relation.ReflTransGen (cutOrStep n C J) u v := by
  induction h with
  | refl => exact ⟨hu, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
    have hv := hclosed _ ih.1 _ hstep
    exact ⟨hv, ih.2.tail ⟨hstep, hv⟩⟩

lemma cutOrPath_reachable (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (W J : Finset ℕ) (hJ : J ⊆ W)
    (ha : ∀ j ∈ J, opnd C (j - n) 0 ∈ W)
    (hb : ∀ j ∈ J, opnd C (j - n) 1 ∈ W)
    {u v : ℕ} (hu : u ∈ W) (h : Relation.ReflTransGen (cutOrStep n C J) u v) :
    ∃ hv : v ∈ W,
      (oldWireGraph W J (fun j => opnd C (j - n) 0) (fun j => opnd C (j - n) 1)
        hJ ha hb).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction h with
  | refl => exact ⟨hu, SimpleGraph.Reachable.refl _⟩
  | tail _ hstep ih =>
    obtain ⟨hw, hreach⟩ := ih
    exact ⟨hJ hstep.2, hreach.trans (old_operand_reachable W J _ _ hJ ha hb
      _ _ hw hstep.2 (orStep_operand_eq n C hAO _ _ hstep.1))⟩

def oldRootNodes (W roots : Finset ℕ) (hR : roots ⊆ W) : Finset {w // w ∈ W} :=
  roots.attach.image fun r : {r // r ∈ roots} => ⟨r, hR r.property⟩

lemma circuit_cut_vertices_reach_roots (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (B J roots : Finset ℕ)
    (ha : ∀ j ∈ J, opnd C (j - n) 0 ∈ B ∪ J)
    (hb : ∀ j ∈ J, opnd C (j - n) 1 ∈ B ∪ J)
    (hR : roots ⊆ B ∪ J)
    (hused : ∀ u ∈ B, ∃ j ∈ J, u = opnd C (j - n) 0 ∨ u = opnd C (j - n) 1)
    (hroot : ∀ j ∈ J, ∃ r ∈ roots, Relation.ReflTransGen (cutOrStep n C J) j r) :
    ∀ u, ∃ r ∈ oldRootNodes (B ∪ J) roots hR,
      (oldWireGraph (B ∪ J) J (fun j => opnd C (j - n) 0)
        (fun j => opnd C (j - n) 1) Finset.subset_union_right ha hb).Reachable u r := by
  classical
  intro u
  have reach_gate : ∀ j (hj : j ∈ J),
      ∃ r ∈ oldRootNodes (B ∪ J) roots hR,
        (oldWireGraph (B ∪ J) J (fun j => opnd C (j - n) 0)
          (fun j => opnd C (j - n) 1) Finset.subset_union_right ha hb).Reachable
            ⟨j, Finset.mem_union_right _ hj⟩ r := by
    intro j hj
    obtain ⟨r, hr, hpath⟩ := hroot j hj
    obtain ⟨hrW, hreach⟩ := cutOrPath_reachable n C hAO (B ∪ J) J
      Finset.subset_union_right ha hb (Finset.mem_union_right _ hj) hpath
    exact ⟨⟨r, hR hr⟩, Finset.mem_image.mpr ⟨⟨r, hr⟩, by simp, rfl⟩, hreach⟩
  rcases Finset.mem_union.mp u.property with huB | huJ
  · obtain ⟨j, hj, hop⟩ := hused u huB
    obtain ⟨r, hr, hreach⟩ := reach_gate j hj
    exact ⟨r, hr, (old_operand_reachable (B ∪ J) J _ _
      Finset.subset_union_right ha hb u j u.property hj hop).trans hreach⟩
  · exact reach_gate u huJ

lemma circuit_cut_components_le_roots (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (B J roots : Finset ℕ)
    (ha : ∀ j ∈ J, opnd C (j - n) 0 ∈ B ∪ J)
    (hb : ∀ j ∈ J, opnd C (j - n) 1 ∈ B ∪ J)
    (hR : roots ⊆ B ∪ J)
    (hused : ∀ u ∈ B, ∃ j ∈ J, u = opnd C (j - n) 0 ∨ u = opnd C (j - n) 1)
    (hroot : ∀ j ∈ J, ∃ r ∈ roots, Relation.ReflTransGen (cutOrStep n C J) j r) :
    Nat.card (oldWireGraph (B ∪ J) J
      (fun j => opnd C (j - n) 0) (fun j => opnd C (j - n) 1)
      Finset.subset_union_right ha hb).ConnectedComponent ≤ roots.card := by
  classical
  have hc := CountDAG.components_le_roots _ (oldRootNodes (B ∪ J) roots hR)
    (circuit_cut_vertices_reach_roots n C hAO B J roots ha hb hR hused hroot)
  exact hc.trans (Finset.card_image_le.trans_eq Finset.card_attach)

lemma circuit_cut_boundary_le_gates_add_roots (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (B J roots : Finset ℕ) (hdis : Disjoint B J)
    (ha : ∀ j ∈ J, opnd C (j - n) 0 ∈ B ∪ J)
    (hb : ∀ j ∈ J, opnd C (j - n) 1 ∈ B ∪ J)
    (hR : roots ⊆ B ∪ J)
    (hused : ∀ u ∈ B, ∃ j ∈ J, u = opnd C (j - n) 0 ∨ u = opnd C (j - n) 1)
    (hroot : ∀ j ∈ J, ∃ r ∈ roots, Relation.ReflTransGen (cutOrStep n C J) j r) :
    B.card ≤ J.card + roots.card :=
  (old_boundary_le_gates_add_components B J hdis _ _ ha hb).trans
    (Nat.add_le_add_left (circuit_cut_components_le_roots n C hAO B J roots
      ha hb hR hused hroot) J.card)

lemma circuit_cut_boundary_le_gates_add_two (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (B J roots : Finset ℕ) (hdis : Disjoint B J) (hcard : roots.card ≤ 2)
    (ha : ∀ j ∈ J, opnd C (j - n) 0 ∈ B ∪ J)
    (hb : ∀ j ∈ J, opnd C (j - n) 1 ∈ B ∪ J)
    (hR : roots ⊆ B ∪ J)
    (hused : ∀ u ∈ B, ∃ j ∈ J, u = opnd C (j - n) 0 ∨ u = opnd C (j - n) 1)
    (hroot : ∀ j ∈ J, ∃ r ∈ roots, Relation.ReflTransGen (cutOrStep n C J) j r) :
    B.card ≤ J.card + 2 := by
  have h := circuit_cut_boundary_le_gates_add_roots n C hAO B J roots hdis
    ha hb hR hused hroot
  omega

lemma circuit_cut_shared_source_boundary_le_gates_add_one
    (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (B J roots : Finset ℕ) (hdis : Disjoint B J)
    (ha : ∀ j ∈ J, opnd C (j - n) 0 ∈ B ∪ J)
    (hb : ∀ j ∈ J, opnd C (j - n) 1 ∈ B ∪ J)
    (hR : roots ⊆ B ∪ J)
    (hused : ∀ u ∈ B, ∃ j ∈ J, u = opnd C (j - n) 0 ∨ u = opnd C (j - n) 1)
    (hroot : ∀ j ∈ J, ∃ r ∈ roots, Relation.ReflTransGen (cutOrStep n C J) j r)
    (u : ℕ) (hu : u ∈ B ∪ J)
    (hshared : ∀ r ∈ roots, Relation.ReflTransGen (cutOrStep n C J) u r) :
    B.card ≤ J.card + 1 := by
  classical
  have hcover := circuit_cut_vertices_reach_roots n C hAO B J roots ha hb hR hused hroot
  have hc := CountDAG.components_le_one_of_roots_connected _
    (oldRootNodes (B ∪ J) roots hR) hcover (by
      intro r hr t ht
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨hrW, hur⟩ := cutOrPath_reachable n C hAO (B ∪ J) J
        Finset.subset_union_right ha hb hu (hshared r r.property)
      obtain ⟨htW, hut⟩ := cutOrPath_reachable n C hAO (B ∪ J) J
        Finset.subset_union_right ha hb hu (hshared t t.property)
      exact hur.symm.trans hut)
  have hv := old_boundary_le_gates_add_components B J hdis _ _ ha hb
  omega

end CountCut

namespace TwoOrBuild

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

lemma run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
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



def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

lemma ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

def ov (gs : List Gate) (x : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => (run gs x).getD w false

lemma ov_ext (gs hs : List Gate) (x : List Bool) (o : Option ℕ)
    (h : ∀ w, o = some w → w < x.length + gs.length) : ov (gs ++ hs) x o = ov gs x o := by
  cases o with
  | none => rfl
  | some w => exact run_prefix gs hs x w (h w rfl)

lemma ov_new (gs : List Gate) (n : ℕ) (x : List Bool) (hx : x.length = n) (o : GateOp) (s t : ℕ)
    (hs : s < n + gs.length) (ht : t < n + gs.length) :
    ov (gs ++ [⟨o, [s, t]⟩]) x (some (n + gs.length)) =
      o.eval [(run gs x).getD s false, (run gs x).getD t false] := by
  unfold ov
  simp only
  rw [run_snoc]
  have : n + gs.length = (run gs x).length := by rw [run_length, hx]
  rw [this, getD_at]
  rfl

lemma ok_ao {n : ℕ} {gs : List Gate} {w : ℕ} (hok : Ok n gs) : TopForm.IsAO2 n ⟨gs, w⟩ := by
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

noncomputable def sourceOr (gs : List Gate) (x : List Bool) (S : Finset ℕ) : Bool :=
  decide (∃ w ∈ S, (run gs x).getD w false = true)

lemma sourceOr_list (gs : List Gate) (x : List Bool) (S : Finset ℕ) :
    sourceOr gs x S = S.toList.any (fun w => (run gs x).getD w false) := by
  apply Bool.eq_iff_iff.mpr
  simp [sourceOr, List.any_eq_true]

lemma sourceOr_prefix (gs hs : List Gate) (x : List Bool) (S : Finset ℕ)
    (hS : ∀ w ∈ S, w < x.length + gs.length) :
    sourceOr (gs ++ hs) x S = sourceOr gs x S := by
  apply Bool.eq_iff_iff.mpr
  simp only [sourceOr, decide_eq_true_eq]
  constructor
  · rintro ⟨w, hw, he⟩
    exact ⟨w, hw, by rwa [run_prefix gs hs x w (hS w hw)] at he⟩
  · rintro ⟨w, hw, he⟩
    exact ⟨w, hw, by rwa [run_prefix gs hs x w (hS w hw)]⟩

lemma sourceOr_split (gs : List Gate) (x : List Bool) (S T : Finset ℕ) :
    (sourceOr gs x (S ∩ T) || sourceOr gs x (S \ T)) = sourceOr gs x S := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, sourceOr, decide_eq_true_eq, Finset.mem_inter, Finset.mem_sdiff]
  constructor
  · rintro (⟨w, ⟨hS, _⟩, hv⟩ | ⟨w, ⟨hS, _⟩, hv⟩) <;> exact ⟨w, hS, hv⟩
  · rintro ⟨w, hS, hv⟩
    by_cases hT : w ∈ T
    · exact Or.inl ⟨w, ⟨hS, hT⟩, hv⟩
    · exact Or.inr ⟨w, ⟨hS, hT⟩, hv⟩

lemma or_list_build (n : ℕ) (gs : List Gate) (hgs : Ok n gs) :
    ∀ l : List ℕ, (∀ w ∈ l, w < n + gs.length) →
    ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs ++ hs) ∧
      hs.length = l.length - 1 ∧ (∀ g ∈ hs, g.op = GateOp.or) ∧
      (o = none ↔ l = []) ∧ (∀ w, o = some w → w < n + (gs ++ hs).length) ∧
      ∀ x : List Bool, x.length = n →
        ov (gs ++ hs) x o = l.any (fun w => (run gs x).getD w false) := by
  intro l
  induction l with
  | nil =>
    intro _
    exact ⟨[], none, by simpa using hgs, by simp, by simp, by simp, by simp,
      fun x hx => by simp [ov]⟩
  | cons a l ih =>
    intro hl
    have ha : a < n + gs.length := hl a (by simp)
    obtain ⟨hs, o, hok, hlen, hops, hnone, ho, hval⟩ := ih (fun w hw => hl w (by simp [hw]))
    cases o with
    | none =>
      have hl0 : l = [] := hnone.mp rfl
      subst l
      refine ⟨[], some a, by simpa using hgs, by simp, by simp, by simp,
        by intro w hw; cases hw; simpa using ha, ?_⟩
      intro x hx
      simp [ov]
    | some b =>
      have hb := ho b rfl
      have hlne : l ≠ [] := by intro h; have hh := hnone.mpr h; cases hh
      have hlpos : 0 < l.length := List.length_pos_iff.mpr hlne
      let g : Gate := ⟨GateOp.or, [a, b]⟩
      have hok' : Ok n ((gs ++ hs) ++ [g]) :=
        ok_snoc hok (Or.inr rfl) (by simp only [List.length_append]; omega) hb
      refine ⟨hs ++ [g], some (n + (gs ++ hs).length), by simpa only [List.append_assoc] using hok',
        by simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]; omega,
        ?_, by simp, ?_, ?_⟩
      · intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hops q hq
        · have hqg : q = g := by simpa using hq
          subst q
          rfl
      · intro w hw
        cases hw
        simp only [List.length_append, List.length_singleton]
        omega
      · intro x hx
        have hkeep : (run (gs ++ hs) x).getD a false = (run gs x).getD a false :=
          run_prefix gs hs x a (by simpa only [hx] using ha)
        have ht := hval x hx
        simp only [ov] at ht
        rw [← List.append_assoc, ov_new (gs ++ hs) n x hx GateOp.or a b
          (by simp only [List.length_append]; omega) hb, hkeep, ht]
        simp [g, GateOp.eval]

lemma or_seed_build (n : ℕ) (gs : List Gate) (hgs : Ok n gs)
    (o : Option ℕ) (ho : ∀ w, o = some w → w < n + gs.length)
    (S : Finset ℕ) (hS : ∀ w ∈ S, w < n + gs.length) :
    ∃ (hs : List Gate) (o' : Option ℕ), Ok n (gs ++ hs) ∧
      hs.length = (S.card + o.toList.length) - 1 ∧ (∀ g ∈ hs, g.op = GateOp.or) ∧
      (∀ w, o' = some w → w < n + (gs ++ hs).length) ∧
      ∀ x : List Bool, x.length = n →
        ov (gs ++ hs) x o' = (ov gs x o || sourceOr gs x S) := by
  have hl : ∀ w ∈ o.toList ++ S.toList, w < n + gs.length := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · cases o with
      | none => simp at hw
      | some z =>
        have hwz : w = z := by simpa using hw
        subst w
        exact ho z rfl
    · exact hS w (by simpa using hw)
  obtain ⟨hs, o', hok, hlen, hops, _, hout, hval⟩ := or_list_build n gs hgs _ hl
  refine ⟨hs, o', hok, ?_, hops, hout, ?_⟩
  · simpa only [List.length_append, Finset.length_toList, Nat.add_comm] using hlen
  · intro x hx
    rw [hval x hx, List.any_append, ← sourceOr_list]
    cases o <;> simp [ov]

lemma two_or_build (n : ℕ) (gs : List Gate) (hgs : Ok n gs)
    (S T : Finset ℕ) (hS : ∀ w ∈ S, w < n + gs.length)
    (hT : ∀ w ∈ T, w < n + gs.length) :
    ∃ (hs : List Gate) (oS oT : Option ℕ), Ok n (gs ++ hs) ∧
      (∀ g ∈ hs, g.op = GateOp.or) ∧
      hs.length = (if S ∩ T = ∅ then (S.card - 1) + (T.card - 1) else (S ∪ T).card - 1) ∧
      (∀ w, oS = some w → w < n + (gs ++ hs).length) ∧
      (∀ w, oT = some w → w < n + (gs ++ hs).length) ∧
      ∀ x : List Bool, x.length = n →
        ov (gs ++ hs) x oS = sourceOr gs x S ∧ ov (gs ++ hs) x oT = sourceOr gs x T := by
  have hI : ∀ w ∈ (S ∩ T).toList, w < n + gs.length := by
    intro w hw
    exact hS w (Finset.mem_inter.mp (by simpa using hw)).1
  obtain ⟨hsI, oI, hokI, hlenI, hopsI, hnoneI, hoI, hvalI⟩ := or_list_build n gs hgs _ hI
  have hlenI' : hsI.length = (S ∩ T).card - 1 := by simpa using hlenI
  have hnoneI' : oI = none ↔ S ∩ T = ∅ := by simpa using hnoneI
  have hA : ∀ w ∈ S \ T, w < n + (gs ++ hsI).length := by
    intro w hw
    have h := hS w (Finset.mem_sdiff.mp hw).1
    simp only [List.length_append]
    omega
  obtain ⟨hsA, oS, hokA, hlenA, hopsA, hoS, hvalA⟩ :=
    or_seed_build n (gs ++ hsI) hokI oI hoI (S \ T) hA
  have hoIA : ∀ w, oI = some w → w < n + ((gs ++ hsI) ++ hsA).length := by
    intro w hw
    have h := hoI w hw
    simp only [List.length_append] at h ⊢
    omega
  have hB : ∀ w ∈ T \ S, w < n + ((gs ++ hsI) ++ hsA).length := by
    intro w hw
    have h := hT w (Finset.mem_sdiff.mp hw).1
    simp only [List.length_append]
    omega
  obtain ⟨hsB, oT, hokB, hlenB, hopsB, hoT, hvalB⟩ :=
    or_seed_build n ((gs ++ hsI) ++ hsA) hokA oI hoIA (T \ S) hB
  refine ⟨hsI ++ hsA ++ hsB, oS, oT, by simpa only [List.append_assoc] using hokB,
    ?_, ?_, ?_, by simpa only [List.append_assoc] using hoT, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · rcases List.mem_append.mp hg with hg | hg
      · exact hopsI g hg
      · exact hopsA g hg
    · exact hopsB g hg
  · have hcS := Finset.card_sdiff_add_card_inter S T
    have hcT := Finset.card_sdiff_add_card_inter T S
    rw [Finset.inter_comm T S] at hcT
    have hcU := Finset.card_union_add_card_inter S T
    simp only [List.length_append]
    rw [hlenI', hlenA, hlenB]
    by_cases hIT : S ∩ T = ∅
    · have ho0 : oI = none := hnoneI'.mpr hIT
      rw [if_pos hIT, ho0]
      simp only [Option.toList_none, List.length_nil, Nat.add_zero]
      have hc0 : (S ∩ T).card = 0 := by rw [hIT]; rfl
      omega
    · have hiPos : 0 < (S ∩ T).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hIT)
      have hoLen : oI.toList.length = 1 := by
        cases oI with
        | none => exact (hIT (hnoneI'.mp rfl)).elim
        | some w => rfl
      rw [if_neg hIT, hoLen]
      omega
  · intro w hw
    have h := hoS w hw
    simp only [List.length_append] at h ⊢
    omega
  · intro x hx
    have hiEval : ov (gs ++ hsI) x oI = sourceOr gs x (S ∩ T) := by
      rw [hvalI x hx, ← sourceOr_list]
    have hsrcA : sourceOr (gs ++ hsI) x (S \ T) = sourceOr gs x (S \ T) := by
      apply sourceOr_prefix
      intro w hw
      simpa only [hx] using hS w (Finset.mem_sdiff.mp hw).1
    have hsrcB : sourceOr ((gs ++ hsI) ++ hsA) x (T \ S) = sourceOr gs x (T \ S) := by
      rw [List.append_assoc]
      apply sourceOr_prefix gs (hsI ++ hsA) x (T \ S) (fun w hw => ?_)
      simpa only [hx] using hT w (Finset.mem_sdiff.mp hw).1
    have hiKeep : ov ((gs ++ hsI) ++ hsA) x oI = ov (gs ++ hsI) x oI :=
      ov_ext (gs ++ hsI) hsA x oI (by simpa only [hx] using hoI)
    have hEvalS : ov ((gs ++ hsI) ++ hsA) x oS = sourceOr gs x S := by
      rw [hvalA x hx, hiEval, hsrcA]
      exact sourceOr_split gs x S T
    have hEvalS' : ov (((gs ++ hsI) ++ hsA) ++ hsB) x oS = sourceOr gs x S := by
      rw [ov_ext ((gs ++ hsI) ++ hsA) hsB x oS (by simpa only [hx] using hoS), hEvalS]
    have hEvalT : ov (((gs ++ hsI) ++ hsA) ++ hsB) x oT = sourceOr gs x T := by
      rw [hvalB x hx, hiKeep, hiEval, hsrcB, Finset.inter_comm S T]
      exact sourceOr_split gs x T S
    simpa only [List.append_assoc] using And.intro hEvalS' hEvalT

def pairCost (S T : Finset ℕ) : ℕ :=
  if S ∩ T = ∅ then (S.card - 1) + (T.card - 1) else (S ∪ T).card - 1

def projectColor (color : ℕ → Bool) (c : Bool) (S : Finset ℕ) : Finset ℕ :=
  S.filter (fun w => color w = c)

def HasBoth (color : ℕ → Bool) (S : Finset ℕ) : Prop :=
  ∀ c : Bool, ∃ w ∈ S, color w = c

lemma pairCost_le_union (S T : Finset ℕ) : pairCost S T ≤ (S ∪ T).card - 1 := by
  unfold pairCost
  split_ifs with h
  · have hc := Finset.card_union_add_card_inter S T
    rw [h, Finset.card_empty] at hc
    omega
  · exact le_rfl

lemma project_subset (color : ℕ → Bool) (c : Bool) (S : Finset ℕ) :
    projectColor color c S ⊆ S := Finset.filter_subset _ _

lemma project_nonempty (color : ℕ → Bool) (c : Bool) (S : Finset ℕ)
    (hS : HasBoth color S) : (projectColor color c S).Nonempty := by
  obtain ⟨w, hw, hc⟩ := hS c
  exact ⟨w, Finset.mem_filter.mpr ⟨hw, hc⟩⟩

lemma project_card_lt (color : ℕ → Bool) (c : Bool) (S : Finset ℕ)
    (hS : HasBoth color S) : (projectColor color c S).card < S.card := by
  obtain ⟨w, hw, hc⟩ := hS (!c)
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨project_subset color c S, ?_⟩
  intro heq
  have hm : w ∈ projectColor color c S := by rw [heq]; exact hw
  have hcol := (Finset.mem_filter.mp hm).2
  rw [hc] at hcol
  cases c <;> cases hcol

lemma project_inter_empty_of_colors (color : ℕ → Bool) (c d : Bool) (S T : Finset ℕ)
    (hcd : c ≠ d) : projectColor color c S ∩ projectColor color d T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hS, hT⟩ := Finset.mem_inter.mp hw
  exact hcd ((Finset.mem_filter.mp hS).2.symm.trans (Finset.mem_filter.mp hT).2)

lemma project_inter_empty_of_sources (color : ℕ → Bool) (c d : Bool) (S T : Finset ℕ)
    (hST : S ∩ T = ∅) : projectColor color c S ∩ projectColor color d T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨hS, hT⟩ := Finset.mem_inter.mp hw
  have hm : w ∈ S ∩ T :=
    Finset.mem_inter.mpr ⟨project_subset color c S hS, project_subset color d T hT⟩
  rw [hST] at hm
  exact Finset.notMem_empty _ hm

lemma project_union_subset (color : ℕ → Bool) (c d : Bool) (S T : Finset ℕ) :
    projectColor color c S ∪ projectColor color d T ⊆ S ∪ T := by
  intro w hw
  rcases Finset.mem_union.mp hw with hw | hw
  · exact Finset.mem_union_left _ (project_subset color c S hw)
  · exact Finset.mem_union_right _ (project_subset color d T hw)

lemma project_pairCost_lt (color : ℕ → Bool) (c d : Bool) (S T : Finset ℕ)
    (hS : HasBoth color S) (hT : HasBoth color T) :
    pairCost (projectColor color c S) (projectColor color d T) < pairCost S T := by
  have hpPos := Finset.card_pos.mpr (project_nonempty color c S hS)
  have hqPos := Finset.card_pos.mpr (project_nonempty color d T hT)
  have hpLt := project_card_lt color c S hS
  have hqLt := project_card_lt color d T hT
  have hsub := Finset.card_le_card (project_union_subset color c d S T)
  by_cases hST : S ∩ T = ∅
  · have hpq := project_inter_empty_of_sources color c d S T hST
    simp only [pairCost, if_pos hST, if_pos hpq]
    omega
  · have hcost : pairCost S T = (S ∪ T).card - 1 := by simp only [pairCost, if_neg hST]
    rw [hcost]
    by_cases hcd : c = d
    · subst d
      have hU : HasBoth color (S ∪ T) := by
        intro c'
        obtain ⟨w, hw, hc⟩ := hS c'
        exact ⟨w, Finset.mem_union_left _ hw, hc⟩
      have hEq : projectColor color c S ∪ projectColor color c T = projectColor color c (S ∪ T) := by
        simp [projectColor, Finset.filter_union]
      have hlt := project_card_lt color c (S ∪ T) hU
      rw [← hEq] at hlt
      have hb := pairCost_le_union (projectColor color c S) (projectColor color c T)
      have hle : (projectColor color c S).card ≤
          (projectColor color c S ∪ projectColor color c T).card :=
        Finset.card_le_card Finset.subset_union_left
      omega
    · have hpq := project_inter_empty_of_colors color c d S T hcd
      have hc := Finset.card_union_add_card_inter (projectColor color c S) (projectColor color d T)
      rw [hpq, Finset.card_empty] at hc
      rw [pairCost, if_pos hpq]
      omega

lemma two_color_projection_build (n : ℕ) (gs : List Gate) (hgs : Ok n gs)
    (color : ℕ → Bool) (c d : Bool) (S T : Finset ℕ)
    (hS : ∀ w ∈ S, w < n + gs.length) (hT : ∀ w ∈ T, w < n + gs.length)
    (hSmixed : HasBoth color S) (hTmixed : HasBoth color T) :
    ∃ (hs : List Gate) (oS oT : Option ℕ), Ok n (gs ++ hs) ∧
      (∀ g ∈ hs, g.op = GateOp.or) ∧ hs.length < pairCost S T ∧
      (∀ w, oS = some w → w < n + (gs ++ hs).length) ∧
      (∀ w, oT = some w → w < n + (gs ++ hs).length) ∧
      ∀ x : List Bool, x.length = n →
        ov (gs ++ hs) x oS = sourceOr gs x (projectColor color c S) ∧
        ov (gs ++ hs) x oT = sourceOr gs x (projectColor color d T) := by
  obtain ⟨hs, oS, oT, hok, hops, hlen, hbS, hbT, heval⟩ :=
    two_or_build n gs hgs (projectColor color c S) (projectColor color d T)
      (fun w hw => hS w (project_subset color c S hw))
      (fun w hw => hT w (project_subset color d T hw))
  refine ⟨hs, oS, oT, hok, hops, ?_, hbS, hbT, heval⟩
  change hs.length = pairCost (projectColor color c S) (projectColor color d T) at hlen
  rw [hlen]
  exact project_pairCost_lt color c d S T hSmixed hTmixed

lemma ao_ok {n : ℕ} (C : Circuit) (hC : TopForm.IsAO2 n C) : Ok n C.gates := by
  intro j hj
  have hm : C.gates[j] ∈ C.gates := List.getElem_mem hj
  obtain ⟨a, b, hin⟩ := List.length_eq_two.mp (hC.2.2 _ hm)
  have heq : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hin' : (gateAt C j).inputs = [a, b] := by rwa [heq]
  refine ⟨(C.gates[j]).op, a, b, ?_, hC.1 _ hm,
    hC.2.1 j hj a (by rw [hin']; simp), hC.2.1 j hj b (by rw [hin']; simp)⟩
  cases hgt : C.gates[j]
  simp only [hgt] at hin ⊢
  cases hin
  rfl

def outputWire (n : ℕ) (gs : List Gate) (o : Option ℕ) : ℕ :=
  o.getD (n + gs.length)

lemma outputWire_eval (n : ℕ) (gs : List Gate) (o : Option ℕ) (x : List Bool)
    (hx : x.length = n) :
    (⟨gs, outputWire n gs o⟩ : Circuit).eval x = ov gs x o := by
  cases o with
  | none =>
    change (run gs x).getD (n + gs.length) false = false
    exact List.getD_eq_default _ _ (by rw [run_length, hx])
  | some w => rfl

lemma two_color_projection_circuits (n : ℕ) (C : Circuit) (hC : TopForm.IsAO2 n C)
    (color : ℕ → Bool) (c d : Bool) (S T : Finset ℕ)
    (hS : ∀ w ∈ S, w < n + C.gates.length) (hT : ∀ w ∈ T, w < n + C.gates.length)
    (hSmixed : HasBoth color S) (hTmixed : HasBoth color T) :
    ∃ (hs : List Gate) (wS wT : ℕ),
      TopForm.IsAO2 n ⟨C.gates ++ hs, wS⟩ ∧ TopForm.IsAO2 n ⟨C.gates ++ hs, wT⟩ ∧
      (∀ g ∈ hs, g.op = GateOp.or) ∧ hs.length < pairCost S T ∧
      ∀ x : Fin n → Bool,
        circuitFun n ⟨C.gates ++ hs, wS⟩ x = sourceOr C.gates (List.ofFn x) (projectColor color c S) ∧
        circuitFun n ⟨C.gates ++ hs, wT⟩ x = sourceOr C.gates (List.ofFn x) (projectColor color d T) := by
  obtain ⟨hs, oS, oT, hok, hops, hlen, _, _, heval⟩ :=
    two_color_projection_build n C.gates (ao_ok C hC) color c d S T hS hT hSmixed hTmixed
  refine ⟨hs, outputWire n (C.gates ++ hs) oS, outputWire n (C.gates ++ hs) oT,
    ok_ao hok, ok_ao hok, hops, hlen, ?_⟩
  intro x
  change (⟨C.gates ++ hs, outputWire n (C.gates ++ hs) oS⟩ : Circuit).eval (List.ofFn x) = _ ∧
    (⟨C.gates ++ hs, outputWire n (C.gates ++ hs) oT⟩ : Circuit).eval (List.ofFn x) = _
  rw [outputWire_eval n _ oS _ (by simp), outputWire_eval n _ oT _ (by simp)]
  exact heval (List.ofFn x) (by simp)

end TwoOrBuild

end PEqualNP.Outside.L_meta_5012
